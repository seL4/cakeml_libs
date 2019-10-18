#!/usr/bin/env python3
#
# Copyright 2019, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

import os
import copy
import operator
import itertools
import xml.dom.minidom
from argparse import ArgumentParser
import sys
from functools import reduce
import jinja2
from jinja2 import Template
from pycparser import c_parser, c_ast
import syscall_stub_gen


# Build a CakeML expression to reduce a list of expressions with a binary function
# Associates right, so: build_expression_tree_r(f, [a, b, c]) = f a (f b c)
def build_expression_tree_r(func_name, args):
    if len(args) == 0:
        raise Exception("we require at least one argument")
    if len(args) == 1:
        return args[0]
    else:
        return "{} ({}) ({})".format(func_name, args[0], build_expression_tree_r(func_name, args[1:]))

# Return a word-sized expression for a CakeML value


def cakeml_word_expression(typ, var_name, target_offset=0):
    if typ.name == "seL4_Bool":
        return "Utils.bool_to_word64 {} {}".format(var_name, target_offset)
    elif typ.name == "seL4_Word":
        # Pass word parameters in directly. This means that callers need to provide word64s.
        return "{}".format(var_name)
    else:
        assert target_offset % 8 == 0, "value not byte-aligned, offset: %s" % target_offset
        assert target_offset + typ.size_bits <= typ.wordsize, "value must fit inside a word"
        if typ.size_bits == 8:
            return "Word64.<< (Word64.fromInt (Word8.toInt {})) {}".format(var_name, target_offset)
        else:
            return "Word64.<< {} {}".format(var_name, target_offset)


def generate_marshal_expressions_cakeml(params, num_mrs, structs, wordsize):
    """
    Generate marshalling expressions for the given set of inputs.

    We return a list of expressions; one expression per word required
    to marshal all the inputs.
    """

    def generate_param_code(param, first_bit, num_bits, word_array, wordsize):
        """
        Generate code to marshal the given parameter into the correct
        location in the message.

        'word_array' is an array of the final contents of the message.
        word_array[k] contains what should be placed in the k'th message
        register, and is an array of expressions that will (eventually)
        be bitwise-or'ed into it.
        """

        target_word = first_bit // wordsize
        target_offset = first_bit % wordsize

        # XXX: hack for object type in seL4_Untyped_Retype
        if param.name == "type_":
            expr = "cdl_obj_id_mapping {}".format(param.name)
            word_array[target_word].append(expr)
            return

        # Double word type
        if param.type.double_word:
            raise Exception("Support for CakeML double word params is not implemented")

        # Single word or less?
        if num_bits <= wordsize:
            expr = cakeml_word_expression(param.type, param.name, target_offset)
            word_array[target_word].append(expr)
            return

        # Multiword array (treat it as a list of words)
        assert target_offset == 0
        num_words = num_bits // wordsize
        for i in range(num_words):
            expr = "list_nth {} {}".format(param.name, i)
            word_array[target_word + i].append(expr)

    # Get their marshalling positions
    positions = syscall_stub_gen.get_parameter_positions(params, wordsize)

    # Generate marshal code.
    words = [[] for _ in range(num_mrs, syscall_stub_gen.MAX_MESSAGE_LENGTH)]
    for (param, first_bit, num_bits) in positions:
        generate_param_code(param, first_bit, num_bits, words, wordsize)

    # Return list of expressions.
    return [build_expression_tree_r("Word64.orb", x) for x in words if len(x) > 0]


def generate_unmarshal_expressions_cakeml(params, wordsize):

    def unmarshal_single_param(first_bit, num_bits, wordsize):
        """
        Unmarshal a single parameter.
        """
        first_word = first_bit // wordsize
        bit_offset = first_bit % wordsize

        # Multiword type?
        if num_bits > wordsize:
            result = []
            for x in range(num_bits // wordsize):
                result.append("%%(w%d)s" % (x + first_word))
            return result

        # Otherwise, bit packed.
        if num_bits == wordsize:
            return ["%%(w%d)s" % first_word]
        elif bit_offset == 0:
            print("unsupported: unmarshalling a value smaller than a word (offset 0)")
            return []
        else:
            print("unsupported: unmarshalling a value smaller than a word")
            return []

    # Get their marshalling positions
    positions = syscall_stub_gen.get_parameter_positions(params, wordsize)

    # Generate the unmarshal code.
    results = []
    for (param, first_bit, num_bits) in positions:
        results.append((param, unmarshal_single_param(first_bit, num_bits, wordsize)))
    return results


CAKEML_WHITELIST = {
    "seL4_Untyped_Retype",
    "seL4_IRQControl_Get",
    "seL4_IRQHandler_SetEndpoint",
    "seL4_TCB_Configure",
    "seL4_TCB_Resume",
    "seL4_TCB_SetSchedParams",
    "seL4_TCB_WriteRegisters",
    "seL4_ASIDPool_Assign",
    "seL4_PageTable_Map",
    "seL4_Page_Map",
    "seL4_CNode_Move",
    "seL4_CNode_Mutate",
    "seL4_CNode_Mint",
    "seL4_CNode_Copy"
}

CAKEML_SEEN = {x: False for x in CAKEML_WHITELIST}

# Partial list of CakeML keywords for use during escaping, expand if necessary
CAKEML_KEYWORDS = {
    "type",
    "datatype"
}


class TemplateParam:
    def __init__(self, fn_name, name, typ, offset, size, output=False):
        self.name = TemplateParam.escape_name(name)
        self.type = TemplateParam.perform_type_mapping(fn_name, name, typ)
        self.offset = offset
        self.size = size
        self.output = output

    @staticmethod
    def escape_name(var_name):
        """Munge a name so that it's safe for use as a CakeML identifier

        Reserved words and identifiers starting with _ are munged
        """
        if var_name in CAKEML_KEYWORDS:
            return "{}_".format(var_name)
        elif var_name.startswith("_"):
            return "{}_".format(var_name.lstrip("_"))
        else:
            return var_name

    @staticmethod
    def perform_type_mapping(fn_name, name, typ):
        "Fix up types that are mismatched with the Isabelle system initialiser"
        if (fn_name == "seL4_IRQControl_Get" and name == "depth" or
            "seL4_CNode_" in fn_name and name == "dest_depth" or
                "seL4_CNode_" in fn_name and name == "src_depth"):
            new_typ = copy.deepcopy(typ)
            new_typ.size_bits = new_typ.wordsize
            new_typ.name += " [modified to Word64]"
            return new_typ
        elif typ is not None and typ.name == "seL4_CapRights_t":
            new_typ = copy.deepcopy(typ)
            new_typ.size_bits = 8
            new_typ.name += " [modified to Word8]"
            return new_typ
        else:
            return typ


def generate_cakeml(inv_label_mapping, template_env, arch, wordsize, interface_name, method_name, method_id, input_params, output_params, structs, use_only_ipc_buffer, comment):
    fn_name = "{}_{}".format(interface_name, method_name)

    # XXX: remove the architecture from the function name, to match DSpec
    if fn_name == "seL4_ARM_ASIDPool_Assign":
        fn_name = "seL4_ASIDPool_Assign"
    elif fn_name == "seL4_ARM_PageTable_Map":
        fn_name = "seL4_PageTable_Map"
    elif fn_name == "seL4_ARM_Page_Map":
        fn_name = "seL4_Page_Map"
    # XXX: this is really unnecessary, someone should just rename the DSpec function
    elif fn_name == "seL4_IRQHandler_SetNotification":
        fn_name = "seL4_IRQHandler_SetEndpoint"  # here we still worship the old gods

    if fn_name not in CAKEML_WHITELIST:
        return ""

    CAKEML_SEEN[fn_name] = True

    template = template_env.get_template("invocation.sml")

    num_mrs = 0 if use_only_ipc_buffer else syscall_stub_gen.MESSAGE_REGISTERS_FOR_ARCH[arch]

    # Split out cap parameters and standard parameters
    all_params = [TemplateParam(fn_name, param.name, param.type, 0, param.type.size_bits // 8)
                  for param in input_params]
    standard_params = [TemplateParam(fn_name, param.name, param.type, 0, param.type.size_bits // 8)
                       for param in input_params if not isinstance(param.type, syscall_stub_gen.CapType)]
    cap_params = [TemplateParam(fn_name, param.name, param.type, 0, param.type.size_bits // 8)
                  for param in input_params if isinstance(param.type, syscall_stub_gen.CapType)]
    return_params = [TemplateParam(fn_name, param.name, param.type, 0, param.type.size_bits // 8)
                     for param in output_params]

    input_expressions = generate_marshal_expressions_cakeml(
        standard_params, num_mrs, structs, wordsize)

    output_expressions_raw = generate_unmarshal_expressions_cakeml(output_params, wordsize)

    # XXX: hack for polymorphic list support (the Isabelle code generator uses its own list type)
    if len([p for p in input_params if p.type.size_bits > wordsize]) != 0:
        all_params.insert(0, TemplateParam(fn_name, "list_nth", None, None, None))

    # XXX: hack for Untyped_Retype to map Isabelle cdl_object_type into a word64
    elif fn_name == "seL4_Untyped_Retype":
        all_params.insert(0, TemplateParam(fn_name, "cdl_obj_id_mapping", None, None, None))

    source_words = {}
    for i in range(syscall_stub_gen.MAX_MESSAGE_LENGTH):
        if i < num_mrs:
            source_words["w%d" % i] = "mr%d" % i
        else:
            source_words["w%d" % i] = "seL4_GetMR(%d)" % i

    output_expressions = []
    for (param, word_expr) in output_expressions_raw:
        output_expressions.append((param.name, word_expr[0] % source_words))

    return template.render({
        "name": fn_name,
        "all_params": all_params,
        "standard_params": standard_params,
        "cap_params": cap_params,
        "input_expressions": input_expressions,
        "output_expressions": output_expressions,
        "return_params": return_params,
        "method_id": method_id,
        "method_id_num": inv_label_mapping[method_id],
        "num_mrs": num_mrs,
        "wordsize": wordsize,
        # TODO: CakeML v2 doesn't support tuple assignment, which makes
        # supporting multiple return values kind of annoying. We don't need
        # them for now so we don't bother.
        "cakeml_v2_compatible": True,
    })


NUM_ENUMS = 3


def enum_decl_named(name, enum_decls):
    return [decl for decl in enum_decls if decl.type.name == name][0]


def extract_invocation_labels(source_string):
    "Extract a mapping from invocation enum variant names to their integer values"
    parser = c_parser.CParser()
    ast = parser.parse(source_string, filename="<source string>")

    enum_decls = [decl for decl in ast.ext if type(getattr(decl, "type", None)) == c_ast.Enum]

    invocation_label = enum_decl_named("invocation_label", enum_decls)
    sel4_arch_invocation_label = enum_decl_named("sel4_arch_invocation_label", enum_decls)
    arch_invocation_label = enum_decl_named("arch_invocation_label", enum_decls)

    mapping = {}

    for (i, variant) in enumerate(invocation_label.type.values.enumerators):
        mapping[variant.name] = i

    # seL4 arch invocation labels should be offset by the number of invocations that came before
    sel4_ai_offset = mapping["nInvocationLabels"]
    for (i, sel4_ai) in enumerate(sel4_arch_invocation_label.type.values.enumerators):
        mapping[sel4_ai.name] = sel4_ai_offset + i

    ai_offset = mapping["nSeL4ArchInvocationLabels"]
    for (i, ai) in enumerate(arch_invocation_label.type.values.enumerators):
        mapping[ai.name] = ai_offset + i

    return mapping


def extract_invocation_labels_from_file(filename):
    """Extract the invocation label mapping from a kernel_all_pp.c source file

    This function is a bit fragile, it will break if there are other definitions between
    the three relevant enum definitions.
    """
    with open(filename, "r") as f:
        return extract_invocation_labels(f.read())


def generate_stub_file(arch, wordsize, input_files, output_file, invocation_source_file, use_only_ipc_buffer, mcs):
    """
    Generate a header file containing system call stubs for seL4.
    """

    # Ensure architecture looks sane.
    if arch not in syscall_stub_gen.WORD_SIZE_BITS_ARCH.keys():
        raise Exception("Invalid architecture.")

    data_types = syscall_stub_gen.init_data_types(wordsize)
    arch_types = syscall_stub_gen.init_arch_types(wordsize)

    # Parse XML
    methods = []
    structs = []
    for infile in input_files:
        method, struct, _ = syscall_stub_gen.parse_xml_file(infile, data_types + arch_types[arch])
        methods += method
        structs += struct

    cakeml_code = []

    # Make Jinja template environment
    template_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "templates")
    template_env = jinja2.Environment(
        trim_blocks=True,
        lstrip_blocks=True,
        loader=jinja2.FileSystemLoader(searchpath=template_dir)
    )

    if invocation_source_file != None:
        inv_label_mapping = extract_invocation_labels_from_file(invocation_source_file)
    else:
        inv_label_mapping = {}

    for (interface_name, method_name, method_id, inputs, outputs, condition, comment) in methods:
        # We don't have CPP directives in CakeML, so apply MCS filter now
        if (condition == 'defined(CONFIG_KERNEL_MCS)') == mcs:
            cakeml_code.append(generate_cakeml(inv_label_mapping, template_env, arch, wordsize, interface_name, method_name,
                                           method_id, inputs, outputs, structs, use_only_ipc_buffer, comment))

    # Check we've seen all the CakeML functions we need
    for (fn_name, seen) in CAKEML_SEEN.items():
        if not seen:
            print("WARNING: no implementation for {} generated".format(fn_name))

    # Write the output
    with open(output_file, "w") as f:
        generated_invocations = "".join(cakeml_code)
        template = template_env.get_template("seL4InvocationsScript.sml")
        f.write(template.render({"generated_invocations": generated_invocations}))


def process_args():
    usage_str = """
    %(prog)s [OPTIONS] [FILES] """
    epilog_str = """

    """
    parser = ArgumentParser(description='seL4 System Call Stub Generator.',
                            usage=usage_str,
                            epilog=epilog_str)
    parser.add_argument("-o", "--output", dest="output", default="/dev/stdout",
                        help="Output file to write stub to. (default: %(default)s).")
    parser.add_argument("--invocation-source", dest="invocation_source", default=None,
                        help="Pre-processed c file to extract invocation labels from.")
    parser.add_argument("-b", "--buffer", dest="buffer", action="store_true", default=False,
                        help="Use IPC buffer exclusively, i.e. do not pass syscall arguments by registers. (default: %(default)s)")
    parser.add_argument("-a", "--arch", dest="arch", required=True, choices=syscall_stub_gen.WORD_SIZE_BITS_ARCH,
                        help="Architecture to generate stubs for.")
    parser.add_argument("--mcs", dest="mcs", action="store_true",
                        help="Generate MCS api.")

    parser.add_argument("-w", "--word-size", dest="wsize", type=int,
                        help="Word size(in bits), for the platform.")

    parser.add_argument("files", metavar="FILES", nargs="+",
                        help="Input XML files.")

    return parser


def main():

    parser = process_args()
    args = parser.parse_args()

    # Generate the stubs.
    generate_stub_file(args.arch, args.wsize, args.files, args.output,
                       args.invocation_source, args.buffer, args.mcs)


if __name__ == "__main__":
    sys.exit(main())
