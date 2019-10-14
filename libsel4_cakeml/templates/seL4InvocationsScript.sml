(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
open preamble basis utilsTheory seL4Theory;

val _ = new_theory "seL4Invocations";

require basisProg utils seL4;

val _ = ml_prog_update (open_module "SeL4Invocations");

val _ = (append_prog o process_topdecs) `
{{ generated_invocations }}
`;

val _ = ml_prog_update (close_module NONE);
val _ = export_theory ();
