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

cmake_minimum_required(VERSION 3.7.2)

project(libsel4_cakeml NONE)
find_package(seL4 REQUIRED)

set(filter_invocation_cfile gen_invocation_labels.c)
file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/${filter_invocation_cfile}.in "
#include <autoconf.h>
#include <sel4/invocation.h>
")
add_custom_command(
    OUTPUT ${filter_invocation_cfile}
    DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${filter_invocation_cfile}.in
    COMMAND
        ${CMAKE_C_COMPILER} -E -P "-I$<JOIN:$<TARGET_PROPERTY:sel4,INCLUDE_DIRECTORIES>,;-I>" - >
        ${filter_invocation_cfile} < ${filter_invocation_cfile}.in COMMAND_EXPAND_LISTS
    DEPENDS sel4
)

set(output seL4InvocationsScript.sml)
set(script_file seL4InvocationsScript.sml)
set(gen_script ${CMAKE_CURRENT_LIST_DIR}/gen_cakeml_invocations.py)
if(KernelIsMCS)
    set(mcs --mcs)
endif()
if(LibSel4StubsUseIPCBufferOnly)
    set(buffer "--buffer")
endif()

set(libsel4_source ${KERNEL_PATH}/libsel4)
set(
    interface_xmls
    "${libsel4_source}/sel4_arch_include/${KernelSel4Arch}/interfaces/sel4arch.xml"
    "${libsel4_source}/arch_include/${KernelArch}/interfaces/sel4arch.xml"
    "${libsel4_source}/include/interfaces/sel4.xml"
)
add_custom_command(
    OUTPUT ${output}
    COMMAND
        PYTHONPATH=${libsel4_source}/tools "${PYTHON3}" "${gen_script}" ${buffer} ${mcs} -a
        "${KernelSel4Arch}"
        --word-size ${KernelWordSize} -o ${output}
        --invocation-source ${CMAKE_CURRENT_BINARY_DIR}/${filter_invocation_cfile} ${interface_xmls}
    DEPENDS
        ${CMAKE_CURRENT_BINARY_DIR}/${filter_invocation_cfile}
        sel4
        ${interface_xmls}
        templates/invocation.sml
        templates/seL4InvocationsScript.sml
        ${gen_script}
    COMMENT "Generate ${output}"
    VERBATIM
)

add_custom_target(libsel4_cakeml DEPENDS ${output} sel4)
set_property(TARGET libsel4_cakeml PROPERTY FILE_PATH "${CMAKE_CURRENT_BINARY_DIR}")
