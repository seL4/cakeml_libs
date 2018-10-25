#
# Copyright 2018, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

cmake_minimum_required(VERSION 3.8.2)

# src_dir - path to meta_utils directory
# output_dir - path relative to the build directory to copy the meta_utils to
# target_name - name to use for the target that initialises the meta utils library
# target_files_var - variable name to use to store the list of meta utils files that should
#                    be depended upon by the Holmake build
# output_dir_var - variable name to use to store the name of the created output directory
#                  which should be added to the Holmakefile's INCLUDES path
function(DeclareCakeMLMetaUtils src_dir output_dir target_name target_files_var output_dir_var)
    set(abs_output_dir "${CMAKE_CURRENT_BINARY_DIR}/${output_dir}")
    set(holmakefile_src "${src_dir}/Holmakefile")
    set(camkes_utils_src "${src_dir}/camkesUtils.sml")
    set(holmakefile_output "${abs_output_dir}/Holmakefile")
    set(camkes_utils_output "${abs_output_dir}/camkesUtils.sml")
    add_custom_command(OUTPUT ${holmakefile_output} ${camkes_utils_output}
        COMMAND ${CMAKE_COMMAND} -E copy_if_different ${holmakefile_src} ${holmakefile_output}
        COMMAND ${CMAKE_COMMAND} -E copy_if_different ${camkes_utils_src} ${camkes_utils_output}
        VERBATIM
        DEPENDS ${holmakefile_src} ${camkes_utils_src}
    )

    # Create custom target for copy command
    add_custom_target(${target_name} DEPENDS ${holmakefile_output} ${camkes_utils_output})

    set(${target_files_var} ${holmakefile_output} ${camkes_utils_output} PARENT_SCOPE)
    set(${output_dir_var} ${abs_output_dir} PARENT_SCOPE)
endfunction()
