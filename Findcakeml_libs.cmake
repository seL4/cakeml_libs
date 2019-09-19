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

set(CAKEML_LIBS_DIR "${CMAKE_CURRENT_LIST_DIR}" CACHE STRING "")
set(LIBCAKEML_PATH "${CMAKE_CURRENT_LIST_DIR}/libcakeml_helpers.cmake" CACHE STRING "")
set(CAKEML_META_PATH "${CMAKE_CURRENT_LIST_DIR}/meta_utils/meta_utils.cmake" CACHE STRING "")
mark_as_advanced(CAKEML_LIBS_DIR LIBCAKEML_PATH CAKEML_META_PATH)

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(
    cakeml_libs
    DEFAULT_MSG
    CAKEML_LIBS_DIR
    LIBCAKEML_PATH
    CAKEML_META_PATH
)
