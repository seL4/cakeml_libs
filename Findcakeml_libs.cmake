#
# Copyright 2019, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

set(CAKEML_LIBS_DIR "${CMAKE_CURRENT_LIST_DIR}" CACHE STRING "")
set(LIBCAKEML_PATH "${CMAKE_CURRENT_LIST_DIR}/libcakeml_helpers.cmake" CACHE STRING "")
set(CAKEML_META_PATH "${CMAKE_CURRENT_LIST_DIR}/meta_utils/meta_utils.cmake" CACHE STRING "")
mark_as_advanced(CAKEML_LIBS_DIR LIBCAKEML_PATH CAKEML_META_PATH)

macro(cakeml_libs_import_libsel4_cakeml)
	add_subdirectory(${CAKEML_LIBS_DIR}/libsel4_cakeml libsel4_cakeml)
endmacro()

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(
    cakeml_libs
    DEFAULT_MSG
    CAKEML_LIBS_DIR
    LIBCAKEML_PATH
    CAKEML_META_PATH
)
