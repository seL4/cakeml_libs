<!--
     Copyright 2018, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

libvirtqueue
============

**_This implementation is currently a work in progress_**

This directory contains a CakeMl library wrapper over the seL4 virtqueue library
(see <https://github.com/SEL4PROJ/projects_libs/tree/master/libvirtqueue>).

This library is templated by CMake in order to define a linear chain of CakeML
libraries. To use libvirtqueue in your CakeML application, use the `CakeMLPP`
helper (defined in `libcakeml_helpers.cmake`) in your application CMake file
to correctly link the virtqueue library i.e.

```cmake
include(path/to/libcakeml_helpers.cmake)
CakeMLPP(destination_directory
    ${CMAKE_SOURCE_DIR}/projects/cakeml_libs/cakeml_libraries/libvirtqueue/virtqueueScript.sml
)
DeclareCAmkESComponent(CakeMLApp
    CAKEML_SOURCES cakemlAppScript.sml
    ${CMAKE_CURRENT_BINARY_DIR}/destination_directory/virtqueueScript.sml
    LIBS vswitch
)
```

Caveats
-------

This library is currently intended to be used in a CAmkES-based system. This results
in assumptions of a CAmkES run-time within the library implementation.
