<!--
     Copyright 2018, Data61
     Commonwealth Scientific and Industrial Research Organisation (CSIRO)
     ABN 41 687 119 230.

     This software may be distributed and modified according to the terms of
     the BSD 2-Clause license. Note that NO WARRANTY is provided.
     See "LICENSE_BSD2.txt" for details.

     @TAG(DATA61_BSD)
-->
libvirtqueue
-------------

**_This implementation is currently a work in progress_**

This directory contains a CakeMl library wrapper over the seL4 virtqueue library
(see https://github.com/SEL4PROJ/projects_libs/tree/master/libvirtqueue).

This library is templated by CMake in order to define a linear chain of CakeML
libraries. To use libvirtqueue in your CakeML application, use the `CakeMLPP`
helper (defined in `libcakeml_helpers.cmake`) in your application CMake file
to correctly link the virtqueue library i.e.

```
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
--------

This library is currently intended to be used in a CAmkES-based system. This results
in assumptions of a CAmkES run-time within the library implementation.
