# SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
# SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception

# Langlandscape JL fragment (not upstream HACS; code/hacs/CHANGES.md), included by the one-line hook in CMakeLists.txt after the
# slot-27 fragments.  OC_ENABLE_JL defaults ON in the Langlandscape fork (so the HJ-6-min spike is built); OFF compiles only an
# empty RegisterJL() and the --list is the upstream 294.  No switch changes a computed value: the JL code adds names, changes none.
option(OC_ENABLE_JL "Langlandscape: compile the Jacquet-Langlands extension (src/hacs/Registry/JL/)" ON)
message(STATUS "OC_ENABLE_JL=${OC_ENABLE_JL}")
if(OC_ENABLE_JL)
    target_sources(cohomology_app PRIVATE
        src/hacs/Registry/JL/JL.cpp
        src/hacs/Registry/JL/JlFreeBlockRead.cpp
        src/hacs/Registry/JL/JlFreeBlockValidation.cpp
        src/hacs/Registry/JL/JlCongruence.cpp
        src/hacs/Registry/JL/JlCongruenceValidation.cpp
        # WP INT (Lane C): the native quaternion core (quat/SOURCES.txt) and its fast validations. Only what the validations
        # need: no TreeK, no tools, no tests. NumberField BigInt/BigRational are already in the binary (not listed again).
        src/hacs/Registry/JL/JlQuatValidation.cpp
        src/hacs/Registry/JL/quat/Quat.cpp
        src/hacs/Registry/JL/quat/Lattice.cpp
        src/hacs/Registry/JL/quat/Order.cpp
        src/hacs/Registry/JL/quat/ClassSet.cpp
        src/hacs/Registry/JL/quat/Brandt2.cpp
        src/hacs/Registry/JL/quat/BrandtSym.cpp
        src/hacs/Registry/JL/quat/Tree.cpp
        src/hacs/Registry/JL/quat/Level.cpp
        src/hacs/Registry/JL/quat/BrandtLevel.cpp
    )
else()
    target_sources(cohomology_app PRIVATE src/hacs/Registry/JL/JLOff.cpp)
endif()
