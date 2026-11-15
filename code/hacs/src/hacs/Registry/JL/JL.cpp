// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception

// Langlandscape JL registration fragment (not upstream HACS; code/hacs/CHANGES.md).  Called once from RegisterAllValidations()
// after the slot-27 fragments (the one-line hook in ValidationRegistry.cpp), so the --list order of the upstream names is unchanged.
// Sources: cmake/jl/JL.cmake.  Every value these validations print is *computed (HACS ReadLocal on a JL lattice)*.
#include "../../ValidationRegistry.h"

uint32_t JLBrandtFreeBlockSpikeValidation();
uint32_t JLBrandtFreeBlockRead();
uint32_t JLBrandtCongruenceSpikeValidation();
uint32_t JLBrandtCongruenceRead();
uint32_t JLQuatCoreValidation();
uint32_t JLBrandtSymValidation();
uint32_t JLLevelValidation();
uint32_t JLTreeW2Validation();
uint32_t JLIharaKValidation();

void RegisterJL() {
    // HJ-6-min: the inline B_11 weight-2 Brandt lattice through LatticeFromFreeZ -> ReadLocal and the own Smith route (Z/5 at ell = 5)
    ValidationRegistry::register_validation("JLBrandtFreeBlockSpikeValidation", &JLBrandtFreeBlockSpikeValidation, ValidationTier::Fast);
    // HJ-6-min: the data-driven read of JL_BRANDT_IN (read-only input hook; arm=off without it); slow, so --all is unaffected
    ValidationRegistry::register_validation("JLBrandtFreeBlockRead", &JLBrandtFreeBlockRead, ValidationTier::Slow);
    // HJ-6b: integral congruence modules L / (L_i (+) L_i^c) per Galois orbit (JlCongruence.h); the inline B_11 fixture (Z/5, Z/5)
    ValidationRegistry::register_validation("JLBrandtCongruenceSpikeValidation", &JLBrandtCongruenceSpikeValidation, ValidationTier::Fast);
    // HJ-6b: the same on JL_BRANDT_IN (read-only input hook; arm=off without it); slow
    ValidationRegistry::register_validation("JLBrandtCongruenceRead", &JLBrandtCongruenceRead, ValidationTier::Slow);
    // WP INT (Lane C): the native quaternion core (Registry/JL/quat), frozen values, fast (JlQuatValidation.cpp)
    ValidationRegistry::register_validation("JLQuatCoreValidation", &JLQuatCoreValidation, ValidationTier::Fast);
    ValidationRegistry::register_validation("JLBrandtSymValidation", &JLBrandtSymValidation, ValidationTier::Fast);
    ValidationRegistry::register_validation("JLLevelValidation", &JLLevelValidation, ValidationTier::Fast);
    ValidationRegistry::register_validation("JLTreeW2Validation", &JLTreeW2Validation, ValidationTier::Fast);
    ValidationRegistry::register_validation("JLIharaKValidation", &JLIharaKValidation, ValidationTier::Fast);
}
