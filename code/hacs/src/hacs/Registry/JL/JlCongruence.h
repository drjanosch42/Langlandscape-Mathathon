// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception

#pragma once
#ifndef REGISTRY_JL_JL_CONGRUENCE_H
#define REGISTRY_JL_JL_CONGRUENCE_H

// ===========================================================================
// Langlandscape JL extension (not upstream HACS; code/hacs/CHANGES.md, WP HJ-6b).  Integral congruence modules of a definite
// Brandt lattice L = Z^h (record langlandscape_brandt/v1, read by hacs_jl::ParseBrandtRecord), at any weight k:
//   * theta = sum c_p T_p (small c_p) with charpoly_Q(theta) squarefree, so T (x) Q = Q[theta];
//   * chi_theta = f_1 ... f_s over Z (nf::factor_monic_over_z): the Galois orbits of eigensystems;
//   * per orbit i: L_i = L cap ker f_i(theta), L_i^c = L cap ker prod_{j != i} f_j(theta), and the congruence module
//     C_i = L / (L_i (+) L_i^c) (Smith invariants, order, factored order);
//   * the ring congruence module (T_i x T_i^c) / T of T = Z[T_p : p in ops] (independent of the lattice L);
//   * the index of Z[T_p : p in ops] in its saturation (T (x) Q) cap End_Z(L) (Smith invariants of its Z-basis in Z^{h^2});
//   * at k = 2 (gammas present): the Smith invariants and determinant of the Gram matrix on L_i of the Hecke-invariant pairing
//     <x, y> = sum_c x_c y_c / w_c, w_c = |Gamma_c| / 2 (rational; printed as reduced fractions).
// All arithmetic is exact (nf::BigInt); dense, h <= ~40.  Every value is *computed (HACS-native JL module)*.
// Column convention (HJ-B0 Sec. 2): T_p b_j = sum_i F_ij b_i, i.e. T_p acts on coordinate columns by F.
// For k > 2 the record's lattice is A Hecke-stable lattice (brandt_symn_int/v1), not a canonical one: C_i depends on it.
// ===========================================================================

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "../../NumberField/BigInt.h"
#include "JlFreeBlockRead.h"

namespace hacs_jl {

using ZMat = std::vector<std::vector<nf::BigInt>>;   // row-major

// Exact integer linear algebra (exposed for the validation).
std::vector<nf::BigInt> CharpolyZ(const ZMat& A);                 // monic, constant term first (Faddeev-LeVerrier, exact)
ZMat HermiteRows(ZMat rows);                                       // reduced row HNF, zero rows dropped (canonical)
ZMat KernelZ(const ZMat& A);                                       // a Z-basis (rows) of {v in Z^n : A v = 0} (saturated)
std::vector<nf::BigInt> SmithInvariants(ZMat A);                   // the nonzero invariant factors d_1 | d_2 | ..., all > 0

struct PrimePower { nf::BigInt p; unsigned e = 0; };
struct Factored {
    std::vector<PrimePower> pp;       // trial division (p < 2^20)
    nf::BigInt cofactor = 1;          // > 1: no factor < 2^20
    bool cofactor_prp = false;        // Miller-Rabin, 16 bases
    std::string text() const;         // "2^3 * 5 * [cofactor]"
};
Factored FactorTrial(const nf::BigInt& n);

struct CongOrbit {
    std::vector<nf::BigInt> f;        // monic, constant term first
    bool eisenstein = false;          // k = 2, deg 1, the constant vector in L_i
    uint32_t rank_i = 0, rank_ic = 0;
    std::vector<nf::BigInt> smith;    // invariants of C_i (the nontrivial ones, > 1)
    nf::BigInt order = 1;
    Factored order_f;
    bool gram_ran = false;
    std::vector<std::string> gram_smith;   // reduced fractions
    std::string gram_det;
    Factored gram_det_num_f;
    // charpoly_Z of T_p restricted to L_i, for the first three ops p prime to N (the GL_2-side comparison key: JL preserves a_p)
    std::vector<std::pair<uint32_t, std::vector<nf::BigInt>>> tp_on_Li;
    // the ring congruence module (T_i x T_i^c) / T for T = Z[T_p : p in ops] (lattice-independent; T_i = the image in End(L_i))
    bool ring_ran = false;
    uint32_t ring_rank_i = 0, ring_rank_ic = 0;
    std::vector<nf::BigInt> ring_smith;
    nf::BigInt ring_order = 1;
    Factored ring_order_f;
};

struct CongCell {
    std::string where;
    uint32_t D = 0, M = 1, k = 2, N = 0, h = 0;
    std::string status;               // "ok" | "rank0" | "no_squarefree_theta" | "bad_decomposition"
    std::vector<std::pair<uint32_t, int>> theta;   // (p, c_p)
    std::string theta_text;
    uint32_t theta_tries = 0;
    // Hecke ring Z[T_p : p in ops]
    uint32_t hecke_rank = 0;
    std::vector<nf::BigInt> hecke_smith;   // nontrivial invariants of the basis matrix
    nf::BigInt hecke_index = 1;
    Factored hecke_index_f;
    bool selfadjoint = false;         // k = 2: F_ij w_j = F_ji w_i on every op (w = gammas)
    bool gram_possible = false;
    uint64_t mazur_num = 0;           // num((N-1)/12) at M = 1
    std::vector<CongOrbit> orbits;
    double seconds = 0;
    std::string json(size_t orbit) const;   // one @@JL_CONG payload (schema jl_congruence/v1); orbit = SIZE_MAX for a cell line
};

CongCell RunJlCongruence(const BrandtRecord& R);

// The prime-to-6 part of n (Mazur's comparison is up to the 2, 3 parts, R3).
nf::BigInt PrimeTo6(nf::BigInt n);

}  // namespace hacs_jl

#endif
