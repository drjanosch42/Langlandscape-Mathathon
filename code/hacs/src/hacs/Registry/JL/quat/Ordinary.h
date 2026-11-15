// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-9, Lane C): the Lambda-adic definite side on HJ-3's p-tower (Level.h) -- U_p at the level prime, the
// ordinary projector e, ranks over Z/p^m[Delta_s].
//
// (O1) U_p (homological, columns = images; = ordinary/tower.py, phicomb.py): for a point (c, v) of X_B(U_1(M p^s) cap U_0(N0)),
//        U_p [c, v] = sum_{lines lam of e I_c / p I_c, lam != <v mod p>} [c', v A_lam],
//      J_lam = O w_lam + p I_c (w_lam lifting lam; = L_{y varpi_j} p), J_lam = I_{c'} mu / N_{c'}, A_lam = the matrix of
//      v -> v conj(mu) / N_c (LevelModel::move; Level.h (L4)), applied to the U_1 vector and to the U_0 line alike.
//      (Row 2 of varpi_j^{-1} is (0, 1), so the level datum is the same vector v in the new lattice; tower.py.)
// (O2) Diamonds Delta_s = (1 + pZ)/(1 + p^s Z), generator <1 + p>: v -> (1 + p)^{-1} v mod p^s, identity mod M and on the
//      U_0 line (Level.h (L6)).
// (O3) e by image stabilisation of U_p^k mod p^m (ordinary/proj.py): k = 1, 2, 4, ...; A = U^k; pivots I, J of A mod p,
//      C = A[I, J]^{-1} A[I, :]; stable iff A = A_J C and C A_J is invertible mod p; then e = A_J (C A_J)^{-1} C.
//      U^k is built by sparse-times-dense products (U has p nonzeros per column).
// (O4) Rank over Z/p^m[Delta] (proj.group_ring_rank): g = r - rk_p((D - 1) A_J), free iff r = g |Delta|.
//      Coinvariant route (for large s, no e on the full module): if Delta acts freely, M = Z/p^m[S] is free over the local
//      ring R = Z/p^m[Delta], eM is a direct summand hence R-free, and g = dim_{F_p} e(M / (p, D - 1)) = the ordinary rank of
//      U_p on F_p[S / Delta] (U_p commutes with Delta; e is a polynomial in U_p). This is exact, not a bound.
#pragma once

#include "Level.h"

namespace hacs_jl {

// sparse integer operator on Z[cells]: cols[j] = list of (row, coefficient)
struct SpOp {
    int n = 0;
    std::vector<std::vector<std::pair<int, i64>>> cols;
};

// U_p on the cells of L (all stabilisers must be trivial; checked); p prime, p | N1 of L
SpOp up_operator(const LevelSet& L, i64 p);
// U'_p (tower.py Up_prime: representatives [[1, 0], [p^s j, p]], j = 0..p-1; homological). Lattice form: J = O v + p I_c (the
// line <v mod p>), L' = J / p = I_{c'} g, g = mu / (p N_{c'}); at p the datum is w = (v - p^s j r1) / p (r1 any complement of v
// mod p; the sum over j does not depend on it), moved by w g^{-1} = (v - p^s j r1) conj(mu) / (p N_c); at the primes of M the
// datum moves by v conj(mu) / N_c as for U_p. The model modulus must be divisible by M p^{s+1}; N1 = M p^s.
SpOp up_prime_operator(const LevelSet& L, i64 p, int s, i64 M);
// <d>_M: v -> u v with u = 1 mod p^s, d^{-1} mod M (tower.py diamond_M)
std::vector<int> diamond_M_perm(const LevelSet& L, i64 p, int s, i64 M, i64 d);
// the diamond permutation v -> u v on the U_1 vector, u = (d^{-1} mod p^s) and 1 mod M (N1 = M p^s)
std::vector<int> diamond_perm(const LevelSet& L, i64 p, int s, i64 M, i64 d);

// dense matrices over Z/q
struct DM {
    int r = 0, c = 0;
    std::vector<i64> a;
    i64& at(int i, int j) { return a[(size_t)i * c + j]; }
    i64 at(int i, int j) const { return a[(size_t)i * c + j]; }
};
DM dense(const SpOp& U, i64 q);
DM transpose(const DM& A);
DM mul(const DM& A, const DM& B, i64 q);
DM sp_mul(const SpOp& U, const DM& A, i64 q);  // U A
int rank_mod_p(const DM& A, i64 p);

struct Projector {
    DM e, basis, coord;  // e = basis * coord, coord * basis = 1_r
    int rank = 0, k = 0;
};
Projector ordinary_projector(const DM& T, i64 p, int m);  // T dense
Projector ordinary_projector(const SpOp& U, i64 p, int m);

struct GroupRank {
    int rank_Zp = 0, generators = 0, order = 1;
    bool free = true;
};
GroupRank group_ring_rank(const Projector& P, const std::vector<int>& Dperm, int order, i64 p);
// the coinvariant route (O4): ordinary rank mod p of U_p on F_p[S / <D>]
struct CoinvRank {
    int orbits = 0, generators = 0;
    bool delta_free = true;     // every orbit has length |Delta| (= order)
    std::vector<int> orbit_of;  // cell -> orbit
    Projector e_bar;            // ordinary projector of U_p on F_p[S / Delta]
};
CoinvRank coinvariant_rank(const SpOp& U, const std::vector<int>& Dperm, i64 p, int order);
// U D == D U for the permutation D (exact, sparse)
bool commutes_with_perm(const SpOp& U, const std::vector<int>& D);

}  // namespace hacs_jl
