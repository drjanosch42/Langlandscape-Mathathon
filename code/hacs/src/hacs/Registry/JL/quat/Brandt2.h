// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-2, weight-2 part of HJ-4): Brandt matrices T_p, p prime not dividing D, on the class set of a maximal
// order, in the order of ClassSet's enumeration.
//
// Convention (binding, = freeblockz-export-format.md section 2 = brandt.py):
//   B[i][j] = #{ p-neighbours I_i alpha + p I_i of I_i lying in class j }   (row sums p + 1)
//   M = Z-valued functions on X_B, basis b_j = 1_{c_j};  T_p b_j = sum_i F_ij b_i  with  F = B  (no transpose).
//   Weighted symmetry: |Gamma_j| F_ij = |Gamma_i| F_ji.
// Storage: F flat, row-major, F[i*r + j].
//
// Two independent routes:
// * "neighbours": the p+1 neighbours of each class, identified by qf_theta + exact test (ClassSet::identify);
// * "theta_pairs": B(n)[i][j] = #{x in conj(I_i) I_j : nrd x = n N_i N_j} / |Gamma_j|, all n <= X at once, from one
//   Fincke-Pohst run per unordered pair (i, j). (J = I_j alpha subset I_i with nrd(J) = n N_i <=> N_j alpha in
//   conj(I_j) I_i of nrd n N_i N_j; alpha is determined up to O_r(I_j)^x.) For prime n this is the Brandt matrix
//   above; the self-test checks that the two routes agree.
#pragma once

#include "ClassSet.h"

#include <map>
#include <optional>

namespace hacs_jl {

using Mat = std::vector<i64>;  // r x r, row-major

Mat brandt_neighbours(const ClassSet& C, i64 p);
std::map<i64, Mat> brandt_theta_pairs(const ClassSet& C, const std::vector<i64>& ns);

// checks
bool row_sums_ok(const Mat& F, int r, i64 value);
bool weighted_symmetric(const Mat& F, const std::vector<int>& gammas);
Mat matmul(const Mat& A, const Mat& B, int r);  // exact (i128 accumulation, checked to fit i64)
bool commute(const Mat& A, const Mat& B, int r);

// HACS MatrixFnv text: rows joined by ';', entries by ',', decimal (freeblockz-export-format.md section 4)
std::string matrix_text(const Mat& F, int r);
u64 matrix_fnv(const Mat& F, int r);

// permutation pi (our class pi[i] <-> reference class i) with ours[pi i][pi k] = ref[i][k] for every op simultaneously
// and gamma_ours[pi i] = gamma_ref[i]; backtracking search. Empty optional if none exists.
// max_nodes > 0 bounds the search (HJ-4b audit m3): if the bound is hit, *exhausted (if given) is set to true and
// nullopt is returned, so a caller can fail loudly instead of hanging.
std::optional<std::vector<int>> match_permutation(const std::vector<Mat>& ours, const std::vector<Mat>& ref, int r,
                                                  const std::vector<int>& gamma_ours, const std::vector<int>& gamma_ref,
                                                  u64 max_nodes = 0, bool* exhausted = nullptr);

// Rank of Q[T_p : p in ops] acting on Q^r: d = number of distinct joint eigen-characters (the algebra is commutative and
// semisimple, so d <= r). Computed as dim of the cyclic span A v mod the prime 2^31 - 1 (a random v): this is a lower
// bound for d, so when it returns r, d = r exactly ("exact_by_bound"); otherwise the value is a mod-p lower bound.
struct AlgebraDim {
    int dim = 0;
    bool exact = false;
};
AlgebraDim algebra_dim(const std::vector<Mat>& ops, int r);

std::vector<int> gammas_of(const ClassSet& C);

// Canonical class order of langlandscape_brandt/v2 (binding, Lane A spec; k = 2): classes sorted ascending,
// lexicographically, on (K1, K2) with
//   K1 = |Gamma_c| = |O_r(I_c)^x| including -1,
//   K2 = theta_c = (r_c(1), ..., r_c(L)), L = 20, r_c(m) = #{x in O_r(I_c) : nrd(x) = m} (not halved; r_c(1) = |Gamma_c|),
// computed on the right order O_r(I_c) = conj(I_c) I_c / N as a rank-4 lattice (Fincke-Pohst up to nrd L).
// No third key: equal keys form contiguous tie groups (recorded in `order_ties`); inside a group the enumeration
// order is kept (any order is allowed by the rule).
struct CanonOrder {
    std::vector<int> perm;                 // perm[new] = old (enumeration index)
    std::vector<std::vector<u64>> theta;   // theta of class new, r(1..L)
    std::vector<std::vector<int>> ties;    // tie groups, positions after sorting (sorted, size >= 2)
};
CanonOrder canonical_order_v2(const ClassSet& C, int L = 20);
// F'[a][b] = F[perm[a]][perm[b]]
Mat permute(const Mat& F, const std::vector<int>& perm);

}  // namespace hacs_jl
