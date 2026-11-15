// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl quaternion core (WP HJ-1): rank-4 Z-lattices.
//
// * Lat: a full-rank lattice (1/den) * span_Z(h[0..3]) in Q^4 (coordinates w.r.t. a fixed basis, in practice the basis of
//   the maximal order, see Order.h). h is the canonical lower-triangular HNF: h[c][m] = 0 for m > c, h[c][c] > 0,
//   0 <= h[k][m] < h[m][m] for m < k. Two Lat are equal iff (den, h) are equal.
// * hnf(): exact, __int128, either plain (overflow-checked) or modulo a known index d with d*Z^4 contained in the
//   lattice (the result's index is checked to be d, so a wrong d throws instead of returning a wrong lattice).
// * Reduction and short vectors: LLL (delta = 0.99) on the real images of the basis vectors under an embedding with
//   |image(x)|^2 = nrd(x) (positive definite), exact integer basis updates; then Fincke-Pohst enumeration on the exact
//   integer Gram matrix (long-double Cholesky with slack, every enumerated vector re-checked with exact integers).
#pragma once

#include "Quat.h"

#include <functional>

namespace hacs_jl {

using Vec4 = std::array<i128, 4>;

struct Lat {
    i128 den = 1;
    std::array<Vec4, 4> h{};
    i128 index() const;                       // product of the diagonal (index of den*L's numerator lattice in Z^4)
    bool operator==(const Lat& o) const { return den == o.den && h == o.h; }
    std::string key() const;                  // canonical text "den|h00,h10,h11,...": used for class_keys / basis_fnv
};

// HNF of the Z-span of gens / den. modulus > 0: the numerator lattice is known to have index exactly `modulus` in Z^4.
Lat hnf(const std::vector<Vec4>& gens, i128 den = 1, i128 modulus = 0);
Lat lat_sum(const Lat& A, const Lat& B);
Lat dual(const Lat& L);                       // w.r.t. the standard pairing on Q^4
Lat intersect(const Lat& A, const Lat& B);    // (A^* + B^*)^*
// coordinates y with v = sum_s y_s h[s] (den = 1 lattice, v an integral vector); throws if v is not in L
Vec4 coords_in(const Lat& L, const Vec4& v);
bool contains(const Lat& L, const Vec4& v);   // v integral, L any den
bool sublattice(const Lat& A, const Lat& B);  // A subset of B

// ---------------------------------------------------------------- reduction and enumeration
struct Embedding {
    long double v[4][4];  // real image of coordinate basis vector s is v[s][0..3]; |sum x_s v[s]|^2 = nrd(x)
};

// Exact integer Gram matrix of the quadratic form q(x) = x^T G x (in practice q = 2 nrd = trd(x conj x)).
struct Gram4 {
    i128 g[4][4];
};

struct Reduced {
    std::array<Vec4, 4> b;  // LLL-reduced basis, rows = coordinates (w.r.t. the ambient basis) of the reduced vectors
    Gram4 G;                 // exact Gram of the reduced basis under the ambient form
    long double chol[4][4];  // Cholesky data of G (q_ii on the diagonal, q_ij above), long double
};

// L must have den = 1 (numerator lattice). G0 is the ambient Gram (x^T G0 x = 2 nrd for x in ambient coordinates).
Reduced lll_reduce(const Lat& L, const Embedding& E, const Gram4& G0);

// Enumerate every nonzero x (reduced-basis coordinates, both x and -x) with x^T G x <= bound2. cb(x, value) returns
// false to stop early. Returns false iff stopped early.
bool fp_enumerate(const Reduced& R, i128 bound2, const std::function<bool(const i64* x, i128 val2)>& cb);

// counts[n] = #{x != 0 : nrd(x) = n * scale}, n = 0..X (counts[0] = 0). Throws if some nrd(x) <= X*scale is not a
// multiple of scale (sanity check of the normalisation).
std::vector<u64> count_values(const Reduced& R, i128 scale, i64 X);

// ambient coordinates of sum_s x_s b[s]
Vec4 combine(const Reduced& R, const i64* x);
i128 qform(const Gram4& G, const Vec4& x);  // x^T G x, overflow-checked

}  // namespace hacs_jl
