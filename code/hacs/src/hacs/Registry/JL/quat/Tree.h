// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-7, Lane C): quotients of the Bruhat-Tits tree of PGL_2(Q_q) by the S-arithmetic group of a definite
// quaternion algebra B_D (q prime, q not dividing D), and the Ribet / Ihara maps on them -- natively, on the HJ-1/2
// core (MaxOrder, ClassSet, Brandt2).
//
// The graph BG(U, q) (stage-02 def:s02-BG, code/python/langlandscape/tree.py) for U = U_1(N1) cap U_0(N0) (N1 a prime
// power or 1, N0 a prime or 1, gcd(N1 N0, D q) = 1):
//   * vertices X = X_B(U) = disjoint union over the classes c of Gamma_c \ F_c, F_c the level-U fibre of c;
//     two types (x, 0), (x, 1) with the same list;
//   * edges E = X_B(U_0(q) U) = union over c of Gamma_c \ (F_c x {q-neighbours of I_c});
//   * s0(e) = [y] (forget the q-neighbour), s1(e) = [y alpha] (move to the class of the q-neighbour J = q L_{y alpha}).
// Model (lattice form of tree.py's idelic model). A class c is a reduced left O-ideal I_c (nrd N_c) from ClassSet,
// Gamma_c = O_r(I_c)^x (INCLUDING -1), acting from the right. Level data of a point of class c:
//   * mod N1: a primitive vector v of e1 I_c / N1 I_c (e1 a fixed rank-1 idempotent of O / N1, Hensel-lifted);
//   * mod N0: a line of e0 I_c / N0 I_c (e0 a fixed rank-1 idempotent of O / N0);
//   * edges also carry a q-neighbour J of I_c (one of the q + 1 lattices I_c alpha + q I_c, [I_c : J] = q^2).
// Gamma_c acts by v -> v gamma, J -> J gamma (gamma = x / N_c with x in conj(I_c) I_c of nrd N_c^2).
// s1: J = I_{c'} mu / N_{c'} with mu in conj(I_{c'}) J of nrd N_{c'} q N_c (found by Fincke-Pohst); then g = mu/(q N_{c'})
// satisfies L_{y alpha} = J/q = I_{c'} g, and the level data move by v -> v g^{-1} = v conj(mu) / N_c (in I_{c'}; the
// scalar q of tree.py's diamond bookkeeping is included).
// Stabilisers: stab = |{gamma in Gamma_c : gamma fixes the point}| (full, with -1 if it fixes the point),
// w = stab / |stab cap {+-1}|. -1 is in U iff N1 <= 2.
//
// Weight 2 (all exact, nf::BigInt):
//   * d = (-s_{0*}, s_{1*}) : Z[E] -> Z[X]^2 (rows: type-0 vertices, then type-1), its rank and Smith form;
//   * s_j^* : Z[X] -> Z[E] (f -> f o s_j) and s_{j*} (e -> s_j e);
//   * the Hecke matrix H[x][x'] = sum_{e : x -> x'} stab_x / stab_e (= the Brandt matrix T_q at U = O^x), and
//     H'[x][x'] = sum_{e : x -> x'} w_{x'} / w_e;
//   * alpha = d and its adjoint alpha^dagger for <x, x> = w_x, <e, e> = w_e (weighted) or 1 (unweighted):
//       alpha alpha^dagger = [[(q+1) I, -H'], [-H^T, (q+1) I]] (weighted; collapse.py's convention);
//   * the weighted Gram on X(G) = ker d (saturated) and Phi^comb = coker(X -> X^v) by integer Smith form;
//   * the Ihara map iota = (s_0^*, -s_1^*) : Z[X]^2 -> Z[E] (amalgam.py's MV sign alpha(x, y) = dg_1 x - dg_q y with
//     the transport, here trivial in weight 2), coker iota = H^1 of the S-arithmetic group with Z coefficients.
// Weight k (HJ-7b) uses the per-edge transport elements stored below (EdgeMove) behind the CoeffModel interface.
#pragma once

#include "Brandt2.h"
#include "../../../NumberField/BigInt.h"

#include <map>
#include <tuple>
#include <string>

namespace hacs_jl {

// ---------------------------------------------------------------- exact integer linear algebra (nf::BigInt)
namespace zlin {
using Z = nf::BigInt;
using ZM = std::vector<std::vector<Z>>;  // row-major; ncols carried separately when nrows may be 0
ZM from_i64(const std::vector<std::vector<i64>>& A);
std::vector<Z> smith(ZM A);                  // nonzero invariant factors d_1 | d_2 | ..., all > 0
ZM kernel_basis(const ZM& A, size_t ncols);  // rows: a Z-basis of {v in Z^ncols : A v = 0} (saturated, HNF)
ZM hermite_rows(ZM rows);                    // row HNF, zero rows dropped
bool in_row_span(const ZM& hnf_rows, std::vector<Z> v);  // v in the Z-span of the rows (hnf_rows = hermite_rows(...))
Z det(ZM A);                                 // Bareiss
ZM transpose(const ZM& A, size_t ncols);
ZM mul(const ZM& A, const ZM& B, size_t bcols);
Z prod(const std::vector<Z>& v);
}  // namespace zlin

struct TreeLevel {
    i64 N1 = 1;  // U_1(N1): N1 = 1 or a prime power
    i64 N0 = 1;  // U_0(N0): N0 = 1 or a prime
    bool maximal() const { return N1 == 1 && N0 == 1; }
    std::string str() const;  // "O^x", "U1(5)", "U0(7)", "U1(5)*U0(7)" (tree.py's Level.__str__)
};

// a point of a fibre: class c, vector mod N1 and line mod N0 in I_c-coordinates, q-neighbour index (edges) or -1
struct TreePoint {
    int c = 0;
    std::array<i64, 4> v{{0, 0, 0, 0}};
    std::array<i64, 4> l{{0, 0, 0, 0}};
    int jq = -1;
    bool operator<(const TreePoint& o) const {
        return std::tie(c, v, l, jq) < std::tie(o.c, o.v, o.l, o.jq);
    }
    bool operator==(const TreePoint& o) const { return c == o.c && v == o.v && l == o.l && jq == o.jq; }
};

struct TreeCell {
    TreePoint rep;                 // orbit representative
    int stab = 0;                  // |Gamma_x| (full stabiliser)
    int w = 0;                     // stab / |stab cap {+-1}|
    std::vector<int> stab_units;   // indices into TreeQuotient::units[rep.c]
    int orbit_size = 0;
};

// transport data of an edge e (class c, representative point y), for weight-k coefficients (HJ-7b):
//   s0: units[c][unit0] = N_c gamma_0 with gamma_0 y = x_{s0 e} (the vertex representative) at level U;
//   s1: c1 = class of J, mu (O-coordinates) with J = I_{c1} mu / N_{c1}, and units[c1][unit1] = N_{c1} gamma_1 moving the
//       transported point to the representative of s1 e; beta = gamma_1 g, g = mu / (q N_{c1}).
struct EdgeMove {
    int unit0 = 0;
    int c1 = 0;
    Vec4 mu{};
    int unit1 = 0;
};

struct TreeQuotient {
    i64 D = 0, q = 0;
    TreeLevel level;
    bool minus_one_in_U = true;
    int h = 0;                                // class number of the maximal order
    std::vector<int> class_gamma;             // |Gamma_c|
    std::vector<std::vector<Vec4>> units;     // per class: x = N_c gamma (O-coordinates), gamma in Gamma_c
    std::vector<TreeCell> V, E;
    std::vector<int> s0, s1;
    std::vector<EdgeMove> moves;
    int X() const { return (int)V.size(); }
    int nE() const { return (int)E.size(); }
    std::vector<int> stab_v() const;
    std::vector<int> stab_e() const;
    std::vector<int> w_v() const;
    std::vector<int> w_e() const;
    int components() const;                   // of the bipartite graph on 2X vertices
    std::vector<std::vector<i64>> hecke() const;       // H (rows sum to q + 1)
    std::vector<std::vector<i64>> hecke_prime() const; // H'
    std::vector<std::vector<i64>> adjacency() const;   // A[x][x'] = #{e : x -> x'}
    double seconds = 0;
    // statistics of the builder
    long points_v = 0, points_e = 0;
    bool orbit_checks = false;                // s0, s1 checked constant on every orbit
};

struct TreeOptions {
    bool check_orbits = true;  // tree.py's check=True: s0, s1 constant on every Gamma_c-orbit of edge points
};

// BG(U, q) for the class set C of the maximal order (C must be complete).
TreeQuotient build_tree(const ClassSet& C, i64 q, TreeLevel U = TreeLevel(), TreeOptions opt = TreeOptions());

// the units of O_r(I_c) as N_c gamma (O-coordinates), count = |Gamma_c|
std::vector<Vec4> class_units(const ClassSet& C, int c);
// mu in conj(I) J with nrd(mu) = N_I N_J (so J = I mu / N_I); throws if none
Vec4 find_mu(const ClassSet& C, const Lat& I, i64 NI, const Lat& J, i64 NJ);
// a rank-1 idempotent e of O / N (N a prime power, not dividing D), O-coordinates mod N
Vec4 idempotent_mod(const MaxOrder& O, i64 N);

// ---------------------------------------------------------------- weight-2 maps
namespace tree2 {
using zlin::Z;
using zlin::ZM;
ZM boundary(const TreeQuotient& T);                       // d, 2X x E
ZM pullback(const TreeQuotient& T, int j);                // s_j^*, E x X
ZM pushforward(const TreeQuotient& T, int j);             // s_{j*}, X x E
ZM ihara(const TreeQuotient& T);                          // iota = (s_0^*, -s_1^*), E x 2X
ZM alpha_alphadag(const TreeQuotient& T, bool weighted, int sign = 1);  // 2X x 2X (sign = -1: Ribet's (s0*, s1*))
// saturated Z-basis of X(G) = ker d for the bipartite graph (rows, length E)
ZM cycle_basis(const TreeQuotient& T);
struct Phi {
    int rank = 0;
    std::vector<Z> divisors;  // > 1
    Z order = 1;
    bool cyclic = true;
};
Phi phi_comb(const ZM& cycles, const std::vector<i64>& edge_w, size_t nE);
Phi phi_two_vertex(const std::vector<i64>& w);  // the two-vertex graph with one edge of weight w_i each
// integer eigenvalues of an integer matrix in [-bound, bound] (distinct, ascending)
std::vector<i64> integer_eigenvalues(const std::vector<std::vector<i64>>& H, i64 bound);
// p-adic elementary divisor valuations of A mod p^m that are < m (= twoterm.elementary_divisors), ascending
std::vector<int> elem_div_vals(const ZM& A, i64 p, int m);
}  // namespace tree2

std::string frac_str(i128 num, i128 den);  // reduced "a/b" (b = 1 -> "a/1", as Python's str(Fraction) would not)

}  // namespace hacs_jl
