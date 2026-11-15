// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-7b, Lane C): the weight-k two-term complexes on BG(U, q) over Z/p^m (p prime to 6 D N q):
//
//   homological   d = (-s_{0*}, s_{1*}) : (+)_e W_{H_e} -> (+)_x W_{H_x} (+) (+)_x W_{H_x},  s_{j*} v = e_{H_x}(u_j v);
//   cohomological alpha with the traces  (s_{j*} g)(x) = [H_x : H_e] e_{H_x}(u_j g(e))   (ribet/ihara.py);
//   coboundary    delta(f0, f1) = s_1^* f1 - s_0^* f0,  (s_j^* f)(e) = u_j^{-1} f(x),  on W^{H}  (twoterm.py);
//   the Ihara map iota = (s_0^*, -s_1^*) = -delta (amalgam.py's MV sign); its cokernel is H^1 of the S-arithmetic group.
// W_H and W^H are both modelled on e_H W (|H| is a unit), as in twoterm.py.
//
// Local model at p (replaces the S01 splittings of the Python code; equal up to GL_2(Z_p)-conjugation, Skolem-Noether):
//   * iota_p : O -> M_2(Z/p^m) is the matrix of right multiplication on e O / p^m O (e a rank-1 idempotent of O / p^m,
//     row-vector convention v -> v iota(x)); a ring homomorphism;
//   * per class c a local generator a_c in I_c with nrd(a_c)/N_c prime to p (I_c (x) Z_p = O_p a_c; the frame
//     x_{c,p} = a_c^{-1});  phi_c(r) = iota_p(a_c r a_c^{-1}) for r in O_r(I_c);
//   * edge e of class c (EdgeMove): u_0 = phi_c(gamma_0), u_1 = iota_p(a_{c'} gamma_1 g a_c^{-1}) with g = mu / (q N_{c'})
//     (L_{y alpha} = I_{c'} g), gamma_j the vertex normalisers (tree.py's movers);  H_x = phi_c(Gamma_x).
// The coefficient module W is behind CoeffModel: Sym^n with (g.P)(X, Y) = P((X, Y) g) (twoterm.sym, columns = images of
// X^{n-t} Y^t), or the Shapiro module Sym^n (x) Z[(Z/p)^2 - 0] of ribet/ihara.py (g (v (x) [r]) = g v (x) [r g^{-1}]).
// HJ-4a's quat/BrandtSym can replace SymCoeff behind the same interface.
#pragma once

#include "Tree.h"

namespace hacs_jl {

using M2 = std::array<i64, 4>;  // (a, b, c, d) = [[a, b], [c, d]] mod the modulus

struct ModMat {
    int r = 0, c = 0;
    std::vector<i64> a;  // row-major
    i64& at(int i, int j) { return a[(size_t)i * c + j]; }
    i64 at(int i, int j) const { return a[(size_t)i * c + j]; }
};

// valuations v < m of the nonzero elementary divisors of A over Z/p^m (twoterm.elementary_divisors), ascending
std::vector<int> elem_divs_mod(ModMat A, i64 p, int m);

class CoeffModel {
public:
    virtual ~CoeffModel() = default;
    virtual int dim() const = 0;
    virtual i64 modulus() const = 0;
    // the matrix of g (column convention: column j = image of basis vector j), dim x dim, mod modulus
    virtual ModMat act(const M2& g) const = 0;
    virtual std::string name() const = 0;
};

class SymCoeff : public CoeffModel {
public:
    SymCoeff(int n, i64 mod) : n_(n), mod_(mod) {}
    int dim() const override { return n_ + 1; }
    i64 modulus() const override { return mod_; }
    ModMat act(const M2& g) const override;
    std::string name() const override { return "Sym^" + std::to_string(n_); }

private:
    int n_;
    i64 mod_;
};

class ShapiroSymCoeff : public CoeffModel {
public:
    ShapiroSymCoeff(int n, i64 p, i64 mod);
    int dim() const override { return (int)pts_.size() * (n_ + 1); }
    i64 modulus() const override { return mod_; }
    ModMat act(const M2& g) const override;
    std::string name() const override { return "Sym^" + std::to_string(n_) + " (x) Z[(Z/p)^2-0]"; }

private:
    int n_;
    i64 p_, mod_;
    std::vector<std::pair<i64, i64>> pts_;
    SymCoeff sym_;
};

// the splitting iota_p mod p^m of the maximal order and the class frames
struct PadicFrames {
    i64 p = 0, mod = 0;
    int m = 0;
    Vec4 e{}, b1{}, b2{};
    int pos[2] = {0, 0};
    std::vector<Vec4> a;       // a_c (O-coordinates)
    std::vector<i64> na;       // nrd(a_c) / N_c mod p^m (a unit)
};
PadicFrames make_frames(const ClassSet& C, i64 p, int m);

M2 m2mul(const M2& A, const M2& B, i64 mod);
M2 m2inv(const M2& A, i64 mod);
M2 m2scale(const M2& A, i64 s, i64 mod);

struct LocalTwist {
    std::vector<std::vector<M2>> Hv, He;  // phi of the stabilisers
    std::vector<M2> u0, u1;
    bool conj_ok = true;                  // u_j H_e u_j^{-1} subset H_{s_j e}
};
LocalTwist local_twist(const ClassSet& C, const TreeQuotient& T, const PadicFrames& F);

struct TwoTerm {
    // bases of e_H W per vertex / edge (columns), coordinates by an invertible minor
    std::vector<int> off_v, off_e;  // offsets; type-1 vertex block x is at off_v[X + x]
    int r0 = 0, r1 = 0;             // rank of (+)_x e_H W twice, rank of (+)_e e_H W
    ModMat d_hom, d_coh, delta;     // d (homological), alpha (cohomological traces), delta (coboundary)
};
TwoTerm two_term(const TreeQuotient& T, const LocalTwist& L, const CoeffModel& W, i64 p);

// structure of W / span(relations) (columns), as an exponent list [m]*(free) + torsion (ihara.structure)
std::vector<int> module_structure(const ModMat& rel_cols_as_rows, int dim, i64 p, int m);

}  // namespace hacs_jl
