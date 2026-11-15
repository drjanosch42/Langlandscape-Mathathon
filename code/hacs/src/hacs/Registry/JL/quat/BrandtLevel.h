// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-4b, Lane C): the integral Sym^n Brandt module at level U = U_1(N1) cap U_0(N0) (Level.h), with
//   T_ell (ell not | D N1 N0), U_ell (ell | N1 N0; CLASSICAL, see (B3)), U'_p, <d>, Pi_p (p | D), Pi_D = W_D,
//   W_ell (ell || N0, ell not | N1), the level-changing maps (pullback, trace, the degeneracy s1^*) and the pairing.
// The maximal-order data (splitting, rho_n, the lattices Lambda_c) are those of BrandtSym.h (C1)-(C7); the level data are
// those of Level.h (L1)-(L6). Exact (nf::BigInt / nf::BigRational).
//
// ======================================================================================================= CONVENTIONS
// (B1) Module (Gross form at level U). A point of X_B(U) is (L, d): L a left O-ideal and d its level datum in e L / N L
//      (Level.h (L2)); adelically d = e x_N^{-1} for L = B cap O^ x^{-1}. Functions Phi with
//        Phi(L alpha, d alpha) = rho_n(alpha)^{-1} Phi(L, d),    Phi(L, d) in Lambda(L) = N(L)^{-n/2} Lambda'(O_r(L)),
//      i.e. F(gamma x u) = rho_n(gamma) F(x) for u in U (U acts trivially on V; global splitting s). So
//        M_Z(U) = (+)_{cells y = (c, d_y)} Lambda_c^{Stab_y},   Stab_y = {gamma in Gamma_c : d_y gamma = d_y} (-1 included
//      iff it fixes d_y). For odd n and -1 in Stab_y the block vanishes; for odd n in general there is no Q-form of
//      Sym^n (B is ramified), so ODD n IS NOT SUPPORTED (throws) -- deviation, see the WP note.
// (B2) Hecke terms. Every operator is a finite sum of terms (Op Phi)(I_c, d) += rho_n(g) Phi(I_c', d g), g in B^x; the
//      datum moves by right multiplication with the SAME element g (Level.h (L4)); writing d g = d_{y'} gamma
//      (gamma in Gamma_c', LevelSet::locate_unit) the term is rho_n(g gamma^{-1}) Phi(y'). For an ideal J = I_c K with
//      J = I_c' mu / N_c' (mu in conj(I_c') J of nrd N_c' nrd J, Tree.h find_mu), g = conj(mu) / N_c (= nrd(K) beta^{-1}).
//      Adelic meaning: (T_h F)(x) = sum_i F(x h_i) with L_{x h_i} = nrd(K)^{-1} J_i; the factor rho_n(nrd K) = nrd(K)^n
//      comes from Phi(L lambda^{-1}) = lambda^n Phi(L) (lambda in Q central), exactly as in BrandtSym (C4).
// (B3) U_ell for ell | N1 N0 (def:s01-NUp, the CLASSICAL U_p, a_n -> a_{np}; NO normalisation p^{k/2-1} or p^{-n/2}):
//        U_ell F(x) = sum_{j=0}^{ell-1} F(x varpi_j),  varpi_j = iota_ell^{-1} [[ell, j], [0, 1]]   (Gross form).
//      In ideal terms: the ell neighbours J of L whose line differs from the datum line; equivalently the ell of the
//      ell+1 neighbours for which the transported datum d g stays primitive (U_1) / a line (U_0) at ell. The builder
//      asserts that exactly ell terms survive. Seed dictionary: f(x) = x_p^{-1} F(x) turns this into the seed's
//      N_{U_p} f(x) = sum_j varpi_j . f(x varpi_j) (rem:s01-dictionary), i.e. our U_p IS N_{U_p}; the eigenvalue on a
//      newform is a_p (no power of p removed). T_ell for ell not | N: all ell+1 neighbours.
//      U'_p = [U iota_p^{-1} diag(1, p) U] (lem:s01-Up(c); level N1 = p^s M1, p not | N0): representatives
//      iota_p^{-1} [[1, 0], [p^s j, p]]; in ideal terms the single neighbour J whose line is the datum line, with data
//      ((v - p^s j w) g / p at p, d g at the other primes), w a complement of v (det(v, w) = 1 mod p). This needs the
//      level model modulo p N1 (LevelModel modulus divisible by p N1; checked).
// (B4) <d> (d in (Z/N1)^x; adelic, def:s01-hecke): (<d> Phi)(L, d_L) = Phi(L, d^{-1} d_L) (v -> d^{-1} v on the U_1
//      datum, U_0 lines unchanged; no V-action). Adelic <d> = classical <d>^{-1} (stage-01 flag).
// (B5) Pi_p (p | D): J = P_p I_c (BrandtSym::two_sided_prime), Pi_D: J = P_D I_c; unnormalised, Pi_D^2 = D^n (BrandtSym
//      (C4)). W_ell (ell || N0, ell not | N1): Gross form F(x w_ell), w_ell = iota_ell^{-1} [[0, 1], [-ell, 0]]; in ideal
//      terms J = the neighbour of the datum line, the new ell-line = the line of e L g in e I_c' / ell I_c', other data
//      d g. W_ell^2 = S_ell = ell^n <ell>^{-1} (= ell^n at U_0 level and whenever N1 <= 2; checked, the sign decided on
//      mixed cells with <ell> != <ell>^{-1}); W_ell is self-adjoint at U_0 level but NOT in general at mixed level (recorded).
//      Old-form relations at O_0(q) (checked): W_q s0^* = s1^*, W_q s1^* = q^n s0^*, U_q s0^* = s0^* T_q - s1^*,
//      U_q s1^* = q^{k-1} s0^*, U_q + W_q = s0^* s0^dagger W_q (so U_q = -W_q on the q-new part).
// (B6) Level maps (on functions). pullback(F, X) for U_F subset U_X: (pi^* Phi)(y) = Phi(pi(d_y)); trace(F, X) for an
//      N1-refinement: (tr Phi)(x) = sum_{u in U_X / U_F} Phi(x u) = sum over the lifts of d_x; s1(E, X) for
//      E = X cap U_0(q): (s1^* Phi)(L, d, line) = F(x varpi_q) = rho_n(g) Phi(I_c', d g), J = O y + q L the neighbour of
//      the q-line (Level.h (L5)), so that T_q = s0^dagger s1^* at level X (checked). The weight-k Ihara map is
//      iota = (s0^*, -s1^*) (TreeK.h; amalgam.py's MV sign): the CONSUMER applies the minus sign, these functions return
//      s0^* and s1^* themselves (jl_ihara_xcheck.cpp, JLIharaKValidation).
// (B7) Pairing: <F, H>_w = sum_cells N_c^n beta_n(F(y), H(y)) / w_y, w_y = |Stab_y| / |Stab_y cap +-1| (Level.h (L3));
//      <,>_stab with |Stab_y|. T_ell (ell not | N) is self-adjoint at U_0(N0); at U_1(N1) its adjoint is <ell> T_ell, and
//      U_p^* = <p>_M U'_p (lem:s01-Up(d)); Pi_p^2 = S_p = p^n <p>^{-1} (prop:s01-relations(b)). The self-test records, per
//      cell, whether the other sign also holds, and requires each sign to be DECIDED on at least one cell (U_1(7), U_1(9),
//      U_1(13), U_1(14), U_1(21), U_1(7) cap U_0(2), U_1(7) cap U_0(3); hj4b_level.json "sign_summary").
// (B8) Matrices: column convention (Op b_j = sum_i A[i][j] b_i), basis = concatenation over cells (LevelSet order) of the
//      HNF bases of Lambda_c^{Stab_y} in Lambda_c coordinates (BrandtSym class lattices).
// =====================================================================================================================
#pragma once
#include "BrandtSym.h"
#include "Level.h"

namespace hacs_jl {

struct SymCell {
    int c_enum = 0, c_mod = 0;  // class in ClassSet order / in BrandtSym order
    ZMat Zinv;                  // invariant basis (rows) in Lambda_c coordinates (HNF)
    std::vector<int> piv;
    std::vector<KVec> EK;       // the same basis in K-coordinates
    QMat B;                     // N_c^n beta_n on the block
    int dim() const { return (int)Zinv.size(); }
};

class BrandtLevel {
public:
    BrandtLevel(const BrandtSym& M, const LevelSet& X);
    const BrandtSym& sym() const { return M_; }
    const LevelSet& level() const { return X_; }
    int rank() const { return rank_; }
    int offset(int cell) const { return off_[cell]; }
    const std::vector<SymCell>& cells() const { return cells_; }

    struct Term {
        int src = 0;  // source cell
        QB h;         // (Op Phi)(target) += rho_n(h) Phi(src)
    };
    using Terms = std::vector<std::vector<Term>>;  // per target cell
    // assemble terms for a map from `src` to `dst` (src = dst = *this for operators)
    static ZMat assemble(const BrandtLevel& dst, const BrandtLevel& src, const Terms& t);

    Terms terms_hecke(i64 ell) const;       // T_ell or U_ell (B3)
    Terms terms_Up_prime(i64 p) const;      // U'_p (B3)
    Terms terms_diamond(i64 d) const;       // <d> (B4)
    Terms terms_Pi(i64 p) const;            // Pi_p, Pi_D (B5)
    Terms terms_W(i64 ell) const;           // W_ell (B5)
    ZMat T(i64 ell) const { return assemble(*this, *this, terms_hecke(ell)); }
    ZMat Up_prime(i64 p) const { return assemble(*this, *this, terms_Up_prime(p)); }
    ZMat diamond(i64 d) const { return assemble(*this, *this, terms_diamond(d)); }
    ZMat Pi(i64 p) const { return assemble(*this, *this, terms_Pi(p)); }
    ZMat W(i64 ell) const { return assemble(*this, *this, terms_W(ell)); }

    // level maps (B6); all on functions, matrices rank(dst) x rank(src)
    static ZMat pullback(const BrandtLevel& fine, const BrandtLevel& coarse);   // coarse -> fine
    static ZMat trace(const BrandtLevel& fine, const BrandtLevel& coarse);      // fine -> coarse (N1 refinement)
    static ZMat degeneracy_s1(const BrandtLevel& E, const BrandtLevel& X, i64 q);  // X -> E

    // pairing (B7)
    QMat gram(bool weights_w = true) const;
    // A^* = G^{-1} A^T G (the adjoint for <,>_w), exact
    QMat adjoint(const ZMat& A) const;

private:
    struct Move {
        int c2;   // target class (enum)
        Vec4 mu;  // J = I_c2 mu / N_c2
    };
    Move connect(int c_enum, const Lat& J, i64 NJ) const;
    LevelPoint transport(const LevelPoint& p, int c2, const Vec4& cmu, i128 div) const;  // data d -> d cmu / div
    QB unit_inv(int c_enum, int u) const;   // gamma_u^{-1}
    QB elt(int c_enum, const Vec4& x, i128 div) const;
    const BrandtSym& M_;
    const LevelSet& X_;
    std::vector<int> enum2mod_;
    std::vector<SymCell> cells_;
    std::vector<int> off_;
    int rank_ = 0;
};

}  // namespace hacs_jl
