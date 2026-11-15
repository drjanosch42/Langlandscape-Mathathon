// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-4a): the integral Sym^n Brandt module at the maximal order of B_D (D squarefree, omega(D) odd),
//   M = (+)_x Lambda_x^{Gamma_x},  n = k - 2,
// with T_ell (ell prime, ell not dividing D), Pi_p (p | D), Pi_D = W_D, and the pairing with weights w_x and |Gamma_x|.
// Exact: every entry is an nf::BigInt / nf::BigRational; nothing is floating point. Mod ell^K = reduce the Z matrices.
//
// ===================================================================================================== CONVENTIONS
// Every choice below is copied from stage 01 (code/python/langlandscape/symn.py, pi_ell.py; plan/staged/stage-01) or is
// a lattice choice stated here. Nothing is normalised silently.
//
// (C1) Algebra and splitting (= symn.py SplitAlgebra, verbatim). B = (a, b)_Q from find_ab (= quat.py), i^2 = a,
//      j^2 = b, k = ij = -ji. Splitting field K = Q(sqrt a) (imaginary quadratic), elements r + s sqrt(a) (KElt).
//      s : B -> M_2(K),  s(c0 + c1 i + c2 j + c3 k) = [[c0 + c1 sqrt a, b (c2 + c3 sqrt a)], [c2 - c3 sqrt a, c0 - c1 sqrt a]],
//      i.e. i -> diag(sqrt a, -sqrt a), j -> [[0, b], [1, 0]]. (Self-test: multiplicative on the order basis.)
// (C2) Coefficients (= [C] def:rhon column convention = symn.py sym_matrix = stage 01 eq:s01-Vk). V = Sym^n(K^2) =
//      homogeneous polynomials of degree n in X, Y, basis u_t = X^{n-t} Y^t (t = 0..n),
//        (g.P)(X, Y) = P((X, Y) g) = P(aX + cY, bX + dY),   g = [[a, b], [c, d]],
//      column t of rho_n(g) = coefficients of (aX + cY)^{n-t} (bX + dY)^t. rho_n(g h) = rho_n(g) rho_n(h); no transpose,
//      inverse or contragredient. rho_n(lambda g) = lambda^n rho_n(g).
// (C3) Brandt module, Gross form with the global splitting (= symn.py, rem:s01-dictionary): Phi on left O-ideals with
//      Phi(L alpha) = rho_n(s(alpha))^{-1} Phi(L); M = (+)_c V^{Gamma_c}, Gamma_c = O_r(I_c)^x INCLUDING -1, over the class
//      representatives I_c (left O-ideals I_c in O, N_c = nrd(I_c)). For odd n, -1 acts by -1 and M = 0 (rank 0).
//      Adelic reading: Phi(I_c) = F(x_c), F(gamma x u) = s(gamma).F(x), I_c = B cap O^ x_c^{-1}. Over Z_p (p not | D)
//      this is the stage-01 cohomological module {f : f(gamma x u) = u_p^{-1} f(x)} via f(x) = x_p^{-1} . F(x)
//      (iota_p in place of s); see (C5) for why the lattice below is exactly that one at every p not dividing D.
// (C4) Hecke operators (= symn.py / pi_ell.py; def:s01-hecke). For J = I_c K (K an integral left O_r(I_c)-ideal of norm
//      ell, i.e. J runs over the ell+1 ell-neighbours I_c alpha + ell I_c of ClassSet::neighbours), write J = I_{c'} beta_J,
//      beta_J = delta / N_{c'}, delta in conj(I_{c'}) J of nrd N_{c'} nrd(J). Then
//        (T_ell Phi)(I_c) = sum_J ell^n rho_n(beta_J^{-1}) Phi(I_{c'}) = sum_J rho_n(conj(delta_J) / N_c) Phi(I_{c'}).
//      Pi_p (p | D): (Pi_p F)(x) = F(x Pi_p) (no V-action), on ideals Phi -> Phi(P_p^{-1} L): the same formula with the
//      single J = P_p I_c, P_p the two-sided prime of O above p (P_p = D O^# + p O, O^# the trd-dual). Pi_D = prod Pi_p
//      (J = P_D I_c, P_D = D O^#). Pi_p^2 = p^n (= S_p), Pi_D^2 = D^n: no normalisation is applied (pi_sign.json).
//      Matrices are in the COLUMN convention of freeblockz-export-format.md section 2: T b_j = sum_i T[i][j] b_i.
// (C5) THE LATTICE (our choice; stated in full). For an order R let R^0 = {x in R : trd x = 0} and (R^0)^# its dual
//      under (x, y) -> trd(x y) inside B^0. For x in B^0 put Q_x(X, Y) := (X, Y) s(x) J (X, Y)^T, J = [[0, 1], [-1, 0]]
//      (a quadratic form, i.e. an element of Sym^2 V; Q_x = -s01 X^2 + (s00 - s11) XY + s10 Y^2). Then
//        rho_2(gamma) Q_x = Q_{gamma x conj(gamma)},  so  rho_n(gamma) (Q_{x_1} ... Q_{x_m}) = prod Q_{gamma x_i conj(gamma)}
//      (n = 2m). Put Lambda'(R) := Z-span{Q_{x_1} ... Q_{x_m} : x_i in (R^0)^#} (rank n+1 inside the Q-form
//      V_Q' = Q-span of these products; V_Q' is a Q-form of V stable under rho_n(s(B)), equal to symn.py's V^phi up to
//      a K^x-scalar -- char-polys are identical) and, for class c,
//        Lambda_c := N_c^{-m} Lambda'(O_r(I_c)),      M_Z := (+)_c Lambda_c^{Gamma_c}.
//      Properties (proved in the WP note; checked numerically by brandtsym_selftest, tests C, H, I): Lambda_c is Gamma_c-stable; it is
//      intrinsic (Phi(L alpha) = rho(alpha^{-1}) Phi(L) maps N(L)^{-m} Lambda'(O_r L) onto N(L alpha)^{-m} Lambda'(O_r(L
//      alpha))), so M_Z does not depend on the class representatives; every single Hecke term rho(conj(delta)/N_c)
//      maps Lambda_{c'} into Lambda_c (because ell O_r(J) is contained in O_r(I_c)), so T_ell is integral termwise;
//      Pi_D maps Lambda_{c''} into D^m Lambda_c (so Pi_D / D^m is an integral involution). At every prime p not
//      dividing D, (O_p^0)^# corresponds under iota_p to {[[al, be], [ga, -al]] : 2al, be, ga in Z_p}, whose Q_x span
//      all of Sym^2(Z_p^2), hence Lambda_c (x) Z_p = (scalar) . rho_n(x_{c,p}) Sym^n(Z_p^2): M_Z (x) Z_p IS the stage-01
//      seed-side module Brandt(O^x; Sym^n(Z_p^2)) (p = 2 included). At p | D the lattice is the choice (O^0)^# above.
//      Bases: the base lattice Lambda_O := Lambda'(O) (O = the HNF maximal order of Order.h, N = 1) defines the base
//      coordinates (Lambda_O = Z^{n+1}, its basis = the integer HNF of its generators in the real coordinates
//      (Re, Im/sqrt a) of the u_t). Lambda_c is given by its HNF basis in base coordinates; Lambda_c^{Gamma_c} by the
//      HNF of the integer kernel in Lambda_c coordinates. The basis of M_Z is the concatenation over classes.
// (C6) Class order: the binding canonical order of langlandscape_brandt/v2 (Brandt2.h canonical_order_v2) by default;
//      Options::canonical_order = false keeps the ClassSet BFS order.
// (C7) Pairing (def:s01-pairingV in the Gross form). beta_n(u_i, u_j) = delta_{i+j,n} (-1)^i / binom(n, i);
//      beta_n(rho_n(g) P, rho_n(g) Q) = det(g)^n beta_n(P, Q). It is Q-valued on V_Q'. Class block
//        B_c[i][j] := N_c^n beta_n(e_{c,i}, e_{c,j})   (intrinsic: invariant under L -> L alpha),
//      and the two pairings  <F, H>_w = sum_c B_c / w_c,  <F, H>_Gamma = sum_c B_c / |Gamma_c|  (w_c = |Gamma_c| / 2, so
//      <,>_w = 2 <,>_Gamma exactly), plus the "multiplied" convenience matrices sum_c w_c B_c, sum_c |Gamma_c| B_c (NOT the homological pairing at
//      k > 2, which lives on the dual lattice / coinvariants; audit m5).
//      T_ell and Pi_D are self-adjoint for <,>_w (checked). Integer versions are scale * Gram with the recorded scale.
// =====================================================================================================================
#pragma once
#include "Brandt2.h"
#include "../../../NumberField/BigInt.h"
#include "../../../NumberField/BigRational.h"

namespace hacs_jl {

using Z = nf::BigInt;
using Q = nf::BigRational;
using ZMat = std::vector<std::vector<Z>>;  // row-major, ZMat[i][j]
using QMat = std::vector<std::vector<Q>>;
using QB = std::array<Q, 4>;               // c0 + c1 i + c2 j + c3 k, standard basis of (a, b)_Q

// ------------------------------------------------------------------------------------- exact linear algebra helpers
namespace symz {
ZMat identity(int d);
ZMat mul(const ZMat& A, const ZMat& B);
QMat mul(const QMat& A, const QMat& B);
ZMat transpose(const ZMat& A);
bool equal(const ZMat& A, const ZMat& B);
bool is_scalar(const ZMat& A, const Z& lambda);  // A == lambda * I
// det(x - A), coefficients low -> high (Faddeev-LeVerrier, exact divisions)
std::vector<Z> charpoly(const ZMat& A);
// entries reduced into [0, m), m >= 1 (the module mod ell^K)
std::vector<std::vector<u64>> reduce_mod(const ZMat& A, u64 m);
// row-style integer HNF: nonzero rows, pivots strictly increasing and positive, entries above a pivot in [0, pivot)
ZMat hnf_rows(ZMat A);
// a Z-basis (HNF rows) of {z in Z^r : z A = 0} (A is r x c); saturated by construction
ZMat left_kernel(const ZMat& A);
// T restricted to {v : (A - lambda) v = 0} (column convention), in the HNF basis of the integral kernel; `basis` gets
// the basis vectors (as rows). Throws if T does not preserve the kernel.
ZMat restrict_to_eigenspace(const ZMat& T, const ZMat& A, const Z& lambda, ZMat* basis = nullptr);
std::string fnv_text(const ZMat& F);  // HACS MatrixFnv text (rows ';', entries ',')
}  // namespace symz

// ------------------------------------------------------------------------------------------- K = Q(sqrt a) and rho_n
struct KElt {
    Q r, s;  // r + s sqrt(a)
};
using KVec = std::vector<KElt>;                // coefficients of u_t = X^{n-t} Y^t, t = 0..n
using KMat = std::vector<std::vector<KElt>>;   // KMat[t][u], column u = image of u_u

// quaternion arithmetic on QB in (a, b)_Q
QB qb_mul(i64 a, i64 b, const QB& x, const QB& y);
QB qb_conj(const QB& x);
Q qb_nrd(i64 a, i64 b, const QB& x);
Q qb_trd(const QB& x);
QB qb_from(const QElt& x);
// s(x) of (C1), as [[s00, s01], [s10, s11]]
std::array<std::array<KElt, 2>, 2> split(i64 a, i64 b, const QB& x);
// rho_n(s(x)) of (C2) (= symn.py sym_matrix(split(x), n))
KMat rho_K(i64 a, i64 b, const QB& x, int n);
KVec apply(i64 a, const KMat& R, const KVec& v);
// Q_x of (C5) (x in B^0) as a KVec of length 3
KVec quad_form(i64 a, i64 b, const QB& x);
// beta_n of (C7) (K-valued)
KElt beta_n(i64 a, const KVec& P, const KVec& R, int n);

// ------------------------------------------------------------------------------------------------- the module
struct SymClass {
    int enum_index = 0;          // index in ClassSet::classes() (BFS order)
    Lat I;                       // the left ideal I_c (O-coordinates)
    i64 N = 1;                   // nrd(I_c)
    int gamma = 0;               // |Gamma_c| including -1
    int w = 0;                   // gamma / 2
    std::vector<QB> units;       // Gamma_c = O_r(I_c)^x, standard coordinates (all |Gamma_c| elements)
    std::array<QB, 4> order_basis;  // O_r(I_c), standard coordinates
    std::array<QB, 3> dual0;     // a Z-basis of (O_r(I_c)^0)^#, standard coordinates
    QMat H;                      // basis of Lambda_c (rows), in base coordinates (n+1 rows)
    ZMat Zinv;                   // basis of Lambda_c^{Gamma_c} (rows) in Lambda_c coordinates (HNF), d_c rows
    QMat E;                      // the same basis in base coordinates (= Zinv * H)
    std::vector<KVec> EK;        // the same basis in K-coordinates of the u_t
    int dim() const { return (int)Zinv.size(); }
};

class BrandtSym {
public:
    struct Options {
        bool canonical_order = true;  // (C6)
    };
    BrandtSym(const ClassSet& C, int n, Options opt);
    BrandtSym(const ClassSet& C, int n) : BrandtSym(C, n, Options()) {}

    const ClassSet& class_set() const { return C_; }
    const MaxOrder& order() const { return C_.order(); }
    i64 D() const { return C_.order().D(); }
    i64 a() const { return C_.order().algebra().a(); }
    i64 b() const { return C_.order().algebra().b(); }
    int n() const { return n_; }
    int h() const { return (int)cl_.size(); }
    int rank() const { return rank_; }
    const std::vector<SymClass>& classes() const { return cl_; }  // in the module's class order (C6)
    int offset(int c) const { return off_[c]; }                    // first basis index of class block c
    std::vector<int> gammas() const;
    std::vector<int> dims() const;

    // ---- coefficients
    // rho_n(gamma) on the base lattice Lambda_O, base coordinates, column convention. Integer for gamma in O;
    // gamma is given in O-coordinates (Order.h), optionally divided by den.
    QMat rho_base(const Vec4& gamma, i128 den = 1) const;
    ZMat rho_base_int(const Vec4& gamma) const;  // throws if not integral
    // rho_n(gamma) on Lambda_c (Lambda_c's HNF basis), gamma in standard coordinates. Integer for gamma in O_r(I_c).
    QMat rho_class(int c, const QB& gamma) const;
    const QMat& base_basis_real() const { return Rreal_; }  // basis of Lambda_O in real coords (2(n+1) columns)
    KVec base_vector(const std::vector<Q>& y) const;          // K-vector of a base-coordinate vector

    // ---- operators on M_Z (rank() x rank(), column convention)
    ZMat T(i64 ell) const;      // ell prime, ell not | D
    ZMat Pi(i64 p) const;       // p | D prime: Pi_p;   p == D(): Pi_D = W_D (for composite D the product)
    // ---- pairing (C7)
    enum class Weight { w, gamma };
    QMat gram(Weight wt, bool divide = true) const;  // divide: sum B_c / weight; else sum weight * B_c (convenience only)
    const QMat& gram_block(int c) const { return Bc_[c]; }
    // the least positive integer s with s * G integral, and s * G
    static Z denominator_lcm(const QMat& G);
    static ZMat scale_to_int(const QMat& G, const Z& s);
    bool self_adjoint(const ZMat& A, Weight wt = Weight::w) const;  // A^T G = G A, G = gram(wt, true)

    // ---- internals exposed for tests
    std::vector<Q> base_coords(const KVec& v) const;   // throws if v not in V_Q'
    std::vector<Q> class_coords(int c, const std::vector<Q>& y) const;  // Lambda_c coordinates of base vector y
    std::vector<Q> inv_coords(int c, const std::vector<Q>& z) const;    // Zinv coordinates of Lambda_c vector z
    struct HeckeTerm {
        int src = 0;  // c'
        QB g;         // conj(delta) / N_c
    };
    std::vector<std::vector<HeckeTerm>> terms_T(i64 ell) const;  // per class c (module order)
    std::vector<std::vector<HeckeTerm>> terms_Pi(i64 p) const;
    ZMat assemble(const std::vector<std::vector<HeckeTerm>>& terms) const;
    Lat two_sided_prime(i64 p) const;  // P_p (p | D) or P_D (p == D), O-coordinates

private:
    HeckeTerm connect(int c, const Lat& J, i64 NJ) const;
    const ClassSet& C_;
    int n_, m_, rank_ = 0;
    std::vector<int> perm_;      // module class index -> enum index
    std::vector<int> inv_perm_;  // enum index -> module class index
    std::vector<SymClass> cl_;
    std::vector<int> off_;
    QMat Rreal_;                 // base lattice basis, real coordinates, echelon rows
    std::vector<int> Rpiv_;
    std::vector<std::vector<int>> Hpiv_, Zpiv_;
    std::vector<QMat> Bc_;
};

}  // namespace hacs_jl
