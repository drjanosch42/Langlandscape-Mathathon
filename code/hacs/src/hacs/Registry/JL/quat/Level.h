// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-3, Lane C): level structures X_B(U) for U = U_1(N1) cap U_0(N0) inside O^^x (gcd(N1, N0) = 1,
// gcd(N1 N0, D) = 1, N1 and N0 arbitrary, composite allowed), the projections between levels, the U_0(q)U correspondence
// (s0, s1), and the p-tower S_s = X_B(U_1(M p^s)) with its maps pi_{s+1,s} and diamonds.
//
// ======================================================================================================= CONVENTIONS
// (L1) Classes, units: as ClassSet / quat.py: left O-ideals I_c (nrd N_c), Gamma_c = O_r(I_c)^x INCLUDING -1, acting on
//      the right; a unit is stored as x = N_c gamma in conj(I_c) I_c (Tree.h class_units), gamma = x / N_c.
// (L2) Level data = the lattice model of HJ-7a's Tree.cpp, generalised to composite levels: fix a rank-1 idempotent
//      e of O / Nbig (Tree.h idempotent_mod on each prime power, combined by CRT; Nbig = the model modulus). For N | Nbig,
//      e I_c / N I_c is free of rank 2 over Z/N with the basis (b1, b2) (reduction of a basis mod Nbig, so all levels
//      dividing Nbig are compatible, which makes the tower maps reductions). A point of class c has
//        v = (a, b) mod N1, primitive (gcd(a, b, N1) = 1)          -- U_1(N1): the vector a b1 + b b2;
//        l = (a, b) mod N0 primitive, up to (Z/N0)^x (canonical rep: lexicographically least multiple) -- U_0(N0).
//      Gamma_c acts by v -> v gamma (right multiplication on e I_c; row-vector convention (a, b) -> (a, b) A_gamma,
//      A_{gamma delta} = A_gamma A_delta). This is the same object as levels.py's GL_2(Z/N)/U' with
//      v = (0,1) h^{-1} (levels.py: phi_x via left multiplication on O_x e, gamma acting by v -> v phi(gamma)^{-1}); a
//      different splitting changes the fibre by a bijection, so sizes, stabilisers and masses agree (checked).
// (L3) Stabilisers: stab = #{gamma in Gamma_c fixing the point} (full, -1 counted if it fixes); w = stab / 2 if -1 fixes the
//      point, else stab. -1 in U iff N1 <= 2. Masses: mass = sum 1/stab, massW = sum 1/w.
// (L4) Transport between classes (the move used by s1 and by every Hecke operator at level): for J = I_{c'} mu / N_{c'}
//      (mu in conj(I_{c'}) J of nrd N_{c'} nrd(J)) the level data move by v -> v conj(mu) / N_c (Tree.h s1 convention;
//      the scalar nrd(J)/N_c is included and is a unit mod N).
// (L5) U_0(q)U (q prime, q not | D N1 N0): edges X_B(U cap U_0(q)) are points with an extra line mod q (stored in the
//      U_0 part: N0' = N0 q). The line spanned by y in e I_c / q I_c determines the q-neighbour J = O y + q I_c (one of the
//      q+1 lattices of ClassSet::neighbours; bijection). s0 forgets the q-line; s1 moves to the class of J by (L4).
// (L6) Tower: S_s = X_B(U_1(M p^s)) from ONE model mod M p^smax, pi_{s+1,s} = reduction mod M p^s; diamond Delta_s,
//      d in (Z/p^s)^x acts by v -> d^{-1} v (identity mod M) (levels.py).
// =====================================================================================================================
#pragma once
#include "Tree.h"

#include <memory>
#include <unordered_map>

namespace hacs_jl {

using Mat2 = std::array<i64, 4>;  // (a b; c d) row-major, acting on row vectors: (x, y) -> (x a + y c, x b + y d)

struct LevelSpec {
    i64 N1 = 1;  // U_1(N1)
    i64 N0 = 1;  // U_0(N0)
    std::string str() const;
};

// the splitting data e I_c / Nbig I_c for every class
class LevelModel {
public:
    LevelModel(const ClassSet& C, i64 Nbig);
    const ClassSet& class_set() const { return C_; }
    i64 modulus() const { return Nbig_; }
    const Vec4& idempotent() const { return e_; }       // O-coordinates mod Nbig
    const std::vector<Vec4>& units(int c) const { return units_[c]; }  // x = N_c gamma
    // I_c-coordinates mod N of a b1 + b b2 (N | Nbig)
    std::array<i64, 4> lift(int c, i64 a, i64 b, i64 N) const;
    // coordinates (a, b) mod N of y (I_c-coordinates mod N, y in e I_c / N I_c; throws otherwise)
    std::array<i64, 2> coords(int c, const std::array<i64, 4>& y, i64 N) const;
    // the matrix of v -> v x / div from class c to class c2 (x in O-coordinates; requires I_c x subset div I_c2), mod N
    Mat2 move(int c, int c2, const Vec4& x, i128 div, i64 N) const;
    // O-coordinates (integer) of the element of I_c with I_c-coordinates y
    Vec4 element(int c, const std::array<i64, 4>& y) const;

private:
    const ClassSet& C_;
    i64 Nbig_;
    Vec4 e_{};
    std::vector<std::vector<Vec4>> units_;
    std::vector<std::array<std::array<i64, 4>, 2>> basis_;  // per class: b1, b2 (I_c coords mod Nbig)
    struct PP {
        i64 l, lk;  // prime and its power in Nbig
    };
    std::vector<PP> pps_;
    std::vector<std::vector<std::pair<int, int>>> piv_;  // per class, per prime power: pivot coordinates (i, j)
};

struct LevelPoint {
    int c = 0;
    i64 v0 = 0, v1 = 0;  // mod N1 (0, 0 if N1 = 1)
    i64 l0 = 0, l1 = 0;  // canonical line mod N0 (0, 0 if N0 = 1)
    bool operator==(const LevelPoint& o) const {
        return c == o.c && v0 == o.v0 && v1 == o.v1 && l0 == o.l0 && l1 == o.l1;
    }
};

struct LevelCell {
    LevelPoint rep;
    int stab = 0, w = 0, orbit_size = 0;
    std::vector<int> stab_units;  // indices into LevelModel::units(rep.c)
};

// X_B(U) for U = U_1(N1) cap U_0(N0), N1 N0 | model modulus
class LevelSet {
public:
    LevelSet(const LevelModel& Mo, LevelSpec U);
    const LevelModel& model() const { return Mo_; }
    LevelSpec spec() const { return U_; }
    bool minus_one_in_U() const { return U_.N1 <= 2; }
    i64 index() const { return index_; }  // [O^^x : U] = #fibre points per class
    int size() const { return (int)cells_.size(); }
    const std::vector<LevelCell>& cells() const { return cells_; }
    int first_cell(int c) const { return first_[c]; }   // cells of class c: [first_cell(c), first_cell(c+1))
    std::pair<i128, i128> mass() const;    // sum 1/stab as (num, den)
    std::pair<i128, i128> massW() const;   // sum 1/w
    // the cell of a point; -1 if the point is not of this level's shape
    int locate(const LevelPoint& p) const;
    // the cell of a point and a unit index u with point = act(rep, unit u) (so point = rep . gamma_u, gamma_u = x_u / N_c);
    // {-1, -1} if the point is not of this level's shape (v not primitive mod N1, or zero line mod N0)
    std::pair<int, int> locate_unit(const LevelPoint& p) const;
    // point helpers
    LevelPoint canon(LevelPoint p) const;  // reduce v mod N1, canonicalise l mod N0
    LevelPoint act(const LevelPoint& p, const Mat2& A1, const Mat2& A0) const;  // v A1, l A0 (same class)
    std::vector<int> stabs() const;
    std::vector<int> ws() const;
    // unit matrices mod N1 / N0 (cached per class)
    const std::vector<Mat2>& unit_mats1(int c) const { return um1_[c]; }
    const std::vector<Mat2>& unit_mats0(int c) const { return um0_[c]; }

private:
    u64 key(const LevelPoint& p) const;
    const LevelModel& Mo_;
    LevelSpec U_;
    i64 index_ = 0;
    std::vector<LevelCell> cells_;
    std::vector<int> first_;
    std::vector<std::vector<Mat2>> um1_, um0_;
    std::vector<std::array<i64, 2>> canon0_;  // canonical line of (a, b) mod N0, index a*N0+b
    std::unordered_map<u64, std::pair<int, int>> where_;  // point -> (cell, unit)
};

// ---- maps between levels
// projection X_B(U') -> X_B(U), U' = U_1(N1') cap U_0(N0') subset U = U_1(N1) cap U_0(N0) (N1 | N1', N0 | N1' N0'), same model;
// the U_0(N0) line at a prime power dividing N1' is the line of the U_1 vector
std::vector<int> project(const LevelSet& from, const LevelSet& to);
// the point of level `to` below a point of level `from` (same nesting rule as project)
LevelPoint reduce_point(const LevelPoint& p, LevelSpec from, LevelSpec to);
// the U_0(q) correspondence: E = X_B(U cap U_0(q)) (N0' = N0 q), X = X_B(U); s0 = projection, s1 by (L5)
struct Correspondence {
    std::vector<int> s0, s1;
    std::vector<int> edge_class_target;  // class c' of J for each edge cell
};
Correspondence u0q_correspondence(const LevelSet& E, const LevelSet& X, i64 q);
// fibre sums sum_{e in s^{-1}(x)} stab_x / stab_e (exact; returns false if some sum != q + 1)
bool fibre_sums_ok(const LevelSet& E, const LevelSet& X, const std::vector<int>& s, i64 q);

// ---- the p-tower
class Tower {
public:
    Tower(const ClassSet& C, i64 p, int smax, i64 M = 1);
    const LevelSet& S(int s) const { return *S_.at(s - 1); }
    int smax() const { return smax_; }
    i64 p() const { return p_; }
    std::vector<int> pi(int s) const;          // pi_{s,s-1} : S_s -> S_{s-1}, s >= 2
    std::vector<int> diamond(int s, i64 d) const;  // Delta_s, d in (Z/p^s)^x: v -> d^{-1} v mod p^s, identity mod M
    bool delta_free(int s) const;              // (1 + pZ)/(1 + p^s Z) acts freely

private:
    LevelModel model_;
    i64 p_, M_;
    int smax_;
    std::vector<std::unique_ptr<LevelSet>> S_;
};

}  // namespace hacs_jl
