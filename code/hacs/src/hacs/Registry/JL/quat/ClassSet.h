// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-2): the class set X_B of left O-ideal classes of a maximal order O of B_D, the unit groups
// Gamma_x = O_r(I_x)^x and exact mass termination.
//
// Conventions (as quat.py / brandt.py): left ideals I of O, classes I ~ I alpha (alpha in B^x), right orders
// O_r(I) = conj(I) I / nrd(I); |Gamma_x| = |O_r(I_x)^x| INCLUDING -1 (|Gamma_x| = 2 w_x, w_x = |Gamma_x / +-1|).
//
// Method.
// * BFS over ell0-neighbours (ell0 = smallest prime not dividing D), starting from O. The ell-neighbours of I are the
//   ell+1 ideals I alpha + ell I, alpha in R = O_r(I) of rank 1 in R/ell R = M_2(F_ell); they are enumerated through
//   a zero divisor alpha_0 (isotropic vector of nrd on R mod ell) and a basis v1, v2 of the right ideal alpha_0 R / ell R:
//   alpha_s = v1 + s v2 (s in F_ell) and v2 give the ell+1 distinct left ideals R alpha + ell R (one per kernel line).
// * Class representatives are reduced: J is replaced by J conj(gamma) / nrd(J), gamma a shortest vector of J, so that
//   nrd(rep) = min_{x in J} nrd(x)/nrd(J) stays O(sqrt D).
// * Isomorphism test (exact, sound): I ~ J iff conj(I) J contains an element of reduced norm nrd(I) nrd(J) (all its
//   nonzero elements have nrd >= nrd(I) nrd(J)); decided by Fincke-Pohst on the LLL-reduced norm form of conj(I) J.
//   (If conj(I) J contains such alpha then J = I alpha / nrd(I).)
// * qf_theta bucketing (a necessary condition only): the theta-series prefix of the normalised norm form
//   (J, nrd / nrd(J)) -- counts r(n) for n = 1 .. n*, n* the least n with r(1)+...+r(n) >= K -- is a class invariant
//   (x -> x alpha is an isometry). Classes are bucketed by its 64-bit FNV hash; an exact test is run against every
//   class in the bucket. Once the class set is complete (mass reached), a neighbour whose bucket has a single class
//   lies in that class without an exact test (it lies in some class, which must have the same qf_theta).
// * |Gamma_x| = #{x in conj(I) I : nrd(x) = nrd(I)^2} (units of O_r(I)), by Fincke-Pohst.
// * Mass: sum_x 1/|Gamma_x| = phi(D)/24 and sum_x 1/w_x = phi(D)/12, phi(D) = prod_{p | D} (p - 1) (Eichler; cited:
//   Voight, Quaternion Algebras, Thm. 25.1.1). The BFS stops as soon as the mass is reached (exact integer arithmetic on
//   sum 24/|Gamma_x|; every |Gamma_x| divides 24 for maximal orders, checked); it throws if the BFS exhausts first.
#pragma once

#include "Order.h"

#include <unordered_map>

namespace hacs_jl {

struct ThetaInfo {
    std::vector<u64> prefix;  // r(1), ..., r(n*)
    u64 hash = 0;             // FNV-1a-64 of the prefix
    Vec4 min_vec{};           // a vector of minimal nrd
    i128 min_nrd = 0;         // its nrd (un-normalised)
};

struct ClassRep {
    Lat I;          // left O-ideal, I subset O
    Lat Ic;         // conj(I) (a right O-ideal)
    i64 N = 1;      // nrd(I)
    Lat RN;         // conj(I) I = N * O_r(I)
    int gamma = 0;  // |O_r(I)^x| including -1
    ThetaInfo theta;
};

struct ClassSetStats {
    u64 identifications = 0, exact_tests = 0, exact_tests_positive = 0, single_bucket_shortcuts = 0;
    size_t max_bucket = 0, buckets = 0;
    double seconds = 0;
};

class ClassSet {
public:
    struct Options {
        int theta_K = 48;      // qf_theta prefix length (cumulative count)
        i64 ell0 = 0;          // 0: smallest prime not dividing D
        bool mass_stop = true; // stop the BFS once the mass formula is attained
    };
    ClassSet(const MaxOrder& O, Options opt);
    explicit ClassSet(const MaxOrder& O) : ClassSet(O, Options()) {}

    const MaxOrder& order() const { return O_; }
    const std::vector<ClassRep>& classes() const { return reps_; }
    int h() const { return (int)reps_.size(); }
    i64 ell0() const { return ell0_; }
    i64 phi() const { return phi_; }      // prod (p - 1); mass target in units of 1/24
    i64 sum24() const { return sum24_; }  // sum 24/|Gamma_x| (== phi() on completion)
    const ClassSetStats& stats() const { return st_; }

    // primitive operations (also used by Brandt2)
    ThetaInfo qf_theta(const Lat& J, i64 N) const;
    std::vector<Lat> neighbours(const ClassRep& c, i64 p) const;  // the p+1 ideals I alpha + p I (nrd p N)
    bool equivalent(const Lat& I, i64 NI, const Lat& J, i64 NJ) const;
    std::pair<Lat, i64> reduce(const Lat& J, i64 N, const ThetaInfo& t) const;
    int unit_count(const Lat& RN, i64 N) const;
    Lat pair_lattice(const ClassRep& a, const ClassRep& b) const;  // conj(I_a) I_b, index (N_a N_b)^2
    // class index of the left ideal J (nrd NJ); -1 if J lies in no known class. complete = class set known complete.
    int identify(const Lat& J, i64 NJ, bool complete) const;

private:
    int add_class(const Lat& I, i64 N, const ThetaInfo& t);
    const MaxOrder& O_;
    Options opt_;
    i64 ell0_, phi_, sum24_ = 0;
    std::vector<ClassRep> reps_;
    std::unordered_map<u64, std::vector<int>> buckets_;
    mutable ClassSetStats st_;
};

u64 fnv1a64(const std::string& s, u64 h = 0xcbf29ce484222325ULL);

}  // namespace hacs_jl
