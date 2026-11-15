// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception

// Langlandscape JL extension (WP INT, Lane C): fast validations of the native quaternion core under Registry/JL/quat
// (HJ-1/2, HJ-3, HJ-4a/b, HJ-7). Every expected value is FROZEN inline (no file is read, no env var is consulted); the
// sources of the frozen values are named next to each check. All values are *computed* (native hacs_jl, exact).
//  * JLQuatCoreValidation:   (a, b), h, |Gamma_x| multiset, mass of B_D (code/results/s01/classsets.json); T_2 of B_11 in the
//                            v2 canonical order (freeblockz-export-format.md Sec. 8); row sums, weighted symmetry.
//  * JLBrandtSymValidation:  char_Z(T_ell) on the integral Sym^n Brandt module (code/results/s01/symn.json cells
//                            (11,10), (2,10), (13,8)); Pi_D^2 = D^n; commutation; self-adjointness for <,>_w.
//  * JLLevelValidation:      the tower |S_s| = 2, 50, 1250 (B_3, p = 5; code/results/s01/levels.json), Delta free, mass identity;
//                            X, E, masses and the fibre sums q + 1 (s0 and s1) on six cells of code/results/s02/validation.json.
//  * JLTreeW2Validation:     B_11, q = 2: X = 2, E = 3, coker(alpha alpha^dagger | Cusp) = Z/5, Phi^comb = Z/5 (cyclic), Ihara coker
//                            free (HJ-7a headline, s03/T1.json); Brandt T_q = tree Hecke matrix on four further (D, q).
//  * JLIharaKValidation:     the exact weight-k Ihara cokernel coker(s0^*, -s1^*) through BrandtLevel (HJ-4b Eichler API) on five
//                            cells of code/results/laneC/hj7_ihara_k.json (TreeK route; equal on 210/210 cells, hj7_ihara_xcheck.json).
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

#include "quat/BrandtLevel.h"
#include "quat/Tree.h"

namespace {

struct Tally {
    uint32_t checks = 0, failing = 0;
    bool check(bool ok, const std::string& what) {
        ++checks;
        if (!ok) ++failing;
        std::cout << (ok ? "  ok   " : "  FAIL ") << what << "\n";
        return ok;
    }
};

std::string Cp(const std::vector<nf::BigInt>& v) {
    std::string o;
    for (size_t i = 0; i < v.size(); ++i) o += (i ? "," : "") + v[i].to_string();
    return o;
}
std::string Gs(std::vector<int> g) {
    std::sort(g.begin(), g.end());
    std::string o;
    for (size_t i = 0; i < g.size(); ++i) o += (i ? "," : "") + std::to_string(g[i]);
    return o;
}
double Secs(std::chrono::steady_clock::time_point t0) {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}
template <class F>
uint32_t Guard(const char* name, F f) {
    Tally T;
    auto t0 = std::chrono::steady_clock::now();
    std::cout << name << ": computed (native hacs_jl, exact; frozen expected values)\n";
    try {
        f(T);
    } catch (const std::exception& e) {
        T.check(false, std::string("exception: ") + e.what());
    }
    std::cout << name << ": " << (T.checks - T.failing) << "/" << T.checks << " checks ok (" << Secs(t0) << " s)\n";
    return T.failing;
}

}  // namespace

uint32_t JLQuatCoreValidation() {
    using namespace hacs_jl;
    return Guard("JLQuatCoreValidation", [](Tally& T) {
        struct Ref {
            i64 D, a, b;
            int h;
            const char* gammas;
        };
        // code/results/s01/classsets.json
        for (const Ref& r : {Ref{2, -1, -1, 1, "24"}, Ref{3, -3, -1, 1, "12"}, Ref{11, -11, -1, 2, "4,6"}, Ref{13, -13, -2, 1, "2"},
                             Ref{30, -10, -3, 2, "6,6"}, Ref{37, -37, -2, 3, "2,2,2"}, Ref{43, -43, -1, 4, "2,2,2,4"}}) {
            MaxOrder O(r.D);
            ClassSet C(O);
            const std::string tag = "D=" + std::to_string(r.D);
            T.check(O.algebra().a() == r.a && O.algebra().b() == r.b, tag + ": (a, b) = quat.py's");
            T.check(O.disc() == (i128)r.D * r.D, tag + ": disc O = D^2 (maximal)");
            T.check(C.h() == r.h && Gs(gammas_of(C)) == r.gammas, tag + ": h = " + std::to_string(r.h) + ", |Gamma_x| = " + r.gammas);
            T.check(C.sum24() == C.phi(), tag + ": mass sum 1/|Gamma_x| = phi(D)/24");
        }
        MaxOrder O(11);
        ClassSet C(O);
        Mat B = permute(brandt_neighbours(C, 2), canonical_order_v2(C).perm);
        T.check(B == Mat{1, 2, 3, 0}, "B_11: T_2 = [[1,2],[3,0]] in the v2 canonical order");
        std::vector<int> g = gammas_of(C);
        for (i64 p : {3, 5, 7}) {
            Mat F = brandt_neighbours(C, p);
            T.check(row_sums_ok(F, 2, p + 1) && weighted_symmetric(F, g), "B_11: T_" + std::to_string(p) + " row sums p+1, weighted symmetry");
        }
    });
}

uint32_t JLBrandtSymValidation() {
    using namespace hacs_jl;
    return Guard("JLBrandtSymValidation", [](Tally& T) {
        struct Ref {
            i64 D;
            int k;
            i64 ell;
            const char* cp;  // code/results/s01/symn.json rhs (low -> high)
        };
        for (const Ref& r : {Ref{11, 10, 2, "28405487616,-1055048192,-715341184,-13692768,2355888,32700,-2730,-16,1"},
                             Ref{2, 10, 3, "156,1"}, Ref{13, 8, 2, "-772800,-2565760,-468456,92836,3534,-589,-6,1"},
                             Ref{3, 12, 2, "-78,1"}}) {
            MaxOrder O(r.D);
            ClassSet C(O);
            BrandtSym M(C, r.k - 2);
            const std::string tag = "D=" + std::to_string(r.D) + " k=" + std::to_string(r.k);
            ZMat Tl = M.T(r.ell);
            T.check(Cp(symz::charpoly(Tl)) == r.cp, tag + ": char_Z(T_" + std::to_string(r.ell) + ") = symn.json");
            if (M.rank() == 0) continue;
            ZMat P = M.Pi(r.D);
            T.check(symz::is_scalar(symz::mul(P, P), nf::BigInt::pow(nf::BigInt(r.D), (uint64_t)(r.k - 2))), tag + ": Pi_D^2 = D^(k-2)");
            T.check(symz::mul(P, Tl) == symz::mul(Tl, P), tag + ": Pi_D T = T Pi_D");
            T.check(M.self_adjoint(Tl) && M.self_adjoint(P), tag + ": T_ell, Pi_D self-adjoint for <,>_w");
        }
        // D = 13, k = 8: T_2, T_3 commute; odd k: rank 0
        MaxOrder O(13);
        ClassSet C(O);
        BrandtSym M(C, 6);
        T.check(symz::mul(M.T(2), M.T(3)) == symz::mul(M.T(3), M.T(2)), "D=13 k=8: T_2 T_3 = T_3 T_2");
        T.check(BrandtSym(C, 5).rank() == 0, "D=13 k=7: rank 0 (-1 acts by -1)");
    });
}

uint32_t JLLevelValidation() {
    using namespace hacs_jl;
    return Guard("JLLevelValidation", [](Tally& T) {
        {
            MaxOrder O(3);
            ClassSet C(O);
            Tower Tw(C, 5, 3);
            const int sizes[3] = {2, 50, 1250};  // code/results/s01/levels.json, D=3, p=5
            for (int s = 1; s <= 3; ++s) {
                auto m = Tw.S(s).mass();
                T.check(Tw.S(s).size() == sizes[s - 1] && m.second == 1 && m.first == sizes[s - 1],
                        "B_3, p=5: |S_" + std::to_string(s) + "| = " + std::to_string(sizes[s - 1]) + " = mass (all Gamma trivial)");
                T.check(Tw.delta_free(s), "B_3, p=5: Delta_" + std::to_string(s) + " acts freely");
            }
            auto pi = Tw.pi(3);
            std::vector<int> cnt(Tw.S(2).size(), 0);
            for (int y : pi) ++cnt[y];
            bool fib = true;
            for (int c : cnt) fib &= c == 25;
            T.check(fib, "pi_{3,2}: every fibre has p^2 = 25 points");
        }
        struct Ref {
            i64 D, q, N1, N0;
            int X, E;
            const char *vm, *em;  // code/results/s02/validation.json
        };
        for (const Ref& r : {Ref{2, 5, 1, 1, 1, 1, "1/24", "1/4"}, Ref{2, 5, 3, 1, 1, 2, "1/3", "2/1"}, Ref{11, 3, 1, 2, 3, 10, "5/4", "5/1"},
                             Ref{11, 3, 4, 1, 5, 20, "5/1", "20/1"}, Ref{23, 7, 3, 1, 8, 60, "22/3", "176/3"},
                             Ref{37, 2, 1, 3, 12, 36, "6/1", "18/1"}}) {
            MaxOrder O(r.D);
            ClassSet C(O);
            LevelModel Mo(C, r.N1 * r.N0 * r.q);
            LevelSet X(Mo, {r.N1, r.N0}), E(Mo, {r.N1, r.N0 * r.q});
            auto R = u0q_correspondence(E, X, r.q);
            const std::string tag = "D=" + std::to_string(r.D) + " q=" + std::to_string(r.q) + " " + X.spec().str();
            T.check(X.size() == r.X && E.size() == r.E && frac_str(X.mass().first, X.mass().second) == r.vm &&
                        frac_str(E.mass().first, E.mass().second) == r.em,
                    tag + ": X, E, masses = validation.json");
            T.check(fibre_sums_ok(E, X, R.s0, r.q) && fibre_sums_ok(E, X, R.s1, r.q), tag + ": fibre sums q+1 for s0 and s1");
        }
    });
}

uint32_t JLTreeW2Validation() {
    using namespace hacs_jl;
    return Guard("JLTreeW2Validation", [](Tally& T) {
        using nf::BigInt;
        MaxOrder O(11);
        ClassSet C(O);
        TreeQuotient Tq = build_tree(C, 2);
        T.check(Tq.X() == 2 && Tq.nE() == 3, "B_11, q=2: X = 2, E = 3");
        auto M = tree2::alpha_alphadag(Tq, true);
        zlin::ZM Mc(2, std::vector<BigInt>(2, BigInt(0)));
        for (int t = 0; t < 2; ++t)
            for (int u = 0; u < 2; ++u) Mc[u][t] = M[u * 2][t * 2] - M[u * 2][t * 2 + 1];
        auto dc = zlin::smith(Mc);
        T.check(dc.size() == 2 && dc[0] == BigInt(1) && dc[1] == BigInt(5), "B_11, q=2: coker(alpha alpha^dagger | Cusp) = Z/5");
        auto phi = tree2::phi_two_vertex({Tq.E[0].w, Tq.E[1].w, Tq.E[2].w});
        T.check(phi.order == BigInt(5) && phi.cyclic, "B_11, q=2: Phi^comb = Z/5, cyclic");
        auto si = zlin::smith(tree2::ihara(Tq));
        bool free = si.size() == 3;
        for (auto& x : si) free &= x == BigInt(1);
        T.check(free, "B_11, q=2: Ihara cokernel torsion-free (weight 2)");
        for (auto [D, q] : std::vector<std::pair<i64, i64>>{{2, 3}, {11, 3}, {23, 2}, {37, 5}}) {
            MaxOrder O2(D);
            ClassSet C2(O2);
            TreeQuotient T2 = build_tree(C2, q);
            auto H = T2.hecke();
            Mat B = brandt_neighbours(C2, q);
            bool eq = true;
            for (int i = 0; i < T2.X(); ++i)
                for (int j = 0; j < T2.X(); ++j) eq &= B[(size_t)i * T2.X() + j] == H[i][j];
            T.check(eq && T2.components() == 1, "D=" + std::to_string(D) + " q=" + std::to_string(q) + ": tree Hecke = Brandt T_q, connected");
        }
    });
}

uint32_t JLIharaKValidation() {
    using namespace hacs_jl;
    return Guard("JLIharaKValidation", [](Tally& T) {
        struct Ref {
            i64 D, q;
            int k, rX, rE, free;
            const char* tors;  // code/results/laneC/hj7_ihara_k.json ihara_exact_NEW
        };
        for (const Ref& r : {Ref{2, 3, 8, 1, 3, 1, "10"}, Ref{2, 3, 10, 1, 3, 1, "84"}, Ref{11, 2, 4, 2, 7, 3, "11"},
                             Ref{11, 3, 6, 4, 16, 8, "12"}, Ref{5, 13, 6, 1, 22, 20, "4"}}) {
            MaxOrder O(r.D);
            ClassSet C(O);
            BrandtSym M(C, r.k - 2);
            LevelModel Mo(C, r.q);
            LevelSet Xs(Mo, {1, 1}), Es(Mo, {1, r.q});
            BrandtLevel X(M, Xs), E(M, Es);
            ZMat s0 = BrandtLevel::pullback(E, X), s1 = BrandtLevel::degeneracy_s1(E, X, r.q);
            zlin::ZM A(E.rank(), std::vector<nf::BigInt>(2 * X.rank(), nf::BigInt(0)));
            for (int i = 0; i < E.rank(); ++i)
                for (int j = 0; j < X.rank(); ++j) {
                    A[i][j] = s0[i][j];
                    A[i][X.rank() + j] = -s1[i][j];
                }
            auto d = zlin::smith(A);
            std::string tors;
            for (const auto& x : d)
                if (x != nf::BigInt(1)) tors += (tors.empty() ? "" : ",") + x.to_string();
            const int free = E.rank() - (int)d.size();
            T.check(X.rank() == r.rX && E.rank() == r.rE && free == r.free && tors == r.tors,
                    "D=" + std::to_string(r.D) + " q=" + std::to_string(r.q) + " k=" + std::to_string(r.k) +
                        ": coker(s0^*, -s1^*) = Z^" + std::to_string(free) + " + torsion [" + tors + "] (frozen: [" + r.tors + "])");
        }
    });
}
