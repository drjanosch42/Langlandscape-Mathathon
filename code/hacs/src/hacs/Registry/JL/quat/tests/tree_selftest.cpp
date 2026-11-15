// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// tree_selftest (WP HJ-7a): standalone checks of hacs_jl::build_tree and the weight-2 maps (Tree.h).
//   1. headline: B_11, q = 2 -- X = 2, E = 3, T_2 = [[1,2],[3,0]] (Brandt), coker(alpha alpha^dagger | Cusp) = Z/5,
//      Phi^comb of the collapsed graph = Z/5 (cyclic), literal coker(alpha alpha^dagger) = Z + Z/3, Ihara coker free;
//   2. for every definite D <= 53 and q in {2, 3, 5, 7, 11, 13}, q !| D, at U = O^x: H = the Brandt matrix T_q (same class
//      order), rows sum to q + 1, E - 2X + 1 = rk H_1 = E - rank d, mass sum 1/|Gamma_e| = (q+1) sum 1/|Gamma_x|, coker d = Z;
//   3. levels U_0(N0), U_1(N1): fibre sums (q + 1) and the mass identity on a sample;
//   4. zlin: Smith form of a fixed matrix.
//   tree_selftest [--quick]
#include "../Tree.h"

#include <cstdio>
#include <numeric>

using namespace hacs_jl;
using zlin::Z;

static int g_fail = 0, g_pass = 0;
#define CHECK(c)                                                         \
    do {                                                                 \
        if (c)                                                           \
            ++g_pass;                                                    \
        else {                                                           \
            ++g_fail;                                                    \
            std::fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #c); \
        }                                                                \
    } while (0)

static i128 lcm128(i128 a, i128 b) { return a / gcd128(a, b) * b; }
static bool mass_ok(const TreeQuotient& T) {
    i128 L = 1;
    for (auto& c : T.V) L = lcm128(L, c.stab);
    for (auto& c : T.E) L = lcm128(L, c.stab);
    i128 v = 0, e = 0;
    for (auto& c : T.V) v += L / c.stab;
    for (auto& c : T.E) e += L / c.stab;
    return e == (T.q + 1) * v;
}
static bool fibres_ok(const TreeQuotient& T) {
    for (int j = 0; j < 2; ++j) {
        std::vector<i128> num(T.X(), 0);
        i128 L = 1;
        for (auto& c : T.E) L = lcm128(L, c.stab);
        for (int e = 0; e < T.nE(); ++e) {
            int x = j ? T.s1[e] : T.s0[e];
            num[x] += (i128)T.V[x].stab * (L / T.E[e].stab);
        }
        for (auto n : num)
            if (n != (T.q + 1) * L) return false;
    }
    return true;
}

int main(int argc, char** argv) {
    const bool quick = argc > 1 && std::string(argv[1]) == "--quick";
    // 4. zlin
    {
        auto d = zlin::smith(zlin::from_i64({{2, 4, 4}, {-6, 6, 12}, {10, -4, -16}}));
        CHECK(d.size() == 3 && d[0] == Z(2) && d[1] == Z(6) && d[2] == Z(12));
        auto K = zlin::kernel_basis(zlin::from_i64({{1, 1, 1}}), 3);
        CHECK(K.size() == 2);
    }
    // 1. headline
    {
        MaxOrder O(11);
        ClassSet C(O);
        TreeQuotient T = build_tree(C, 2);
        CHECK(T.X() == 2 && T.nE() == 3);
        auto H = T.hecke();
        Mat B = brandt_neighbours(C, 2);
        bool eq = true;
        for (int i = 0; i < 2; ++i)
            for (int j = 0; j < 2; ++j) eq &= B[i * 2 + j] == H[i][j];
        CHECK(eq);
        auto ev = tree2::integer_eigenvalues(H, 3);
        CHECK(ev.size() == 2 && ev[0] == -2 && ev[1] == 3);
        auto M = tree2::alpha_alphadag(T, true);
        auto d = zlin::smith(M);
        CHECK(d.size() == 3 && d[2] == Z(3));  // Z + Z/3
        // cuspidal part: degree zero in each type, basis e_0 - e_1 per type
        zlin::ZM Mc(2, std::vector<Z>(2, Z(0)));
        for (int t = 0; t < 2; ++t)
            for (int u = 0; u < 2; ++u) Mc[u][t] = M[u * 2][t * 2] - M[u * 2][t * 2 + 1];
        auto dc = zlin::smith(Mc);
        CHECK(dc.size() == 2 && dc[0] == Z(1) && dc[1] == Z(5));
        auto phi = tree2::phi_two_vertex({T.E[0].w, T.E[1].w, T.E[2].w});
        CHECK(phi.order == Z(5) && phi.cyclic);
        auto si = zlin::smith(tree2::ihara(T));
        bool free = si.size() == 3;
        for (auto& x : si) free &= x == Z(1);
        CHECK(free);
    }
    // 2. maximal level, all D <= 53
    int cells = 0;
    for (i64 D = 2; D <= (quick ? 23 : 53); ++D) {
        if (!is_squarefree(D) || prime_factors(D).size() % 2 == 0) continue;
        MaxOrder O(D);
        ClassSet C(O);
        for (i64 q : {2, 3, 5, 7, 11, 13}) {
            if (D % q == 0) continue;
            TreeQuotient T = build_tree(C, q);
            ++cells;
            auto H = T.hecke();
            Mat B = brandt_neighbours(C, q);
            bool eq = true, rows = true;
            for (int i = 0; i < T.X(); ++i) {
                i64 s = 0;
                for (int j = 0; j < T.X(); ++j) {
                    eq &= B[(size_t)i * T.X() + j] == H[i][j];
                    s += H[i][j];
                }
                rows &= s == q + 1;
            }
            CHECK(eq);
            CHECK(rows);
            CHECK(mass_ok(T));
            CHECK(fibres_ok(T));
            CHECK(T.components() == 1);
            auto sd = zlin::smith(tree2::boundary(T));
            bool ones = true;
            for (auto& x : sd) ones &= x == Z(1);
            CHECK(ones && (int)sd.size() == 2 * T.X() - 1);
            CHECK((int)tree2::cycle_basis(T).size() == T.nE() - 2 * T.X() + 1);
        }
    }
    // 3. levels
    for (auto [D, q, N1, N0] : std::vector<std::array<i64, 4>>{{3, 2, 5, 1}, {2, 3, 7, 1}, {3, 2, 1, 7}, {13, 2, 3, 1},
                                                                {11, 3, 4, 1}, {7, 2, 1, 3}, {2, 5, 3, 7}}) {
        MaxOrder O(D);
        ClassSet C(O);
        TreeQuotient T = build_tree(C, q, TreeLevel{N1, N0});
        CHECK(fibres_ok(T));
        CHECK(mass_ok(T));
        CHECK(T.components() == 1);
    }
    std::printf("tree_selftest: %d maximal-level cells; %d passed, %d failed\n", cells, g_pass, g_fail);
    return g_fail ? 1 : 0;
}
