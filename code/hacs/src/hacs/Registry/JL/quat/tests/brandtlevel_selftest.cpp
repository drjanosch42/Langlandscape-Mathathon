// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// Standalone self-test of the Sym^n Brandt module at level (WP HJ-4b, BrandtLevel.h). Not registered in HACS.
//   brandtlevel_selftest [--results DIR] [--write PATH] [--quick]
// Checks (exit code = number of failures):
//   A. code/results/s01/up.json (B_3, p = 5, k = 2, S_s = X_B(U_1(5^s))): at s = 1, 2 our T_2, U_5, U'_5, <2> and pi^*
//      equal the transposes of the stored homological matrices up to ONE simultaneous permutation of S_s (and of S_1
//      for pi); at s = 1, 2 (exact) and s = 3 (|S_3| = 1250, mod 2^61-1 on random vectors): U_p pi^* = pi^* U_p,
//      U'_p pi^* != pi^* U'_p (the expected failure), tr U'_p = U'_p tr, U_p and U'_p commute with T_2 and <2>,
//      U_p^* = U'_p (w = 1).
//   B. code/results/s01/pi_sign.json through BrandtLevel at O^x: Pi_D-eigenspace dims and char_Z(T_ell | eigenspace).
//   C. Sym^n at U_0(M), U_1(N), U_1(N1) cap U_0(N0) (prime D <= 13, k = 2, 4, 6): every pair of commuting operators
//      commutes (T_ell, U_ell, <d>, Pi_p, Pi_D, W_ell; not the pairs (W_ell, U_ell)); T_ell self-adjoint at U_0;
//      T_ell^* = <ell>^{e} T_ell and U_p^* = <p>_M^{e} U'_p at U_1 (the sign e recorded); Pi_D^2, W_ell^2 against
//      S = ell^n <ell>^{+-1}; k = 2 at U_0: T_ell 1 = (ell + 1) 1 on the constant function.
//   D. Eichler level O_0(q) (the API for HJ-7b): s0^* (pullback) and s1^* (degeneracy) commute with T_ell (ell not | Dq),
//      and T_q = s0^dagger s1^* (s0^dagger = the <,>_w-adjoint of s0^*).
// --write PATH: code/results/laneC/hj4b_level.json (charpolys for the PARI cross-check check_hj4b_mf.py).
#include "../BrandtLevel.h"
#include "../../../../NumberField/Sha256.h"
#include "JsonMin.h"
#include "RepoRoot.h"

#include <chrono>
#include <map>
#include <cstdio>
#include <ctime>
#include <fstream>
#include <numeric>
#include <random>
#include <sstream>

using namespace hacs_jl;
using hacs_jl_test::JV;

static int g_fail = 0, g_pass = 0;
// relation -> (cells deciding the claimed sign, cells contradicting it)
static std::map<std::string, std::pair<int, int>> g_sign;
static std::string g_sign_json = "{}";
static void check(bool ok, const std::string& what) {
    if (ok) ++g_pass;
    else {
        ++g_fail;
        std::printf("  [FAIL] %s\n", what.c_str());
        std::fflush(stdout);
    }
}
static JV load(const std::string& path) {
    std::ifstream f(path);
    if (!f) throw std::runtime_error("cannot open " + path);
    std::stringstream ss;
    ss << f.rdbuf();
    std::string txt = ss.str();
    return hacs_jl_test::JParser(txt).parse();
}
static std::string sha256_file(const std::string& path) {
    std::ifstream f(path, std::ios::binary);
    nf::Sha256 h;
    char buf[1 << 16];
    while (f) {
        f.read(buf, sizeof buf);
        if (f.gcount() > 0) h.update(buf, (size_t)f.gcount());
    }
    return h.hex();
}
static std::string cp_text(const std::vector<Z>& cp) {
    std::string s = "[";
    for (size_t i = 0; i < cp.size(); ++i) s += (i ? "," : "") + cp[i].to_string();
    return s + "]";
}
static std::string json_list_text(const JV& v) {
    std::string s = "[";
    for (size_t i = 0; i < v.a.size(); ++i) s += (i ? "," : "") + v.a[i].s;
    return s + "]";
}
static ZMat zmul(const ZMat& A, const ZMat& B) { return symz::mul(A, B); }
static ZMat zscale(ZMat A, const Z& s) {
    for (auto& r : A)
        for (auto& x : r) x *= s;
    return A;
}
static bool qeqz(const QMat& A, const ZMat& B) {
    for (size_t i = 0; i < A.size(); ++i)
        for (size_t j = 0; j < A[i].size(); ++j)
            if (A[i][j] != Q(B[i][j])) return false;
    return true;
}
static bool comm(const ZMat& A, const ZMat& B) { return zmul(A, B) == zmul(B, A); }

// ---- sparse mod-P helpers for large matrices
static const unsigned __int128 P61 = (((unsigned __int128)1) << 61) - 1;
struct Sp {
    int r = 0, c = 0;
    std::vector<std::vector<std::pair<int, u64>>> rows;
};
static Sp sparse(const ZMat& A) {
    Sp s;
    s.r = (int)A.size();
    s.c = A.empty() ? 0 : (int)A[0].size();
    s.rows.resize(s.r);
    const Z M = Z::from_u64((u64)P61);
    for (int i = 0; i < s.r; ++i)
        for (int j = 0; j < s.c; ++j)
            if (!A[i][j].is_zero()) s.rows[i].push_back({j, (u64)A[i][j].floor_mod(M).to_int64()});
    return s;
}
static std::vector<u64> app(const Sp& A, const std::vector<u64>& v) {
    std::vector<u64> y(A.r, 0);
    for (int i = 0; i < A.r; ++i) {
        unsigned __int128 s = 0;
        for (auto [j, x] : A.rows[i]) s = (s + (unsigned __int128)x * v[j]) % P61;
        y[i] = (u64)s;
    }
    return y;
}
static std::vector<u64> rvec(int n, u64 seed) {
    std::mt19937_64 g(seed);
    std::vector<u64> v(n);
    for (auto& x : v) x = g() % (u64)P61;
    return v;
}
// A B == C D on random vectors (dims compatible)
static bool eq_prod(const Sp& A, const Sp& B, const Sp& C, const Sp& D, int ncols, u64 seed) {
    for (int t = 0; t < 3; ++t) {
        auto v = rvec(ncols, seed + t);
        if (app(A, app(B, v)) != app(C, app(D, v))) return false;
    }
    return true;
}
static std::vector<i64> mat_i64(const ZMat& A) {
    std::vector<i64> m;
    for (const auto& r : A)
        for (const auto& x : r) m.push_back(x.to_int64());
    return m;
}
static std::vector<i64> json_T(const JV& v) {  // transpose of a stored homological matrix
    const size_t r = v.a.size(), c = v.a[0].a.size();
    std::vector<i64> m(r * c);
    for (size_t i = 0; i < r; ++i)
        for (size_t j = 0; j < c; ++j) m[j * r + i] = v[i][j].i();
    return m;
}

// ------------------------------------------------------------------ A. up.json
static std::string test_up(const std::string& dir, bool quick) {
    std::printf("A. up.json (B_3, p = 5, k = 2)\n");
    JV J = load(dir + "/up.json");
    const JV& lv = J["data"]["levels"];
    MaxOrder O(3);
    ClassSet C(O);
    BrandtSym M(C, 0);
    const int smax = quick ? 2 : 3;
    LevelModel Mo(C, 5 * 5 * 5 * 5);  // p N1 for U'_p up to s = 3
    std::vector<std::unique_ptr<LevelSet>> S;
    std::vector<std::unique_ptr<BrandtLevel>> B;
    i64 N = 1;
    for (int s = 1; s <= smax; ++s) {
        N *= 5;
        S.push_back(std::make_unique<LevelSet>(Mo, LevelSpec{N, 1}));
        B.push_back(std::make_unique<BrandtLevel>(M, *S.back()));
    }
    std::ostringstream js;
    js << "{";
    std::vector<std::vector<int>> perms;
    for (int s = 1; s <= smax; ++s) {
        const BrandtLevel& Bs = *B[s - 1];
        const int r = Bs.rank();
        ZMat T2 = Bs.T(2), Up = Bs.T(5), Upr = Bs.Up_prime(5), D2 = Bs.diamond(2);
        bool exact = r <= 60;
        std::string tag = "s=" + std::to_string(s);
        check(r == (int)lv["S_" + std::to_string(s)]["size"].i(), "up.json size " + tag);
        bool perm_ok = true;
        if (lv["S_" + std::to_string(s)].has("T2")) {
            const JV& L = lv["S_" + std::to_string(s)];
            std::vector<Mat> ours{mat_i64(T2), mat_i64(Up), mat_i64(Upr), mat_i64(D2)};
            std::vector<Mat> ref{json_T(L["T2"]), json_T(L["Up"]), json_T(L["Upr"]), json_T(L["diamond_2"])};
            std::vector<int> g(r, 1);
            // audit m3: cheap invariants first (char-poly of a generic combination), then a node-bounded search that
            // fails loudly instead of hanging
            auto comb = [&](const std::vector<Mat>& ops) {
                ZMat A(r, std::vector<Z>(r, Z(0)));
                const i64 c[4] = {1, 3, 7, 11};
                for (int o = 0; o < 4; ++o)
                    for (int i = 0; i < r; ++i)
                        for (int j = 0; j < r; ++j) A[i][j] += Z(c[o] * ops[o][(size_t)i * r + j]);
                return symz::charpoly(A);
            };
            bool inv_ok = comb(ours) == comb(ref);
            check(inv_ok, "up.json: char-poly of T2 + 3 U5 + 7 U5' + 11 <2> equal, " + tag);
            bool exhausted = false;
            auto pm = inv_ok ? match_permutation(ours, ref, r, g, g, 20000000ULL, &exhausted) : std::nullopt;
            check(!exhausted, "up.json: permutation search within the node bound (2e7), " + tag);
            perm_ok = pm.has_value();
            check(perm_ok, "up.json: T2, U5, U5', <2> = stored matrices^T up to a simultaneous permutation, " + tag);
            perms.push_back(pm ? *pm : std::vector<int>());
        }
        // structural checks
        Sp sT2 = sparse(T2), sUp = sparse(Up), sUpr = sparse(Upr), sD2 = sparse(D2);
        bool c1 = exact ? comm(Up, T2) : eq_prod(sUp, sT2, sT2, sUp, r, 11);
        bool c2 = exact ? comm(Up, D2) : eq_prod(sUp, sD2, sD2, sUp, r, 12);
        bool c3 = exact ? comm(Upr, T2) : eq_prod(sUpr, sT2, sT2, sUpr, r, 13);
        bool c4 = exact ? comm(Upr, D2) : eq_prod(sUpr, sD2, sD2, sUpr, r, 14);
        check(c1 && c2 && c3 && c4, "U_p, U'_p commute with T_2, <2>, " + tag);
        // U_p^* = U'_p (all stabilisers trivial, w = 1): U_p^T = U'_p
        bool adj = exact ? qeqz(Bs.adjoint(Up), Upr) : (symz::transpose(Up) == Upr);
        check(adj, "U_p^* = U'_p (lem:s01-Up(d), M = 1), " + tag);
        js << (s > 1 ? ", " : "") << "\"S_" << s << "\": {\"size\": " << r << ", \"matches_up_json_by_permutation\": "
           << (lv["S_" + std::to_string(s)].has("T2") ? (perm_ok ? "true" : "false") : "\"n/a (no stored matrices)\"")
           << ", \"Up_Upr_commute_T2_diamond2\": " << (c1 && c2 && c3 && c4 ? "true" : "false")
           << ", \"Up_adjoint_eq_Upr\": " << (adj ? "true" : "false");
        if (exact) js << ", \"charpoly_Up\": \"" << cp_text(symz::charpoly(Up)) << "\", \"charpoly_T2\": \"" << cp_text(symz::charpoly(T2)) << "\"";
        if (s >= 2) {
            const BrandtLevel& Bc = *B[s - 2];
            ZMat Pi = BrandtLevel::pullback(Bs, Bc), Tr = BrandtLevel::trace(Bs, Bc);
            ZMat Upc = Bc.T(5), Uprc = Bc.Up_prime(5);
            Sp sPi = sparse(Pi), sTr = sparse(Tr), sUpc = sparse(Upc), sUprc = sparse(Uprc);
            bool b = exact ? zmul(Up, Pi) == zmul(Pi, Upc) : eq_prod(sUp, sPi, sPi, sUpc, Bc.rank(), 21);
            bool bf = exact ? zmul(Upr, Pi) == zmul(Pi, Uprc) : eq_prod(sUpr, sPi, sPi, sUprc, Bc.rank(), 22);
            bool c = exact ? zmul(Tr, Upr) == zmul(Uprc, Tr) : eq_prod(sTr, sUpr, sUprc, sTr, r, 23);
            bool cu = exact ? zmul(Tr, Up) == zmul(Upc, Tr) : eq_prod(sTr, sUp, sUpc, sTr, r, 24);
            check(b, "U_p pi^* = pi^* U_p (lem:s01-Up(b)), " + tag);
            check(!bf, "U'_p pi^* != pi^* U'_p (expected failure, lem:s01-Up(c)), " + tag);
            check(c, "tr U'_p = U'_p tr (lem:s01-Up(c)), " + tag);
            js << ", \"pi_star_Up_commute\": " << (b ? "true" : "false") << ", \"pi_star_Upr_commute (expected false)\": "
               << (bf ? "true" : "false") << ", \"trace_Upr_commute\": " << (c ? "true" : "false")
               << ", \"trace_Up_commute (info)\": " << (cu ? "true" : "false");
            if (s == 2 && lv["S_1"].has("T2") && lv["S_2"].has("T2")) {
                // joint matching on S_1 + S_2 (52 points): block-diagonal T2, U5, U5', <2> plus the pi block, levels kept apart
                // by the gamma labels (1 on S_1, 2 on S_2); ref: the stored homological matrices transposed, pi_* transposed
                const BrandtLevel& B1 = *B[0];
                const int r1 = B1.rank(), r2 = r, R = r1 + r2;
                auto blk = [&](const ZMat& A1, const ZMat& A2) {
                    std::vector<i64> m((size_t)R * R, 0);
                    for (int i = 0; i < r1; ++i)
                        for (int j = 0; j < r1; ++j) m[(size_t)i * R + j] = A1[i][j].to_int64();
                    for (int i = 0; i < r2; ++i)
                        for (int j = 0; j < r2; ++j) m[(size_t)(r1 + i) * R + r1 + j] = A2[i][j].to_int64();
                    return m;
                };
                auto blkj = [&](const JV& A1, const JV& A2) {
                    std::vector<i64> m((size_t)R * R, 0);
                    for (int i = 0; i < r1; ++i)
                        for (int j = 0; j < r1; ++j) m[(size_t)i * R + j] = A1[j][i].i();
                    for (int i = 0; i < r2; ++i)
                        for (int j = 0; j < r2; ++j) m[(size_t)(r1 + i) * R + r1 + j] = A2[j][i].i();
                    return m;
                };
                const JV &L1 = lv["S_1"], &L2 = lv["S_2"], &PP = J["data"]["pi_push_S2_to_S1"];
                std::vector<Mat> ours{blk(B1.T(2), T2), blk(B1.T(5), Up), blk(B1.Up_prime(5), Upr), blk(B1.diamond(2), D2)};
                std::vector<Mat> ref{blkj(L1["T2"], L2["T2"]), blkj(L1["Up"], L2["Up"]), blkj(L1["Upr"], L2["Upr"]),
                                     blkj(L1["diamond_2"], L2["diamond_2"])};
                std::vector<i64> po((size_t)R * R, 0), pr((size_t)R * R, 0);
                for (int i = 0; i < r2; ++i)
                    for (int j = 0; j < r1; ++j) {
                        po[(size_t)(r1 + i) * R + j] = Pi[i][j].to_int64();
                        pr[(size_t)(r1 + i) * R + j] = PP[j][i].i();  // (pi_*)^T
                    }
                ours.push_back(po);
                ref.push_back(pr);
                std::vector<int> g(R, 2);
                for (int i = 0; i < r1; ++i) g[i] = 1;
                bool exh = false;
                bool ok = match_permutation(ours, ref, R, g, g, 20000000ULL, &exh).has_value();
                check(!exh, "pi_push joint search within the node bound (2e7)");
                check(ok, "pi_push_S2_to_S1 = (pi^*)^T jointly with all S_1, S_2 operators (one permutation)");
                js << ", \"pi_push_matches_jointly\": " << (ok ? "true" : "false");
            }
        }
        js << "}";
    }
    js << "}";
    return js.str();
}

// ------------------------------------------------------------------ B. pi_sign.json at level O^x
static std::string test_pi_sign(const std::string& dir) {
    std::printf("B. pi_sign.json through BrandtLevel at O^x\n");
    JV J = load(dir + "/pi_sign.json");
    std::ostringstream js;
    js << "{";
    bool first = true, all = true;
    for (const auto& kv : J["data"]["grid"].o) {
        const JV& br = kv.second["brandt"];
        const i64 D = kv.second["D"].i();
        const int k = (int)kv.second["k"].i();
        MaxOrder O(D);
        ClassSet C(O);
        BrandtSym M(C, k - 2);
        LevelModel Mo(C, 1);
        LevelSet X(Mo, {1, 1});
        BrandtLevel BL(M, X);
        ZMat P = BL.Pi(D);
        bool ok = BL.rank() == (int)br["dim"].i();
        // same operators as BrandtSym (block permutation): equal char-polys
        ok &= symz::charpoly(P) == symz::charpoly(M.Pi(D));
        for (const auto& es : br["eigenspaces"].o) {
            Z lam = Z::from_string(es.second["lambda"].s);
            for (const auto& cpj : es.second["charpoly_T"].o) {
                ZMat R = symz::restrict_to_eigenspace(BL.T(std::stoll(cpj.first)), P, lam);
                ok &= cp_text(symz::charpoly(R)) == json_list_text(cpj.second);
            }
            ok &= (int)symz::restrict_to_eigenspace(P, P, lam).size() == (int)es.second["dim"].i();
        }
        check(ok, "pi_sign via BrandtLevel " + kv.first);
        all &= ok;
        js << (first ? "" : ", ") << "\"" << kv.first << "\": " << (ok ? "true" : "false");
        first = false;
    }
    js << ", \"all\": " << (all ? "true" : "false") << "}";
    return js.str();
}

// ------------------------------------------------------------------ C. levels with Sym^n
static i64 md_pos(i64 a, i64 m) { return ((a % m) + m) % m; }
static i64 inv_pos(i64 a, i64 m) {
    for (i64 x = 1; x < m; ++x)
        if (md_pos(a * x, m) == 1) return x;
    throw std::logic_error("inv_pos");
}
struct Case {
    i64 D, N1, N0;
    int k;
};
static std::string test_levels(bool quick) {
    std::printf("C. Sym^n at U_0(M), U_1(N), mixed\n");
    std::vector<Case> cs;
    for (i64 D : {2, 3, 5, 7, 11, 13})
        for (int k : {2, 4, 6}) {
            int nm = 0;
            for (i64 Mm : {2, 3, 5, 7})
                if (D % Mm && nm < 2) {
                    cs.push_back({D, 1, Mm, k});
                    ++nm;
                }
            if (D % 2) cs.push_back({D, 1, 4, k});
            if (D % 2 && D % 3) cs.push_back({D, 1, 6, k});
            if (k <= 4)
                for (i64 Nn : {3, 4, 5})
                    if (std::gcd(Nn, D) == 1) {
                        cs.push_back({D, Nn, 1, k});
                        break;
                    }
        }
    cs.push_back({2, 3, 5, 2});
    cs.push_back({2, 3, 5, 4});
    cs.push_back({3, 4, 5, 2});
    cs.push_back({7, 5, 3, 2});
    cs.push_back({2, 15, 1, 2});
    cs.push_back({11, 5, 1, 4});
    // audit m1: U_1(N) with <ell> != <ell>^-1 (N = 7, 9, 13), so that the adjoint / square signs are decided
    for (i64 D : {2, 3, 5})
        for (i64 Nn : {7, 9, 13})
            for (int k : {2, 4})
                if (std::gcd(Nn, D) == 1) cs.push_back({D, Nn, 1, k});
    // ... and the cells that decide U_p^* = <p>_M U'_p (M > 1 with <p>_M != <p>_M^-1) and W_ell^2 (mixed, <ell> != <ell>^-1)
    cs.push_back({2, 21, 1, 2});
    cs.push_back({5, 14, 1, 2});
    cs.push_back({2, 7, 3, 2});
    cs.push_back({5, 7, 2, 2});
    cs.push_back({2, 7, 3, 4});
    std::ostringstream js;
    js << "[";
    bool first = true;
    for (const auto& cc : cs) {
        if (quick && (cc.k > 4 || cc.D > 7)) continue;
        const i64 D = cc.D;
        const int n = cc.k - 2;
        MaxOrder O(D);
        ClassSet C(O);
        BrandtSym M(C, n);
        // model modulus: N1 N0 times every prime of N1 (for U'_p)
        i64 Nb = cc.N1 * cc.N0;
        for (i64 p : prime_factors(cc.N1)) Nb *= p;
        LevelModel Mo(C, Nb);
        LevelSet X(Mo, {cc.N1, cc.N0});
        BrandtLevel BL(M, X);
        const int r = BL.rank();
        const i64 N = cc.N1 * cc.N0;
        std::string tag = "D=" + std::to_string(D) + " " + X.spec().str() + " k=" + std::to_string(cc.k);
        js << (first ? "" : ",") << "\n   {\"D\": " << D << ", \"N1\": " << cc.N1 << ", \"N0\": " << cc.N0 << ", \"k\": " << cc.k
           << ", \"cells\": " << X.size() << ", \"rank\": " << r;
        first = false;
        if (r == 0) {
            js << "}";
            continue;
        }
        std::vector<std::pair<std::string, ZMat>> ops;
        std::map<i64, ZMat> T, U, W, Pi, Dm;
        for (i64 l : {2, 3, 5, 7, 11})
            if (D % l && N % l) T[l] = BL.T(l), ops.push_back({"T" + std::to_string(l), T[l]});
        for (i64 l : prime_factors(N)) U[l] = BL.T(l), ops.push_back({"U" + std::to_string(l), U[l]});
        if (cc.N1 > 2)
            for (i64 d = 2; d < cc.N1; ++d)
                if (std::gcd(d, cc.N1) == 1) Dm[d] = BL.diamond(d), ops.push_back({"<" + std::to_string(d) + ">", Dm[d]});
        for (i64 p : prime_factors(D)) Pi[p] = BL.Pi(p), ops.push_back({"Pi" + std::to_string(p), Pi[p]});
        for (i64 l : prime_factors(cc.N0))
            if ((cc.N0 / l) % l && cc.N1 % l) W[l] = BL.W(l), ops.push_back({"W" + std::to_string(l), W[l]});
        bool cm = true;
        for (size_t i = 0; i < ops.size(); ++i)
            for (size_t j = i + 1; j < ops.size(); ++j) {
                const std::string &a = ops[i].first, &b = ops[j].first;
                if ((a[0] == 'W' && b[0] == 'U' && a.substr(1) == b.substr(1)) ||
                    (b[0] == 'W' && a[0] == 'U' && a.substr(1) == b.substr(1)))
                    continue;
                bool c = comm(ops[i].second, ops[j].second);
                if (!c) std::printf("    non-commuting %s %s (%s)\n", a.c_str(), b.c_str(), tag.c_str());
                cm &= c;
            }
        check(cm, "all operators commute " + tag);
        auto diam = [&](i64 d) -> ZMat {
            if (cc.N1 <= 2) return symz::identity(r);
            return BL.diamond(md_pos(d, cc.N1));
        };
        // adjoints and squares (audit m1): for each relation record whether the claimed sign holds and whether the OTHER
        // sign holds too ("both" = this cell does not decide the sign); the claimed signs are
        //   T_ell^* = <ell> T_ell,  U_p^* = <p>_M U'_p,  Pi_p^2 = p^n <p>^-1,  W_ell^2 = ell^n <ell>^-1  (<.> = identity if N1 <= 2)
        auto sgn = [&](bool claimed, bool other) -> std::string {
            return claimed ? (other ? "both" : "claimed only") : (other ? "OTHER only" : "none");
        };
        auto note = [&](const std::string& rel, const std::string& res) {
            g_sign[rel].first += res == "claimed only";
            g_sign[rel].second += res != "claimed only" && res != "both";
        };
        for (auto& kv : T) {
            const i64 l = kv.first;
            QMat A = BL.adjoint(kv.second);
            bool cl = qeqz(A, zmul(diam(l), kv.second));
            bool ot = cc.N1 > 2 ? qeqz(A, zmul(diam(inv_pos(l, cc.N1)), kv.second)) : cl;
            std::string res = sgn(cl, ot);
            note("T_ell^* = <ell> T_ell", res);
            check(cl, "T_ell^* = <ell> T_ell (" + res + ") " + tag + " ell=" + std::to_string(l));
            js << ", \"T" << l << "_adjoint\": \"" << res << "\"";
        }
        // U_p^* vs <p>_M^{+-1} U'_p at U_1(p^s M), p not | N0
        for (i64 p : prime_factors(cc.N1)) {
            if (cc.N0 % p == 0) continue;
            ZMat Upr = BL.Up_prime(p);
            i64 ps = 1;
            while (cc.N1 % (ps * p) == 0) ps *= p;
            i64 Mm = cc.N1 / ps;
            i64 d = 1;  // p mod M, 1 mod p^s
            while (!(d % ps == 1 % ps && (Mm == 1 || d % Mm == p % Mm))) ++d;
            i64 di = 1;  // p^-1 mod M, 1 mod p^s
            while (!(di % ps == 1 % ps && (Mm == 1 || (di * p) % Mm == 1 % Mm))) ++di;
            QMat A = BL.adjoint(U[p]);
            std::string res = sgn(qeqz(A, zmul(diam(d), Upr)), qeqz(A, zmul(diam(di), Upr)));
            note("U_p^* = <p>_M U'_p", res);
            check(res == "claimed only" || res == "both", "U_p^* = <p>_M U'_p (" + res + ") " + tag + " p=" + std::to_string(p));
            bool cmT = true;
            for (auto& kv : T) cmT &= comm(Upr, kv.second);
            check(cmT, "U'_p commutes with T_ell " + tag);
            js << ", \"U" << p << "_adjoint\": \"" << res << "\"";
        }
        auto square = [&](const std::string& name, i64 l, const ZMat& S2) {
            ZMat base = zscale(symz::identity(r), Z::pow(Z(l), (uint64_t)n));
            bool cl = cc.N1 > 2 ? S2 == zmul(base, diam(inv_pos(l, cc.N1))) : S2 == base;
            bool ot = cc.N1 > 2 ? S2 == zmul(base, diam(md_pos(l, cc.N1))) : cl;
            std::string res = sgn(cl, ot);
            note(name + "^2 = ell^n <ell>^-1", res);
            check(cl, name + "^2 = ell^n <ell>^-1 (" + res + ") " + tag);
            js << ", \"" << name << l << "_squared\": \"" << res << "\"";
        };
        for (auto& kv : Pi) square("Pi", kv.first, zmul(kv.second, kv.second));
        for (auto& kv : W) {
            square("W", kv.first, zmul(kv.second, kv.second));
            bool sa = qeqz(BL.adjoint(kv.second), kv.second);
            js << ", \"W" << kv.first << "_self_adjoint (recorded)\": " << (sa ? "true" : "false");
        }
        bool saPi = true;
        for (auto& kv : Pi) saPi &= qeqz(BL.adjoint(kv.second), kv.second);
        js << ", \"Pi_self_adjoint\": " << (saPi ? "true" : "false");
        if (cc.k == 2 && cc.N1 == 1) {
            // the constant function: every cell has Zinv = [1]
            bool eis = true;
            for (auto& kv : T)
                for (const auto& row : kv.second) {
                    Z s(0);
                    for (const auto& x : row) s += x;
                    eis &= s == Z(kv.first + 1);
                }
            check(eis, "k=2 U_0: T_ell 1 = (ell+1) 1 " + tag);
        }
        js << ", \"commute_all\": " << (cm ? "true" : "false") << ", \"charpoly\": {";
        bool f2 = true;
        for (auto& kv : T) {
            js << (f2 ? "" : ", ") << "\"T" << kv.first << "\": \"" << cp_text(symz::charpoly(kv.second)) << "\"";
            f2 = false;
        }
        for (auto& kv : U) {
            js << (f2 ? "" : ", ") << "\"U" << kv.first << "\": \"" << cp_text(symz::charpoly(kv.second)) << "\"";
            f2 = false;
        }
        js << "}}";
    }
    js << "]";
    std::string sum = "{";
    bool f3 = true;
    for (const auto& kv : g_sign) {
        check(kv.second.first > 0 && kv.second.second == 0,
              "sign of " + kv.first + " decided on " + std::to_string(kv.second.first) + " cells, contradicted on " +
                  std::to_string(kv.second.second));
        sum += (f3 ? "\"" : ", \"") + kv.first + "\": {\"decisive_cells\": " + std::to_string(kv.second.first) +
               ", \"contradicting_cells\": " + std::to_string(kv.second.second) + "}";
        f3 = false;
    }
    g_sign_json = sum + "}";
    return js.str();
}

// ------------------------------------------------------------------ D. Eichler level O_0(q)
static std::string test_eichler(bool quick) {
    std::printf("D. Eichler level O_0(q): s0^*, s1^*\n");
    std::ostringstream js;
    js << "[";
    bool first = true;
    for (i64 D : {2, 3, 5, 11, 13})
        for (i64 q : {2, 3, 5, 7})
            for (int k : {2, 4, 6}) {
                if (D % q == 0 || (quick && k > 4)) continue;
                MaxOrder O(D);
                ClassSet C(O);
                BrandtSym M(C, k - 2);
                LevelModel Mo(C, q);
                LevelSet Xs(Mo, {1, 1}), Es(Mo, {1, q});
                BrandtLevel X(M, Xs), E(M, Es);
                if (X.rank() == 0) continue;
                ZMat s0 = BrandtLevel::pullback(E, X), s1 = BrandtLevel::degeneracy_s1(E, X, q);
                bool ok = true;
                for (i64 l : {2, 3, 5, 7})
                    if (D % l && l != q) {
                        ZMat TX = X.T(l), TE = E.T(l);
                        ok &= zmul(TE, s0) == zmul(s0, TX) && zmul(TE, s1) == zmul(s1, TX);
                    }
                // s0^dagger = G_X^{-1} s0^T G_E
                QMat GE = E.gram(true), GX = X.gram(true);
                ZMat s0t = symz::transpose(s0);
                QMat a(s0t.size()), b(s1.size());
                for (size_t i = 0; i < s0t.size(); ++i)
                    for (auto& x : s0t[i]) a[i].push_back(Q(x));
                for (size_t i = 0; i < s1.size(); ++i)
                    for (auto& x : s1[i]) b[i].push_back(Q(x));
                QMat lhs = symz::mul(symz::mul(a, GE), b);  // s0^T G_E s1
                ZMat Tq = X.T(q);
                QMat rhs = symz::mul(GX, [&] {
                    QMat t(Tq.size());
                    for (size_t i = 0; i < Tq.size(); ++i)
                        for (auto& x : Tq[i]) t[i].push_back(Q(x));
                    return t;
                }());
                bool tq = lhs == rhs;  // <=> s0^dagger s1^* = T_q
                std::string tag = "D=" + std::to_string(D) + " q=" + std::to_string(q) + " k=" + std::to_string(k);
                check(ok, "s0^*, s1^* commute with T_ell " + tag);
                check(tq, "T_q = s0^dagger s1^* " + tag);
                // audit m5: the old-form relations at O_0(q) that separate U_q from W U_q W^-1 and fix s0, s1
                ZMat Uq = E.T(q), Wq = E.W(q);
                const Z qn = Z::pow(Z(q), (uint64_t)(k - 2)), qk1 = Z::pow(Z(q), (uint64_t)(k - 1));
                ZMat s0Tq = zmul(s0, Tq);
                for (size_t i = 0; i < s0Tq.size(); ++i)
                    for (size_t j = 0; j < s0Tq[i].size(); ++j) s0Tq[i][j] -= s1[i][j];
                bool ra = zmul(Uq, s0) == s0Tq;                 // U_q s0^* = s0^* T_q - s1^*
                bool rb = zmul(Uq, s1) == zscale(s0, qk1);      // U_q s1^* = q^{k-1} s0^*
                bool rc = zmul(Wq, s0) == s1;                   // W_q s0^* = s1^*
                bool rd = zmul(Wq, s1) == zscale(s0, qn);       // W_q s1^* = q^n s0^*
                // U_q + W_q = s0^* s0^dagger W_q, i.e. G_E (U_q + W_q) = (s0^T G_E)^T G_X^-1 (s0^T G_E) W_q
                QMat sTG = symz::mul(a, GE);  // s0^T G_E
                QMat GXinv = [&] {  // G_X^-1 by Gauss-Jordan
                    const int rx = X.rank();
                    QMat A2 = GX, I2(rx, std::vector<Q>(rx, Q(0)));
                    for (int i = 0; i < rx; ++i) I2[i][i] = Q(1);
                    for (int c = 0; c < rx; ++c) {
                        int p = c;
                        while (A2[p][c].is_zero()) ++p;
                        std::swap(A2[p], A2[c]);
                        std::swap(I2[p], I2[c]);
                        Q iv = Q(1) / A2[c][c];
                        for (int j = 0; j < rx; ++j) {
                            A2[c][j] *= iv;
                            I2[c][j] *= iv;
                        }
                        for (int rr = 0; rr < rx; ++rr)
                            if (rr != c && !A2[rr][c].is_zero()) {
                                Q fct = A2[rr][c];
                                for (int j = 0; j < rx; ++j) {
                                    A2[rr][j] -= fct * A2[c][j];
                                    I2[rr][j] -= fct * I2[c][j];
                                }
                            }
                    }
                    return I2;
                }();
                QMat sTGt(sTG[0].size(), std::vector<Q>(sTG.size()));
                for (size_t i = 0; i < sTG.size(); ++i)
                    for (size_t j = 0; j < sTG[i].size(); ++j) sTGt[j][i] = sTG[i][j];
                QMat Wqq(Wq.size()), UW(Wq.size());
                for (size_t i = 0; i < Wq.size(); ++i)
                    for (size_t j = 0; j < Wq.size(); ++j) {
                        Wqq[i].push_back(Q(Wq[i][j]));
                        UW[i].push_back(Q(Uq[i][j] + Wq[i][j]));
                    }
                bool re = symz::mul(GE, UW) == symz::mul(symz::mul(symz::mul(sTGt, GXinv), sTG), Wqq);
                check(ra, "U_q s0^* = s0^* T_q - s1^* " + tag);
                check(rb, "U_q s1^* = q^(k-1) s0^* " + tag);
                check(rc && rd, "W_q s0^* = s1^*, W_q s1^* = q^n s0^* " + tag);
                check(re, "U_q + W_q = s0^* s0^dagger W_q " + tag);
                js << (first ? "" : ",") << "\n   {\"relations\": {\"Uq_s0 = s0_Tq - s1\": " << (ra ? "true" : "false")
                   << ", \"Uq_s1 = q^(k-1) s0\": " << (rb ? "true" : "false") << ", \"Wq_s0 = s1, Wq_s1 = q^n s0\": "
                   << (rc && rd ? "true" : "false") << ", \"Uq + Wq = s0 s0^dagger Wq\": " << (re ? "true" : "false") << "}, ";
                first = true;
                js << (first ? "" : ",") << "\"D\": " << D << ", \"q\": " << q << ", \"k\": " << k << ", \"rank_X\": " << X.rank()
                   << ", \"rank_E\": " << E.rank() << ", \"s_j_commute_T\": " << (ok ? "true" : "false")
                   << ", \"Tq_eq_s0dagger_s1\": " << (tq ? "true" : "false") << "}";
                first = false;
            }
    js << "]";
    return js.str();
}

int main(int argc, char** argv) {
    std::string repo = hacs_jl_test::repo_root_guess(__FILE__);
    std::string dir = repo + "/code/results/s01", write;
    bool quick = false;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--results" && i + 1 < argc) dir = argv[++i];
        else if (a == "--write" && i + 1 < argc) write = argv[++i];
        else if (a == "--quick") quick = true;
    }
    auto t0 = std::chrono::steady_clock::now();
    std::string ja, jb, jc, jd;
    try {
        ja = test_up(dir, quick);
        jb = test_pi_sign(dir);
        jc = test_levels(quick);
        jd = test_eichler(quick);
    } catch (const std::exception& e) {
        check(false, std::string("exception: ") + e.what());
    }
    double rt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::printf("brandtlevel_selftest: %d passed, %d failed (%.1f s)\n", g_pass, g_fail, rt);
    if (!write.empty()) {
        std::time_t t = std::time(nullptr);
        char date[64];
        std::strftime(date, sizeof date, "%Y-%m-%dT%H:%M:%SZ", std::gmtime(&t));
        std::string commit = hacs_jl_test::run_capture("git -C '" + repo + "' rev-parse HEAD 2>/dev/null");
        if (commit.empty()) commit = "unknown";
        else if (!hacs_jl_test::run_capture("git -C '" + repo + "' status --porcelain -- code/hacs/src/hacs/Registry/JL/quat 2>/dev/null").empty())
            commit += "-dirty";
        std::ofstream f(write);
        f << "{\"provenance\": {\"script\": \"code/hacs/src/hacs/Registry/JL/quat/tests/brandtlevel_selftest.cpp\", \"commit\": \"" << commit
          << "\", \"params\": {\"quick\": " << (quick ? "true" : "false")
          << ", \"references\": [\"code/results/s01/up.json\", \"code/results/s01/pi_sign.json\"]}, \"date\": \"" << date
          << "\", \"runtime_s\": " << rt << ", \"binary_sha256\": \"" << sha256_file("/proc/self/exe") << "\", \"tag\": \"computed\""
          << ", \"checks_passed\": " << g_pass << ", \"checks_failed\": " << g_fail << "},\n \"data\": {"
          << "\"conventions\": \"BrandtLevel.h (B1)-(B8): Gross form at level, data move by the Hecke element; U_ell CLASSICAL "
             "(sum_j F(x iota^-1[[ell,j],[0,1]]), no p^{k/2-1}); <d>: v -> d^-1 v (adelic); Pi_p, W_ell unnormalised; "
             "matrices on functions, column convention\",\n  \"up\": "
          << ja << ",\n  \"pi_sign\": " << jb << ",\n  \"sign_summary\": " << g_sign_json << ",\n  \"levels\": " << jc << ",\n  \"eichler\": " << jd << "}}\n";
        std::printf("wrote %s\n", write.c_str());
    }
    return g_fail;
}
