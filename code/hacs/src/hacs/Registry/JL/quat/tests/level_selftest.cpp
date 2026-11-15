// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// Standalone self-test of the level structures (WP HJ-3, Level.h). Not registered in HACS.
//   level_selftest [--results DIR] [--write PATH] [--quick]
// Checks (exit code = number of failures):
//   A. code/results/s01/levels.json: the 13 mass level changes (index, factor_two, both masses, both conventions),
//      |X_B(U_1(5))| at D = 2, trivial stabilisers at U_1(p) (D <= 13, p in {5, 7, 11}), the towers
//      (D, p, smax) = (3, 5, 3), (2, 5, 3), (3, 7, 2): sizes, expected sizes, Delta_s free.
//   B. new: the tower B_3, p = 5 to s = 4 (|S_4| = 31 250 = 2 * 25^3), mass(S_s) = phi(D)/24 psi(N) phi(N),
//      pi_{s+1,s} surjective with fibre sums sum stab_x / stab_y = p^2, pi o <d> = <d> o pi, Delta_4 free.
//   C. code/results/s02/validation.json (240 cases): X, E, vertex/edge masses, and the fibre sums
//      sum_{e in s_j^{-1}(x)} |Gamma_x| / |Gamma_e| = q + 1 for j = 0, 1 (s1 by the transport (L4)/(L5));
//      cross-check X, E and the stabiliser multisets against HJ-7a's build_tree (independent fibre code).
#include "../Level.h"
#include "../../../../NumberField/Sha256.h"
#include "JsonMin.h"
#include "RepoRoot.h"

#include <chrono>
#include <cstdio>
#include <ctime>
#include <fstream>
#include <numeric>
#include <sstream>

using namespace hacs_jl;
using hacs_jl_test::JV;

static int g_fail = 0, g_pass = 0;
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
static std::string run_cmd(const std::string& cmd) {
    std::string out;
    FILE* p = popen(cmd.c_str(), "r");
    if (!p) return "";
    char buf[256];
    while (fgets(buf, sizeof buf, p)) out += buf;
    pclose(p);
    while (!out.empty() && (out.back() == '\n' || out.back() == '\r')) out.pop_back();
    return out;
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
static std::string fr(std::pair<i128, i128> f) { return frac_str(f.first, f.second); }
static i64 phi_fn(i64 n) {
    i64 r = 1;
    for (i64 p : prime_factors(n)) {
        i64 k = n;
        i64 pk = 1;
        while (k % p == 0) {
            k /= p;
            pk *= p;
        }
        r *= pk / p * (p - 1);
    }
    return r;
}
static i64 psi_fn(i64 n) {
    i64 r = n;
    for (i64 p : prime_factors(n)) r = r / p * (p + 1);
    return r;
}
static std::string mults(std::vector<int> v) {
    std::sort(v.begin(), v.end());
    std::string s;
    for (int x : v) s += std::to_string(x) + ",";
    return s;
}

struct Out {
    std::ostringstream mass, misc, tower, val;
};

// ------------------------------------------------------------------ A. levels.json
static void test_levels_json(const std::string& dir, Out& o) {
    std::printf("A. levels.json\n");
    JV J = load(dir + "/levels.json");
    const JV& d = J["data"];
    bool first = true;
    o.mass << "[";
    for (const auto& r : d["mass_level_change"].a) {
        const i64 D = r["D"].i();
        const i64 n1 = r["U"][0].i(), n0 = r["U"][1].i(), m1 = r["Uprime"][0].i(), m0 = r["Uprime"][1].i();
        MaxOrder O(D);
        ClassSet C(O);
        LevelModel Mo(C, m1 * m0 * (n1 * n0 / std::gcd(n1 * n0, m1 * m0)));
        LevelSet X(Mo, {n1, n0}), Y(Mo, {m1, m0});
        const i64 idx = Y.index() / X.index();
        const bool f2 = X.minus_one_in_U() && !Y.minus_one_in_U();
        auto mx = X.mass(), my = Y.mass(), wx = X.massW(), wy = Y.massW();
        bool ok_full = my.first * mx.second == (i128)idx * mx.first * my.second;
        bool ok_w = (f2 ? 2 : 1) * wy.first * wx.second == (i128)idx * wx.first * wy.second;
        std::string tag = "D=" + std::to_string(D) + " " + LevelSpec{n1, n0}.str() + " > " + LevelSpec{m1, m0}.str();
        bool ok = idx == r["index"].i() && f2 == r["factor_two"].b && fr(mx) == r["mass_U"].s && fr(my) == r["mass_Up"].s &&
                  fr(wx) == r["massW_U"].s && fr(wy) == r["massW_Up"].s && ok_full && ok_w;
        check(ok, "mass level change " + tag + " ours " + fr(mx) + " " + fr(my) + " " + fr(wx) + " " + fr(wy));
        // the projection Y -> X: fibre sums sum stab_x / stab_y = index
        auto pr = project(Y, X);
        std::vector<i128> acc(X.size(), 0);
        for (int y = 0; y < Y.size(); ++y) acc[pr[y]] += (i128)X.cells()[pr[y]].stab * (24 / Y.cells()[y].stab);
        bool fs = true;
        for (auto v : acc) fs &= v == 24 * (i128)idx;
        check(fs, "projection fibre sums = index " + tag);
        o.mass << (first ? "" : ",") << "\n   {\"D\": " << D << ", \"U\": [" << n1 << "," << n0 << "], \"Uprime\": [" << m1 << ","
               << m0 << "], \"index\": " << idx << ", \"factor_two\": " << (f2 ? "true" : "false") << ", \"mass_U\": \"" << fr(mx)
               << "\", \"mass_Up\": \"" << fr(my) << "\", \"massW_U\": \"" << fr(wx) << "\", \"massW_Up\": \"" << fr(wy)
               << "\", \"sizes\": [" << X.size() << "," << Y.size() << "], \"ok_full\": " << (ok_full ? "true" : "false")
               << ", \"ok_w\": " << (ok_w ? "true" : "false") << ", \"projection_fibre_sums\": " << (fs ? "true" : "false")
               << ", \"matches_levels_json\": " << (ok ? "true" : "false") << "}";
        first = false;
    }
    o.mass << "]";
    {
        MaxOrder O(2);
        ClassSet C(O);
        LevelModel Mo(C, 5);
        LevelSet X(Mo, {5, 1});
        check(X.size() == (int)d["x_u1_5_D2"].i(), "|X_B(U_1(5))| at D = 2");
        o.misc << "\"x_u1_5_D2\": " << X.size() << ", \"trivial_stab_u1p\": {";
    }
    first = true;
    for (const auto& kv : d["trivial_stab_u1p"].o) {
        i64 D = std::stoll(kv.first.substr(2)), p = std::stoll(kv.first.substr(kv.first.find("p=") + 2));
        MaxOrder O(D);
        ClassSet C(O);
        LevelModel Mo(C, p);
        LevelSet X(Mo, {p, 1});
        bool triv = true;
        for (int s : X.stabs()) triv &= s == 1;
        check(X.size() == (int)kv.second["size"].i() && triv == kv.second["all_gamma_trivial"].b, "trivial stab " + kv.first);
        o.misc << (first ? "" : ", ") << "\"" << kv.first << "\": {\"size\": " << X.size()
               << ", \"all_gamma_trivial\": " << (triv ? "true" : "false") << "}";
        first = false;
    }
    o.misc << "}";
    first = true;
    o.tower << "{";
    for (const auto& kv : d["tower"].o) {
        i64 D = std::stoll(kv.first.substr(2)), p = std::stoll(kv.first.substr(kv.first.find("p=") + 2));
        int smax = (int)kv.second["sizes"].o.size();
        if (D == 3 && p == 5) smax = 4;  // B: extended to s = 4
        MaxOrder O(D);
        ClassSet C(O);
        Tower T(C, p, smax);
        o.tower << (first ? "" : ",") << "\n   \"D=" << D << ",p=" << p << "\": {\"sizes\": {";
        first = false;
        std::ostringstream ex, fr_, ms;
        for (int s = 1; s <= smax; ++s) {
            const LevelSet& S = T.S(s);
            i64 N = 1;
            for (int t = 0; t < s; ++t) N *= p;
            // expected size phi(D)/24 psi(N) phi(N) (all stabilisers trivial)
            i128 en = (i128)phi_fn(D) * psi_fn(N) * phi_fn(N);
            std::string exp = frac_str(en, 24);
            bool free = T.delta_free(s);
            auto m = S.mass();
            bool mass_id = m.first * 24 == en * m.second;  // mass(S_s) = phi(D)/24 * [O^x : U_1(p^s)]
            std::string ss = std::to_string(s);
            if (kv.second["sizes"].has(ss)) {
                check(S.size() == (int)kv.second["sizes"][ss].i(), "tower size " + kv.first + " s=" + ss);
                check(exp == kv.second["expected"][ss].s + (kv.second["expected"][ss].s.find('/') == std::string::npos ? "/1" : ""),
                      "tower expected " + kv.first + " s=" + ss);
                check(free == kv.second["delta_free"][ss].b, "tower delta_free " + kv.first + " s=" + ss);
            }
            check(mass_id, "tower mass identity " + kv.first + " s=" + ss);
            if (D == 3 && p == 5 && s == 4) check(S.size() == 31250, "|S_4| = 31250 (B_3, p = 5)");
            o.tower << (s > 1 ? ", " : "") << "\"" << s << "\": " << S.size();
            ex << (s > 1 ? ", " : "") << "\"" << s << "\": \"" << exp << "\"";
            fr_ << (s > 1 ? ", " : "") << "\"" << s << "\": " << (free ? "true" : "false");
            ms << (s > 1 ? ", " : "") << "\"" << s << "\": \"" << fr(m) << "\"";
        }
        // tower maps
        std::ostringstream pis;
        bool all_pi = true;
        for (int s = 2; s <= smax; ++s) {
            auto pi = T.pi(s);
            const LevelSet &A = T.S(s), &B = T.S(s - 1);
            std::vector<i128> acc(B.size(), 0);
            for (int y = 0; y < A.size(); ++y) acc[pi[y]] += (i128)B.cells()[pi[y]].stab * (24 / A.cells()[y].stab);
            bool fs = true;
            for (auto v : acc) fs &= v == 24 * (i128)(p * p);
            // pi o <d> = <d> o pi for d = 2 (a generator-ish unit) and d = 1 + p
            bool comm = true;
            i64 ps = 1;
            for (int t = 0; t < s; ++t) ps *= p;
            for (i64 dd : {(i64)2, (i64)(1 + p)}) {
                if (std::gcd(dd, p) != 1) continue;
                auto da = T.diamond(s, dd), db = T.diamond(s - 1, dd % (ps / p) ? dd % (ps / p) : dd);
                for (int y = 0; y < A.size(); ++y) comm &= pi[da[y]] == db[pi[y]];
            }
            check(fs, "pi_{s,s-1} fibre sums = p^2, " + kv.first + " s=" + std::to_string(s));
            check(comm, "pi o <d> = <d> o pi, " + kv.first + " s=" + std::to_string(s));
            all_pi &= fs && comm;
            pis << (s > 2 ? ", " : "") << "\"" << s << "\": {\"fibre_sums_p2\": " << (fs ? "true" : "false")
                << ", \"commutes_with_diamonds\": " << (comm ? "true" : "false") << "}";
        }
        o.tower << "}, \"expected\": {" << ex.str() << "}, \"delta_free\": {" << fr_.str() << "}, \"mass\": {" << ms.str()
                << "}, \"pi\": {" << pis.str() << "}}";
    }
    o.tower << "}";
}

// ------------------------------------------------------------------ C. validation.json
static void test_validation(const std::string& dir, bool quick, Out& o) {
    std::printf("C. s02/validation.json\n");
    JV J = load(dir + "/../s02/validation.json");
    int n = 0, ok_all = 0, tree_ok = 0;
    std::map<i64, std::unique_ptr<MaxOrder>> Os;
    std::map<i64, std::unique_ptr<ClassSet>> Cs;
    o.val << "[";
    for (const auto& cs : J["data"]["cases"].a) {
        const i64 D = cs["D"].i(), q = cs["q"].i(), N1 = cs["level"]["N1"].i(), N0 = cs["level"]["N0"].i();
        if (quick && D > 13) continue;
        if (!Os.count(D)) {
            Os[D] = std::make_unique<MaxOrder>(D);
            Cs[D] = std::make_unique<ClassSet>(*Os[D]);
        }
        const ClassSet& C = *Cs[D];
        LevelModel Mo(C, N1 * N0 * q);
        LevelSet X(Mo, {N1, N0}), E(Mo, {N1, N0 * q});
        auto R = u0q_correspondence(E, X, q);
        bool f0 = fibre_sums_ok(E, X, R.s0, q), f1 = fibre_sums_ok(E, X, R.s1, q);
        auto vm = X.mass(), em = E.mass();
        bool m = em.first * vm.second == (i128)(q + 1) * vm.first * em.second;
        std::string tag = "D=" + std::to_string(D) + " q=" + std::to_string(q) + " " + LevelSpec{N1, N0}.str();
        bool ok = X.size() == (int)cs["X"].i() && E.size() == (int)cs["E"].i() && fr(vm) == cs["vertex_mass"].s &&
                  fr(em) == cs["edge_mass"].s && f0 && f1 && m;
        check(ok, "validation " + tag + " X=" + std::to_string(X.size()) + " E=" + std::to_string(E.size()) + " f0=" +
                      std::to_string(f0) + " f1=" + std::to_string(f1));
        // independent cross-check against HJ-7a's Tree builder
        TreeLevel TL;
        TL.N1 = N1;
        TL.N0 = N0;
        TreeQuotient T = build_tree(C, q, TL, TreeOptions{false});
        bool tok = T.X() == X.size() && T.nE() == E.size() && mults(T.stab_v()) == mults(X.stabs()) &&
                   mults(T.stab_e()) == mults(E.stabs());
        // s0/s1 degree sequences agree as multisets (graph invariants)
        std::vector<int> d0(X.size(), 0), d1(X.size(), 0), t0(T.X(), 0), t1(T.X(), 0);
        for (int e = 0; e < E.size(); ++e) {
            ++d0[R.s0[e]];
            ++d1[R.s1[e]];
        }
        for (int e = 0; e < T.nE(); ++e) {
            ++t0[T.s0[e]];
            ++t1[T.s1[e]];
        }
        tok &= mults(d0) == mults(t0) && mults(d1) == mults(t1);
        check(tok, "Level = Tree (X, E, stabilisers, degrees) " + tag);
        ++n;
        ok_all += ok;
        tree_ok += tok;
        o.val << (n > 1 ? "," : "") << "\n   {\"D\": " << D << ", \"q\": " << q << ", \"level\": {\"N1\": " << N1 << ", \"N0\": " << N0
              << "}, \"X\": " << X.size() << ", \"E\": " << E.size() << ", \"vertex_mass\": \"" << fr(vm) << "\", \"edge_mass\": \""
              << fr(em) << "\", \"fibre_sums_s0\": " << (f0 ? "true" : "false") << ", \"fibre_sums_s1\": " << (f1 ? "true" : "false")
              << ", \"mass\": " << (m ? "true" : "false") << ", \"matches_validation_json\": " << (ok ? "true" : "false")
              << ", \"matches_tree\": " << (tok ? "true" : "false") << "}";
    }
    o.val << "]";
    std::printf("  validation.json: %d / %d cases pass, %d / %d agree with build_tree\n", ok_all, n, tree_ok, n);
    check(quick || n == 240, "validation.json has 240 cases");
}

int main(int argc, char** argv) {
    std::string repo = hacs_jl_test::repo_root_guess(__FILE__);  // override with --results
    std::string dir = repo + "/code/results/s01", write;
    bool quick = false;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--results" && i + 1 < argc) dir = argv[++i];
        else if (a == "--write" && i + 1 < argc) write = argv[++i];
        else if (a == "--quick") quick = true;
    }
    auto t0 = std::chrono::steady_clock::now();
    Out o;
    try {
        test_levels_json(dir, o);
        test_validation(dir, quick, o);
    } catch (const std::exception& e) {
        check(false, std::string("exception: ") + e.what());
    }
    double rt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::printf("level_selftest: %d passed, %d failed (%.1f s)\n", g_pass, g_fail, rt);
    if (!write.empty()) {
        std::time_t t = std::time(nullptr);
        char date[64];
        std::strftime(date, sizeof date, "%Y-%m-%dT%H:%M:%SZ", std::gmtime(&t));
        std::string commit = run_cmd("git -C '" + repo + "' rev-parse HEAD 2>/dev/null");
        if (commit.empty()) commit = "unknown";
        else if (!run_cmd("git -C '" + repo + "' status --porcelain -- code/hacs/src/hacs/Registry/JL/quat 2>/dev/null").empty())
            commit += "-dirty";
        std::ofstream f(write);
        f << "{\"provenance\": {\"script\": \"code/hacs/src/hacs/Registry/JL/quat/tests/level_selftest.cpp\", \"commit\": \"" << commit
          << "\", \"params\": {\"quick\": " << (quick ? "true" : "false")
          << ", \"references\": [\"code/results/s01/levels.json\", \"code/results/s02/validation.json\"]}, \"date\": \"" << date
          << "\", \"runtime_s\": " << rt << ", \"binary_sha256\": \"" << sha256_file("/proc/self/exe")
          << "\", \"tag\": \"computed\", \"checks_passed\": " << g_pass << ", \"checks_failed\": " << g_fail << "},\n \"data\": {"
          << "\"conventions\": \"Level.h (L1)-(L6): U = (N1, N0) means U_1(N1) cap U_0(N0); level data in e I_c / N I_c "
             "(lattice model of Tree.cpp, generalised to composite N); stab includes -1, w = stab/2 if -1 fixes; masses "
             "sum 1/stab and sum 1/w; s1 by v -> v conj(mu)/N_c\",\n  \"mass_level_change\": "
          << o.mass.str() << ",\n  " << o.misc.str() << ",\n  \"tower\": " << o.tower.str() << ",\n  \"validation_s02\": " << o.val.str()
          << "}}\n";
        std::printf("wrote %s\n", write.c_str());
    }
    return g_fail;
}
