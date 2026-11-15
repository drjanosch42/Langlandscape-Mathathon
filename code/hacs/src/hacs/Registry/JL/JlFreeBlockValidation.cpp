// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception

// Langlandscape JL extension (WP HJ-6-min): the two validations of the Brandt free-block read.
//  * JLBrandtFreeBlockSpikeValidation (fast): the inline B_11 weight-2 fixture (HJ-B0 spec Sec. 8 + T_7), Mazur's Z/5 at ell = 5.
//  * JLBrandtFreeBlockRead (slow): the data-driven read of JL_BRANDT_IN (a Langlandscape READ-ONLY input hook: it writes nothing;
//    without the variable it prints `EFFECTIVE JLBrandtFreeBlockRead arm=off` and passes).  One `@@JL_READ {json}` line per (D, ell, K).
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "JlFreeBlockRead.h"

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

const char* kB11 = R"JSON({"provenance":{"script":"inline fixture (HJ-B0 spec Sec. 8, + T_7 from brandt.module(11))"},
 "data":{"schema":"langlandscape_brandt/v1","writer":"inline:JLBrandtFreeBlockSpikeValidation","future_field":{"x":[1,2]},
 "free_block_z":{"schema": "langlandscape_brandt/v1", "status": "ok", "D": 11,
 "M": 1, "k": 2, "n": 0, "N": 11, "rank": 2,
 "ops": [2, 3, 5, 7],
 "F": [[["1","2"],["3","0"]], [["2","2"],["3","1"]], [["4","2"],["3","3"]], [["4","4"],["6","2"]]],
 "F_fnv": ["0x12097637b2c137e0", "0xfee36f1e9928151a", "0x825d45ddc0a53cba", "0x1c347fdf29291f78"],
 "proof": ["exact_count", "exact_count", "exact_count", "exact_count"],
 "basis_rule": "brandt_delta/v1: b_j = 1_{c_j}, c_j the j-th left-ideal class of brandt.module(D, M) (BFS order of brandt.py)",
 "basis_fnv": "-", "phi_fnv": "-", "saturation": "exact_basis", "q0_key": "-", "bound_basis": "-",
 "bits_F": [2, 2, 3, 3], "gammas": [4, 6], "d_algebra": 2, "e_eis": 1,
 "charpoly_Z": [["-6","-1","1"], ["-4","-3","1"], ["6","-7","1"], ["-16","-6","1"]],
 "lattice": "functions", "convention": "column: T_p b_j = sum_i F[i][j] b_i; F = B_p (B[c][c'] = #neighbours of c in c'); row sums l+1",
 "origin": "jl:brandt.py", "tag": "computed"}}})JSON";

std::string Replace(std::string s, const std::string& a, const std::string& b) {
    const size_t p = s.find(a);
    if (p != std::string::npos) s.replace(p, a.size(), b);
    return s;
}

bool IsPrime(uint64_t n) {
    if (n < 2) return false;
    for (uint64_t d = 2; d * d <= n; ++d)
        if (n % d == 0) return false;
    return true;
}

}  // namespace

uint32_t JLBrandtFreeBlockSpikeValidation() {
    using namespace hacs_jl;
    Tally T;
    std::cout << "JLBrandtFreeBlockSpikeValidation: B_11, k = 2 (inline fixture), computed (HACS ReadLocal on a JL lattice)\n";
    BrandtRecord R;
    std::string err;
    if (!T.check(ParseBrandtRecord(kB11, "inline:B11", &R, &err), "parse the B_11 record " + err)) return T.failing;
    T.check(R.D == 11 && R.N == 11 && R.r == 2 && R.ops.size() == 4 && R.d_algebra == 2 && R.e_eis == 1 && R.gammas.size() == 2,
            "fields: D = N = 11, r = 2, 4 ops, d_algebra = 2, e_eis = 1, gammas");
    T.check(R.fnv_mismatch == 0, "F_fnv: HACS MatrixFnv = the JSON (Python) hash on every op");
    T.check(R.F[0][2].to_string() == "3" && R.F[0][1].to_string() == "2", "row-major flatten: F_2[1][0] = 3, F_2[0][1] = 2");
    {   // tolerant reader: unknown fields ignored; flat F and number entries accepted; schema mismatch rejected; F_fnv tamper detected
        BrandtRecord R2;
        std::string e2;
        const std::string flat = Replace(kB11, R"([["1","2"],["3","0"]])", R"([1,2,3,0])");
        T.check(ParseBrandtRecord(flat, "inline:flat", &R2, &e2) && R2.fnv_mismatch == 0 && R2.F[0][2].to_string() == "3",
                "tolerant: a flat F[o] with JSON numbers reads the same " + e2);
        T.check(ParseBrandtRecord(Replace(kB11, "\"langlandscape_brandt/v1\"", "\"langlandscape_brandt/v2\""), "inline:v2", &R2, &e2),
                "schema v2 accepted (HJ-6b) " + e2);
        T.check(!ParseBrandtRecord(Replace(kB11, "\"langlandscape_brandt/v1\"", "\"langlandscape_brandt/v3\""), "inline:v3", &R2, &e2),
                "schema v3 rejected: " + e2);
        T.check(ParseBrandtRecord(Replace(kB11, "0x12097637b2c137e0", "0x12097637b2c137e1"), "inline:tamper", &R2, &e2) &&
                    R2.fnv_mismatch == 1,
                "a tampered F_fnv is counted (fnv_mismatch = 1)");
    }
    // ell = 5, K = 3: Mazur's Z/5 = num(10/12) (code/results/s03/T1.json)
    const JlRead A = RunJlRead(R, 5, 3);
    std::cout << "@@JL_READ " << A.json() << "\n";
    T.check(A.lm_status == "ok" && A.t_ell == "in_P", "ell = 5: LatticeFromFreeZ ok, T_5 in P");
    T.check(A.own.status == "ok" && A.own.v_cong == 1 && A.own.v_mass == 1,
            "own Smith route: v_5 [L : L_eis + L_cusp] = 1 on every op, = v_5 of the weight index (gammas)");
    T.check(A.own.T_len == 2 * 3 && A.own.T_gens == 2 && A.own.A1_dim == 2, "T (x) Z/5^3 free of rank 2 (length hK = 6), dim A'_1 = 2");
    T.check(A.LL.dim_A1 == 2 && A.LL.c3 == "certified", "ReadLocal on L+L: dim A'_1 = d = 2 (HACS word c3 printed as met(hacs_word))");
    T.check(A.LL.root == "closes" && A.LL.v_eta == 1 && A.LL.v_gP == 1 && A.LL.C_T == "5^1_exact",
            "ReadLocal on L+L: v_eta = v_gP = 1, C_T = 5^1 (" + A.LL.root + ", " + A.LL.C_T + ")");
    T.check(A.plain.dim_A1 == 2 && A.plain.c3 == "certified", "ReadLocal on L: dim A'_1 = 2");
    T.check(A.plain.root == "inconsistent",
            "ReadLocal on L: the at-root read finds no monic sqrt of chi/(x-l) (S_k once on L): root = " + A.plain.root);
    T.check(A.json().find("certified") == std::string::npos, "no 'certified' in the @@JL_READ line");
    // ell = 7: no congruence
    const JlRead B = RunJlRead(R, 7, 2);
    std::cout << "@@JL_READ " << B.json() << "\n";
    T.check(B.own.v_cong == 0 && B.own.v_mass == 0 && B.LL.v_eta == 0, "ell = 7: v_cong = v_eta = 0");
    // ell = 13 not in ops: T_13 omitted, not a crash
    const JlRead C = RunJlRead(R, 13, 2, false, false);
    T.check(C.t_ell == "omitted(not_in_record)" && C.lm_status == "ok", "ell = 13 not in ops: t_ell = omitted(not_in_record), no ENGINE_CHECK");
    // word modulus, ell | N
    T.check(RunJlRead(R, 5, 28, false, false).lm_status == "refused(word_modulus)", "5^28 >= 2^63: refused(word_modulus)");
    T.check(RunJlRead(R, 11, 2, false, false).lm_status == "skipped(ell|N)", "ell = 11 | N: skipped");
    std::cout << "JLBrandtFreeBlockSpikeValidation: checks=" << T.checks << " failing=" << T.failing << "\n";
    return T.failing;
}

uint32_t JLBrandtFreeBlockRead() {
    using namespace hacs_jl;
    const char* in = std::getenv("JL_BRANDT_IN");
    if (!in || !*in) {
        std::cout << "EFFECTIVE JLBrandtFreeBlockRead arm=off cells=0 (JL_BRANDT_IN unset; read-only input hook)\n";
        return 0;
    }
    std::string err;
    const std::vector<std::string> files = BrandtInputFiles(in, &err);
    // ell list: JL_BRANDT_ELLS = "5:4,7:3" (ell:K, K optional); default per record: every prime ell >= 5 dividing num((N-1)/12) with
    // K = v + 2, plus ell = 5, 7 (K = v + 2)
    std::vector<std::pair<uint64_t, uint32_t>> ells;
    if (const char* e = std::getenv("JL_BRANDT_ELLS"); e && *e) {
        std::stringstream ss(e);
        std::string tok;
        while (std::getline(ss, tok, ',')) {
            // HJ-6b m2: a prime ell >= 2 and 1 <= K <= 64, else refuse by name (ell = 1 looped in MazurValuation; stoull threw)
            const size_t c = tok.find(':');
            uint64_t ell = 0, K = 0;
            try {
                size_t used = 0;
                ell = std::stoull(tok.substr(0, c), &used);
                if (used != tok.substr(0, c).size()) ell = 0;
                if (c != std::string::npos) {
                    K = std::stoull(tok.substr(c + 1), &used);
                    if (used != tok.substr(c + 1).size() || K == 0 || K > 64) ell = 0;
                }
            } catch (const std::exception&) {
                ell = 0;
            }
            if (!IsPrime(ell)) {
                std::cout << "  FAIL JL_BRANDT_ELLS: token '" << tok << "' is not ell[:K] with ell a prime >= 2 and 1 <= K <= 64\n";
                return 1;
            }
            ells.emplace_back(ell, static_cast<uint32_t>(K));
        }
    }
    // HJ-6b: JL_BRANDT_SMALL_ELLS=1 adds ell = 2, 3 to the default list when they divide num((N-1)/12) (flag small_ell in the output;
    // at ell = 2 ReadLocal's root stays open(precision) even on L (+) L: use the own Smith route there)
    const bool small_ells = std::getenv("JL_BRANDT_SMALL_ELLS") && std::string(std::getenv("JL_BRANDT_SMALL_ELLS")) == "1";
    const bool skip_plain = std::getenv("JL_BRANDT_SKIP_PLAIN") && std::string(std::getenv("JL_BRANDT_SKIP_PLAIN")) == "1";
    std::cout << "EFFECTIVE JLBrandtFreeBlockRead arm=on cells=" << files.size() << " in=" << in
              << " ells=" << (ells.empty() ? "default" : std::getenv("JL_BRANDT_ELLS")) << " plain=" << (skip_plain ? "off" : "on")
              << " small_ells=" << (small_ells ? "on" : "off") << "\n";
    if (!err.empty()) {
        std::cout << "  FAIL " << err << "\n";
        return 1;
    }
    uint32_t fail = 0, reads = 0, agree = 0, disagree = 0, other = 0, cells = 0, fnv_bad = 0;
    const auto t0 = std::chrono::steady_clock::now();
    for (const std::string& f : files) {
        std::ifstream is(f);
        std::stringstream buf;
        buf << is.rdbuf();
        BrandtRecord R;
        std::string e;
        bool parsed = false;
        try {   // HJ-6b m1/m4: a throwing parse (ENGINE_CHECK on a range guard) is counted as an exception; the run continues
            parsed = ParseBrandtRecord(buf.str(), f, &R, &e);
        } catch (const std::exception& ex) {
            std::cout << "  FAIL exception parsing " << f << ": " << ex.what() << "\n";
            ++fail;
            continue;
        }
        if (!parsed) {
            std::cout << "@@JL_SKIP {\"file\":\"" << f << "\",\"reason\":\"" << e << "\"}\n";
            continue;
        }
        ++cells;
        if (R.fnv_mismatch) {
            ++fnv_bad;
            std::cout << "  FAIL F_fnv mismatch on " << R.fnv_mismatch << " ops: " << f << "\n";
        }
        std::vector<std::pair<uint64_t, uint32_t>> L = ells;
        if (L.empty()) {
            uint64_t m = R.M == 1 ? MazurNumber(R.N) : 0;
            std::vector<uint64_t> ps;
            for (uint64_t p = small_ells ? 2 : 5; m > 1 && p <= m; ++p)
                if (m % p == 0 && IsPrime(p)) {
                    ps.push_back(p);
                    while (m % p == 0) m /= p;
                }
            for (uint64_t p : {uint64_t(5), uint64_t(7)})
                if (std::find(ps.begin(), ps.end(), p) == ps.end()) ps.push_back(p);
            std::sort(ps.begin(), ps.end());
            for (uint64_t p : ps) L.emplace_back(p, 0);
        }
        bool cell_ok = true;
        for (auto [ell, K] : L) {
            if (K == 0) K = MazurValuation(R.N, ell) + 2;
            JlRead X;
            try {
                X = RunJlRead(R, ell, K, !skip_plain, true);
            } catch (const std::exception& ex) {
                std::cout << "  FAIL exception D=" << R.D << " ell=" << ell << ": " << ex.what() << "\n";
                ++fail;
                continue;
            }
            if (X.lm_status == "skipped(ell|N)") continue;
            ++reads;
            std::string js = X.json();
            const bool small = ell < 5;
            if (small && !js.empty() && js.back() == '}') js.insert(js.size() - 1, ",\"small_ell\":true");
            std::cout << "@@JL_READ " << js << "\n" << std::flush;
            if (R.M == 1 && R.k == 2 && X.lm_status == "ok" && R.r > 0 && !small) {   // ell = 2, 3: Mazur's prediction is up to 2, 3 (R3)
                const int32_t vm = static_cast<int32_t>(MazurValuation(R.N, ell));
                const bool ok = X.own.v_cong == vm && (!X.ran_LL || X.LL.v_eta == vm) && (X.own.v_mass < 0 || X.own.v_mass == vm);
                cell_ok = cell_ok && ok;
                if (!ok) std::cout << "  NOTE D=" << R.D << " ell=" << ell << ": differs from v_ell num((q-1)/12) = " << vm << "\n";
            }
        }
        if (R.M == 1 && R.k == 2 && R.r > 0) (cell_ok ? agree : disagree)++;
        else ++other;
    }
    const double s = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "JLBrandtFreeBlockRead: cells=" << cells << " reads=" << reads << " agree_mazur=" << agree << " differ=" << disagree << " not_compared(k!=2|M>1|rank0)=" << other
              << " fnv_mismatch_cells=" << fnv_bad << " exceptions=" << fail << " wall_s=" << s << "\n";
    return fail + fnv_bad;
}
