// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception

// Langlandscape JL extension (WP HJ-6b): the two validations of the integral congruence modules (JlCongruence.h).
//  * JLBrandtCongruenceSpikeValidation (fast): the inline B_11 weight-2 fixture: Eisenstein orbit C = Z/5, cusp orbit C = Z/5
//    (Mazur, num(10/12) = 5), plus the exact kernels (Smith, charpoly, factoring) on fixed inputs.
//  * JLBrandtCongruenceRead (slow): the data-driven read of JL_BRANDT_IN (the same READ-ONLY input hook as JLBrandtFreeBlockRead,
//    the same reader BrandtInputFiles / ParseBrandtRecord; it writes nothing).  One `@@JL_CONG {json}` line per (cell, orbit), schema
//    jl_congruence/v1; a cell without orbits (rank 0, no squarefree theta) prints one line with "orbit": null.
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "JlCongruence.h"
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

// The B_11 fixture of JLBrandtFreeBlockSpikeValidation (HJ-B0 spec Sec. 8, + T_7), repeated here so that file stays untouched.
const char* kB11 = R"JSON({"provenance":{"script":"inline fixture (HJ-B0 spec Sec. 8, + T_7 from brandt.module(11))"},
 "data":{"schema":"langlandscape_brandt/v1","writer":"inline:JLBrandtCongruenceSpikeValidation",
 "free_block_z":{"schema": "langlandscape_brandt/v1", "status": "ok", "D": 11,
 "M": 1, "k": 2, "n": 0, "N": 11, "rank": 2,
 "ops": [2, 3, 5, 7],
 "F": [[["1","2"],["3","0"]], [["2","2"],["3","1"]], [["4","2"],["3","3"]], [["4","4"],["6","2"]]],
 "F_fnv": ["0x12097637b2c137e0", "0xfee36f1e9928151a", "0x825d45ddc0a53cba", "0x1c347fdf29291f78"],
 "proof": ["exact_count", "exact_count", "exact_count", "exact_count"],
 "basis_rule": "brandt_delta/v1", "gammas": [4, 6], "d_algebra": 2, "e_eis": 1,
 "convention": "column: T_p b_j = sum_i F[i][j] b_i", "origin": "jl:brandt.py", "tag": "computed"}}})JSON";

std::string Join(const std::vector<nf::BigInt>& v) {
    std::string o;
    for (size_t i = 0; i < v.size(); ++i) o += (i ? "," : "") + v[i].to_string();
    return o;
}
hacs_jl::ZMat Z(std::initializer_list<std::initializer_list<int64_t>> rows) {
    hacs_jl::ZMat A;
    for (auto r : rows) {
        A.emplace_back();
        for (int64_t x : r) A.back().push_back(nf::BigInt(x));
    }
    return A;
}

}  // namespace

uint32_t JLBrandtCongruenceSpikeValidation() {
    using namespace hacs_jl;
    Tally T;
    std::cout << "JLBrandtCongruenceSpikeValidation: B_11, k = 2 (inline fixture), computed (HACS-native JL module)\n";
    // the exact kernels on fixed inputs
    T.check(Join(SmithInvariants(Z({{2, 4, 4}, {-6, 6, 12}, {10, -4, -16}}))) == "2,6,12", "Smith([[2,4,4],[-6,6,12],[10,-4,-16]]) = 2, 6, 12");
    T.check(Join(SmithInvariants(Z({{1, 2}, {1, -3}}))) == "1,5", "Smith([[1,2],[1,-3]]) = 1, 5");
    T.check(Join(CharpolyZ(Z({{1, 2}, {3, 0}}))) == "-6,-1,1", "charpoly(B_2 of B_11) = x^2 - x - 6");
    T.check(KernelZ(Z({{3, 2}, {3, 2}})).size() == 1 && Join(KernelZ(Z({{3, 2}, {3, 2}}))[0]) == "2,-3", "ker_Z [[3,2],[3,2]] = Z (2, -3)");
    T.check(FactorTrial(nf::BigInt(int64_t(8) * 5 * 1000003)).text() == "2^3*5*1000003", "factor 8 * 5 * 1000003");
    T.check(FactorTrial(nf::BigInt::from_string("340282366920938463463374607431768211457")).text() ==
                "[340282366920938463463374607431768211457:composite]",
            "2^128 + 1 = F_7: no factor < 2^20, Miller-Rabin composite: " +
                FactorTrial(nf::BigInt::from_string("340282366920938463463374607431768211457")).text());
    BrandtRecord R;
    std::string err;
    if (!T.check(ParseBrandtRecord(kB11, "inline:B11", &R, &err), "parse the B_11 record " + err)) return T.failing;
    const CongCell C = RunJlCongruence(R);
    for (size_t i = 0; i < C.orbits.size(); ++i) std::cout << "@@JL_CONG " << C.json(i) << "\n";
    T.check(C.status == "ok" && C.orbits.size() == 2 && C.theta_text == "T_2", "status ok, theta = T_2, two orbits (" + C.theta_text + ")");
    T.check(C.hecke_rank == 2 && C.hecke_index == nf::BigInt(1), "Z[T_2, T_3, T_5, T_7] saturated in End(L), rank 2");
    T.check(C.selfadjoint, "T_p self-adjoint for sum x_c y_c / w_c, w = (2, 3)");
    const CongOrbit* E = nullptr;
    const CongOrbit* S = nullptr;
    for (const auto& O : C.orbits) (O.eisenstein ? E : S) = &O;
    T.check(E && S, "one Eisenstein orbit (x - 3), one cusp orbit (x + 2)");
    if (E && S) {
        T.check(Join(E->f) == "-3,1" && Join(S->f) == "2,1", "f_eis = x - 3, f_cusp = x + 2");
        T.check(Join(E->smith) == "5" && E->order == nf::BigInt(5), "Eisenstein orbit: C = Z/5 (Mazur: num((11-1)/12) = 5)");
        T.check(Join(S->smith) == "5" && S->order == nf::BigInt(5), "cusp orbit: C = Z/5");
        T.check(E->ring_ran && S->ring_ran && E->ring_order == nf::BigInt(5) && S->ring_order == nf::BigInt(5),
                "ring congruence module (T_eis x T_cusp)/T = Z/5 = T/I_eis (Mazur's Eisenstein ideal)");
        T.check(PrimeTo6(E->order) == PrimeTo6(nf::BigInt::from_u64(C.mazur_num)), "Mazur comparison up to 2, 3 (R3)");
        T.check(E->gram_ran && E->gram_det == "5/6" && S->gram_ran && S->gram_det == "5",
                "Gram on L_eis = 5/6 = (q-1)/12 (mass), on L_cusp = 5 (" + E->gram_det + ", " + S->gram_det + ")");
    }
    T.check(C.json(0).find("certified") == std::string::npos, "no 'certified' in the @@JL_CONG line");
    std::cout << "JLBrandtCongruenceSpikeValidation: checks=" << T.checks << " failing=" << T.failing << "\n";
    return T.failing;
}

uint32_t JLBrandtCongruenceRead() {
    using namespace hacs_jl;
    const char* in = std::getenv("JL_BRANDT_IN");
    if (!in || !*in) {
        std::cout << "EFFECTIVE JLBrandtCongruenceRead arm=off cells=0 (JL_BRANDT_IN unset; read-only input hook)\n";
        return 0;
    }
    std::string err;
    const std::vector<std::string> files = BrandtInputFiles(in, &err);
    std::cout << "EFFECTIVE JLBrandtCongruenceRead arm=on cells=" << files.size() << " in=" << in << "\n";
    if (!err.empty()) {
        std::cout << "  FAIL " << err << "\n";
        return 1;
    }
    uint32_t cells = 0, lines = 0, exc = 0, bad = 0, nosqf = 0, rank0 = 0, agree = 0, differ = 0, nontrivial = 0;
    const auto t0 = std::chrono::steady_clock::now();
    for (const std::string& f : files) {
        std::ifstream is(f);
        std::stringstream buf;
        buf << is.rdbuf();
        BrandtRecord R;
        std::string e;
        CongCell C;
        try {
            if (!ParseBrandtRecord(buf.str(), f, &R, &e)) {
                std::cout << "@@JL_SKIP {\"file\":\"" << f << "\",\"reason\":\"" << e << "\"}\n";
                continue;
            }
            C = RunJlCongruence(R);
        } catch (const std::exception& ex) {
            std::cout << "  FAIL exception " << f << ": " << ex.what() << "\n";
            ++exc;
            continue;
        }
        ++cells;
        if (C.status == "rank0") ++rank0;
        if (C.status == "no_squarefree_theta") { ++nosqf; std::cout << "  NOTE no squarefree theta: " << f << "\n"; }
        if (C.status == "bad_decomposition") { ++bad; std::cout << "  FAIL L_i + L_i^c not of full rank: " << f << "\n"; }
        if (C.orbits.empty()) {
            std::cout << "@@JL_CONG " << C.json(SIZE_MAX) << "\n";
            ++lines;
        }
        for (size_t i = 0; i < C.orbits.size(); ++i) {
            std::cout << "@@JL_CONG " << C.json(i) << "\n";
            ++lines;
            if (C.orbits[i].order != nf::BigInt(1)) ++nontrivial;
        }
        std::cout << std::flush;
        if (R.k == 2 && R.M == 1 && R.r > 0) {
            bool ok = false;
            for (const auto& O : C.orbits)
                if (O.eisenstein) ok = PrimeTo6(O.order) == PrimeTo6(nf::BigInt::from_u64(C.mazur_num));
            (ok ? agree : differ)++;
            if (!ok) std::cout << "  NOTE D=" << R.D << ": Eisenstein C differs from num((q-1)/12) = " << C.mazur_num << " (prime to 6)\n";
        }
    }
    const double s = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::cout << "JLBrandtCongruenceRead: cells=" << cells << " lines=" << lines << " rank0=" << rank0 << " nontrivial_orbits=" << nontrivial
              << " mazur_agree(k=2, prime to 6)=" << agree << " differ=" << differ << " no_squarefree_theta=" << nosqf
              << " bad_decomposition=" << bad << " exceptions=" << exc << " wall_s=" << s << "\n";
    return exc + bad + differ;
}
