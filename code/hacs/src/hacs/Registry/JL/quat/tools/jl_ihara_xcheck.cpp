// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// jl_ihara_xcheck: an independent second route to the exact integral weight-k Ihara cokernel of HJ-7b
// (code/results/laneC/hj7_ihara_k.json, TreeK): via the BrandtLevel Eichler-level API (HJ-4b),
//   iota = (s0^*, -s1^*) : M_Z(O^x)^2 -> M_Z(O_0(q)),
// s0^* = BrandtLevel::pullback, s1^* = BrandtLevel::degeneracy_s1 (BrandtLevel.h (B6): s1^* F(x) = F(x varpi_q) =
// rho_n(g) Phi(I_c', d g), g = conj(mu)/N_c), cokernel by an exact Smith form (Tree.h zlin::smith), compared with TreeK's
// invariant factors cell by cell: exactly, away from q, and away from D q (the primary parts).
//   jl_ihara_xcheck [--ref PATH] [--out PATH]      (defaults: the repo's code/results/laneC/hj7_ihara_k.json, and
//                                                    code/results/laneC/hj7_ihara_xcheck.json)
#include "../BrandtLevel.h"
#include "../../../../NumberField/Sha256.h"
#include "../tests/JsonMin.h"
#include "../tests/RepoRoot.h"

#include <chrono>
#include <cstdio>
#include <ctime>
#include <fstream>
#include <map>
#include <sstream>

using namespace hacs_jl;
using hacs_jl_test::JV;

namespace {
std::string sha256_file(const std::string& path) {
    std::ifstream f(path, std::ios::binary);
    nf::Sha256 h;
    char buf[1 << 16];
    while (f) {
        f.read(buf, sizeof buf);
        if (f.gcount() > 0) h.update(buf, (size_t)f.gcount());
    }
    return h.hex();
}
struct Coker {
    int free_rank = 0;
    std::vector<std::string> tors;  // invariant factors > 1
};
Coker coker(const ZMat& s0, const ZMat& s1, int rE, int rX) {
    zlin::ZM A(rE, std::vector<Z>(2 * rX, Z(0)));
    for (int i = 0; i < rE; ++i)
        for (int j = 0; j < rX; ++j) {
            A[i][j] = s0[i][j];
            A[i][rX + j] = -s1[i][j];
        }
    Coker c;
    if (rX == 0) {
        c.free_rank = rE;
        return c;
    }
    auto d = zlin::smith(A);
    c.free_rank = rE - (int)d.size();
    for (const auto& x : d)
        if (x != Z(1)) c.tors.push_back(x.to_string());
    return c;
}
std::string jlist(const std::vector<std::string>& v) {
    std::string s = "[";
    for (size_t i = 0; i < v.size(); ++i) s += (i ? "," : "") + v[i];
    return s + "]";
}
// the q-free and D-free parts of the torsion invariants: list of (prime, exponents) away from a set
std::map<i64, std::vector<int>> primary(const std::vector<std::string>& t) {
    std::map<i64, std::vector<int>> m;
    for (const auto& s : t) {
        Z x = Z::from_string(s);
        for (i64 p = 2; Z(p) * Z(p) <= x; ++p) {
            int e = 0;
            while ((x % Z(p)).is_zero()) {
                x = x / Z(p);
                ++e;
            }
            if (e) m[p].push_back(e);
        }
        if (x > Z(1)) m[x.to_int64()].push_back(1);
    }
    for (auto& kv : m) std::sort(kv.second.begin(), kv.second.end());
    return m;
}
std::map<i64, std::vector<int>> away(const std::map<i64, std::vector<int>>& m, i64 D, i64 q) {
    std::map<i64, std::vector<int>> r;
    for (const auto& kv : m)
        if (D % kv.first && kv.first != q) r.insert(kv);
    return r;
}
std::string pjson(const std::map<i64, std::vector<int>>& m) {
    std::string s = "{";
    bool f = true;
    for (const auto& kv : m) {
        s += (f ? "\"" : ", \"") + std::to_string(kv.first) + "\": [";
        for (size_t i = 0; i < kv.second.size(); ++i) s += (i ? "," : "") + std::to_string(kv.second[i]);
        s += "]";
        f = false;
    }
    return s + "}";
}
}  // namespace

int main(int argc, char** argv) {
    std::string repo = hacs_jl_test::repo_root_guess(__FILE__);
    std::string ref = repo + "/code/results/laneC/hj7_ihara_k.json", out = repo + "/code/results/laneC/hj7_ihara_xcheck.json";
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--ref" && i + 1 < argc) ref = argv[++i];
        else if (a == "--out" && i + 1 < argc) out = argv[++i];
    }
    std::ifstream f(ref);
    if (!f) {
        std::fprintf(stderr, "cannot open %s (pass --ref)\n", ref.c_str());
        return 2;
    }
    std::stringstream ss;
    ss << f.rdbuf();
    std::string txt = ss.str();
    JV R = hacs_jl_test::JParser(txt).parse();
    auto t0 = std::chrono::steady_clock::now();
    std::map<i64, std::unique_ptr<MaxOrder>> Os;
    std::map<i64, std::unique_ptr<ClassSet>> Cs;
    std::ostringstream js;
    int n = 0, eq_treek = 0, eq_away_q = 0, eq_away_Dq = 0;
    js << "[";
    for (const auto& cell : R["ihara_exact_NEW"].a) {
        const i64 D = cell["D"].i(), q = cell["q"].i();
        const int k = (int)cell["k"].i(), nn = k - 2;
        if (!Os.count(D)) {
            Os[D] = std::make_unique<MaxOrder>(D);
            Cs[D] = std::make_unique<ClassSet>(*Os[D]);
        }
        const ClassSet& C = *Cs[D];
        BrandtSym M(C, nn);
        LevelModel Mo(C, q);
        LevelSet Xs(Mo, {1, 1}), Es(Mo, {1, q});
        BrandtLevel X(M, Xs), E(M, Es);
        ZMat s0 = BrandtLevel::pullback(E, X), s1 = BrandtLevel::degeneracy_s1(E, X, q);
        Coker ours = coker(s0, s1, E.rank(), X.rank());
        std::vector<std::string> ref_t;
        for (const auto& t : cell["torsion_invariants"].a) ref_t.push_back(t.s);
        const int ref_free = (int)cell["coker_free_rank"].i();
        const bool rank_ok = E.rank() == (int)cell["rank_M_O0q"].i() && X.rank() == (int)cell["rank_M_O"].i();
        const bool m_tk = rank_ok && ours.free_rank == ref_free && ours.tors == ref_t;
        auto pr_ref = primary(ref_t), pr_ours = primary(ours.tors);
        const bool m_aq = ours.free_rank == ref_free && away(pr_ours, 1, q) == away(pr_ref, 1, q);
        const bool m_adq = ours.free_rank == ref_free && away(pr_ours, D, q) == away(pr_ref, D, q);
        ++n;
        eq_treek += m_tk;
        eq_away_q += m_aq;
        eq_away_Dq += m_adq;
        js << (n > 1 ? "," : "") << "\n  {\"D\": " << D << ", \"q\": " << q << ", \"k\": " << k << ", \"rank_M_O\": " << X.rank()
           << ", \"rank_M_O0q\": " << E.rank() << ", \"ours\": {\"free_rank\": " << ours.free_rank << ", \"torsion_invariants\": "
           << jlist(ours.tors) << ", \"primary\": " << pjson(pr_ours) << "}, \"ref\": {\"free_rank\": " << ref_free << ", \"torsion_invariants\": " << jlist(ref_t) << "}"
           << ", \"equal_exactly\": " << (m_tk ? "true" : "false")
           << ", \"equal_away_from_q\": " << (m_aq ? "true" : "false") << ", \"equal_away_from_Dq\": " << (m_adq ? "true" : "false")
           << ", \"at_q_ours\": " << pjson([&] {
                  std::map<i64, std::vector<int>> r;
                  if (pr_ours.count(q)) r[q] = pr_ours[q];
                  return r;
              }())
           << "}";
        if (!m_tk) std::printf("D=%lld q=%lld k=%d: ours %s/%d vs ref %s/%d\n", (long long)D, (long long)q, k,
                               jlist(ours.tors).c_str(), ours.free_rank, jlist(ref_t).c_str(), ref_free);
    }
    js << "]";
    double rt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::string commit = hacs_jl_test::run_capture("git -C '" + repo + "' rev-parse HEAD 2>/dev/null");
    if (commit.empty()) commit = "unknown";
    else if (!hacs_jl_test::run_capture("git -C '" + repo + "' status --porcelain -- code/hacs/src/hacs/Registry/JL/quat 2>/dev/null").empty())
        commit += "-dirty";
    std::time_t t = std::time(nullptr);
    char date[64];
    std::strftime(date, sizeof date, "%Y-%m-%dT%H:%M:%SZ", std::gmtime(&t));
    std::ofstream o(out);
    o << "{\"provenance\": {\"script\": \"code/hacs/src/hacs/Registry/JL/quat/tools/jl_ihara_xcheck.cpp\", \"commit\": \"" << commit
      << "\", \"params\": {\"ref\": \"code/results/laneC/hj7_ihara_k.json\", \"ref_commit\": \"" << R["provenance"]["commit"].s
      << "\"}, \"date\": \"" << date << "\", \"runtime_s\": " << rt << ", \"binary_sha256\": \"" << sha256_file("/proc/self/exe")
      << "\", \"tag\": \"computed\"},\n \"data\": {\"route\": \"BrandtLevel Eichler API (HJ-4b): iota = (s0^*, -s1^*), s0^* = pullback, "
         "s1^* = degeneracy_s1 = rho_n(g), g = conj(mu)/N_c; exact Smith form (zlin::smith); independent of TreeK's local "
         "model (TreeK: iota_p frames; here: global splitting and the intrinsic lattice through BrandtSym/Level)\",\n  "
         "\"summary\": {\"cells\": "
      << n << ", \"equal_exactly\": " << eq_treek
      << ", \"ours_equal_away_from_q\": " << eq_away_q << ", \"ours_equal_away_from_Dq\": " << eq_away_Dq << "},\n  \"cells\": "
      << js.str() << "}}\n";
    std::printf("cells %d: equal exactly %d, away from q %d, away from Dq %d; %.1f s -> %s\n", n, eq_treek, eq_away_q,
                eq_away_Dq, rt, out.c_str());
    return n == eq_treek ? 0 : 1;
}
