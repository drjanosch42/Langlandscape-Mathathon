// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// jl_brandt2_dump: the weight-2 Brandt module of B_q (q prime, M = 1) as a `free_block_z` record in the binding format
// $HACS_DATA/laneB/freeblockz-export-format.md (section 1a), schema langlandscape_brandt/v2 (canonical class order).
//
//   jl_brandt2_dump <q> [<q2> ...] [--ops p1,p2,...] [--ops-mode lean|literal] [--method neighbours|theta]
//                   [--out DIR] [--commit SHA] [--write-index] [--order key:v2|enum]
// Class order: --order key:v2 (default; the binding v2 rule, Brandt2.h canonical_order_v2: sort by (|Gamma_c|,
// theta of O_r(I_c) up to nrd 20), ties in `order_ties`) or --order enum (ClassSet enumeration = BFS order; debugging
// only, the record then does not satisfy v2). Further rules go in as new key:<spec> branches.
//
// Default ops (--ops-mode lean): every prime p < 50 with p != q (coverage rule, format section 5), plus every prime
// ell dividing num((q-1)/12) (the Mazur/Eisenstein read primes, so T_ell is in ops). --ops-mode literal: all primes
// p <= max(13, largest prime dividing num((q-1)/12)), p != q, together with the primes < 50.
// Output: DIR/D<q>_M1_k2.json (DIR default /home/janosch/data/hacs-run/laneB/brandt_native); --write-index rebuilds
// DIR/index.json from the D*_M*_k*.json files present.
#include "../Brandt2.h"
#include "../../../../NumberField/Sha256.h"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <ctime>
#include <filesystem>
#include <fstream>
#include <random>
#include <sstream>

using namespace hacs_jl;

namespace {

// the record schema: a one-line change for langlandscape_brandt/v2
const char* const kSchema = "langlandscape_brandt/v2";

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

std::string run_cmd(const std::string& cmd) {
    std::string out;
    FILE* p = popen(cmd.c_str(), "r");
    if (!p) return "";
    char buf[256];
    while (fgets(buf, sizeof buf, p)) out += buf;
    pclose(p);
    while (!out.empty() && (out.back() == '\n' || out.back() == '\r')) out.pop_back();
    return out;
}

std::string jstr(const std::string& s) {
    std::string o = "\"";
    for (char c : s) {
        if (c == '"' || c == '\\') o += '\\';
        o += c;
    }
    return o + "\"";
}

std::string hex64(u64 v) {
    char b[32];
    std::snprintf(b, sizeof b, "0x%016llx", (unsigned long long)v);
    return b;
}

int bitlen(i64 v) {
    u64 a = v < 0 ? (u64)(-v) : (u64)v;
    int b = 0;
    while (a) {
        ++b;
        a >>= 1;
    }
    return b;
}

// T_a T_b v == T_b T_a v for a random v mod 2^61-1 (sparse; probabilistic commutativity check)
bool commute_random(const Mat& A, const Mat& B, int r, u64 seed) {
    const unsigned __int128 P = (((unsigned __int128)1) << 61) - 1;
    std::mt19937_64 rng(seed);
    std::vector<u64> v(r);
    for (auto& x : v) x = rng() % (u64)P;
    auto app = [&](const Mat& M, const std::vector<u64>& x) {
        std::vector<u64> y(r, 0);
        for (int i = 0; i < r; ++i) {
            unsigned __int128 s = 0;
            for (int j = 0; j < r; ++j) {
                i64 m = M[(size_t)i * r + j];
                if (m) s = (s + (unsigned __int128)((u64)((m % (i64)P + (i64)P) % (i64)P)) * x[j]) % P;
            }
            y[i] = (u64)s;
        }
        return y;
    };
    return app(A, app(B, v)) == app(B, app(A, v));
}

std::vector<i64> primes_upto(i64 n) {
    std::vector<i64> o;
    for (i64 p = 2; p <= n; ++p)
        if (is_prime(p)) o.push_back(p);
    return o;
}

std::string utc_now() {
    std::time_t t = std::time(nullptr);
    char b[64];
    std::strftime(b, sizeof b, "%Y-%m-%dT%H:%M:%SZ", std::gmtime(&t));
    return b;
}

void write_index(const std::string& dir) {
    namespace fs = std::filesystem;
    std::vector<std::string> files;
    for (auto& e : fs::directory_iterator(dir)) {
        std::string n = e.path().filename().string();
        if (n.size() > 5 && n[0] == 'D' && n.find("_M") != std::string::npos && n.substr(n.size() - 5) == ".json")
            files.push_back(n);
    }
    std::sort(files.begin(), files.end(), [](const std::string& a, const std::string& b) {
        return std::stoll(a.substr(1)) < std::stoll(b.substr(1));
    });
    std::ofstream f(dir + "/index.json");
    f << "{\"schema\": " << jstr(kSchema) << ", \"writer_kind\": \"hacs_jl\", \"cells\": [\n";
    for (size_t i = 0; i < files.size(); ++i) {
        i64 D = std::stoll(files[i].substr(1));
        f << "  {\"D\": " << D << ", \"M\": 1, \"k\": 2, \"status\": \"ok\", \"file\": " << jstr(files[i]) << "}"
          << (i + 1 < files.size() ? ",\n" : "\n");
    }
    f << "]}\n";
    std::printf("index.json: %zu cells\n", files.size());
}

}  // namespace

int main(int argc, char** argv) {
    std::vector<i64> qs, user_ops;
    std::string out = "/home/janosch/data/hacs-run/laneB/brandt_native", mode = "lean", method = "neighbours", commit,
                order = "key:v2";
    bool index = false;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--ops" && i + 1 < argc) {
            std::stringstream ss(argv[++i]);
            std::string t;
            while (std::getline(ss, t, ',')) user_ops.push_back(std::stoll(t));
        } else if (a == "--ops-mode" && i + 1 < argc) mode = argv[++i];
        else if (a == "--method" && i + 1 < argc) method = argv[++i];
        else if (a == "--order" && i + 1 < argc) order = argv[++i];
        else if (a == "--out" && i + 1 < argc) out = argv[++i];
        else if (a == "--commit" && i + 1 < argc) commit = argv[++i];
        else if (a == "--write-index") index = true;
        else if (!a.empty() && a[0] != '-') qs.push_back(std::stoll(a));
        else {
            std::fprintf(stderr, "unknown argument %s\n", a.c_str());
            return 2;
        }
    }
    if (qs.empty() && !index) {
        std::fprintf(stderr, "usage: jl_brandt2_dump <q> [...] [--ops p,..] [--ops-mode lean|literal] "
                             "[--method neighbours|theta] [--out DIR] [--commit SHA] [--write-index]\n");
        return 2;
    }
    const std::string src = __FILE__;
    const std::string srcdir = src.substr(0, src.rfind('/'));
    if (commit.empty()) commit = run_cmd("git -C '" + srcdir + "' rev-parse HEAD 2>/dev/null");
    if (commit.empty()) commit = "unknown";
    const std::string sha = sha256_file("/proc/self/exe");
    std::filesystem::create_directories(out);
    int fails = 0;
    for (i64 q : qs) {
        try {
            if (!is_prime(q)) throw std::invalid_argument("q must be prime");
            auto t0 = std::chrono::steady_clock::now();
            i64 num = (q - 1) / (i64)gcd128(q - 1, 12);
            auto ellset = prime_factors(num);
            i64 lmax = ellset.empty() ? 1 : ellset.back();
            std::vector<i64> ops;
            if (!user_ops.empty()) ops = user_ops;
            else {
                ops = primes_upto(47);
                if (mode == "literal")
                    for (i64 p : primes_upto(std::max<i64>(13, lmax))) ops.push_back(p);
                else
                    for (i64 l : ellset) ops.push_back(l);
            }
            std::sort(ops.begin(), ops.end());
            ops.erase(std::unique(ops.begin(), ops.end()), ops.end());
            ops.erase(std::remove(ops.begin(), ops.end(), q), ops.end());
            MaxOrder O(q);
            ClassSet C(O);
            double t_cs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
            const int r = C.h();
            // class order: canonical (default) or BFS
            std::vector<int> perm(r);
            for (int i = 0; i < r; ++i) perm[i] = i;
            CanonOrder co;
            if (order == "key:v2") {
                co = canonical_order_v2(C);
                perm = co.perm;
            } else if (order != "enum") {
                throw std::invalid_argument("unknown --order " + order + " (key:v2 | enum)");
            }
            std::vector<int> g(r);
            {
                auto g0 = gammas_of(C);
                for (int i = 0; i < r; ++i) g[i] = g0[perm[i]];
            }
            std::vector<Mat> F;
            std::vector<double> t_op;
            if (method == "theta") {
                auto t1 = std::chrono::steady_clock::now();
                auto TH = brandt_theta_pairs(C, ops);
                for (i64 p : ops) F.push_back(permute(TH[p], perm));
                t_op.assign(ops.size(), std::chrono::duration<double>(std::chrono::steady_clock::now() - t1).count() /
                                            std::max<size_t>(1, ops.size()));
            } else {
                for (i64 p : ops) {
                    auto t1 = std::chrono::steady_clock::now();
                    F.push_back(permute(brandt_neighbours(C, p), perm));
                    t_op.push_back(std::chrono::duration<double>(std::chrono::steady_clock::now() - t1).count());
                }
            }
            // writer-side checks (refuse to write on failure)
            for (size_t o = 0; o < ops.size(); ++o) {
                if (!row_sums_ok(F[o], r, ops[o] + 1)) throw std::logic_error("row sums != p+1 for p=" + std::to_string(ops[o]));
                if (!weighted_symmetric(F[o], g)) throw std::logic_error("weighted symmetry fails for p=" + std::to_string(ops[o]));
            }
            for (size_t o = 1; o < ops.size(); ++o)
                if (!commute_random(F[0], F[o], r, 77 + o)) throw std::logic_error("T_p do not commute");
            AlgebraDim ad = algebra_dim(F, r);
            double t_all = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();

            std::string class_keys;
            for (int i = 0; i < r; ++i) {
                if (i) class_keys += ";";
                class_keys += C.classes()[perm[i]].I.key();
            }
            std::string path = out + "/D" + std::to_string(q) + "_M1_k2.json";
            std::string tmp = path + ".tmp";
            {
                std::ofstream f(tmp);
                f << "{\"provenance\": {\"script\": \"code/hacs/src/hacs/Registry/JL/quat/tools/jl_brandt2_dump.cpp\", "
                  << "\"commit\": " << jstr(commit) << ", \"params\": {\"q\": " << q << ", \"ops_mode\": " << jstr(user_ops.empty() ? mode : "user")
                  << ", \"method\": " << jstr(method) << ", \"class_order\": " << jstr(order) << ", \"ell0\": " << C.ell0() << ", \"qf_theta_K\": 48}, "
                  << "\"date\": " << jstr(utc_now()) << ", \"runtime_s\": " << t_all
                  << ", \"hacs_version\": \"none: standalone hacs_jl tool, no HACS binary run\"},\n";
                f << " \"data\": {\"schema\": " << jstr(kSchema) << ", \"writer\": " << jstr("hacs_jl:" + sha)
                  << ", \"D\": " << q << ", \"M\": 1, \"k\": 2,\n  \"weights\": [";
                for (int i = 0; i < r; ++i) f << (i ? "," : "") << g[i];
                f << "],\n  \"free_block_z\": {\"schema\": " << jstr(kSchema) << ", \"status\": \"ok\", \"D\": " << q
                  << ", \"M\": 1, \"k\": 2, \"n\": 0, \"N\": " << q << ", \"rank\": " << r << ", \"r\": " << r << ",\n   \"ops\": [";
                for (size_t o = 0; o < ops.size(); ++o) f << (o ? "," : "") << ops[o];
                f << "],\n   \"F\": [";
                for (size_t o = 0; o < ops.size(); ++o) {
                    f << (o ? ",\n    [" : "\n    [");
                    for (int i = 0; i < r; ++i) {
                        f << (i ? ",[" : "[");
                        for (int j = 0; j < r; ++j) f << (j ? ",\"" : "\"") << F[o][(size_t)i * r + j] << "\"";
                        f << "]";
                    }
                    f << "]";
                }
                f << "],\n   \"F_fnv\": [";
                for (size_t o = 0; o < ops.size(); ++o) f << (o ? "," : "") << jstr(hex64(matrix_fnv(F[o], r)));
                f << "],\n   \"proof\": [";
                for (size_t o = 0; o < ops.size(); ++o) f << (o ? "," : "") << "\"exact_count\"";
                f << "],\n   \"basis_rule\": "
                  << jstr("brandt_delta/v1: b_j = 1_{c_j}, c_j the j-th left-ideal class of hacs_jl::ClassSet(D) "
                          + std::string(order == "key:v2"
                                            ? "canonical order of langlandscape_brandt/v2: sorted by (|Gamma_c|, "
                                              "theta of O_r(I_c) r(1..20)); tie groups in order_ties, enumeration "
                                              "order inside a group"
                                            : "enumeration (BFS) order of ell0-neighbours from O; NOT the v2 order")
                          + "; reduced representatives; hacs_jl native writer)")
                  << ",\n   \"basis_fnv\": " << jstr(hex64(fnv1a64(class_keys)))
                  << ", \"phi_fnv\": \"-\", \"saturation\": \"exact_basis\", \"q0_key\": \"-\", \"bound_basis\": \"-\",\n   \"bits_F\": [";
                for (size_t o = 0; o < ops.size(); ++o) {
                    int b = 0;
                    for (i64 v : F[o]) b = std::max(b, bitlen(v));
                    f << (o ? "," : "") << b;
                }
                f << "],\n   \"gammas\": [";
                for (int i = 0; i < r; ++i) f << (i ? "," : "") << g[i];
                f << "],\n   \"order_ties\": [";
                for (size_t t = 0; t < co.ties.size(); ++t) {
                    f << (t ? ",[" : "[");
                    for (size_t k = 0; k < co.ties[t].size(); ++k) f << (k ? "," : "") << co.ties[t][k];
                    f << "]";
                }
                f << "],\n   \"class_theta\": [";
                for (size_t t = 0; t < co.theta.size(); ++t) {
                    f << (t ? ",[" : "[");
                    for (size_t k = 0; k < co.theta[t].size(); ++k) f << (k ? "," : "") << co.theta[t][k];
                    f << "]";
                }
                f << "],\n   \"d_algebra\": " << ad.dim << ", \"d_algebra_exact\": " << (ad.exact ? "true" : "false")
                  << ", \"d_algebra_method\": "
                  << jstr(ad.exact ? "exact_by_bound: dim of cyclic span mod 2^31-1 equals r (and d <= r)"
                                   : "lower_bound_mod_p: dim of cyclic span mod 2^31-1 (d may be larger)")
                  << ", \"e_eis\": 1,\n   \"lattice\": \"functions\", \"convention\": "
                  << jstr("column: T_p b_j = sum_i F[i][j] b_i; F = B_p (B[c][c'] = #neighbours of c in c'); row sums l+1")
                  << ",\n   \"origin\": \"jl:hacs_jl_native\", \"tag\": \"computed\",\n   \"gamma_convention\": "
                  << jstr("|Gamma_x| = |O_r(I_x)^x| including -1; w_x = |Gamma_x|/2; mass sum 1/|Gamma_x| = (q-1)/24, sum 1/w_x = (q-1)/12")
                  << ",\n   \"diagnostics\": {\"t_classset_s\": " << t_cs << ", \"t_ops_s\": [";
                for (size_t o = 0; o < t_op.size(); ++o) f << (o ? "," : "") << t_op[o];
                f << "], \"qf_theta_max_bucket\": " << C.stats().max_bucket << ", \"exact_tests\": " << C.stats().exact_tests
                  << "}}}}\n";
            }
            std::filesystem::rename(tmp, path);
            std::printf("q=%lld h=%d ops=%zu classset %.2fs total %.2fs d_algebra=%d%s -> %s\n", (long long)q, r, ops.size(),
                        t_cs, t_all, ad.dim, ad.exact ? "" : " (lower bound)", path.c_str());
        } catch (const std::exception& e) {
            std::fprintf(stderr, "q=%lld: ERROR %s\n", (long long)q, e.what());
            ++fails;
        }
    }
    if (index) write_index(out);
    return fails;
}
