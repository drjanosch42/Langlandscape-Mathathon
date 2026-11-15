// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// jl_brandtsym_dump: the integral Sym^n Brandt module M_Z of B_D (D squarefree, omega(D) odd; level O^x, M = 1) as
// `free_block_z` records in the format of plan/hacs/freeblockz-export-format.md, schema langlandscape_brandt/v2, at any
// weight k >= 2 (BrandtSym.h, conventions (C1)-(C7)).
//
//   jl_brandtsym_dump <D> [<D2> ...] --k k1,k2,... [--ops p1,p2,...] [--gram] [--no-pi]
//                     [--out DIR] [--commit SHA] [--order key:v2|enum] [--write-index]
//
// --k      weights (default 2..12); odd k gives status "rank0".
// --ops    the T_p in `F` (default: every prime p < 50 with p not | D). Ascending, duplicates removed, p | D removed.
// --gram   also write the Gram matrices of (C7): gram_w (= sum_c N_c^n beta_n / w_c, exact rationals "p/q"),
//          gram_Gamma (weights |Gamma_c|), their integer forms scale * G with the recorded scale, and the class blocks.
// --no-pi  omit the Pi_p / Pi_D (= W_D) matrices (written by default as optional fields `Pi`, unnormalised, Pi_D^2 = D^n).
// --order  class order: key:v2 (default; Brandt2.h canonical_order_v2) or enum (BFS; debugging only).
// Output: DIR/D<D>_M1_k<k>.json (DIR default /home/janosch/data/hacs-run/laneC/brandtsym), envelope {provenance, data}.
// The k > 2 records carry canonical: false (F depends on the class representatives and the base order up to a
// block-diagonal GL_d(Z) change of basis; compare by charpoly_Z), and lattice_intrinsic: true (the lattice M_Z itself
// does not depend on any choice, BrandtSym.h (C5)).
#include "../BrandtSym.h"
#include "../../../../NumberField/Sha256.h"
#include "../tests/RepoRoot.h"

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
std::string utc_now() {
    std::time_t t = std::time(nullptr);
    char b[64];
    std::strftime(b, sizeof b, "%Y-%m-%dT%H:%M:%SZ", std::gmtime(&t));
    return b;
}
std::vector<i64> parse_list(const std::string& s) {
    std::vector<i64> o;
    std::stringstream ss(s);
    std::string t;
    while (std::getline(ss, t, ',')) {
        auto d = t.find("..");
        if (d != std::string::npos)
            for (i64 x = std::stoll(t.substr(0, d)); x <= std::stoll(t.substr(d + 2)); ++x) o.push_back(x);
        else o.push_back(std::stoll(t));
    }
    return o;
}
std::string zmat_json(const ZMat& F) {
    std::string s = "[";
    for (size_t i = 0; i < F.size(); ++i) {
        s += i ? ",[" : "[";
        for (size_t j = 0; j < F[i].size(); ++j) s += (j ? ",\"" : "\"") + F[i][j].to_string() + "\"";
        s += "]";
    }
    return s + "]";
}
std::string qmat_json(const QMat& F) {
    std::string s = "[";
    for (size_t i = 0; i < F.size(); ++i) {
        s += i ? ",[" : "[";
        for (size_t j = 0; j < F[i].size(); ++j) s += (j ? ",\"" : "\"") + F[i][j].to_string() + "\"";
        s += "]";
    }
    return s + "]";
}
std::string zvec_json(const std::vector<Z>& v) {
    std::string s = "[";
    for (size_t i = 0; i < v.size(); ++i) s += (i ? ",\"" : "\"") + v[i].to_string() + "\"";
    return s + "]";
}
size_t bits(const ZMat& F) {
    size_t b = 0;
    for (const auto& r : F)
        for (const auto& x : r) b = std::max(b, x.bit_length());
    return b;
}
// dim_Q Q[ops] acting on Q^r: dimension of the cyclic span of a random v mod P = 2^31 - 1 (a lower bound for d; exact when
// it equals r, since the algebra is commutative semisimple and d <= r).
std::pair<int, bool> algebra_dim(const std::vector<ZMat>& ops, int r) {
    if (r == 0) return {0, true};
    const u64 P = 2147483647ULL;
    std::vector<std::vector<std::vector<u64>>> M;
    for (const auto& F : ops) M.push_back(symz::reduce_mod(F, P));
    std::mt19937_64 rng(12345);
    std::vector<std::vector<u64>> basis;  // echelon rows mod P
    std::vector<int> piv;
    auto reduce_in = [&](std::vector<u64> v) -> bool {
        for (size_t i = 0; i < basis.size(); ++i) {
            u64 c = v[piv[i]];
            if (!c) continue;
            for (int j = 0; j < r; ++j) v[j] = (v[j] + (P - c) * basis[i][j]) % P;  // basis rows normalised (pivot 1)
        }
        int p = 0;
        while (p < r && !v[p]) ++p;
        if (p == r) return false;
        // normalise
        u64 inv = 1, b = v[p], e = P - 2;
        while (e) {
            if (e & 1) inv = (unsigned __int128)inv * b % P;
            b = (unsigned __int128)b * b % P;
            e >>= 1;
        }
        for (int j = 0; j < r; ++j) v[j] = (unsigned __int128)v[j] * inv % P;
        basis.push_back(v);
        piv.push_back(p);
        return true;
    };
    std::vector<std::vector<u64>> queue;
    std::vector<u64> v(r);
    for (auto& x : v) x = rng() % P;
    if (reduce_in(v)) queue.push_back(v);
    while (!queue.empty() && (int)basis.size() < r) {
        auto x = queue.back();
        queue.pop_back();
        for (const auto& A : M) {
            std::vector<u64> y(r, 0);
            for (int i = 0; i < r; ++i) {
                unsigned __int128 s = 0;
                for (int j = 0; j < r; ++j) s = (s + (unsigned __int128)A[i][j] * x[j]) % P;
                y[i] = (u64)s;
            }
            if (reduce_in(y)) queue.push_back(y);
        }
    }
    return {(int)basis.size(), (int)basis.size() == r};
}

void write_index(const std::string& dir) {
    namespace fs = std::filesystem;
    std::vector<std::pair<std::pair<i64, int>, std::string>> files;
    for (auto& e : fs::directory_iterator(dir)) {
        std::string n = e.path().filename().string();
        auto kpos = n.find("_k");
        if (n.size() > 5 && n[0] == 'D' && n.find("_M") != std::string::npos && kpos != std::string::npos &&
            n.substr(n.size() - 5) == ".json")
            files.push_back({{std::stoll(n.substr(1)), std::stoi(n.substr(kpos + 2))}, n});
    }
    std::sort(files.begin(), files.end());
    std::ofstream f(dir + "/index.json");
    f << "{\"schema\": " << jstr(kSchema) << ", \"writer_kind\": \"hacs_jl\", \"cells\": [\n";
    for (size_t i = 0; i < files.size(); ++i)
        f << "  {\"D\": " << files[i].first.first << ", \"M\": 1, \"k\": " << files[i].first.second
          << ", \"file\": " << jstr(files[i].second) << "}" << (i + 1 < files.size() ? ",\n" : "\n");
    f << "]}\n";
    std::printf("index.json: %zu cells\n", files.size());
}

}  // namespace

int main(int argc, char** argv) {
    std::vector<i64> Ds, ks = parse_list("2..12"), user_ops;
    std::string out = "/home/janosch/data/hacs-run/laneC/brandtsym", commit, order = "key:v2";
    bool gram = false, pi = true, index = false;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--k" && i + 1 < argc) ks = parse_list(argv[++i]);
        else if (a == "--ops" && i + 1 < argc) user_ops = parse_list(argv[++i]);
        else if (a == "--gram") gram = true;
        else if (a == "--no-pi") pi = false;
        else if (a == "--order" && i + 1 < argc) order = argv[++i];
        else if (a == "--out" && i + 1 < argc) out = argv[++i];
        else if (a == "--commit" && i + 1 < argc) commit = argv[++i];
        else if (a == "--write-index") index = true;
        else if (!a.empty() && a[0] != '-') Ds.push_back(std::stoll(a));
        else {
            std::fprintf(stderr, "unknown argument %s\n", a.c_str());
            return 2;
        }
    }
    if (Ds.empty() && !index) {
        std::fprintf(stderr, "usage: jl_brandtsym_dump <D> [...] [--k k1,k2|a..b] [--ops p,..] [--gram] [--no-pi] "
                             "[--out DIR] [--commit SHA] [--order key:v2|enum] [--write-index]\n");
        return 2;
    }
    if (order != "key:v2" && order != "enum") {
        std::fprintf(stderr, "unknown --order %s\n", order.c_str());
        return 2;
    }
    const std::string src = __FILE__;
    const std::string srcdir = src.substr(0, src.rfind('/'));
    if (commit.empty()) commit = run_cmd("git -C '" + srcdir + "' rev-parse HEAD 2>/dev/null");
    if (commit.empty()) {  // relative __FILE__ and another cwd (audit m1)
        std::string root = hacs_jl_test::repo_root_guess(src);
        if (!root.empty()) commit = run_cmd("git -C '" + root + "' rev-parse HEAD 2>/dev/null");
    }
    if (commit.empty()) commit = "unknown";
    const std::string sha = sha256_file("/proc/self/exe");
    std::filesystem::create_directories(out);
    int fails = 0;
    for (i64 D : Ds) {
        try {
            auto t0 = std::chrono::steady_clock::now();
            MaxOrder O(D);
            ClassSet C(O);
            CanonOrder co = canonical_order_v2(C);
            double t_cs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
            std::vector<i64> ops;
            if (!user_ops.empty()) ops = user_ops;
            else
                for (i64 p = 2; p < 50; ++p)
                    if (is_prime(p)) ops.push_back(p);
            std::sort(ops.begin(), ops.end());
            ops.erase(std::unique(ops.begin(), ops.end()), ops.end());
            ops.erase(std::remove_if(ops.begin(), ops.end(), [&](i64 p) { return D % p == 0 || !is_prime(p); }), ops.end());
            const auto ps = prime_factors(D);
            for (i64 k : ks) {
                auto t1 = std::chrono::steady_clock::now();
                const int n = (int)k - 2;
                BrandtSym::Options opt;
                opt.canonical_order = order == "key:v2";
                BrandtSym M(C, n, opt);
                const int r = M.rank();
                std::vector<ZMat> F;
                std::vector<double> t_op;
                for (i64 p : ops) {
                    auto t2 = std::chrono::steady_clock::now();
                    F.push_back(M.T(p));
                    t_op.push_back(std::chrono::duration<double>(std::chrono::steady_clock::now() - t2).count());
                }
                std::vector<std::pair<i64, ZMat>> Pis;
                if (pi && r > 0) {
                    for (i64 p : ps) Pis.push_back({p, M.Pi(p)});
                    if (ps.size() > 1) Pis.push_back({D, M.Pi(D)});
                }
                // writer-side checks (refuse to write on failure)
                for (size_t a = 0; a < F.size(); ++a) {
                    if (!M.self_adjoint(F[a])) throw std::logic_error("T_p not self-adjoint for <,>_w, p=" + std::to_string(ops[a]));
                    for (size_t b = a + 1; b < F.size(); ++b)
                        if (symz::mul(F[a], F[b]) != symz::mul(F[b], F[a])) throw std::logic_error("T_p do not commute");
                    for (const auto& P : Pis)
                        if (symz::mul(F[a], P.second) != symz::mul(P.second, F[a])) throw std::logic_error("T_p, Pi do not commute");
                    if (k == 2)
                        for (const auto& row : F[a]) {
                            Z s(0);
                            for (const auto& x : row) s += x;
                            if (s != Z(ops[a] + 1)) throw std::logic_error("k=2 row sums != p+1");
                        }
                }
                for (const auto& P : Pis)
                    if (!symz::is_scalar(symz::mul(P.second, P.second), Z::pow(Z(P.first), (uint64_t)n)))
                        throw std::logic_error("Pi_p^2 != p^n");
                auto ad = algebra_dim(F, r);
                std::string class_keys;
                for (int c = 0; c < M.h(); ++c) class_keys += (c ? ";" : "") + M.classes()[c].I.key();
                double t_all = std::chrono::duration<double>(std::chrono::steady_clock::now() - t1).count() + t_cs;

                const std::string status = r == 0 ? "rank0" : "ok";
                std::string path = out + "/D" + std::to_string(D) + "_M1_k" + std::to_string(k) + ".json";
                std::string tmp = path + ".tmp";
                {
                    std::ofstream f(tmp);
                    f << "{\"provenance\": {\"script\": \"code/hacs/src/hacs/Registry/JL/quat/tools/jl_brandtsym_dump.cpp\", "
                      << "\"commit\": " << jstr(commit) << ", \"params\": {\"D\": " << D << ", \"k\": " << k << ", \"ops\": "
                      << jstr(user_ops.empty() ? "primes < 50 not dividing D" : "user") << ", \"gram\": " << (gram ? "true" : "false")
                      << ", \"class_order\": " << jstr(order) << ", \"ell0\": " << C.ell0() << "}, \"date\": " << jstr(utc_now())
                      << ", \"runtime_s\": " << t_all << ", \"binary_sha256\": " << jstr(sha)
                      << ", \"hacs_version\": \"none: standalone hacs_jl tool, no HACS binary run\"},\n";
                    f << " \"data\": {\"schema\": " << jstr(kSchema) << ", \"writer\": " << jstr("hacs_jl:" + sha) << ", \"D\": " << D
                      << ", \"M\": 1, \"k\": " << k << ",\n  \"free_block_z\": {\"schema\": " << jstr(kSchema) << ", \"status\": "
                      << jstr(status) << ", \"D\": " << D << ", \"M\": 1, \"k\": " << k << ", \"n\": " << n << ", \"N\": " << D
                      << ", \"rank\": " << r << ",\n   \"ops\": [";
                    for (size_t o = 0; o < ops.size(); ++o) f << (o ? "," : "") << ops[o];
                    f << "],\n   \"F\": [";
                    for (size_t o = 0; o < ops.size(); ++o) f << (o ? ",\n    " : "\n    ") << (r ? zmat_json(F[o]) : "[]");
                    f << "],\n   \"F_fnv\": [";
                    for (size_t o = 0; o < ops.size(); ++o) f << (o ? "," : "") << jstr(hex64(fnv1a64(symz::fnv_text(F[o]))));
                    f << "],\n   \"proof\": [";
                    for (size_t o = 0; o < ops.size(); ++o) f << (o ? "," : "") << (r ? "\"exact_rational_model\"" : "\"rank0\"");
                    f << "],\n   \"basis_rule\": "
                      << jstr("brandt_symn_lattice/v1 (hacs_jl BrandtSym.h (C5)): M_Z = (+)_c Lambda_c^{Gamma_c}, Lambda_c = "
                              "N_c^{-n/2} Z-span{Q_{x_1}...Q_{x_{n/2}} : x_i in (O_r(I_c)^0)^#}, Q_x = (X,Y) s(x) J (X,Y)^T; "
                              "basis of block c = HNF of the integral Gamma_c-invariants in the HNF basis of Lambda_c, in base "
                              "coordinates of Lambda'(O) (O = HNF maximal order of hacs_jl); blocks in the class order " +
                              std::string(order == "key:v2" ? "of langlandscape_brandt/v2 (|Gamma_c|, theta_c)" : "of the BFS (enum; not v2)"))
                      << ",\n   \"basis_fnv\": " << jstr(hex64(fnv1a64(class_keys)))
                      << ", \"phi_fnv\": \"-\", \"saturation\": " << jstr(r ? "exact_basis" : "rank0")
                      << ", \"q0_key\": \"-\", \"bound_basis\": \"-\",\n   \"bits_F\": [";
                    for (size_t o = 0; o < ops.size(); ++o) f << (o ? "," : "") << bits(F[o]);
                    f << "],\n   \"gammas\": [";
                    for (int c = 0; c < M.h(); ++c) f << (c ? "," : "") << M.gammas()[c];
                    f << "], \"class_dims\": [";
                    for (int c = 0; c < M.h(); ++c) f << (c ? "," : "") << M.dims()[c];
                    f << "], \"basis_class\": [";
                    for (int c = 0, first = 1; c < M.h(); ++c)
                        for (int j = 0; j < M.dims()[c]; ++j, first = 0) f << (first ? "" : ",") << c;
                    f << "],\n   \"order_ties\": [";
                    if (order == "key:v2")
                        for (size_t t = 0, first = 1; t < co.ties.size(); ++t)
                            for (size_t a = 0; a < co.ties[t].size(); ++a)
                                for (size_t b = a + 1; b < co.ties[t].size(); ++b, first = 0)
                                    f << (first ? "[" : ",[") << co.ties[t][a] << "," << co.ties[t][b] << "]";
                    f << "], \"class_keys\": " << jstr(class_keys);
                    if (r) f << ",\n   \"d_algebra\": " << ad.first << ", \"d_algebra_exact\": " << (ad.second ? "true" : "false");
                    f << ", \"e_eis\": " << (k == 2 ? 1 : 0) << ",\n   \"charpoly_Z\": [";
                    for (size_t o = 0; o < ops.size(); ++o) f << (o ? ",\n    " : "\n    ") << zvec_json(symz::charpoly(F[o]));
                    f << "],\n   \"lattice\": \"functions\", \"canonical\": " << (k == 2 && order == "key:v2" ? "true" : "false")
                      << ", \"lattice_intrinsic\": true, \"convention\": "
                      << jstr(k == 2 ? "column: T_p b_j = sum_i F[i][j] b_i; F = B_p (B[c][c'] = #neighbours of c in c'); row sums l+1"
                                     : "column: T_p b_j = sum_i F[i][j] b_i; b_j = the j-th basis vector of M_Z (basis_rule); "
                                       "(T_p Phi)(I_c) = sum_J rho_n(conj(delta_J)/N_c) Phi(I_c'), rho_n = [C] def:rhon via "
                                       "symn.py's splitting s; no row-sum identity (no Eisenstein system at k > 2)")
                      << ",\n   \"origin\": \"jl:hacs_jl_native_brandtsym\", \"tag\": \"computed\"";
                    if (!Pis.empty()) {
                        f << ",\n   \"Pi\": {\"convention\": "
                          << jstr("(Pi_p F)(x) = F(x Pi_p): Phi(I_c) -> rho_n(conj(delta)/N_c) Phi(I_c''), P_p I_c = I_c'' beta; "
                                  "unnormalised, Pi_p^2 = p^n; key D = Pi_D = W_D = prod Pi_p; column convention as F")
                          << ", \"ops\": [";
                        for (size_t t = 0; t < Pis.size(); ++t) f << (t ? "," : "") << Pis[t].first;
                        f << "], \"F\": [";
                        for (size_t t = 0; t < Pis.size(); ++t) f << (t ? ",\n    " : "\n    ") << zmat_json(Pis[t].second);
                        f << "], \"charpoly_Z\": [";
                        for (size_t t = 0; t < Pis.size(); ++t) f << (t ? "," : "") << zvec_json(symz::charpoly(Pis[t].second));
                        f << "]}";
                    }
                    if (gram && r) {
                        QMat Gw = M.gram(BrandtSym::Weight::w, true), Gg = M.gram(BrandtSym::Weight::gamma, true);
                        Z sw = BrandtSym::denominator_lcm(Gw), sg = BrandtSym::denominator_lcm(Gg);
                        f << ",\n   \"gram\": {\"convention\": "
                          << jstr("<F,H>_w = sum_c N_c^n beta_n(F(I_c), H(I_c)) / w_c, beta_n(u_i,u_j) = delta_{i+j,n} (-1)^i / "
                                  "binom(n,i); <,>_Gamma: weights |Gamma_c| = 2 w_c; *_int = scale * G; blocks = N_c^n beta_n "
                                  "on the class block (unweighted); multiplied (divisor-side) Grams = sum_c weight_c * block_c")
                          << ",\n    \"gram_w\": " << qmat_json(Gw) << ",\n    \"gram_w_scale\": " << jstr(sw.to_string())
                          << ", \"gram_w_int\": " << zmat_json(BrandtSym::scale_to_int(Gw, sw))
                          << ",\n    \"gram_Gamma\": " << qmat_json(Gg) << ",\n    \"gram_Gamma_scale\": " << jstr(sg.to_string())
                          << ", \"gram_Gamma_int\": " << zmat_json(BrandtSym::scale_to_int(Gg, sg)) << ",\n    \"blocks\": [";
                        for (int c = 0; c < M.h(); ++c) f << (c ? "," : "") << qmat_json(M.gram_block(c));
                        f << "]}";
                    }
                    f << ",\n   \"diagnostics\": {\"t_classset_s\": " << t_cs << ", \"t_ops_s\": [";
                    for (size_t o = 0; o < t_op.size(); ++o) f << (o ? "," : "") << t_op[o];
                    f << "]}}}}\n";
                }
                std::filesystem::rename(tmp, path);
                std::printf("D=%lld k=%lld h=%d rank=%d ops=%zu d_algebra=%d%s %.2fs -> %s\n", (long long)D, (long long)k, M.h(), r,
                            ops.size(), ad.first, ad.second ? "" : " (lower bound)", t_all, path.c_str());
            }
        } catch (const std::exception& e) {
            std::fprintf(stderr, "D=%lld: ERROR %s\n", (long long)D, e.what());
            ++fails;
        }
    }
    if (index) write_index(out);
    return fails;
}
