// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// Standalone self-test of the hacs_jl quaternion core (WPs HJ-1, HJ-2). Not registered as a HACS validation yet.
//   quat_selftest [--results DIR] [--eichler-max N] [--timing-q q1,q2,...] [--quick]
// Exit code = number of failed checks. DIR defaults to <repo>/code/results/s01 (derived from __FILE__).
#include "../Brandt2.h"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <fstream>
#include <sstream>

namespace hacs_jl_test {

struct JV {
    enum T { Null, Bool, Num, Str, Arr, Obj } t = Null;
    std::string s;  // number text or string
    bool b = false;
    std::vector<JV> a;
    std::map<std::string, JV> o;
    const JV& operator[](const std::string& k) const {
        auto it = o.find(k);
        if (it == o.end()) throw std::runtime_error("json: missing key " + k);
        return it->second;
    }
    const JV& operator[](size_t i) const { return a.at(i); }
    bool has(const std::string& k) const { return o.count(k) > 0; }
    long long i() const { return std::stoll(s); }
};

class JParser {
public:
    explicit JParser(const std::string& txt) : t_(txt) {}
    JV parse() {
        JV v = value();
        ws();
        return v;
    }

private:
    const std::string& t_;
    size_t p_ = 0;
    void ws() {
        while (p_ < t_.size() && std::isspace((unsigned char)t_[p_])) ++p_;
    }
    char peek() {
        ws();
        if (p_ >= t_.size()) throw std::runtime_error("json: eof");
        return t_[p_];
    }
    std::string str() {
        ++p_;  // opening quote
        std::string out;
        while (t_[p_] != '"') {
            if (t_[p_] == '\\') {
                ++p_;
                char c = t_[p_];
                if (c == 'n') out += '\n';
                else if (c == 't') out += '\t';
                else if (c == 'u') {
                    out += '?';
                    p_ += 4;
                } else out += c;
            } else out += t_[p_];
            ++p_;
        }
        ++p_;
        return out;
    }
    JV value() {
        char c = peek();
        JV v;
        if (c == '{') {
            v.t = JV::Obj;
            ++p_;
            if (peek() == '}') {
                ++p_;
                return v;
            }
            for (;;) {
                peek();
                std::string k = str();
                if (peek() != ':') throw std::runtime_error("json: expected :");
                ++p_;
                v.o[k] = value();
                char d = peek();
                ++p_;
                if (d == '}') break;
                if (d != ',') throw std::runtime_error("json: expected , in object");
            }
        } else if (c == '[') {
            v.t = JV::Arr;
            ++p_;
            if (peek() == ']') {
                ++p_;
                return v;
            }
            for (;;) {
                v.a.push_back(value());
                char d = peek();
                ++p_;
                if (d == ']') break;
                if (d != ',') throw std::runtime_error("json: expected , in array");
            }
        } else if (c == '"') {
            v.t = JV::Str;
            v.s = str();
        } else if (t_.compare(p_, 4, "true") == 0) {
            v.t = JV::Bool;
            v.b = true;
            p_ += 4;
        } else if (t_.compare(p_, 5, "false") == 0) {
            v.t = JV::Bool;
            p_ += 5;
        } else if (t_.compare(p_, 4, "null") == 0) {
            p_ += 4;
        } else {
            v.t = JV::Num;
            size_t q = p_;
            while (q < t_.size() && (std::isdigit((unsigned char)t_[q]) || t_[q] == '-' || t_[q] == '+' || t_[q] == '.' ||
                                     t_[q] == 'e' || t_[q] == 'E'))
                ++q;
            v.s = t_.substr(p_, q - p_);
            p_ = q;
        }
        return v;
    }
};

}  // namespace hacs_jl_test

using namespace hacs_jl;
using hacs_jl_test::JV;

static int g_fail = 0, g_pass = 0;
static void check(bool ok, const std::string& what) {
    std::fflush(stdout);
    if (ok) ++g_pass;
    else {
        ++g_fail;
        std::printf("  [FAIL] %s\n", what.c_str());
    }
}
static double now_s() {
    return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}
static JV load(const std::string& path) {
    std::ifstream f(path);
    if (!f) throw std::runtime_error("cannot open " + path);
    std::stringstream ss;
    ss << f.rdbuf();
    std::string txt = ss.str();
    return hacs_jl_test::JParser(txt).parse();
}
static Mat json_mat(const JV& v) {
    Mat m;
    for (const auto& row : v.a)
        for (const auto& x : row.a) m.push_back(x.i());
    return m;
}
static std::vector<int> sorted_gammas(const ClassSet& C) {
    auto g = gammas_of(C);
    std::sort(g.begin(), g.end());
    return g;
}
static std::string frac(i64 n, i64 d) {
    i64 g = (i64)gcd128(n, d);
    n /= g;
    d /= g;
    return std::to_string(n) + "/" + std::to_string(d);  // results.py writes Fractions as "n/d", also d = 1
}

// ---------------------------------------------------------------- 1. classsets.json
static void test_classsets(const std::string& dir) {
    std::printf("[1] class sets vs classsets.json\n");
    JV d = load(dir + "/classsets.json")["data"];
    int n = 0;
    for (const auto& kv : d.o) {
        i64 D = std::stoll(kv.first);
        const JV& e = kv.second;
        MaxOrder O(D);
        check(O.algebra().a() == e["a"].i() && O.algebra().b() == e["b"].i(), "D=" + kv.first + " (a,b) = quat.py");
        check(O.disc() == (i128)D * D, "D=" + kv.first + " disc(O) = D^2");
        ClassSet C(O);
        check(C.h() == e["h"].i(), "D=" + kv.first + " h");
        std::vector<int> gr;
        for (const auto& x : e["gammas"].a) gr.push_back((int)x.i());
        check(sorted_gammas(C) == gr, "D=" + kv.first + " |Gamma_x| multiset");
        check(frac(C.sum24(), 24) == e["mass"].s && frac(C.phi(), 24) == e["expected_mass"].s,
              "D=" + kv.first + " mass (|Gamma_x| convention)");
        // generic right order == conj(I) I / N on every class
        for (const auto& c : C.classes()) {
            Lat R = O.right_order(c.I);
            Lat R2 = hnf(std::vector<Vec4>(c.RN.h.begin(), c.RN.h.end()), c.N);
            check(R == R2, "D=" + kv.first + " right_order(I) = conj(I) I / N");
            check(O.left_order(c.I) == O.unit(), "D=" + kv.first + " left_order(I) = O");
        }
        ++n;
    }
    std::printf("    %d discriminants checked\n", n);
}

// ---------------------------------------------------------------- 2. Eichler class number formula
static void test_eichler(i64 Dmax) {
    std::printf("[2] Eichler class number formula, primes D < %lld\n", (long long)Dmax);
    double t0 = now_s();
    int n = 0;
    double worst = 0;
    i64 worstD = 0;
    for (i64 D = 2; D < Dmax; ++D) {
        if (!is_prime(D)) continue;
        double t1 = now_s();
        MaxOrder O(D);
        ClassSet C(O);
        double dt = now_s() - t1;
        if (dt > worst) {
            worst = dt;
            worstD = D;
        }
        int c4 = (D == 2) ? 0 : kronecker(-4, D), c3 = (D == 3) ? 0 : kronecker(-3, D);
        if (D == 2) c4 = 0;
        i64 h12 = (D - 1) + 3 * (1 - c4) + 4 * (1 - c3);
        check(h12 % 12 == 0 && C.h() == h12 / 12, "Eichler h(D) for D=" + std::to_string(D));
        check(C.sum24() == D - 1, "mass sum 1/|Gamma| = (D-1)/24 for D=" + std::to_string(D));
        if (D > 3) {
            auto g = gammas_of(C);
            int n4 = (int)std::count(g.begin(), g.end(), 4), n6 = (int)std::count(g.begin(), g.end(), 6);
            int n2 = (int)std::count(g.begin(), g.end(), 2);
            check(n4 == (1 - c4) / 2 && n6 == (1 - c3) / 2 && n2 + n4 + n6 == C.h(),
                  "|Gamma_x| = 4 / 6 counts for D=" + std::to_string(D));
            // w-convention: sum 1/|Gamma/+-1| = (D-1)/12
            i64 s12 = 0;
            for (int x : g) s12 += 24 / (x / 2);  // 24 * 1/w
            check(s12 == 2 * (D - 1), "mass sum 1/w_x = (D-1)/12 for D=" + std::to_string(D));
        }
        ++n;
    }
    std::printf("    %d primes, total %.2fs, slowest D=%lld (%.3fs)\n", n, now_s() - t0, (long long)worstD, worst);
}

// ---------------------------------------------------------------- 3. brandt_w2.json up to permutation
static void test_brandt_json(const std::string& dir) {
    std::printf("[3] Brandt T_p vs brandt_w2.json (up to class permutation)\n");
    JV d = load(dir + "/brandt_w2.json")["data"];
    int nm = 0;
    // T2_table: one ell per D
    for (const auto& kv : d["T2_table"].o) {
        i64 D = std::stoll(kv.first);
        const JV& e = kv.second;
        MaxOrder O(D);
        ClassSet C(O);
        i64 ell = e["ell"].i();
        Mat ref = json_mat(e["T"]);
        Mat ours = brandt_neighbours(C, ell);
        std::vector<int> gr;
        for (const auto& x : e["gammas_in_rep_order"].a) gr.push_back((int)x.i());
        auto pi = match_permutation({ours}, {ref}, C.h(), gammas_of(C), gr);
        check(C.h() == e["h"].i() && pi.has_value(), "T2_table D=" + kv.first + " ell=" + std::to_string(ell));
        ++nm;
    }
    // seed_C4ii: all ells simultaneously
    for (const auto& kv : d["seed_C4ii"].o) {
        i64 D = std::stoll(kv.first);
        const JV& e = kv.second;
        MaxOrder O(D);
        ClassSet C(O);
        std::vector<Mat> ours, ref;
        std::string ells;
        for (const auto& lk : e["ell"].o) {
            i64 ell = std::stoll(lk.first);
            ref.push_back(json_mat(lk.second["T"]));
            ours.push_back(brandt_neighbours(C, ell));
            ells += " " + lk.first;
        }
        std::vector<int> gr;
        for (const auto& x : e["gammas"].a) gr.push_back((int)x.i());
        auto pi = match_permutation(ours, ref, C.h(), gammas_of(C), gr);
        check(pi.has_value(), "seed_C4ii D=" + kv.first + " ells" + ells + " simultaneous permutation");
        ++nm;
    }
    {
        const JV& e = d["T1"];
        MaxOrder O(11);
        ClassSet C(O);
        std::vector<int> gr;
        for (const auto& x : e["gammas"].a) gr.push_back((int)x.i());
        auto pi = match_permutation({brandt_neighbours(C, 2)}, {json_mat(e["T2"])}, C.h(), gammas_of(C), gr);
        check(pi.has_value(), "T1 (D=11, T_2)");
        ++nm;
    }
    std::printf("    %d records matched\n", nm);
}

// ---------------------------------------------------------------- 4. relations; two independent routes
static void test_relations(i64 Dmax) {
    std::printf("[4] row sums, weighted symmetry, commutativity, neighbours == theta_pairs, Hecke relations (D < %lld + "
                "composite D)\n", (long long)Dmax);
    std::vector<i64> Ds;
    for (i64 D = 2; D < Dmax; ++D)
        if (is_prime(D)) Ds.push_back(D);
    for (i64 D : {30, 42, 66, 70, 78, 102, 105, 110}) Ds.push_back(D);
    int ncases = 0;
    for (i64 D : Ds) {
        MaxOrder O(D);
        ClassSet C(O);
        const int r = C.h();
        auto g = gammas_of(C);
        std::vector<i64> ps;
        for (i64 p : {2, 3, 5, 7, 11, 13})
            if (D % p) ps.push_back(p);
        std::vector<Mat> T;
        for (i64 p : ps) T.push_back(brandt_neighbours(C, p));
        std::vector<i64> ns = ps;
        bool has2 = D % 2 != 0, has3 = D % 3 != 0;
        if (has2) ns.push_back(4);
        if (has2 && has3) ns.push_back(6);
        ns.push_back(1);
        auto TH = brandt_theta_pairs(C, ns);
        std::string sD = " D=" + std::to_string(D);
        for (size_t k = 0; k < ps.size(); ++k) {
            check(row_sums_ok(T[k], r, ps[k] + 1), "row sums p+1" + sD + " p=" + std::to_string(ps[k]));
            check(weighted_symmetric(T[k], g), "weighted symmetry" + sD + " p=" + std::to_string(ps[k]));
            check(T[k] == TH[ps[k]], "neighbours == theta_pairs" + sD + " p=" + std::to_string(ps[k]));
            for (size_t l = k + 1; l < ps.size(); ++l)
                check(commute(T[k], T[l], r), "commute" + sD);
        }
        Mat Id((size_t)r * r, 0);
        for (int i = 0; i < r; ++i) Id[(size_t)i * r + i] = 1;
        check(TH[1] == Id, "B(1) = 1" + sD);
        if (has2) {
            Mat T22 = matmul(T[0], T[0], r);
            for (int i = 0; i < r; ++i) T22[(size_t)i * r + i] -= 2;
            check(TH[4] == T22, "B(4) = T_2^2 - 2" + sD);
        }
        if (has2 && has3) check(TH[6] == matmul(T[0], T[1], r), "B(6) = T_2 T_3" + sD);
        ++ncases;
    }
    std::printf("    %d discriminants\n", ncases);
}

// ---------------------------------------------------------------- 5. Eichler orders
static void test_eichler_orders() {
    std::printf("[5] Eichler orders O cap O_r(J): disc = (D M)^2, order\n");
    for (i64 D : {2, 3, 5, 11, 13, 37}) {
        MaxOrder O(D);
        for (i64 M : {2, 3, 5, 7}) {
            if (D % M == 0) continue;
            Lat E = O.eichler_order(M);
            check(O.lattice_disc(E) == (i128)(D * M) * (D * M), "Eichler disc D=" + std::to_string(D) + " M=" + std::to_string(M));
            check(O.right_order(E) == E && O.left_order(E) == E, "Eichler order is its own left/right order");
        }
    }
}

// ---------------------------------------------------------------- 6. timings
static void timing(i64 q, bool pairs) {
    double t0 = now_s();
    MaxOrder O(q);
    ClassSet C(O);
    double tc = now_s() - t0;
    const auto& st = C.stats();
    std::printf("  q=%lld h=%d classset %.3fs (exact tests %llu, max qf_theta bucket %zu, buckets %zu)\n", (long long)q,
                C.h(), tc, (unsigned long long)st.exact_tests, st.max_bucket, st.buckets);
    int r = C.h();
    auto g = gammas_of(C);
    for (i64 p : {2, 13, 101}) {
        if (q % p == 0) continue;
        double t1 = now_s();
        Mat T = brandt_neighbours(C, p);
        double dt = now_s() - t1;
        bool ok = row_sums_ok(T, r, p + 1) && weighted_symmetric(T, g);
        check(ok, "timing run relations q=" + std::to_string(q) + " p=" + std::to_string(p));
        std::printf("    T_%lld (neighbours) %.3fs  [row sums, symmetry %s]\n", (long long)p, dt, ok ? "ok" : "FAIL");
    }
    if (pairs) {
        double t1 = now_s();
        auto TH = brandt_theta_pairs(C, {2, 3, 5, 7, 11, 13});
        std::printf("    theta_pairs, all n <= 13: %.3fs\n", now_s() - t1);
        check(TH[2] == brandt_neighbours(C, 2), "theta_pairs == neighbours at q=" + std::to_string(q));
    }
}


// ---------------------------------------------------------------- 7. F_fnv byte-exactness (freeblockz-export-format.md section 4, 8)
static void test_fnv() {
    std::printf("[7] F_fnv = HACS MatrixFnv text hash\n");
    Mat m = {-24, 0, 68040, 0, -24, 0, 0, 0, 2049};
    check(matrix_text(m, 3) == "-24,0,68040;0,-24,0;0,0,2049", "matrix_text");
    check(matrix_fnv(m, 3) == 0xb69e2fb38c33b922ULL, "MatrixFnv of 061_s25_module_z_exact.expected");
    MaxOrder O(11);
    ClassSet C(O);
    check(matrix_fnv(brandt_neighbours(C, 2), 2) == 0x12097637b2c137e0ULL, "D=11 T_2 F_fnv (format section 8)");
    check(matrix_fnv(brandt_neighbours(C, 3), 2) == 0xfee36f1e9928151aULL, "D=11 T_3 F_fnv (format section 8)");
    check(matrix_fnv(brandt_neighbours(C, 5), 2) == 0x825d45ddc0a53cbaULL, "D=11 T_5 F_fnv (format section 8)");
    auto ad = algebra_dim({brandt_neighbours(C, 2), brandt_neighbours(C, 3)}, 2);
    check(ad.dim == 2 && ad.exact, "D=11 d_algebra = 2");
    // v2 canonical order: expected ties (Lane A) at D <= 43 only for D = 37, 43: [[0,1]]
    for (i64 D : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}) {
        MaxOrder O2(D);
        ClassSet C2(O2);
        auto co = canonical_order_v2(C2);
        bool want_tie = D == 37 || D == 43;
        bool ok = want_tie ? (co.ties.size() == 1 && co.ties[0] == std::vector<int>{0, 1}) : co.ties.empty();
        auto g = gammas_of(C2);
        std::vector<int> gp(g.size());
        for (size_t i = 0; i < g.size(); ++i) gp[i] = g[co.perm[i]];
        Mat T = brandt_neighbours(C2, D == 2 ? 3 : 2), Tp = permute(T, co.perm);
        ok = ok && std::is_sorted(gp.begin(), gp.end()) && weighted_symmetric(Tp, gp) &&
             match_permutation({T}, {Tp}, C2.h(), g, gp).has_value();
        check(ok, "v2 canonical order / order_ties D=" + std::to_string(D));
    }
}

int main(int argc, char** argv) {
    std::string f = __FILE__;
    std::string dir = f.substr(0, f.find("/code/hacs/")) + "/code/results/s01";
    i64 eich = 10000, rel = 400;
    std::vector<i64> tq = {1009, 10007, 100003};
    bool quick = false;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--results" && i + 1 < argc) dir = argv[++i];
        else if (a == "--eichler-max" && i + 1 < argc) eich = std::stoll(argv[++i]);
        else if (a == "--relations-max" && i + 1 < argc) rel = std::stoll(argv[++i]);
        else if (a == "--quick") {
            quick = true;
            eich = 1000;
            rel = 100;
            tq = {1009};
        } else if (a == "--timing-q" && i + 1 < argc) {
            tq.clear();
            std::stringstream ss(argv[++i]);
            std::string t;
            while (std::getline(ss, t, ',')) tq.push_back(std::stoll(t));
        }
    }
    (void)quick;
    try {
        test_fnv();
        test_classsets(dir);
        test_brandt_json(dir);
        test_eichler_orders();
        test_relations(rel);
        test_eichler(eich);
        std::printf("[6] timings\n");
        for (i64 q : tq) timing(q, q < 20000);
    } catch (const std::exception& e) {
        std::printf("  [EXCEPTION] %s\n", e.what());
        ++g_fail;
    }
    std::printf("quat_selftest: %d passed, %d failed\n", g_pass, g_fail);
    return g_fail;
}
