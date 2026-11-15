// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// Standalone self-test of the integral Sym^n Brandt module (WP HJ-4a, BrandtSym.h). Not registered in HACS.
//   brandtsym_selftest [--results DIR] [--write PATH] [--quick]
// Checks (exit code = number of failures):
//   A. algebra: qb_mul = QuatAlgebra::mul_std; s multiplicative; rho_K multiplicative; rho_2(g) Q_x = Q_{g x conj g};
//      beta_n(rho g P, rho g Q) = nrd(g)^n beta_n(P, Q); rho_base integral on O.
//   B. symn.json (66 cells, D in {2,3,5,7,11,13}, k = 2..12): multiset of (|Gamma_c|, dim V^{Gamma_c}), rank, and
//      char_Z(T_ell) = rhs for every recorded ell.
//   C. for every cell of rank > 0: all T_ell (ell < 20, ell not | D) and Pi_p (p | D), Pi_D commute pairwise;
//      Pi_p^2 = p^n, Pi_D^2 = D^n; Pi_D = D^{n/2} W with W integral; self-adjointness for <,>_w (and <,>_Gamma).
//   D. pi_sign.json (8 cells): Pi_D-eigenspace dims and char_Z(T_ell | eigenspace) for ell in {2, 3, 5}.
//   E. weight 2: T_ell = Brandt2 brandt_neighbours in the canonical order (row sums ell + 1).
//   F. squarefree composite D in classsets.json (30, 42, 66, 70, 78), k = 2..12 even: as C, plus odd k -> rank 0.
//   G. mod ell^K: reduce_mod(T T') = reduce_mod(T) reduce_mod(T') mod ell^K.
//   I. (C5) seed lattice at p not | D: O_r(I_c)-stability and det(N_c^n beta_n | Lambda_c) = +-prod binom(n,i)^-1 D^(-n^2/2).
//   H. (C5) intrinsic: Lambda(I) = rho_n(beta^{-1}) Lambda(I beta) for the representatives of two class sets.
// --write PATH writes the per-cell results (code/results/laneC/hj4_symn.json) with provenance.
#include "../BrandtSym.h"
#include "../../../../NumberField/Sha256.h"
#include "JsonMin.h"
#include "RepoRoot.h"

#include <chrono>
#include <cstdio>
#include <ctime>
#include <fstream>
#include <set>
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
static std::vector<i64> primes_below(i64 n, i64 D) {
    std::vector<i64> o;
    for (i64 p = 2; p < n; ++p)
        if (is_prime(p) && D % p) o.push_back(p);
    return o;
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

// ------------------------------------------------------------------ A. algebra
static void test_algebra() {
    std::printf("A. algebra / rho_n / Q_x / beta_n\n");
    for (i64 D : {2, 3, 11, 13, 30}) {
        MaxOrder O(D);
        const i64 a = O.algebra().a(), b = O.algebra().b();
        std::vector<QB> es;
        for (int t = 0; t < 4; ++t) {
            Vec4 e{{0, 0, 0, 0}};
            e[t] = 1;
            es.push_back(qb_from(O.to_std(e)));
        }
        es.push_back(QB{Q(1), Q(2), Q(-1), Q(3)});
        bool mul_ok = true, split_ok = true, rho_ok = true, qx_ok = true, beta_ok = true;
        for (const auto& x : es)
            for (const auto& y : es) {
                QB z = qb_mul(a, b, x, y);
                // vs QuatAlgebra::mul_std on scaled integer coordinates
                Z dx(1), dy(1);
                for (int s = 0; s < 4; ++s) {
                    dx = dx * x[s].den() / Z::gcd(dx, x[s].den());
                    dy = dy * y[s].den() / Z::gcd(dy, y[s].den());
                }
                std::array<i128, 4> xi, yi;
                for (int s = 0; s < 4; ++s) {
                    xi[s] = (x[s] * Q(dx)).num().to_int64();
                    yi[s] = (y[s] * Q(dy)).num().to_int64();
                }
                auto zi = O.algebra().mul_std(xi, yi);
                for (int s = 0; s < 4; ++s)
                    mul_ok &= (z[s] * Q(dx) * Q(dy)) == Q(Z::from_string(to_string128(zi[s])));
                // s multiplicative (via rho_1 = s^T in our layout: column t of rho_1 is the image of u_t)
                for (int n : {1, 2, 4}) {
                    KMat Rx = rho_K(a, b, x, n), Ry = rho_K(a, b, y, n), Rz = rho_K(a, b, z, n);
                    for (int c = 0; c <= n; ++c) {
                        KVec e(n + 1, KElt{Q(0), Q(0)});
                        e[c] = KElt{Q(1), Q(0)};
                        KVec l = apply(a, Rz, e), r = apply(a, Rx, apply(a, Ry, e));
                        for (int t = 0; t <= n; ++t) (n == 1 ? split_ok : rho_ok) &= (l[t].r == r[t].r && l[t].s == r[t].s);
                    }
                }
                // rho_2(x) Q_y = Q_{x y conj x} for y trace zero
                QB y0 = y;
                y0[0] = Q(0);
                KVec q = quad_form(a, b, y0), lhs = apply(a, rho_K(a, b, x, 2), q);
                KVec rhs = quad_form(a, b, qb_mul(a, b, qb_mul(a, b, x, y0), qb_conj(x)));
                for (int t = 0; t < 3; ++t) qx_ok &= (lhs[t].r == rhs[t].r && lhs[t].s == rhs[t].s);
                // beta_n quasi-invariance on random-ish vectors
                for (int n : {2, 4, 6}) {
                    KVec P(n + 1), R(n + 1);
                    for (int t = 0; t <= n; ++t) {
                        P[t] = KElt{Q(t + 1), Q(t % 3)};
                        R[t] = KElt{Q(2 * t - 3), Q(1 - t)};
                    }
                    KMat G = rho_K(a, b, x, n);
                    KElt l = beta_n(a, apply(a, G, P), apply(a, G, R), n), r = beta_n(a, P, R, n);
                    Q f = Q(1);
                    Q nr = qb_nrd(a, b, x);
                    for (int i = 0; i < n; ++i) f *= nr;
                    beta_ok &= (l.r == r.r * f && l.s == r.s * f);
                }
            }
        check(mul_ok, "qb_mul = mul_std D=" + std::to_string(D));
        check(split_ok, "s multiplicative D=" + std::to_string(D));
        check(rho_ok, "rho_n multiplicative D=" + std::to_string(D));
        check(qx_ok, "rho_2(g) Q_x = Q_{g x conj g} D=" + std::to_string(D));
        check(beta_ok, "beta_n quasi-invariant D=" + std::to_string(D));
        // rho_base integral on the basis of O and on 1 + basis
        ClassSet C(O);
        for (int n : {2, 4, 8}) {
            BrandtSym M(C, n);
            bool ok = true;
            for (int t = 0; t < 4; ++t) {
                Vec4 e{{0, 0, 0, 0}};
                e[t] = 1;
                try {
                    (void)M.rho_base_int(e);
                } catch (...) {
                    ok = false;
                }
            }
            check(ok, "rho_base integral on O, D=" + std::to_string(D) + " n=" + std::to_string(n));
        }
    }
}

// ------------------------------------------------------------------ per-cell operator checks (C)
struct CellOut {
    i64 D = 0;
    int k = 0;
    std::string json;
};

static std::string cell_checks(const BrandtSym& M, const std::vector<i64>& ells, std::map<i64, ZMat>& Ts,
                               bool& all_ok) {
    const i64 D = M.D();
    const int n = M.n(), m = n / 2;
    std::ostringstream js;
    all_ok = true;
    auto ck = [&](bool ok, const std::string& w) {
        check(ok, w);
        all_ok &= ok;
        return ok;
    };
    std::string tag = "D=" + std::to_string(D) + " k=" + std::to_string(n + 2);
    for (i64 l : ells)
        if (!Ts.count(l)) Ts[l] = M.T(l);
    std::vector<std::pair<std::string, ZMat>> ops;
    for (i64 l : ells) ops.push_back({"T" + std::to_string(l), Ts[l]});
    auto ps = prime_factors(D);
    std::map<i64, ZMat> Pis;
    for (i64 p : ps) Pis[p] = M.Pi(p);
    ZMat PiD = ps.size() == 1 ? Pis[D] : M.Pi(D);
    for (i64 p : ps) ops.push_back({"Pi" + std::to_string(p), Pis[p]});
    if (ps.size() > 1) ops.push_back({"Pi" + std::to_string(D), PiD});
    bool comm = true;
    for (size_t i = 0; i < ops.size(); ++i)
        for (size_t j = i + 1; j < ops.size(); ++j)
            comm &= symz::mul(ops[i].second, ops[j].second) == symz::mul(ops[j].second, ops[i].second);
    ck(comm, "all operators commute " + tag);
    bool pi2 = true;
    for (i64 p : ps) pi2 &= symz::is_scalar(symz::mul(Pis[p], Pis[p]), Z::pow(Z(p), n));
    pi2 &= symz::is_scalar(symz::mul(PiD, PiD), Z::pow(Z(D), n));
    ck(pi2, "Pi_p^2 = p^n, Pi_D^2 = D^n " + tag);
    bool prod = true;
    if (ps.size() > 1) {
        ZMat P = symz::identity(M.rank());
        for (i64 p : ps) P = symz::mul(P, Pis[p]);
        prod = P == PiD;
        ck(prod, "Pi_D = prod Pi_p " + tag);
    }
    bool div = true;
    Z Dm = Z::pow(Z(D), m);
    for (const auto& r : PiD)
        for (const auto& x : r) div &= x.floor_mod(Dm).is_zero();
    ck(div, "Pi_D divisible by D^{n/2} on M_Z " + tag);
    bool sa = true, saG = true;
    for (const auto& o : ops) {
        sa &= M.self_adjoint(o.second, BrandtSym::Weight::w);
        saG &= M.self_adjoint(o.second, BrandtSym::Weight::gamma);
    }
    ck(sa, "self-adjoint <,>_w " + tag);
    ck(saG, "self-adjoint <,>_Gamma " + tag);
    // Gram data
    QMat Gw = M.gram(BrandtSym::Weight::w, true);
    Z sw = BrandtSym::denominator_lcm(Gw);
    // determinant of the w-Gram (exact rational, by blocks)
    Q det(1);
    for (int c = 0; c < M.h(); ++c) {
        QMat B = M.gram_block(c);
        const int d = (int)B.size();
        for (int col = 0; col < d; ++col) {
            int p = col;
            while (p < d && B[p][col].is_zero()) ++p;
            if (p == d) {
                det = Q(0);
                break;
            }
            if (p != col) {
                std::swap(B[p], B[col]);
                det = -det;
            }
            det *= B[col][col] / Q(M.classes()[c].w);
            for (int r = col + 1; r < d; ++r) {
                if (B[r][col].is_zero()) continue;
                Q f = B[r][col] / B[col][col];
                for (int j = col; j < d; ++j) B[r][j] -= f * B[col][j];
            }
        }
    }
    js << "\"rank\": " << M.rank() << ", \"h\": " << M.h() << ", \"gammas\": [";
    for (int c = 0; c < M.h(); ++c) js << (c ? "," : "") << M.gammas()[c];
    js << "], \"dims\": [";
    for (int c = 0; c < M.h(); ++c) js << (c ? "," : "") << M.dims()[c];
    js << "], \"charpoly_T\": {";
    for (size_t i = 0; i < ells.size(); ++i)
        js << (i ? ", " : "") << "\"" << ells[i] << "\": \"" << cp_text(symz::charpoly(Ts[ells[i]])) << "\"";
    js << "}, \"charpoly_Pi_D\": \"" << cp_text(symz::charpoly(PiD)) << "\"";
    js << ", \"commute_all\": " << (comm ? "true" : "false") << ", \"Pi_squared_ok\": " << (pi2 ? "true" : "false")
       << ", \"Pi_D_eq_prod_Pi_p\": " << (prod ? "true" : "false") << ", \"Pi_D_divisible_by_D^(n/2)\": " << (div ? "true" : "false")
       << ", \"self_adjoint_w\": " << (sa ? "true" : "false") << ", \"self_adjoint_Gamma\": " << (saG ? "true" : "false")
       << ", \"gram_w_det\": \"" << det.to_string() << "\", \"gram_w_denominator_lcm\": \"" << sw.to_string() << "\"";
    return js.str();
}

// ------------------------------------------------------------------ B + C + E: symn.json
static std::vector<CellOut> test_symn(const std::string& dir, bool quick) {
    std::printf("B/C/E. symn.json cells\n");
    JV J = load(dir + "/symn.json");
    const JV& grid = J["data"]["grid"];
    std::vector<CellOut> out;
    int matched = 0, total = 0;
    for (const auto& kv : grid.o) {
        const JV& cell = kv.second;
        const i64 D = cell["D"].i();
        const int k = (int)cell["k"].i();
        if (quick && k > 6) continue;
        ++total;
        MaxOrder O(D);
        ClassSet C(O);
        BrandtSym M(C, k - 2);
        const std::string tag = "D=" + std::to_string(D) + " k=" + std::to_string(k);
        bool ok = true;
        // dims multiset
        std::multiset<std::pair<int, int>> ours, ref;
        for (int c = 0; c < M.h(); ++c) ours.insert({M.gammas()[c], M.dims()[c]});
        for (size_t c = 0; c < cell["gammas"].a.size(); ++c)
            ref.insert({(int)cell["gammas"][c].i(), (int)cell["dims_V_Gamma"][c].i()});
        bool dok = ours == ref && M.rank() == (int)cell["dim_brandt"].i();
        check(dok, "symn dims " + tag);
        ok &= dok;
        std::map<i64, ZMat> Ts;
        std::ostringstream js;
        js << "{\"D\": " << D << ", \"k\": " << k << ", \"symn_match\": {";
        bool first = true;
        for (const auto& e : cell["ell"].o) {
            i64 l = std::stoll(e.first);
            Ts[l] = M.T(l);
            std::string mine = cp_text(symz::charpoly(Ts[l])), theirs = json_list_text(e.second["rhs"]);
            bool cok = mine == theirs;
            check(cok, "symn charpoly " + tag + " ell=" + e.first + " ours " + mine + " ref " + theirs);
            ok &= cok;
            js << (first ? "" : ", ") << "\"" << l << "\": " << (cok ? "true" : "false");
            first = false;
        }
        js << "}";
        if (k == 2) {  // E: weight 2 = Brandt2 in canonical order
            auto perm = canonical_order_v2(C).perm;
            bool w2 = true;
            for (const auto& t : Ts) {
                Mat B = permute(brandt_neighbours(C, t.first), perm);
                const int r = M.h();
                for (int i = 0; i < r; ++i)
                    for (int j = 0; j < r; ++j) w2 &= t.second[i][j] == Z(B[(size_t)i * r + j]);
            }
            check(w2, "k=2: T_ell = Brandt2 " + tag);
            ok &= w2;
        }
        if (M.rank() > 0) {
            bool cok = true;
            js << ", " << cell_checks(M, primes_below(20, D), Ts, cok);
            ok &= cok;
        } else {
            js << ", \"rank\": 0";
        }
        js << ", \"all_ok\": " << (ok ? "true" : "false") << "}";
        matched += ok;
        out.push_back({D, k, js.str()});
    }
    std::printf("  symn.json: %d / %d cells fully matched\n", matched, total);
    check(quick || total == 66, "symn.json has 66 cells");
    return out;
}

// ------------------------------------------------------------------ D. pi_sign.json
static std::vector<CellOut> test_pi_sign(const std::string& dir) {
    std::printf("D. pi_sign.json\n");
    JV J = load(dir + "/pi_sign.json");
    std::vector<CellOut> out;
    for (const auto& kv : J["data"]["grid"].o) {
        const JV& br = kv.second["brandt"];
        const i64 D = kv.second["D"].i();
        const int k = (int)kv.second["k"].i(), n = k - 2;
        MaxOrder O(D);
        ClassSet C(O);
        BrandtSym M(C, n);
        ZMat P = M.Pi(D);
        bool ok = M.rank() == (int)br["dim"].i();
        std::ostringstream js;
        js << "{\"D\": " << D << ", \"k\": " << k << ", \"eigenspaces\": {";
        bool first = true;
        for (const auto& es : br["eigenspaces"].o) {
            Z lam = Z::from_string(es.second["lambda"].s);
            int dim = -1;
            js << (first ? "" : ", ") << "\"" << es.first << "\": {\"lambda\": \"" << lam.to_string() << "\"";
            first = false;
            for (const auto& cpj : es.second["charpoly_T"].o) {
                ZMat R = symz::restrict_to_eigenspace(M.T(std::stoll(cpj.first)), P, lam);
                dim = (int)R.size();
                std::string mine = cp_text(symz::charpoly(R)), theirs = json_list_text(cpj.second);
                bool c = mine == theirs;
                check(c, "pi_sign D=" + std::to_string(D) + " k=" + std::to_string(k) + " " + es.first + " ell=" + cpj.first +
                             " ours " + mine + " ref " + theirs);
                ok &= c;
            }
            if (dim < 0) dim = (int)symz::restrict_to_eigenspace(P, P, lam).size();
            bool dok = dim == (int)es.second["dim"].i();
            check(dok, "pi_sign dim D=" + std::to_string(D) + " k=" + std::to_string(k) + " " + es.first);
            ok &= dok;
            js << ", \"dim\": " << dim << "}";
        }
        js << "}, \"all_ok\": " << (ok ? "true" : "false") << "}";
        out.push_back({D, k, js.str()});
    }
    return out;
}

// ------------------------------------------------------------------ F. composite D
static std::vector<CellOut> test_composite(const std::string& dir, bool quick) {
    std::printf("F. composite squarefree D\n");
    JV J = load(dir + "/classsets.json");
    std::vector<CellOut> out;
    for (const auto& kv : J["data"].o) {
        const i64 D = kv.second["D"].i();
        if (prime_factors(D).size() < 2) continue;
        MaxOrder O(D);
        ClassSet C(O);
        for (int k = 2; k <= (quick ? 6 : 12); ++k) {
            BrandtSym M(C, k - 2);
            std::ostringstream js;
            js << "{\"D\": " << D << ", \"k\": " << k << ", ";
            bool ok = true;
            if (k % 2) {
                ok = M.rank() == 0;
                check(ok, "odd k rank 0 D=" + std::to_string(D) + " k=" + std::to_string(k));
                js << "\"rank\": 0";
            } else if (M.rank() == 0) {
                js << "\"rank\": 0";
            } else {
                std::map<i64, ZMat> Ts;
                js << cell_checks(M, primes_below(20, D), Ts, ok);
                if (k == 2) {
                    bool rs = true;
                    for (const auto& t : Ts)
                        for (const auto& r : t.second) {
                            Z s(0);
                            for (const auto& x : r) s += x;
                            rs &= s == Z(t.first + 1);
                        }
                    check(rs, "k=2 row sums D=" + std::to_string(D));
                    ok &= rs;
                }
            }
            js << ", \"all_ok\": " << (ok ? "true" : "false") << "}";
            out.push_back({D, k, js.str()});
        }
    }
    return out;
}

// ------------------------------------------------------------------ G. mod ell^K
static void test_mod() {
    std::printf("G. mod ell^K\n");
    MaxOrder O(13);
    ClassSet C(O);
    BrandtSym M(C, 8);
    ZMat T2 = M.T(2), T3 = M.T(3);
    const u64 m = 37ULL * 37 * 37;
    auto A = symz::reduce_mod(T2, m), B = symz::reduce_mod(T3, m), AB = symz::reduce_mod(symz::mul(T2, T3), m);
    bool ok = true;
    for (size_t i = 0; i < A.size(); ++i)
        for (size_t j = 0; j < A.size(); ++j) {
            unsigned __int128 s = 0;
            for (size_t t = 0; t < A.size(); ++t) s = (s + (unsigned __int128)A[i][t] * B[t][j]) % m;
            ok &= (u64)s == AB[i][j];
        }
    check(ok, "reduce_mod is a ring map (D=13, k=10, mod 37^3)");
}

// ------------------------------------------------------------------ H. the lattice is intrinsic (C5)
// Two class sets of the same order with different BFS primes ell0 have different representatives I_c, I'_c = I_c beta.
// (C5) says Lambda(I_c) = rho_n(beta^{-1}) Lambda(I'_c) exactly: the images of the HNF basis of Lambda(I'_c) have
// integral coordinates in the HNF basis of Lambda(I_c), with determinant +-1.
static void test_intrinsic() {
    std::printf("H. lattice independent of the class representatives\n");
    int n_differ = 0, n_cases = 0;
    for (i64 D : {2, 11, 13, 17, 23, 30, 42}) {
        MaxOrder O(D);
        ClassSet C1(O);
        ClassSet::Options o2;
        o2.ell0 = C1.ell0() == 2 ? 3 : 5;
        if (D % o2.ell0 == 0) o2.ell0 = 7;
        ClassSet C2(O, o2);
        const i64 a = O.algebra().a(), b = O.algebra().b();
        for (int n : {2, 4, 6}) {
            BrandtSym M1(C1, n), M2(C2, n);
            bool ok = true, differ = false;
            for (int c2 = 0; c2 < M2.h(); ++c2) {
                const SymClass& s2 = M2.classes()[c2];
                int e1 = C1.identify(s2.I, s2.N, true);
                int c1 = -1;
                for (int c = 0; c < M1.h(); ++c)
                    if (M1.classes()[c].enum_index == e1) c1 = c;
                const SymClass& s1 = M1.classes()[c1];
                differ |= !(s1.I == s2.I);
                // I_1 = I_2 beta, beta = delta / N_2, delta in conj(I_2) I_1 of nrd N_2 N_1
                i128 nn = (i128)s1.N * s2.N;
                Lat P = O.product(O.conj(s2.I), s1.I, nn * nn);
                Reduced R = lll_reduce(P, O.embedding(), O.gram());
                Vec4 delta{};
                bool found = false;
                fp_enumerate(R, 2 * nn, [&](const i64* x, i128 v2) {
                    if (v2 == 2 * nn) {
                        delta = combine(R, x);
                        found = true;
                        return false;
                    }
                    return true;
                });
                if (!found) {
                    ok = false;
                    continue;
                }
                QB beta = qb_from(O.to_std(delta, s2.N));
                Q nb = qb_nrd(a, b, beta);
                QB binv = qb_conj(beta);
                for (auto& x : binv) x = x / nb;
                KMat Rb = rho_K(a, b, binv, n);
                ZMat U;
                for (int j = 0; j <= n; ++j) {
                    auto z = M1.class_coords(c1, M1.base_coords(apply(a, Rb, M1.base_vector(s2.H[j]))));
                    std::vector<Z> row;
                    for (const auto& x : z) {
                        if (x.den() != Z(1)) ok = false;
                        row.push_back(x.num());
                    }
                    U.push_back(row);
                }
                if (ok) {
                    Z det = symz::charpoly(U)[0];
                    ok &= det == Z(1) || det == Z(-1);
                }
            }
            check(ok, "Lambda(I) = rho(beta^{-1}) Lambda(I beta), D=" + std::to_string(D) + " n=" + std::to_string(n) +
                          (differ ? " (representatives differ)" : " (same representatives)"));
            ++n_cases;
            n_differ += differ;
        }
    }
    std::printf("  %d / %d cases with differing representatives\n", n_differ, n_cases);
    check(n_differ > 0, "intrinsic test exercises differing representatives");
}

// ------------------------------------------------------------------ I. Lambda_c is the seed lattice at p not | D (audit m2)
// For every class: Lambda_c is O_r(I_c)-stable (rho_class integral on its Z-basis), and
//   det(N_c^n beta_n | Lambda_c) = +- prod_i binom(n, i)^{-1} * D^{-n^2/2},
// i.e. away from D it equals det(beta_n | Sym^n(Z_p^2)) = +- prod binom(n,i)^{-1}: an O_r(I_c) (x) Z_p = M_2(Z_p)-stable
// lattice with the determinant of Sym^n(Z_p^2) (for p > n the stable lattices are the p^k Sym^n, so this pins it).
static void test_seed_lattice() {
    std::printf("I. Lambda_c = seed lattice at p not | D (stability + determinant)\n");
    for (i64 D : {2, 3, 5, 7, 11, 13, 17, 23, 30, 42}) {
        MaxOrder O(D);
        ClassSet C(O);
        for (int n : {2, 4, 6, 8, 10}) {
            BrandtSym M(C, n);
            const i64 a = M.a();
            bool ok = true;
            for (int c = 0; c < M.h(); ++c) {
                const SymClass& s = M.classes()[c];
                std::vector<KVec> v;
                for (const auto& hrow : s.H) v.push_back(M.base_vector(hrow));
                QMat G(n + 1, std::vector<Q>(n + 1));
                Q Nn(Z::pow(Z(s.N), (uint64_t)n));
                for (int i = 0; i <= n; ++i)
                    for (int j = 0; j <= n; ++j) {
                        KElt b = beta_n(a, v[i], v[j], n);
                        ok &= b.s.is_zero();
                        G[i][j] = b.r * Nn;
                    }
                for (int t = 0; t < 4; ++t)
                    for (const auto& r : M.rho_class(c, s.order_basis[t]))
                        for (const auto& x : r) ok &= x.den() == Z(1);
                // determinant by elimination
                Q det(1);
                for (int col = 0; col <= n && !det.is_zero(); ++col) {
                    int p = col;
                    while (p <= n && G[p][col].is_zero()) ++p;
                    if (p > n) {
                        det = Q(0);
                        break;
                    }
                    if (p != col) {
                        std::swap(G[p], G[col]);
                        det = -det;
                    }
                    det *= G[col][col];
                    for (int r = col + 1; r <= n; ++r) {
                        if (G[r][col].is_zero()) continue;
                        Q f = G[r][col] / G[col][col];
                        for (int j = col; j <= n; ++j) G[r][j] -= f * G[col][j];
                    }
                }
                Q target(1);
                for (int i = 0; i <= n; ++i) {
                    Z bnm(1);
                    for (int t = 1; t <= i; ++t) bnm = bnm * Z(n - i + t) / Z(t);
                    target = target / Q(bnm);
                }
                target = target / Q(Z::pow(Z(D), (uint64_t)(n * n / 2)));
                ok &= det == target || det == -target;
            }
            check(ok, "seed lattice (O_r-stable, det = +-prod binom^-1 D^(-n^2/2)) D=" + std::to_string(D) + " n=" + std::to_string(n));
        }
    }
}

int main(int argc, char** argv) {
    std::string repo = hacs_jl_test::repo_root_guess(__FILE__);  // audit m1; override with --results
    std::string dir = repo + "/code/results/s01", write;
    bool quick = false;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--results" && i + 1 < argc) dir = argv[++i];
        else if (a == "--write" && i + 1 < argc) write = argv[++i];
        else if (a == "--quick") quick = true;
    }
    auto t0 = std::chrono::steady_clock::now();
    std::vector<CellOut> symn, pis, comp;
    try {
        test_algebra();
        symn = test_symn(dir, quick);
        pis = test_pi_sign(dir);
        comp = test_composite(dir, quick);
        test_mod();
        test_intrinsic();
        test_seed_lattice();
    } catch (const std::exception& e) {
        check(false, std::string("exception: ") + e.what());
    }
    double rt = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    std::printf("brandtsym_selftest: %d passed, %d failed (%.1f s)\n", g_pass, g_fail, rt);
    if (!write.empty()) {
        std::time_t t = std::time(nullptr);
        char date[64];
        std::strftime(date, sizeof date, "%Y-%m-%dT%H:%M:%SZ", std::gmtime(&t));
        std::string commit = run_cmd("git -C '" + repo + "' rev-parse HEAD 2>/dev/null");
        if (commit.empty()) commit = "unknown";
        std::string dirty = run_cmd("git -C '" + repo + "' status --porcelain -- code/hacs/src/hacs/Registry/JL/quat 2>/dev/null");
        if (!dirty.empty()) commit += "-dirty";
        std::ofstream o(write);
        o << "{\"provenance\": {\"script\": \"code/hacs/src/hacs/Registry/JL/quat/tests/brandtsym_selftest.cpp\", \"commit\": \""
          << commit << "\", \"params\": {\"quick\": " << (quick ? "true" : "false")
          << ", \"ells_checks\": \"primes < 20 not dividing D\", \"references\": [\"code/results/s01/symn.json\", "
             "\"code/results/s01/pi_sign.json\", \"code/results/s01/classsets.json\"]}, \"date\": \""
          << date << "\", \"runtime_s\": " << rt << ", \"binary_sha256\": \"" << sha256_file("/proc/self/exe")
          << "\", \"tag\": \"computed\", \"checks_passed\": " << g_pass << ", \"checks_failed\": " << g_fail << "},\n \"data\": {"
          << "\"conventions\": \"BrandtSym.h (C1)-(C7): symn.py splitting and rho_n column convention; Gross form; lattice "
             "Lambda_c = N_c^{-n/2} span{Q_{x_1}..Q_{x_{n/2}} : x_i in (O_r(I_c)^0)^#}; T_ell = sum_J rho(conj(delta_J)/N_c); "
             "Pi_p unnormalised (Pi_D^2 = D^n); <,>_w = sum_c N_c^n beta_n / w_c\",\n  \"symn\": [\n";
        for (size_t i = 0; i < symn.size(); ++i) o << "   " << symn[i].json << (i + 1 < symn.size() ? ",\n" : "\n");
        o << "  ],\n  \"pi_sign\": [\n";
        for (size_t i = 0; i < pis.size(); ++i) o << "   " << pis[i].json << (i + 1 < pis.size() ? ",\n" : "\n");
        o << "  ],\n  \"composite_D\": [\n";
        for (size_t i = 0; i < comp.size(); ++i) o << "   " << comp[i].json << (i + 1 < comp.size() ? ",\n" : "\n");
        o << "  ]}}\n";
        std::printf("wrote %s\n", write.c_str());
    }
    return g_fail;
}
