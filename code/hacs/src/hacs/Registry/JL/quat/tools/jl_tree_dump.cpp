// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// jl_tree_dump (WP HJ-7a): native tree quotients BG(U, q) of B_D and their weight-2 Ribet / Ihara data, for the cells of
// the stage-02/03 reference files (code/results/s02/{T2,T3,H_Vk,validation}.json, s03/{T1,T2,T6}.json).
//
//   jl_tree_dump [--suite NAME]... [--out FILE]
// Suites (each mirrors the generating Python script's case list; the Python file is named per suite):
//   s02_validation  validate_s02.py: D <= 53 definite, q in {2,3,5,7,11,13}, q !| D; levels max, U0(first prime of
//                   {2,..,13} prime to Dq), U1(first of 3,4,5,7 prime to Dq) if D <= 23
//   s02_T2          tables_s02.py t2: (D, q) in {(2,7), (2,13), (11,2)}, U = O^x (full graph data)
//   s02_T3          tables_s02.py t3: D = 3, q = 2, U_1(5^s), s = 1, 2, 3
//   s02_HVk2        twoterm.py CASES at k = 2 (weight 2 part of H_Vk.json): H_0, H_1, H^0, H^1 over Z/p^m
//   s03_T1          ribet/mazur.py: B_q, q in {11, 23, 37, 101, 131}: weights, Phi^comb, Eisenstein check
//   s03_T2          ribet/collapse.py: (D, q) in {(2,7), (2,13), (11,2)}: alpha alpha^dagger, Phi^comb, sign checks
//   s03_T6k2        ribet/ihara.py at k = 2: B_3, q = 2, levels max and U_1(p) (p = 5, 7), H_0 in both conventions
// Every number is computed natively (MaxOrder, ClassSet, Brandt2, Tree); the comparison with the reference values is
// done by code/python/langlandscape/hacs_bridge/laneC_hj7_compare.py, which reads this file and recomputes nothing.
#include "../Tree.h"

#include <chrono>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <numeric>
#include <set>
#include <sstream>

using namespace hacs_jl;
using zlin::Z;
using zlin::ZM;

namespace {

// ---------------------------------------------------------------- JSON
std::string js(const std::string& s) { return "\"" + s + "\""; }
std::string jb(bool b) { return b ? "true" : "false"; }
template <class T>
std::string jl(const std::vector<T>& v) {
    std::string o = "[";
    for (size_t i = 0; i < v.size(); ++i) {
        if (i) o += ",";
        if constexpr (std::is_same_v<T, Z>)
            o += v[i].to_string();
        else if constexpr (std::is_same_v<T, std::string>)
            o += js(v[i]);
        else
            o += std::to_string(v[i]);
    }
    return o + "]";
}
template <class T>
std::string jm(const std::vector<std::vector<T>>& M) {
    std::string o = "[";
    for (size_t i = 0; i < M.size(); ++i) o += (i ? "," : "") + jl(M[i]);
    return o + "]";
}
struct Obj {
    std::string s;
    Obj& add(const std::string& k, const std::string& raw) {
        s += (s.empty() ? "" : ",") + js(k) + ":" + raw;
        return *this;
    }
    std::string str() const { return "{" + s + "}"; }
};

// ---------------------------------------------------------------- caches
std::map<i64, std::unique_ptr<MaxOrder>> g_orders;
std::map<i64, std::unique_ptr<ClassSet>> g_classes;
const ClassSet& classes(i64 D) {
    auto it = g_classes.find(D);
    if (it != g_classes.end()) return *it->second;
    g_orders[D] = std::make_unique<MaxOrder>(D);
    g_classes[D] = std::make_unique<ClassSet>(*g_orders[D]);
    return *g_classes[D];
}

i64 phi_ram(i64 D) {
    i64 r = 1;
    for (i64 p : prime_factors(D)) r *= p - 1;
    return r;
}
i128 lcm128(i128 a, i128 b) { return a / gcd128(a, b) * b; }
std::string mass(const std::vector<int>& s) {
    i128 L = 1;
    for (int x : s) L = lcm128(L, x);
    i128 n = 0;
    for (int x : s) n += L / x;
    return frac_str(n, L);
}
// sum 1/s as (num, den)
std::pair<i128, i128> massq(const std::vector<int>& s) {
    i128 L = 1;
    for (int x : s) L = lcm128(L, x);
    i128 n = 0;
    for (int x : s) n += L / x;
    i128 g = gcd128(n, L);
    return {n / g, L / g};
}
bool eqq(std::pair<i128, i128> a, std::pair<i128, i128> b) { return a.first * b.second == a.second * b.first; }

std::vector<std::vector<i64>> to64(const ZM& M) {
    std::vector<std::vector<i64>> o;
    for (auto& r : M) {
        std::vector<i64> x;
        for (auto& z : r) x.push_back(z.to_int64());
        o.push_back(x);
    }
    return o;
}

std::vector<i64> V64(const std::vector<int>& v) { return std::vector<i64>(v.begin(), v.end()); }

// ---------------------------------------------------------------- the common graph block
Obj graph_block(const TreeQuotient& T, bool full) {
    Obj o;
    o.add("D", std::to_string(T.D)).add("q", std::to_string(T.q));
    o.add("level", Obj().add("N1", std::to_string(T.level.N1)).add("N0", std::to_string(T.level.N0)).str());
    o.add("level_str", js(T.level.str())).add("h", std::to_string(T.h));
    o.add("X", std::to_string(T.X())).add("E", std::to_string(T.nE()));
    o.add("components", std::to_string(T.components())).add("minus_one_in_U", jb(T.minus_one_in_U));
    o.add("stab_v", jl(T.stab_v())).add("stab_e", jl(T.stab_e())).add("w_v", jl(T.w_v())).add("w_e", jl(T.w_e()));
    o.add("s0", jl(T.s0)).add("s1", jl(T.s1));
    o.add("points_v", std::to_string(T.points_v)).add("points_e", std::to_string(T.points_e));
    o.add("orbit_checks", jb(T.orbit_checks)).add("build_seconds", std::to_string(T.seconds));
    // boundary
    ZM d = tree2::boundary(T);
    auto sd = zlin::smith(d);
    const int rk = (int)sd.size();
    std::vector<Z> gt1;
    for (auto& x : sd)
        if (x != Z(1)) gt1.push_back(x);
    o.add("rank_boundary", std::to_string(rk)).add("rk_H1", std::to_string(T.nE() - rk));
    o.add("rk_H1_formula", std::to_string(T.nE() - 2 * T.X() + 1)).add("boundary_divisors_gt1", jl(gt1));
    // masses, fibre sums (validate_s02.check_case)
    auto sv = T.stab_v(), se = T.stab_e(), wv = T.w_v(), we = T.w_e();
    o.add("vertex_mass", js(mass(sv))).add("edge_mass", js(mass(se)));
    o.add("vertex_mass_w", js(mass(wv))).add("edge_mass_w", js(mass(we)));
    bool fibre = true;
    for (int j = 0; j < 2; ++j) {
        std::vector<std::pair<i128, i128>> f(T.X(), {0, 1});
        for (int e = 0; e < T.nE(); ++e) {
            int x = j ? T.s1[e] : T.s0[e];
            auto& a = f[x];
            i128 n = (i128)sv[x], dd = se[e];  // a + n/dd
            a = {a.first * dd + n * a.second, a.second * dd};
            i128 g = gcd128(a.first, a.second);
            a = {a.first / g, a.second / g};
        }
        for (auto& a : f) fibre &= (a.second == 1 && a.first == T.q + 1);
    }
    auto mv = massq(sv), me = massq(se), mvw = massq(wv), mew = massq(we);
    bool ms = eqq(me, {(T.q + 1) * mv.first, mv.second}) && eqq(mew, {(T.q + 1) * mvw.first, mvw.second});
    if (T.level.maximal()) ms &= eqq(mvw, {phi_ram(T.D), 12});
    o.add("fibre_sums", jb(fibre)).add("mass", jb(ms));
    const bool conn = T.components() == 1;
    const bool h1ok = (T.nE() - rk) == T.nE() - 2 * T.X() + T.components() && (T.nE() - rk) == T.nE() - 2 * T.X() + 1;
    o.add("connected", jb(conn)).add("rk_H1_ok", jb(h1ok)).add("all_pass", jb(conn && fibre && ms && h1ok));
    bool free = true;
    for (int s : sv) free &= (s == 1);
    for (int s : se) free &= (s == 1);
    o.add("free", jb(free));
    // Hecke matrix; at U = O^x it must equal the Brandt matrix T_q (same class order)
    auto H = T.hecke();
    if (T.level.maximal()) {
        const ClassSet& C = classes(T.D);
        Mat B = brandt_neighbours(C, T.q);
        bool eq = true;
        for (int i = 0; i < T.X(); ++i)
            for (int j = 0; j < T.X(); ++j) eq &= (B[(size_t)i * T.X() + j] == H[i][j]);
        o.add("hecke_equals_brandt_Tq", jb(eq));
    }
    // the Ihara map iota = (s_0^*, -s_1^*) : Z[X]^2 -> Z[E]
    {
        ZM I = tree2::ihara(T);
        auto si = zlin::smith(I);
        std::vector<Z> tors;
        for (auto& x : si)
            if (x != Z(1)) tors.push_back(x);
        o.add("ihara", Obj()
                           .add("map", js("iota(f0,f1) = s0^* f0 - s1^* f1 : Z[X]^2 -> Z[E]"))
                           .add("rank", std::to_string(si.size()))
                           .add("kernel_rank", std::to_string(2 * T.X() - (int)si.size()))
                           .add("coker_free_rank", std::to_string(T.nE() - (int)si.size()))
                           .add("coker_torsion", jl(tors))
                           .str());
    }
    if (full) {
        std::vector<std::vector<i64>> mult;
        auto A = T.adjacency();
        o.add("hecke", jm(H)).add("hecke_prime", jm(T.hecke_prime())).add("adjacency", jm(A));
    }
    return o;
}

// ---------------------------------------------------------------- s03/T2 (collapse.py)
std::string coker_extras(const TreeQuotient& T, const ZM& M, bool weighted, Obj& o) {
    const int X = T.X(), n = 2 * X;
    auto d = zlin::smith(M);
    std::vector<Z> gt1;
    for (auto& x : d)
        if (x != Z(1)) gt1.push_back(x);
    o.add("matrix", jm(to64(M))).add("rank_matrix", std::to_string(d.size()));
    o.add("free_rank", std::to_string(n - (int)d.size())).add("torsion_order", zlin::prod(d).to_string());
    o.add("divisors_gt1", jl(gt1)).add("rank_Q", std::to_string(d.size()));
    // index on ker eps (basis e_i - e_{n-1})
    {
        ZM R(n - 1, std::vector<Z>(n - 1, Z(0)));
        for (int i = 0; i < n - 1; ++i)
            for (int r = 0; r < n - 1; ++r) R[r][i] = M[r][i] - M[r][n - 1];
        auto dd = zlin::smith(R);
        o.add("index_on_ker_eps", ((int)dd.size() == n - 1 ? zlin::prod(dd) : Z(0)).to_string());
    }
    // Eisenstein vector and the two other readings
    std::vector<i64> w = weighted ? V64(T.w_v()) : std::vector<i64>(X, 1);
    i128 L = 1;
    for (auto x : w) L = lcm128(L, x);
    std::vector<i64> v;
    for (int t = 0; t < 2; ++t)
        for (auto x : w) v.push_back((i64)(L / x));
    i64 g0 = 0;
    for (auto x : v) g0 = std::gcd(g0, x);
    for (auto& x : v) x /= g0;
    bool kills = true;
    for (int r = 0; r < n; ++r) {
        Z s = 0;
        for (int c = 0; c < n; ++c) s += M[r][c] * Z(v[c]);
        kills &= s.is_zero();
    }
    o.add("eisenstein_vector", jl(v)).add("eisenstein_vector_in_kernel", jb(kills));
    {
        ZM Mv = M;
        for (int r = 0; r < n; ++r) Mv[r].push_back(Z(v[r]));
        o.add("coker_on_quotient_by_Eis_saturation", zlin::prod(zlin::smith(Mv)).to_string());
    }
    {
        std::vector<i64> W2 = w;
        W2.insert(W2.end(), w.begin(), w.end());
        ZM Bf(n - 1, std::vector<Z>(n - 1, Z(0)));
        for (int a = 0; a < n - 1; ++a)
            for (int b = 0; b < n - 1; ++b) {
                // sum_r W2[r] ka[r] (M kb)[r], ka = e_a - e_{n-1}
                auto Mk = [&](int r) { return M[r][b] - M[r][n - 1]; };
                Z s = Z(W2[a]) * Mk(a) - Z(W2[n - 1]) * Mk(n - 1);
                Bf[a][b] = s;
            }
        auto db = zlin::smith(Bf);
        o.add("coker_W_to_Wdual_order", ((int)db.size() == n - 1 ? zlin::prod(db) : Z(0)).to_string());
    }
    // NEW: the cuspidal part Cusp = {(f0, f1) : sum f0 = sum f1 = 0} (degree zero on each type); stable for the weighted
    // alpha alpha^dagger (fibre sums), basis e_i - e_{X-1} in each type
    {
        bool stable = true;
        const int c = X - 1;
        ZM Mc(2 * c, std::vector<Z>(2 * c, Z(0)));
        for (int t = 0; t < 2; ++t)
            for (int i = 0; i < c; ++i) {
                std::vector<Z> img(n, Z(0));
                for (int r = 0; r < n; ++r) img[r] = M[r][t * X + i] - M[r][t * X + X - 1];
                Z s0 = 0, s1 = 0;
                for (int r = 0; r < X; ++r) {
                    s0 += img[r];
                    s1 += img[X + r];
                }
                stable &= s0.is_zero() && s1.is_zero();
                for (int u = 0; u < 2; ++u)
                    for (int r = 0; r < c; ++r) Mc[u * c + r][t * c + i] = img[u * X + r];
            }
        Obj cu;
        cu.add("stable", jb(stable)).add("rank", std::to_string(2 * c));
        if (stable && c > 0) {
            auto dc = zlin::smith(Mc);
            std::vector<Z> g;
            for (auto& x : dc)
                if (x != Z(1)) g.push_back(x);
            cu.add("full_rank", jb((int)dc.size() == 2 * c)).add("divisors_gt1", jl(g));
            cu.add("order", zlin::prod(dc).to_string()).add("cyclic", jb(g.size() <= 1));
        }
        o.add("cuspidal_coker", cu.str());
    }
    return o.str();
}

Obj phi_obj(const tree2::Phi& p) {
    Obj o;
    o.add("rank", std::to_string(p.rank)).add("divisors", jl(p.divisors)).add("order", p.order.to_string());
    o.add("cyclic", jb(p.cyclic));
    return o;
}

std::string t2_case(i64 D, i64 q) {
    const ClassSet& C = classes(D);
    TreeQuotient T = build_tree(C, q);
    Obj o = graph_block(T, true);
    const int X = T.X(), nE = T.nE(), n = 2 * X;
    ZM d = tree2::boundary(T);
    ZM B = tree2::cycle_basis(T);
    auto we = V64(T.w_e());
    o.add("phi_comb_BG", phi_obj(tree2::phi_comb(B, we, nE)).str());
    o.add("phi_comb_BG_unweighted", phi_obj(tree2::phi_comb(B, std::vector<i64>(nE, 1), nE)).str());
    auto phic = tree2::phi_two_vertex(we);
    o.add("phi_comb_collapsed", phi_obj(phic).str()).add("phi_collapsed_order", phic.order.to_string());
    {
        auto w2 = we;
        std::sort(w2.begin(), w2.end(), std::greater<i64>());
        o.add("collapse_two_vertex_weights_sorted", jl(w2));
    }
    // lem:s03-bip
    {
        Obj b;
        bool deg0 = true;
        for (auto& r : B) {
            Z s = 0;
            for (auto& x : r) s += x;
            deg0 &= s.is_zero();
        }
        b.add("a_ker_in_deg0", jb(deg0));
        ZM img(n, std::vector<Z>(nE - 1, Z(0)));
        bool parts = true;
        for (int i = 0; i < nE - 1; ++i) {
            Z a = 0, c = 0;
            for (int v = 0; v < n; ++v) {
                img[v][i] = d[v][i] - d[v][nE - 1];
                (v < X ? a : c) += img[v][i];
            }
            parts &= a.is_zero() && c.is_zero();
        }
        auto di = zlin::smith(img);
        bool all1 = true;
        for (auto& x : di) all1 &= (x == Z(1));
        b.add("a_surjective", jb((int)di.size() == n - 2 && all1 && parts));
        b.add("a_rank", jb((int)B.size() == nE - n + 1));
        ZM dT = zlin::transpose(d, nE);
        ZM K = zlin::kernel_basis(dT, n);
        bool kz = K.size() == 1;
        if (kz) {
            bool p1 = true, m1 = true;
            for (auto& x : K[0]) {
                p1 &= (x == Z(1));
                m1 &= (x == Z(-1));
            }
            kz = p1 || m1;
        }
        b.add("b_ker_Z", jb(kz)).add("b_ker_Q", jb((int)zlin::smith(dT).size() == n - 1));
        auto B2 = zlin::kernel_basis([&] {
            ZM d2(2, std::vector<Z>(nE, Z(0)));
            for (int e = 0; e < nE; ++e) {
                d2[0][e] = -1;
                d2[1][e] = 1;
            }
            return d2;
        }(), nE);
        bool c1 = (int)B2.size() == nE - 1;
        for (auto& r : B2) {
            Z s = 0;
            for (auto& x : r) s += x;
            c1 &= s.is_zero();
        }
        b.add("c_collapse_H1", jb(c1)).add("c_connecting_kernel", jb((int)B.size() == nE - 1 - (n - 2)));
        o.add("lem_bip", b.str());
    }
    // ribet_exact
    {
        auto sd = zlin::smith(d);
        const int rkA = (int)sd.size();
        bool tf = true;
        for (auto& x : sd) tf &= (x == Z(1));
        bool eps = true;
        for (int e = 0; e < nE; ++e) {
            Z s = 0;
            for (int i = 0; i < n; ++i) s += d[i][e];
            eps &= s.is_zero();
        }
        Obj r;
        r.add("ker_alpha_rank", std::to_string(nE - rkA)).add("rk_H1", std::to_string(B.size()));
        r.add("rk_H1_formula", std::to_string(nE - n + 1)).add("alpha_injective_mod_H1", jb(nE - rkA == (int)B.size()));
        r.add("rank_alpha", std::to_string(rkA)).add("coker_alpha_rank", std::to_string(n - rkA));
        r.add("coker_alpha_torsion_free", jb(tf)).add("eps_kills_im_alpha", jb(eps));
        r.add("coker_alpha_iso_Z", jb(n - rkA == 1 && tf)).add("ker_alpha_saturated", jb(true));
        o.add("ribet_exact", r.str());
    }
    // Hecke blocks
    auto H = T.hecke(), Hp = T.hecke_prime();
    std::vector<std::vector<i64>> HT(X, std::vector<i64>(X));
    for (int i = 0; i < X; ++i)
        for (int j = 0; j < X; ++j) HT[i][j] = H[j][i];
    o.add("hecke_block", Obj().add("H", jm(H)).add("Hprime", jm(Hp)).add("H_transpose", jm(HT))
                               .add("Hprime_equals_HT", jb(Hp == HT)).str());
    auto ev = tree2::integer_eigenvalues(H, T.q + 1);
    o.add("T_q_eigenvalues", jl(ev));
    std::vector<i64> cd;
    for (auto l : ev)
        if (l != T.q + 1) cd.push_back((T.q + 1) * (T.q + 1) - l * l);
    o.add("cusp_det_q1sq_minus_lam_sq", jl(cd));
    for (int wt = 1; wt >= 0; --wt) {
        ZM M = tree2::alpha_alphadag(T, wt == 1);
        Obj a;
        coker_extras(T, M, wt == 1, a);
        o.add(wt ? "alpha_alphadag_weighted" : "alpha_alphadag_unweighted", a.str());
        o.add(wt ? "alpha_alphadag_weighted_RibetSign" : "alpha_alphadag_unweighted_RibetSign",
              Obj().add("matrix", jm(to64(tree2::alpha_alphadag(T, wt == 1, -1)))).str());
    }
    {
        ZM M = tree2::alpha_alphadag(T, true);
        bool diag = true, up = true, lo = true, np = true;
        for (int i = 0; i < n; ++i) diag &= (M[i][i] == Z(T.q + 1));
        for (int i = 0; i < X; ++i)
            for (int k = 0; k < X; ++k) {
                up &= (M[i][X + k] == Z(-Hp[i][k]));
                lo &= (M[X + i][k] == Z(-HT[i][k]));
            }
        for (int i = 0; i < n; ++i)
            for (int k = 0; k < n; ++k)
                if ((i < X) != (k < X)) np &= (M[i][k] <= Z(0));
        o.add("sign_check", Obj().add("diag_blocks_are_q_plus_1", jb(diag)).add("offdiag_upper_is_minus_Hprime", jb(up))
                                .add("offdiag_lower_is_minus_HT", jb(lo)).add("offdiag_entries_nonpositive", jb(np)).str());
    }
    return o.str();
}

// ---------------------------------------------------------------- s02/H_Vk at k = 2 (twoterm.py)
std::string hvk2_case(i64 D, i64 q, i64 N1, i64 N0, i64 p, int m) {
    TreeQuotient T = build_tree(classes(D), q, TreeLevel{N1, N0});
    Obj o = graph_block(T, false);
    o.add("p", std::to_string(p)).add("m", std::to_string(m));
    const int X = T.X(), nE = T.nE();
    ZM d = tree2::boundary(T);
    auto ed = tree2::elem_div_vals(d, p, m);
    const int s = (int)ed.size(), r0 = 2 * X, r1 = nE;
    std::vector<int> tors;
    for (int v : ed)
        if (v > 0) tors.push_back(v);
    auto rep = [&](int k, const std::vector<int>& t) {
        std::vector<int> r(k, m);
        r.insert(r.end(), t.begin(), t.end());
        return r;
    };
    // coboundary delta(f0, f1) = s_1^* f1 - s_0^* f0 = -iota
    ZM I = tree2::ihara(T);
    auto edc = tree2::elem_div_vals(I, p, m);
    const int sc = (int)edc.size(), c0 = 2 * X, c1 = nE;
    std::vector<int> torc;
    for (int v : edc)
        if (v > 0) torc.push_back(v);
    const int rkd = (int)zlin::smith(d).size();
    Obj k2;
    k2.add("rank_C1", std::to_string(r1)).add("rank_C0", std::to_string(r0)).add("rank_M_U", std::to_string(r0 / 2));
    k2.add("rank_M_Uprime", std::to_string(r1)).add("elem_div_vals_d", jl(ed));
    k2.add("H1", jl(rep(r1 - s, tors))).add("H0", jl(rep(r0 - s, tors)));
    k2.add("Hco0", jl(rep(c0 - sc, torc))).add("Hco1", jl(rep(c1 - sc, torc)));
    k2.add("rank_d_Qp_lower", std::to_string(s)).add("rank_H1_Zp_upper", std::to_string(r1 - s));
    k2.add("rank_H0_Zp_upper", std::to_string(r0 - s)).add("rank_Hco0_Zp_upper", std::to_string(c0 - sc));
    k2.add("rank_d_Q", std::to_string(rkd)).add("rank_H1", std::to_string(r1 - rkd)).add("rank_H0", std::to_string(r0 - rkd));
    bool exact = true;
    for (int v : ed) exact &= v < m - 1;
    k2.add("H0_p_part_exact", jb(exact)).add("p_le_k_minus_2", jb(p <= 0));
    k2.add("pred_free_rank_H1", std::to_string(nE - 2 * X + T.components()));
    o.add("k2", k2.str());
    return o.str();
}

// ---------------------------------------------------------------- s03/T6 at k = 2 (ihara.py)
std::string t6k2_case(i64 p, int m, bool U1p) {
    const i64 D = 3, q = 2;
    TreeQuotient T = build_tree(classes(D), q, TreeLevel{U1p ? p : 1, 1});
    Obj o = graph_block(T, false);
    o.add("p", std::to_string(p)).add("m", std::to_string(m)).add("level_T6", js(U1p ? "U1p" : "max"));
    const int X = T.X(), nE = T.nE();
    // homological d = (-s_{0*}, s_{1*}); cohomological alpha with the traces [Gamma_x : Gamma_e]
    ZM dh = tree2::boundary(T), dc = dh;
    for (int e = 0; e < nE; ++e) {
        dc[T.s0[e]][e] = Z(-(T.V[T.s0[e]].stab / T.E[e].stab));
        dc[X + T.s1[e]][e] = Z(T.V[T.s1[e]].stab / T.E[e].stab);
    }
    auto h0 = [&](const ZM& A) {
        auto ed = tree2::elem_div_vals(A, p, m);
        std::vector<int> r(2 * X - (int)ed.size(), m);
        for (int v : ed)
            if (v > 0) r.push_back(v);
        return r;
    };
    o.add("H0_homological", jl(h0(dh))).add("H0_cohomological", jl(h0(dc)));
    o.add("rank_P", std::to_string(2 * X)).add("rank_edge_module", std::to_string(nE));
    return o.str();
}

// ---------------------------------------------------------------- s03/T1 (mazur.py)
std::string t1_case(i64 q) {
    const ClassSet& C = classes(q);
    std::vector<i64> gam, w;
    for (auto& c : C.classes()) {
        gam.push_back(c.gamma);
        w.push_back(c.gamma / 2);
    }
    auto ws = w, gs = gam;
    std::sort(ws.begin(), ws.end());
    std::sort(gs.begin(), gs.end());
    std::vector<int> wi(w.begin(), w.end()), gi(gam.begin(), gam.end());
    auto mw = massq(wi), mg = massq(gi);
    auto phi = tree2::phi_two_vertex(w);
    const i64 num = (q - 1) / std::gcd<i64>(q - 1, 12);
    Obj o;
    o.add("q", std::to_string(q)).add("h", std::to_string(C.h())).add("weights", jl(ws)).add("gammas", jl(gs));
    o.add("n2", std::to_string(std::count(w.begin(), w.end(), 2))).add("n3", std::to_string(std::count(w.begin(), w.end(), 3)));
    o.add("mass_w", js(frac_str(mw.first, mw.second))).add("mass_w_ok", jb(eqq(mw, {q - 1, 12})));
    o.add("mass_gamma_ok", jb(eqq(mg, {q - 1, 24})));
    o.add("phi_order", phi.order.to_string()).add("phi_divisors", jl(phi.divisors)).add("phi_cyclic", jb(phi.cyclic));
    o.add("num_q_minus_1_over_12", std::to_string(num)).add("phi_order_ok", jb(phi.order == Z(num)));
    // Eisenstein check: (B - (l+1)) Z^h subset span(W X_basis, 1)
    const int h = C.h();
    Obj eis;
    bool all = true;
    ZM d2(2, std::vector<Z>(h, Z(0)));
    for (int e = 0; e < h; ++e) {
        d2[0][e] = -1;
        d2[1][e] = 1;
    }
    ZM Xb = zlin::kernel_basis(d2, h);
    ZM gens;
    for (auto& b : Xb) {
        std::vector<Z> r(h);
        for (int e = 0; e < h; ++e) r[e] = Z(w[e]) * b[e];
        gens.push_back(r);
    }
    gens.push_back(std::vector<Z>(h, Z(1)));
    ZM Hn = zlin::hermite_rows(gens);
    for (i64 l : {2, 3, 5, 7, 11, 13}) {
        if (l == q) continue;
        bool ok = true;
        if (h > 1) {
            Mat B = brandt_neighbours(C, l);
            for (int j = 0; j < h && ok; ++j) {
                std::vector<Z> col(h);
                for (int i = 0; i < h; ++i) col[i] = Z(B[(size_t)i * h + j] - (i == j ? l + 1 : 0));
                ok = zlin::in_row_span(Hn, col);
            }
        }
        eis.add(std::to_string(l), jb(ok));
        all &= ok;
    }
    o.add("eisenstein", eis.str()).add("eisenstein_all", jb(all));
    // the same through the tree: Phi^comb of the collapsed BG(O^x, l) at l = 2 equals ... (not part of T1; omitted)
    return o.str();
}

// ---------------------------------------------------------------- suites
std::vector<i64> definite_D(i64 Dmax) {
    std::vector<i64> out;
    for (i64 D = 2; D <= Dmax; ++D)
        if (is_squarefree(D) && prime_factors(D).size() % 2 == 1) out.push_back(D);
    return out;
}

std::string run_suite(const std::string& name) {
    std::vector<std::string> cells;
    const std::vector<i64> PR = {2, 3, 5, 7, 11, 13};
    if (name == "s02_validation") {
        for (i64 D : definite_D(53))
            for (i64 q : PR) {
                if (D % q == 0) continue;
                std::vector<TreeLevel> lv{TreeLevel{1, 1}};
                for (i64 p : PR)
                    if ((D * q) % p) {
                        lv.push_back(TreeLevel{1, p});
                        break;
                    }
                if (D <= 23)
                    for (i64 N : {3, 4, 5, 7})
                        if (std::gcd(N, D * q) == 1) {
                            lv.push_back(TreeLevel{N, 1});
                            break;
                        }
                for (auto& L : lv) {
                    TreeQuotient T = build_tree(classes(D), q, L);
                    cells.push_back(graph_block(T, false).str());
                    std::fprintf(stderr, "s02_validation D=%lld q=%lld %s X=%d E=%d (%.2fs)\n", (long long)D, (long long)q,
                                 L.str().c_str(), T.X(), T.nE(), T.seconds);
                }
            }
    } else if (name == "s02_T2") {
        for (auto [D, q] : std::vector<std::pair<i64, i64>>{{2, 7}, {2, 13}, {11, 2}})
            cells.push_back(graph_block(build_tree(classes(D), q), true).str());
    } else if (name == "s02_T3") {
        i64 N = 1;
        for (int s = 1; s <= 3; ++s) {
            N *= 5;
            TreeQuotient T = build_tree(classes(3), 2, TreeLevel{N, 1});
            Obj o = graph_block(T, s <= 2);
            o.add("s", std::to_string(s));
            cells.push_back(o.str());
            std::fprintf(stderr, "s02_T3 s=%d X=%d E=%d (%.2fs)\n", s, T.X(), T.nE(), T.seconds);
        }
    } else if (name == "s02_HVk2") {
        const std::vector<std::array<i64, 6>> CASES = {
            {3, 2, 5, 1, 7, 4}, {3, 2, 7, 1, 5, 4}, {2, 3, 7, 1, 5, 4}, {3, 2, 13, 1, 5, 3}, {2, 3, 1, 1, 5, 4},
            {2, 5, 1, 1, 7, 4}, {2, 7, 1, 1, 5, 4}, {3, 2, 1, 1, 5, 4}, {3, 5, 1, 1, 7, 4}, {3, 7, 1, 1, 5, 4},
            {5, 2, 1, 1, 7, 4}, {7, 2, 1, 1, 5, 4}, {13, 2, 1, 1, 5, 4}, {2, 3, 1, 5, 7, 4}, {3, 2, 1, 7, 5, 4}};
        for (auto& c : CASES) cells.push_back(hvk2_case(c[0], c[1], c[2], c[3], c[4], (int)c[5]));
    } else if (name == "s03_T1") {
        for (i64 q : {11, 23, 37, 101, 131}) cells.push_back(t1_case(q));
    } else if (name == "s03_T2") {
        for (auto [D, q] : std::vector<std::pair<i64, i64>>{{2, 7}, {2, 13}, {11, 2}}) cells.push_back(t2_case(D, q));
    } else if (name == "s03_T6k2") {
        cells.push_back(t6k2_case(5, 2, false));
        cells.push_back(t6k2_case(5, 1, true));
        cells.push_back(t6k2_case(7, 2, false));
        cells.push_back(t6k2_case(7, 1, true));
    } else {
        throw std::invalid_argument("unknown suite " + name);
    }
    std::string o = "[";
    for (size_t i = 0; i < cells.size(); ++i) o += (i ? ",\n" : "\n") + cells[i];
    return o + "\n]";
}

}  // namespace

int main(int argc, char** argv) {
    std::vector<std::string> suites;
    std::string out;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--suite" && i + 1 < argc)
            suites.push_back(argv[++i]);
        else if (a == "--out" && i + 1 < argc)
            out = argv[++i];
        else {
            std::cerr << "usage: jl_tree_dump [--suite NAME]... [--out FILE]\n";
            return 2;
        }
    }
    if (suites.empty())
        suites = {"s02_T2", "s03_T2", "s03_T1", "s02_HVk2", "s03_T6k2", "s02_T3", "s02_validation"};
    std::string body = "{\"schema\":\"langlandscape_tree/v1\",\"suites\":{";
    Obj timing;
    for (size_t i = 0; i < suites.size(); ++i) {
        auto t0 = std::chrono::steady_clock::now();
        std::string r = run_suite(suites[i]);
        double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        timing.add(suites[i], std::to_string(sec));
        body += (i ? ",\n" : "\n") + js(suites[i]) + ":" + r;
        std::fprintf(stderr, "suite %s done (%.2fs)\n", suites[i].c_str(), sec);
    }
    body += "},\"suite_seconds\":" + timing.str() + "}\n";
    if (out.empty())
        std::cout << body;
    else
        std::ofstream(out) << body;
    return 0;
}
