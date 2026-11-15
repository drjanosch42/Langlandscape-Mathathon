// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// jl_tree_k (WP HJ-7b): weight-k two-term complexes on BG(U, q) natively (TreeK.h), for
//   s02_HVk   twoterm.py CASES x k = 2..10: H_1, H_0, H^0, H^1 over Z/p^m, elementary divisors of d, ranks;
//   s03_T6    ribet/ihara.py cases(): B_3, q = 2, U = O^x, W = Sym^{k-2} (max) or the Shapiro module (U1p), H_0 = coker
//             in the cohomological (traces) and homological conventions, rank_P, rank_edge_module, V_{U^1_p};
//   ihara     NEW: the quaternionic Ihara map iota = (s_0^*, -s_1^*) : M(O; V_k)^2 -> M(O_0(q); V_k) for
//             D in {2,3,5,7,11,13}, q in {2,3,5,7,11,13} \ {D}, even k = 2..14: rank over Q (mod a large prime) and the
//             torsion of coker iota over Z_(l) for every prime 5 <= l <= L, l !| D q (rank drop mod l, then the
//             elementary divisors mod l^m); Task 2's range is l > k, the primes l <= k are reported with l_gt_k = false.
//   jl_tree_k [--suite NAME]... [--L 1000] [--out FILE]
// Every number is computed natively; laneC_hj7k_compare.py compares with the Python references.
#include "../TreeK.h"
#include "../BrandtSym.h"

#include <chrono>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <numeric>

using namespace hacs_jl;

namespace {
std::string js(const std::string& s) { return "\"" + s + "\""; }
std::string jb(bool b) { return b ? "true" : "false"; }
template <class T>
std::string jl(const std::vector<T>& v) {
    std::string o = "[";
    for (size_t i = 0; i < v.size(); ++i) o += (i ? "," : "") + std::to_string(v[i]);
    return o + "]";
}
struct Obj {
    std::string s;
    Obj& add(const std::string& k, const std::string& raw) {
        s += (s.empty() ? "" : ",") + js(k) + ":" + raw;
        return *this;
    }
    Obj& add(const std::string& k, long long v) { return add(k, std::to_string(v)); }
    std::string str() const { return "{" + s + "}"; }
};

std::map<i64, std::unique_ptr<MaxOrder>> g_orders;
std::map<i64, std::unique_ptr<ClassSet>> g_classes;
const ClassSet& classes(i64 D) {
    auto it = g_classes.find(D);
    if (it != g_classes.end()) return *it->second;
    g_orders[D] = std::make_unique<MaxOrder>(D);
    g_classes[D] = std::make_unique<ClassSet>(*g_orders[D]);
    return *g_classes[D];
}

i64 inv_mod_pub(i64 a, i64 l) {
    i64 r = 1, b = ((a % l) + l) % l, e = l - 2;
    while (e) {
        if (e & 1) r = (i64)((i128)r * b % l);
        b = (i64)((i128)b * b % l);
        e >>= 1;
    }
    return r;
}
i64 ipow(i64 p, int m) {
    i64 r = 1;
    while (m--) r *= p;
    return r;
}
int rank_mod(const ModMat& A, i64 l) {
    int r = 0;
    for (int v : elem_divs_mod(A, l, 1)) r += (v == 0);
    return r;
}
std::vector<int> with_free(int k, const std::vector<int>& ed, int m) {
    std::vector<int> o(k, m);
    for (int v : ed)
        if (v > 0) o.push_back(v);
    return o;
}

const i64 kBigEll = 1000003;  // twoterm's global-model prime (here: the local model at ell)

// ---------------------------------------------------------------- s02/H_Vk
std::string hvk_case(i64 D, i64 q, i64 N1, i64 N0, i64 p, int m) {
    const ClassSet& C = classes(D);
    TreeQuotient T = build_tree(C, q, TreeLevel{N1, N0});
    PadicFrames F = make_frames(C, p, m);
    LocalTwist L = local_twist(C, T, F);
    PadicFrames Fb = make_frames(C, kBigEll, 1);
    LocalTwist Lb = local_twist(C, T, Fb);
    Obj o;
    o.add("D", D).add("q", q).add("N1", N1).add("N0", N0).add("p", p).add("m", m).add("X", T.X()).add("E", T.nE());
    o.add("components", T.components()).add("conj_ok", jb(L.conj_ok && Lb.conj_ok));
    bool free = true;
    for (auto& c : T.V) free &= c.stab == 1;
    for (auto& c : T.E) free &= c.stab == 1;
    o.add("free", jb(free));
    Obj ks;
    for (int k = 2; k <= 10; ++k) {
        SymCoeff W(k - 2, F.mod);
        TwoTerm R = two_term(T, L, W, p);
        auto ed = elem_divs_mod(R.d_hom, p, m);
        auto edc = elem_divs_mod(R.delta, p, m);
        const int s = (int)ed.size(), sc = (int)edc.size();
        SymCoeff Wb(k - 2, kBigEll);
        TwoTerm Rb = two_term(T, Lb, Wb, kBigEll);
        if (Rb.r0 != R.r0 || Rb.r1 != R.r1) throw std::logic_error("module ranks differ between p and ell");
        const int rgl = rank_mod(Rb.d_hom, kBigEll);
        const int lower = std::max(s, rgl);
        const int upper = std::min(R.r1, R.r0 - ((k == 2 && R.r0) ? T.components() : 0));
        Obj r;
        r.add("rank_C1", R.r1).add("rank_C0", R.r0).add("rank_M_U", R.r0 / 2).add("rank_M_Uprime", R.r1);
        r.add("elem_div_vals_d", jl(ed));
        r.add("H1", jl(with_free(R.r1 - s, ed, m))).add("H0", jl(with_free(R.r0 - s, ed, m)));
        r.add("Hco0", jl(with_free(R.r0 - sc, edc, m))).add("Hco1", jl(with_free(R.r1 - sc, edc, m)));
        r.add("rank_d_Qp_lower", s).add("rank_H1_Zp_upper", R.r1 - s).add("rank_H0_Zp_upper", R.r0 - s);
        r.add("rank_Hco0_Zp_upper", R.r0 - sc).add("rank_d_mod_ell", rgl).add("ell", kBigEll);
        if (lower == upper) {
            r.add("rank_d_pinned", lower).add("rank_H1", R.r1 - lower).add("rank_H0", R.r0 - lower);
        } else
            r.add("rank_d_pinned", "null");
        bool ex = true;
        for (int v : ed) ex &= v < m - 1;
        r.add("H0_p_part_exact", jb(ex)).add("p_le_k_minus_2", jb(p <= k - 2));
        if (k > 2) {
            r.add("pred_coh_d_rank_H1", R.r1 - R.r0);
            r.add("pred_free_rank_H1", free ? std::to_string((q - 1) * (k - 1) * T.X()) : std::string("null"));
        } else
            r.add("pred_free_rank_H1", T.nE() - 2 * T.X() + T.components());
        ks.add(std::to_string(k), r.str());
    }
    o.add("k", ks.str());
    return o.str();
}

// ---------------------------------------------------------------- s03/T6
std::string t6_case(int k, i64 p, int m, bool U1p) {
    const ClassSet& C = classes(3);
    TreeQuotient T = build_tree(C, 2);
    PadicFrames F = make_frames(C, p, m);
    LocalTwist L = local_twist(C, T, F);
    std::unique_ptr<CoeffModel> W;
    if (U1p)
        W = std::make_unique<ShapiroSymCoeff>(k - 2, p, F.mod);
    else
        W = std::make_unique<SymCoeff>(k - 2, F.mod);
    TwoTerm R = two_term(T, L, *W, p);
    auto h0 = [&](const ModMat& A) { return with_free(R.r0 - (int)elem_divs_mod(A, p, m).size(), elem_divs_mod(A, p, m), m); };
    // V_{U^1_p}: relations (g - 1) e_i for generators of SL_2 (max) or U_1(p) cap SL_2 (U1p), in V = Sym^{k-2}
    SymCoeff V(k - 2, F.mod);
    std::vector<M2> gens;
    if (U1p)
        gens = {M2{1, 1, 0, 1}, M2{1, 0, p % F.mod, 1}, M2{(1 + p) % F.mod, 0, 0, m2inv(M2{(1 + p) % F.mod, 0, 0, 1}, F.mod)[0]}};
    else
        gens = {M2{1, 1, 0, 1}, M2{1, 0, 1, 1}};
    ModMat Rl;
    Rl.c = k - 1;
    for (auto& g : gens) {
        ModMat S = V.act(g);
        for (int i = 0; i < k - 1; ++i) {
            for (int t = 0; t < k - 1; ++t) Rl.a.push_back(((S.at(t, i) - (t == i)) % F.mod + F.mod) % F.mod);
            ++Rl.r;
        }
    }
    Obj o;
    o.add("k", k).add("p", p).add("m", m).add("level", js(U1p ? "U1p" : "max")).add("D", 3).add("q", 2);
    o.add("coeff", js(W->name())).add("conj_ok", jb(L.conj_ok));
    o.add("rank_P", R.r0).add("rank_edge_module", R.r1);
    o.add("H0_cohomological", jl(h0(R.d_coh))).add("H0_homological", jl(h0(R.d_hom)));
    o.add("V_U1_coinvariants", jl(module_structure(Rl, k - 1, p, m)));
    return o.str();
}

// ---------------------------------------------------------------- NEW: Ihara cokernel torsion
std::string ihara_case(i64 D, i64 q, int k, i64 Lmax) {
    const ClassSet& C = classes(D);
    TreeQuotient T = build_tree(C, q);
    PadicFrames Fb = make_frames(C, kBigEll, 1);
    LocalTwist Lb = local_twist(C, T, Fb);
    SymCoeff Wb(k - 2, kBigEll);
    TwoTerm Rb = two_term(T, Lb, Wb, kBigEll);
    const int rq = rank_mod(Rb.delta, kBigEll);
    Obj o;
    o.add("D", D).add("q", q).add("k", k).add("h", C.h()).add("X", T.X()).add("E", T.nE());
    o.add("rank_M_O", Rb.r0 / 2).add("rank_M_O0q", Rb.r1).add("rank_iota_Q", rq);
    o.add("coker_iota_free_rank", Rb.r1 - rq).add("ker_iota_rank", Rb.r0 - rq);
    o.add("scan", Obj().add("l_min", 5).add("l_max", Lmax).add("excluded", js("l | 6 D q")).add("task2_range", js("l > k")).str());
    std::string tors = "[";
    int nscan = 0, nscan_gt = 0, ntors = 0, ntors_gt = 0;
    bool conj = Lb.conj_ok;
    for (i64 l = 5; l <= Lmax; ++l) {
        if (!is_prime(l) || l < 5 || D % l == 0 || q == l) continue;
        ++nscan;
        if (l > k) ++nscan_gt;
        PadicFrames F = make_frames(C, l, 1);
        LocalTwist L = local_twist(C, T, F);
        conj &= L.conj_ok;
        SymCoeff W(k - 2, l);
        TwoTerm R = two_term(T, L, W, l);
        const int r1 = rank_mod(R.delta, l);
        if (r1 == rq) continue;
        // exponents: m with l^m < 10^12
        int m = 1;
        while ((double)ipow(l, m + 1) < 1.0e12) ++m;
        PadicFrames Fm = make_frames(C, l, m);
        LocalTwist Lm = local_twist(C, T, Fm);
        SymCoeff Wm(k - 2, Fm.mod);
        TwoTerm Rm = two_term(T, Lm, Wm, l);
        auto ed = elem_divs_mod(Rm.delta, l, m);
        std::vector<int> tv;
        for (int v : ed)
            if (v > 0) tv.push_back(v);
        const bool full = (int)ed.size() == rq;  // no divisor reached l^m
        tors += std::string(ntors ? "," : "") +
                Obj().add("l", l).add("l_gt_k", jb(l > k)).add("exponents", jl(tv)).add("m", m).add("all_divisors_below_l^m", jb(full)).str();
        ++ntors;
        if (l > k) ++ntors_gt;
    }
    tors += "]";
    o.add("primes_scanned", nscan).add("primes_scanned_gt_k", nscan_gt).add("torsion_primes_gt_k", ntors_gt).add("torsion", tors).add("conj_ok", jb(conj));
    return o.str();
}


// ---------------------------------------------------------------- charpoly mod l (Faddeev-LeVerrier, l > dim)
std::vector<i64> charpoly_mod(const ModMat& A, i64 l) {
    const int n = A.r;
    std::vector<i64> c(n + 1, 0);
    c[n] = 1;
    ModMat M;
    M.r = M.c = n;
    M.a.assign((size_t)n * n, 0);
    auto mul = [&](const ModMat& X, const ModMat& Y) {
        ModMat Z;
        Z.r = Z.c = n;
        Z.a.assign((size_t)n * n, 0);
        for (int i = 0; i < n; ++i)
            for (int k = 0; k < n; ++k) {
                i64 x = X.at(i, k);
                if (!x) continue;
                for (int j = 0; j < n; ++j) Z.at(i, j) = (i64)((Z.at(i, j) + (i128)x * Y.at(k, j)) % l);
            }
        return Z;
    };
    for (int k = 1; k <= n; ++k) {
        M = mul(A, M);
        for (int i = 0; i < n; ++i) M.at(i, i) = (M.at(i, i) + c[n - k + 1]) % l;
        ModMat AM = mul(A, M);
        i128 tr = 0;
        for (int i = 0; i < n; ++i) tr += AM.at(i, i);
        i64 t = (i64)(tr % l);
        // c[n-k] = -tr / k
        i64 kinv = 1;
        {
            i64 b = k % l, e = l - 2;
            while (e) {
                if (e & 1) kinv = (i64)((i128)kinv * b % l);
                b = (i64)((i128)b * b % l);
                e >>= 1;
            }
        }
        c[n - k] = (i64)((l - (i128)t * kinv % l) % l);
    }
    return c;  // low -> high
}

// my T_q on M(O; V) (cohomological): T = s_{0*}^{coh} s_1^*, from the two-term matrices
ModMat tq_local(const TwoTerm& R, i64 mod) {
    const int half = R.r0 / 2;
    ModMat T;
    T.r = T.c = half;
    T.a.assign((size_t)half * half, 0);
    for (int i = 0; i < half; ++i)
        for (int j = 0; j < half; ++j) {
            i128 s = 0;
            for (int e = 0; e < R.r1; ++e) s += (i128)(mod - R.d_coh.at(i, e)) % mod * R.delta.at(e, half + j) % mod;
            T.at(i, j) = (i64)(s % mod);
        }
    return T;
}

std::string brandtsym_case(i64 D, i64 q, int k) {
    const ClassSet& C = classes(D);
    TreeQuotient T = build_tree(C, q);
    PadicFrames F = make_frames(C, kBigEll, 1);
    LocalTwist L = local_twist(C, T, F);
    SymCoeff W(k - 2, kBigEll);
    TwoTerm R = two_term(T, L, W, kBigEll);
    BrandtSym M(C, k - 2);
    Obj o;
    o.add("D", D).add("q", q).add("k", k).add("rank_local", R.r0 / 2).add("rank_brandtsym", M.rank());
    if (M.rank() == R.r0 / 2 && M.rank() > 0) {
        ModMat Tl = tq_local(R, kBigEll);
        auto cl = charpoly_mod(Tl, kBigEll);
        auto cz = symz::charpoly(M.T(q));
        std::vector<i64> cb;
        for (auto& z : cz) cb.push_back((i64)z.floor_mod(Z(kBigEll)).to_int64());
        // compare charpoly(q^j T_local) for j = -n, 0, n with charpoly(T_brandtsym) mod ell
        std::string match = "none";
        for (int j : {0, k - 2, -(k - 2)}) {
            i64 s = 1;
            i64 qq = j >= 0 ? q : inv_mod_pub(q, kBigEll);
            for (int t = 0; t < std::abs(j); ++t) s = (i64)((i128)s * qq % kBigEll);
            ModMat Ts = Tl;
            for (auto& x : Ts.a) x = (i64)((i128)x * s % kBigEll);
            if (charpoly_mod(Ts, kBigEll) == cb) {
                match = "q^" + std::to_string(j) + " * T_tree";
                break;
            }
        }
        o.add("charpoly_Tq_match", js(match));
        o.add("charpoly_Tq_tree_eq_brandtsym", jb(cl == cb));
    }
    return o.str();
}

std::string wd_case(i64 D, int k) {
    const ClassSet& C = classes(D);
    BrandtSym M(C, k - 2);
    Obj o;
    o.add("D", D).add("k", k).add("rank", M.rank());
    const int r = M.rank();
    if (r == 0) return o.str();
    ZMat P = M.Pi(D);
    Z s = Z::pow(Z(D), (uint64_t)((k - 2) / 2));
    ZMat Wn(r, std::vector<Z>(r));
    bool integral = true;
    for (int i = 0; i < r; ++i)
        for (int j = 0; j < r; ++j) {
            Z qq, rr;
            Z::divmod(P[i][j], s, qq, rr);
            integral &= rr.is_zero();
            Wn[i][j] = qq;
        }
    o.add("Pi_D_over_D^m_integral", jb(integral));
    ZMat W2 = symz::mul(Wn, Wn);
    o.add("W_squared_is_identity", jb(symz::is_scalar(W2, Z(1))));
    Z tr = 0;
    for (int i = 0; i < r; ++i) tr += Wn[i][i];
    o.add("trace", tr.to_string());
    const i64 trv = tr.to_int64();
    o.add("mult_plus1", (r + trv) / 2).add("mult_minus1", (r - trv) / 2);
    i64 l0 = 2;
    while (D % l0 == 0) ++l0;
    ZMat Tl = M.T(l0);
    o.add("commutes_with_T_" + std::to_string(l0), jb(symz::equal(symz::mul(Wn, Tl), symz::mul(Tl, Wn))));
    o.add("selfadjoint_w", jb(M.self_adjoint(Wn)));
    o.add("gammas", jl(M.gammas())).add("dims", jl(M.dims()));
    std::string mat = "[";
    for (int i = 0; i < r; ++i) {
        mat += (i ? ",[" : "[");
        for (int j = 0; j < r; ++j) mat += (j ? "," : "") + Wn[i][j].to_string();
        mat += "]";
    }
    o.add("W_D", mat + "]").add("convention", js("W_D = Pi_D / D^((k-2)/2), Pi_D of BrandtSym.h (C4), basis (C5)/(C6), column convention"));
    return o.str();
}


// ---------------------------------------------------------------- exact integral Ihara cokernel (HJ-7b, part 2)
// Lattice (stated): BrandtSym's intrinsic Lambda_c (HJ-4a (C5); = Sym^n(Z_l^2) at l !| D) on every cell; vertex module
// Lambda_c^{Gamma_c}, edge module Lambda_c^{Gamma_e} (c = class of the edge representative y, Gamma_e = its stabiliser),
// Gross form (C3): (s_0^* f)(e) = rho(gamma_0^{-1}) f(x),  (s_1^* f)(e) = rho(beta^{-1}) f(x'),  beta^{-1} = conj(mu) x_1 / (N_c N_c').
// rho(beta^{-1}) maps Lambda_{c'} onto the lattice of L_{y alpha}, which equals Lambda_c away from q; the s_1^* block is
// multiplied by q^a (a minimal, uniform) to make it integral: iota' = (s_0^*, -q^a s_1^*) = iota o diag(1, q^a), so
// coker iota' = coker iota over Z[1/q]. The q-part of the torsion is therefore not meaningful and is reported apart.
namespace {
std::vector<Q> solve_rows(const ZMat& K, const std::vector<Q>& z, bool& ok) {
    const size_t r = K.size(), d = z.size();
    std::vector<Q> t(r, Q(0));
    std::vector<size_t> piv(r);
    for (size_t i = 0; i < r; ++i) {
        size_t c = 0;
        while (c < d && K[i][c].is_zero()) ++c;
        piv[i] = c;
    }
    for (size_t i = 0; i < r; ++i) {
        Q v = z[piv[i]];
        for (size_t j = 0; j < i; ++j) v -= t[j] * Q(K[j][piv[i]]);
        t[i] = v / Q(K[i][piv[i]]);
    }
    ok = true;
    for (size_t c = 0; c < d; ++c) {
        Q v = 0;
        for (size_t i = 0; i < r; ++i) v += t[i] * Q(K[i][c]);
        if (v != z[c]) ok = false;
    }
    return t;
}
std::vector<Q> matvecq(const QMat& R, const std::vector<Q>& y) {
    std::vector<Q> o(R.size(), Q(0));
    for (size_t i = 0; i < R.size(); ++i)
        for (size_t j = 0; j < y.size(); ++j)
            if (!y[j].is_zero() && !R[i][j].is_zero()) o[i] += R[i][j] * y[j];
    return o;
}
std::string factor_str(Z n) {
    std::string o;
    for (i64 p = 2; p < 100000 && n > Z(1); ++p) {
        int e = 0;
        while ((n % Z(p)).is_zero()) {
            n = n / Z(p);
            ++e;
        }
        if (e) o += (o.empty() ? "" : "*") + std::to_string(p) + (e > 1 ? "^" + std::to_string(e) : "");
    }
    if (n > Z(1)) o += (o.empty() ? "" : "*") + std::string("[") + n.to_string() + "]";
    return o.empty() ? "1" : o;
}
}  // namespace

std::string ihara_exact_case(i64 D, i64 q, int k) {
    auto t0 = std::chrono::steady_clock::now();
    const ClassSet& C = classes(D);
    const MaxOrder& O = C.order();
    TreeQuotient T = build_tree(C, q);
    BrandtSym::Options bo;
    bo.canonical_order = false;
    BrandtSym M(C, k - 2, bo);
    for (int c = 0; c < M.h(); ++c)
        if (M.classes()[c].enum_index != c) throw std::logic_error("BrandtSym class order is not the enumeration order");
    const int X = T.X(), E = T.nE();
    auto qb = [&](const Vec4& x, i128 den) { return qb_from(O.to_std(x, den)); };
    // vertex bases (max level: vertex x = class x)
    std::vector<int> voff(2 * X + 1, 0);
    for (int t = 0; t < 2 * X; ++t) voff[t + 1] = voff[t] + M.classes()[t % X].dim();
    // edge invariant bases
    std::vector<ZMat> Ke(E);
    std::vector<int> eoff(E + 1, 0);
    for (int e = 0; e < E; ++e) {
        const int c = T.E[e].rep.c;
        const int d = k - 1;
        ZMat A(d, std::vector<Z>());
        for (int u : T.E[e].stab_units) {
            QMat R = M.rho_class(c, qb(T.units[c][u], C.classes()[c].N));
            for (int i = 0; i < d; ++i)
                for (int j = 0; j < d; ++j) {
                    Q v = R[j][i] - Q(i == j ? 1 : 0);
                    if (v.den() != Z(1)) throw std::logic_error("rho_class of a unit not integral");
                    A[i].push_back(v.num());
                }
        }
        Ke[e] = A[0].empty() ? symz::identity(d) : symz::left_kernel(A);
        eoff[e + 1] = eoff[e] + (int)Ke[e].size();
    }
    const int r1 = eoff[E], r0 = voff[2 * X];
    // the two blocks with rational entries
    std::vector<std::vector<Q>> S0(r1, std::vector<Q>(r0, Q(0))), S1 = S0;
    bool ok_all = true, den_q_only = true;
    int a = 0;
    for (int e = 0; e < E; ++e) {
        const int c = T.E[e].rep.c;
        const EdgeMove& mv = T.moves[e];
        const i64 N = C.classes()[c].N, N1 = C.classes()[mv.c1].N;
        QMat R0 = M.rho_base(O.conj(T.units[c][mv.unit0]), N);
        QMat R1 = M.rho_base(O.mul(O.conj(mv.mu), T.units[mv.c1][mv.unit1]), (i128)N * N1);
        for (int j = 0; j < 2; ++j) {
            const int v = j ? T.s1[e] : T.s0[e];
            const QMat& Ev = M.classes()[v].E;
            for (size_t b = 0; b < Ev.size(); ++b) {
                auto y = matvecq(j ? R1 : R0, Ev[b]);
                bool ok;
                auto t = solve_rows(Ke[e], M.class_coords(c, y), ok);
                ok_all &= ok;
                for (size_t i = 0; i < t.size(); ++i) {
                    (j ? S1 : S0)[eoff[e] + i][voff[j * X + v] + b] = t[i];
                    Z dd = t[i].den();
                    int vq = 0;
                    while ((dd % Z(q)).is_zero()) {
                        dd = dd / Z(q);
                        ++vq;
                    }
                    if (dd != Z(1)) den_q_only = false;
                    if (!j && t[i].den() != Z(1)) den_q_only = false;
                    a = std::max(a, vq);
                }
            }
        }
    }
    Obj o;
    o.add("D", D).add("q", q).add("k", k).add("rank_M_O", r0 / 2).add("rank_M_O0q", r1);
    o.add("coords_ok", jb(ok_all)).add("denominators_q_only", jb(den_q_only)).add("q_scaling_exponent_a", a);
    if (!ok_all || !den_q_only) return o.str();
    zlin::ZM I(r1, std::vector<Z>(r0, Z(0)));
    const Z qa = Z::pow(Z(q), (uint64_t)a);
    for (int i = 0; i < r1; ++i)
        for (int j = 0; j < r0; ++j) {
            Z v = S0[i][j].num();
            if (!S1[i][j].is_zero()) {
                Q w = S1[i][j] * Q(qa);
                v -= w.num();
            }
            I[i][j] = v;
        }
    auto sd = zlin::smith(I);
    std::vector<std::string> tors, tors_prime_to_q;
    Z ord = 1, ordq = 1;
    for (auto& x : sd)
        if (x != Z(1)) {
            tors.push_back(x.to_string());
            ord *= x;
            Z y = x;
            while ((y % Z(q)).is_zero()) y = y / Z(q);
            if (y != Z(1)) tors_prime_to_q.push_back(y.to_string());
            ordq *= y;
        }
    std::string tl = "[", tq = "[";
    for (size_t i = 0; i < tors.size(); ++i) tl += (i ? "," : "") + js(tors[i]);
    for (size_t i = 0; i < tors_prime_to_q.size(); ++i) tq += (i ? "," : "") + js(tors_prime_to_q[i]);
    o.add("rank_iota_Q", (long long)sd.size()).add("coker_free_rank", r1 - (int)sd.size());
    o.add("torsion_invariants_iota_prime", tl + "]").add("torsion_order", js(ord.to_string()));
    o.add("torsion_invariants_prime_to_q", tq + "]").add("torsion_order_prime_to_q", js(ordq.to_string()));
    o.add("torsion_order_prime_to_q_factored", js(factor_str(ordq)));
    o.add("seconds", std::to_string(std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count()));
    return o.str();
}

std::string run_suite(const std::string& name, i64 Lmax) {
    std::vector<std::string> cells;
    if (name == "s02_HVk") {
        const std::vector<std::array<i64, 6>> CASES = {
            {3, 2, 5, 1, 7, 4}, {3, 2, 7, 1, 5, 4}, {2, 3, 7, 1, 5, 4}, {3, 2, 13, 1, 5, 3}, {2, 3, 1, 1, 5, 4},
            {2, 5, 1, 1, 7, 4}, {2, 7, 1, 1, 5, 4}, {3, 2, 1, 1, 5, 4}, {3, 5, 1, 1, 7, 4}, {3, 7, 1, 1, 5, 4},
            {5, 2, 1, 1, 7, 4}, {7, 2, 1, 1, 5, 4}, {13, 2, 1, 1, 5, 4}, {2, 3, 1, 5, 7, 4}, {3, 2, 1, 7, 5, 4}};
        for (auto& c : CASES) cells.push_back(hvk_case(c[0], c[1], c[2], c[3], c[4], (int)c[5]));
    } else if (name == "s03_T6") {
        // ihara.cases(): max level m = 2, 2 <= k <= 2p; U_1(p) at m = 1, 2 <= k <= KMAX_U1[p]; extra (7, 5, 2, U1p)
        for (i64 p : {5, 7}) {
            for (int k = 2; k <= 2 * p; ++k) cells.push_back(t6_case(k, p, 2, false));
            for (int k = 2; k <= (p == 5 ? 9 : 10); ++k) cells.push_back(t6_case(k, p, 1, true));
        }
        cells.push_back(t6_case(7, 5, 2, true));
    } else if (name == "ihara") {
        for (i64 D : {2, 3, 5, 7, 11, 13})
            for (i64 q : {2, 3, 5, 7, 11, 13}) {
                if (q == D) continue;
                for (int k = 2; k <= 14; k += 2) {
                    auto t0 = std::chrono::steady_clock::now();
                    cells.push_back(ihara_case(D, q, k, Lmax));
                    std::fprintf(stderr, "ihara D=%lld q=%lld k=%d (%.2fs)\n", (long long)D, (long long)q, k,
                                 std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count());
                }
            }
    } else if (name == "brandtsym_xcheck") {
        for (i64 D : {2, 3, 5, 7, 11, 13})
            for (i64 q : {2, 3, 5, 7, 11, 13}) {
                if (q == D) continue;
                for (int k = 2; k <= 14; k += 2) cells.push_back(brandtsym_case(D, q, k));
            }
    } else if (name == "ihara_exact") {
        for (i64 D : {2, 3, 5, 7, 11, 13})
            for (i64 q : {2, 3, 5, 7, 11, 13}) {
                if (q == D) continue;
                for (int k = 2; k <= 14; k += 2) {
                    cells.push_back(ihara_exact_case(D, q, k));
                    std::fprintf(stderr, "ihara_exact D=%lld q=%lld k=%d\n", (long long)D, (long long)q, k);
                }
            }
    } else if (name == "W_D") {
        for (i64 D : {2, 3, 5, 7, 11, 13})
            for (int k = 2; k <= 14; k += 2) cells.push_back(wd_case(D, k));
    } else
        throw std::invalid_argument("unknown suite " + name);
    std::string o = "[";
    for (size_t i = 0; i < cells.size(); ++i) o += (i ? ",\n" : "\n") + cells[i];
    return o + "\n]";
}
}  // namespace

int main(int argc, char** argv) {
    std::vector<std::string> suites;
    std::string out;
    i64 Lmax = 2000;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--suite" && i + 1 < argc)
            suites.push_back(argv[++i]);
        else if (a == "--out" && i + 1 < argc)
            out = argv[++i];
        else if (a == "--L" && i + 1 < argc)
            Lmax = std::stoll(argv[++i]);
        else {
            std::cerr << "usage: jl_tree_k [--suite NAME]... [--L N] [--out FILE]\n";
            return 2;
        }
    }
    if (suites.empty()) suites = {"s02_HVk", "s03_T6", "brandtsym_xcheck", "W_D", "ihara_exact", "ihara"};
    std::string body = "{\"schema\":\"langlandscape_tree_k/v1\",\"L\":" + std::to_string(Lmax) + ",\"suites\":{";
    Obj timing;
    for (size_t i = 0; i < suites.size(); ++i) {
        auto t0 = std::chrono::steady_clock::now();
        std::string r = run_suite(suites[i], Lmax);
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
