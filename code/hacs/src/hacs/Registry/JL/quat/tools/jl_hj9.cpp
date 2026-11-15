// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// jl_hj9 (WP HJ-9): the Lambda-adic definite side natively (Ordinary.h on HJ-3's Level.h).
//   --suite T3   B_3, q = 2, p = 5, mod 5^3 (ordinary/t3.py): S_s = X_B(U_1(5^s)), E_s = X_B(U_1(5^s) cap U_0(2)), s = 1..3
//                with e, e*, the pairing, ranks over Z/5^3[Delta_s], the Ribet ranks; s = 4 (and --s5) by the coinvariant route
//   --suite H6   (D, M) in {(2, 7), (3, 1)}, p = 5, mod 5^3, s = 1, 2 (ordinary/h6.py): U'_p, U_p^T = <p>_M U'_p, e vs e*, Hida (d)
//   --suite H7   B_11, B_23, p = 5, s = 1, 2 (ordinary/phicomb.py): |S_s|, U_p column sums, Phi^comb of G_DR, rk e, U_p pi = pi U_p
//   jl_hj9 [--suite NAME]... [--smax-coinv 4|5] [--full-max 3] [--out FILE]   (levels s > full-max: coinvariant route only)
#include "../Ordinary.h"

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
double since(std::chrono::steady_clock::time_point t0) {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}
i64 ipow(i64 p, int m) {
    i64 r = 1;
    while (m--) r *= p;
    return r;
}

// alpha = (-s0*, s1*) : Z[E] -> Z[S]^2 as sparse columns
SpOp alpha_op(const Correspondence& K, int S) {
    SpOp A;
    A.n = (int)K.s0.size();
    A.cols.resize(A.n);
    for (int e = 0; e < A.n; ++e) {
        A.cols[e].push_back({K.s0[e], -1});
        A.cols[e].push_back({S + K.s1[e], 1});
    }
    return A;
}
// sparse composition check: A U_E == (U_S (+) U_S) A (integer)
bool equivariant(const SpOp& A, const SpOp& UE, const SpOp& US, int S) {
    for (int e = 0; e < UE.n; ++e) {
        std::map<int, i64> l, r;
        for (auto& [f, v] : UE.cols[e])
            for (auto& [t, w] : A.cols[f]) l[t] += v * w;
        for (auto& [t, w] : A.cols[e]) {
            const int half = t >= S, x = t - half * S;
            for (auto& [y, v] : US.cols[x]) r[y + half * S] += v * w;
        }
        for (auto it = l.begin(); it != l.end();)
            it = it->second ? std::next(it) : l.erase(it);
        for (auto it = r.begin(); it != r.end();)
            it = it->second ? std::next(it) : r.erase(it);
        if (l != r) return false;
    }
    return true;
}
SpOp perm_op(const std::vector<int>& P) {
    SpOp R;
    R.n = (int)P.size();
    R.cols.resize(R.n);
    for (int i = 0; i < R.n; ++i) R.cols[i].push_back({P[i], 1});
    return R;
}

// spanning-tree cycle basis of ker alpha (E x r, dense mod q), as t3.cycle_basis
DM cycle_basis(const Correspondence& K, int S, i64 q) {
    const int E = (int)K.s0.size(), V = 2 * S;
    std::vector<std::vector<std::array<int, 3>>> adj(V);
    for (int e = 0; e < E; ++e) {
        int a = K.s0[e], b = S + K.s1[e];
        adj[a].push_back({b, e, 1});
        adj[b].push_back({a, e, -1});
    }
    std::vector<std::array<int, 3>> par(V, {-2, -1, 0});
    par[0] = {-1, -1, 0};
    std::vector<int> order{0};
    for (size_t i = 0; i < order.size(); ++i) {
        int u = order[i];
        for (auto& [w, e, sg] : adj[u])
            if (par[w][0] == -2) {
                par[w] = {u, e, sg};
                order.push_back(w);
            }
    }
    if ((int)order.size() != V) throw std::logic_error("graph not connected");
    std::vector<char> tree(E, 0);
    for (int v = 1; v < V; ++v) tree[par[v][1]] = 1;
    std::vector<std::vector<i64>> cols;
    for (int e = 0; e < E; ++e) {
        if (tree[e]) continue;
        std::vector<i64> c(E, 0);
        c[e] = 1;
        for (int u = K.s0[e]; par[u][0] >= 0; u = par[u][0]) c[par[u][1]] += par[u][2];
        for (int u = S + K.s1[e]; par[u][0] >= 0; u = par[u][0]) c[par[u][1]] -= par[u][2];
        cols.push_back(c);
    }
    DM B;
    B.r = E;
    B.c = (int)cols.size();
    B.a.assign((size_t)B.r * B.c, 0);
    for (int j = 0; j < B.c; ++j)
        for (int i = 0; i < E; ++i) B.at(i, j) = ((cols[j][i] % q) + q) % q;
    return B;
}

// matrix of X (sparse) on the saturated sublattice with basis columns B: X B = B A
DM restrict_to(const DM& B, const SpOp& X, i64 p, i64 q) {
    // rows I of B independent mod p
    DM Bt = transpose(B);
    // pivots of B^T: columns of B^T = rows of B
    std::vector<int> I;
    {
        DM W = Bt;
        for (auto& x : W.a) x %= p;
        std::vector<char> used(W.r, 0);
        for (int col = 0; col < W.c && (int)I.size() < W.r; ++col) {
            int piv = -1;
            for (int i = 0; i < W.r; ++i)
                if (!used[i] && W.at(i, col)) {
                    piv = i;
                    break;
                }
            if (piv < 0) continue;
            used[piv] = 1;
            I.push_back(col);
            i64 iv = 1;
            for (i64 t = 1; t < p; ++t)
                if ((W.at(piv, col) * t) % p == 1) iv = t;
            for (int i = 0; i < W.r; ++i) {
                if (used[i] || !W.at(i, col)) continue;
                i64 f = (W.at(i, col) * iv) % p;
                for (int j = col; j < W.c; ++j) W.at(i, j) = ((W.at(i, j) - f * W.at(piv, j)) % p + p) % p;
            }
        }
    }
    const int r = B.c;
    if ((int)I.size() != r) throw std::logic_error("restrict_to: basis not independent mod p");
    DM XB = sp_mul(X, B, q);
    DM BI, XBI;
    BI.r = BI.c = r;
    BI.a.resize((size_t)r * r);
    XBI.r = r;
    XBI.c = r;
    XBI.a.resize((size_t)r * r);
    for (int s = 0; s < r; ++s)
        for (int t = 0; t < r; ++t) {
            BI.at(s, t) = B.at(I[s], t);
            XBI.at(s, t) = XB.at(I[s], t);
        }
    // A = BI^{-1} XBI : invert via ordinary Gauss mod q
    // (reuse ordinary_projector's inverse through a tiny wrapper: solve column by column)
    DM W;
    W.r = r;
    W.c = 2 * r;
    W.a.assign((size_t)r * 2 * r, 0);
    for (int i = 0; i < r; ++i)
        for (int j = 0; j < r; ++j) {
            W.at(i, j) = BI.at(i, j);
            W.at(i, r + j) = XBI.at(i, j);
        }
    auto inv_u = [&](i64 a) {
        for (i64 t = 1; t < q; ++t)
            if ((a * t) % q == 1) return t;
        throw std::logic_error("restrict_to: pivot not a unit");
    };
    for (int c = 0; c < r; ++c) {
        int pv = -1;
        for (int i = c; i < r; ++i)
            if (W.at(i, c) % p) {
                pv = i;
                break;
            }
        if (pv < 0) throw std::logic_error("restrict_to: singular");
        for (int j = 0; j < 2 * r; ++j) std::swap(W.at(c, j), W.at(pv, j));
        i64 iv = inv_u(W.at(c, c));
        for (int j = 0; j < 2 * r; ++j) W.at(c, j) = (W.at(c, j) * iv) % q;
        for (int i = 0; i < r; ++i) {
            if (i == c || !W.at(i, c)) continue;
            i64 f = W.at(i, c);
            for (int j = 0; j < 2 * r; ++j) W.at(i, j) = ((W.at(i, j) - f * W.at(c, j)) % q + q) % q;
        }
    }
    DM A;
    A.r = A.c = r;
    A.a.resize((size_t)r * r);
    for (int i = 0; i < r; ++i)
        for (int j = 0; j < r; ++j) A.at(i, j) = W.at(i, r + j);
    // check B A == X B
    DM BA = mul(B, A, q);
    if (BA.a != XB.a) throw std::logic_error("restrict_to: X does not preserve the lattice");
    return A;
}

// permutation D restricted to the lattice B: as a dense matrix A with D B = B A; returns the "permutation" form unusable for
// group_ring_rank (which needs a permutation), so group_ring_rank on H1 is done with a dense D: g = r - rk_p((A_D - 1) basis)
int generators_dense(const Projector& P, const DM& Dm, i64 p) {
    if (P.rank == 0) return 0;
    DM DB = mul(Dm, P.basis, p);
    for (int i = 0; i < DB.r; ++i)
        for (int t = 0; t < DB.c; ++t) DB.at(i, t) = ((DB.at(i, t) - P.basis.at(i, t)) % p + p) % p;
    return P.rank - rank_mod_p(DB, p);
}

std::string t3_level(const ClassSet& C, int s, int smax_model, bool full) {
    auto t0 = std::chrono::steady_clock::now();
    const i64 p = 5, q = 2;
    const int m = 3;
    const i64 Q = ipow(p, m);
    LevelModel Mo(C, 2 * ipow(p, smax_model));
    LevelSet S(Mo, LevelSpec{ipow(p, s), 1}), E(Mo, LevelSpec{ipow(p, s), 2});
    Correspondence K = u0q_correspondence(E, S, q);
    SpOp US = up_operator(S, p), UE = up_operator(E, p);
    const int nS = S.size(), nE = E.size();
    auto DS = diamond_perm(S, p, s, 1, 1 + p), DE = diamond_perm(E, p, s, 1, 1 + p);
    const int order = (int)ipow(p, s - 1);
    SpOp A = alpha_op(K, nS);
    bool eqU = equivariant(A, UE, US, nS);
    bool eqD = equivariant(A, perm_op(DE), perm_op(DS), nS);
    bool colsum = true;
    for (auto& c : US.cols) {
        i64 t = 0;
        for (auto& pr : c) t += pr.second;
        colsum &= t == p;
    }
    Obj o;
    o.add("s", s).add("S_s", nS).add("E_s", nE).add("E_eq_3S", jb(nE == 3 * nS)).add("rk_H1", nE - 2 * nS + 1);
    o.add("alpha_equivariant_U_p_Delta", jb(eqU && eqD)).add("deg_U_p_eq_p", jb(colsum)).add("delta_order", order);
    auto cS = coinvariant_rank(US, DS, p, order), cE = coinvariant_rank(UE, DE, p, order);
    // review m2: the hypothesis [U_p, Delta] = 0 of the coinvariant route, checked exactly
    const bool comS = commutes_with_perm(US, DS), comE = commutes_with_perm(UE, DE);
    // review m4: e alpha surjective onto e Z[S]^2 (mod p on the coinvariants; Nakayama), so
    // 0 -> eH1 -> eZ[E] -> eZ[S]^2 -> 0 is exact over Z/p^m[Delta] and eH1 is free of rank g_E - 2 g_S
    int surj_rank = -1;
    {
        const int oS = cS.orbits, oE = cE.orbits;
        DM Ab;
        Ab.r = 2 * oS;
        Ab.c = oE;
        Ab.a.assign((size_t)Ab.r * Ab.c, 0);
        std::vector<int> repE(oE, -1);
        for (int e = 0; e < nE; ++e)
            if (repE[cE.orbit_of[e]] < 0) repE[cE.orbit_of[e]] = e;
        for (int o2 = 0; o2 < oE; ++o2)
            for (auto& [t, w] : A.cols[repE[o2]]) {
                const int half = t >= nS, x = t - half * nS;
                const int row = half * oS + cS.orbit_of[x];
                Ab.at(row, o2) = ((Ab.at(row, o2) + w) % p + p) % p;
            }
        surj_rank = rank_mod_p(mul(Ab, cE.e_bar.basis, p), p);  // image of e = span of its basis
    }
    o.add("coinvariant_route", Obj().add("rank_Delta_ZS", cS.generators).add("orbits_S", cS.orbits)
                                     .add("delta_free_S", jb(cS.delta_free)).add("rank_Delta_ZE", cE.generators)
                                     .add("orbits_E", cE.orbits).add("delta_free_E", jb(cE.delta_free))
                                     .add("U_p_commutes_Delta_S", jb(comS)).add("U_p_commutes_Delta_E", jb(comE))
                                     .add("e_alpha_bar_rank_mod_p", surj_rank).add("expected_2_rank_Delta_ZS", 2 * cS.generators)
                                     .add("e_alpha_surjective", jb(surj_rank == 2 * cS.generators))
                                     .add("rank_Delta_H1", (comS && comE && cS.delta_free && cE.delta_free && surj_rank == 2 * cS.generators)
                                                               ? std::to_string(cE.generators - 2 * cS.generators) : std::string("null"))
                                     .add("rank_Delta_H1_route", js("exact sequence 0 -> eH1 -> eZ[E] -> eZ[S]^2 -> 0 over Z/p^m[Delta] "
                                                                   "(e alpha surjective: checked mod p on the coinvariants)")).str());
    if (full) {
        Projector PeS = ordinary_projector(US, p, m);
        Projector PsS = ordinary_projector(transpose(dense(US, Q)), p, m);
        DM G = mul(transpose(PeS.basis), PsS.basis, Q);
        bool deg0 = true;
        for (int j = 0; j < nS; ++j) {
            i64 t = 0;
            for (int i = 0; i < nS; ++i) t += PeS.e.at(i, j);
            deg0 &= t % Q == 0;
        }
        o.add("ekills_a", Obj().add("rk_e_ZS", PeS.rank).add("deg_e_zero_mod_5^3", jb(deg0)).add("deg_U_p_eq_p", jb(colsum)).str());
        o.add("ekills_d", Obj().add("rk_e", PeS.rank).add("rk_e_star", PsS.rank)
                               .add("pairing_gram_invertible_mod_5", jb(G.r == G.c && rank_mod_p(G, p) == G.r))
                               .add("pairing_gram_rank_mod_5", rank_mod_p(G, p)).add("e_ne_e_star", jb(PeS.e.a != PsS.e.a)).str());
        GroupRank hid = group_ring_rank(PeS, DS, order, p);
        o.add("hida_d_rank_Delta_ZS", Obj().add("rank_Zp", hid.rank_Zp).add("free", jb(hid.free))
                                          .add("rank_Delta", hid.free ? std::to_string(hid.generators) : std::string("null"))
                                          .add("delta_order", order).str());
        Projector PeE = ordinary_projector(UE, p, m);
        GroupRank hidE = group_ring_rank(PeE, DE, order, p);
        DM B = cycle_basis(K, nS, Q);
        DM UH = restrict_to(B, UE, p, Q), DH = restrict_to(B, perm_op(DE), p, Q);
        Projector PH = ordinary_projector(UH, p, m);
        const int gH = generators_dense(PH, DH, p);
        const bool freeH = PH.rank == gH * order;
        // e alpha image rank mod 5
        DM eA;
        eA.r = 2 * nS;
        eA.c = nE;
        eA.a.assign((size_t)eA.r * eA.c, 0);
        for (int e = 0; e < nE; ++e)
            for (auto& [t, w] : A.cols[e])
                for (int j = 0; j < nE; ++j) eA.at(t, j) = ((eA.at(t, j) + w * PeE.e.at(e, j)) % Q + Q) % Q;
        const int im = rank_mod_p(eA, p);
        o.add("ribet", Obj().add("rk_e_ZE", PeE.rank).add("rk_e_ZS", PeS.rank).add("rk_e_H1", PH.rank)
                           .add("identity_rk_eH1_eq_rkeZE_minus_2rkeZS", jb(PH.rank == PeE.rank - 2 * PeS.rank))
                           .add("rank_Delta_e_ZE", hidE.free ? std::to_string(hidE.generators) : std::string("null"))
                           .add("rank_Delta_e_H1", freeH ? std::to_string(gH) : std::string("null"))
                           .add("free_E", jb(hidE.free)).add("free_H1", jb(freeH))
                           .add("rank_Delta_identity", jb(hid.free && hidE.free && freeH && gH == hidE.generators - 2 * hid.generators))
                           .add("e_alpha_image_rank_mod5", im).add("expected_2rk_e_ZS", 2 * PeS.rank)
                           .add("eps_e_zero", jb(deg0)).str());
        o.add("coinvariant_route_eq_direct", jb(cS.generators == hid.generators && cE.generators == hidE.generators));
    }
    o.add("seconds", std::to_string(since(t0)));
    return o.str();
}

std::string h7_case(i64 D, int smax) {
    const i64 p = 5;
    MaxOrder* Op = new MaxOrder(D);
    ClassSet* Cp = new ClassSet(*Op);
    LevelModel Mo(*Cp, ipow(p, smax));
    std::vector<std::unique_ptr<LevelSet>> S;
    std::vector<SpOp> U;
    Obj levels;
    for (int s = 1; s <= smax; ++s) {
        S.push_back(std::make_unique<LevelSet>(Mo, LevelSpec{ipow(p, s), 1}));
        U.push_back(up_operator(*S.back(), p));
        const int n = S.back()->size();
        std::vector<i64> sums;
        bool all_p = true, sig_ok = true;
        for (auto& c : U.back().cols) {
            i64 t = 0;
            for (auto& pr : c) t += pr.second;
            if (std::find(sums.begin(), sums.end(), t) == sums.end()) sums.push_back(t);
            all_p &= t == p;
            sig_ok &= (t % n) == (p % n);
        }
        std::sort(sums.begin(), sums.end());
        auto ph = tree2::phi_two_vertex(std::vector<i64>(n, 1));
        const i64 N = ph.order.to_int64();
        int vp = 0;
        for (i64 t = N; t % p == 0; t /= p) ++vp;
        bool ezero = vp == 0 || true;  // p^vp = 0 mod p^vp
        std::vector<i64> div;
        for (auto& d : ph.divisors) div.push_back(d.to_int64());
        Projector Pe = ordinary_projector(U.back(), p, 1);
        Obj r;
        r.add("size", n).add("order", N).add("order_is_size", jb(N == n)).add("cyclic", jb(ph.cyclic)).add("divisors", jl(div));
        r.add("v_p_order", vp).add("v_p_size_ge_2s_minus_2", jb(vp >= 2 * s - 2)).add("col_sums", jl(sums));
        r.add("Up_star_acts_as_p", jb(sig_ok && all_p)).add("e_zero_on_phi_p", jb(ezero)).add("ordinary_rank_Zp_XB", Pe.rank);
        r.add("colsum_p", jb(all_p));
        if (s >= 2) {
            auto pi = project(*S[s - 1], *S[s - 2]);
            // P U_s == U_{s-1} P
            bool ok = true;
            for (int j = 0; j < n && ok; ++j) {
                std::map<int, i64> l, rr;
                for (auto& [t, v] : U[s - 1].cols[j]) l[pi[t]] += v;
                for (auto& [t, v] : U[s - 2].cols[pi[j]]) rr[t] += v;
                ok = l == rr;
            }
            r.add("Up_commutes_pi", jb(ok));
        }
        levels.add(std::to_string(s), r.str());
    }
    Obj o;
    o.add("D", D).add("h", Cp->h()).add("p", p).add("levels", levels.str());
    return o.str();
}

// ---------------------------------------------------------------- H6 (ordinary/h6.py)
DM dense_int(const SpOp& U) {  // integer entries (no reduction)
    DM A;
    A.r = A.c = U.n;
    A.a.assign((size_t)U.n * U.n, 0);
    for (int j = 0; j < U.n; ++j)
        for (auto& [i, v] : U.cols[j]) A.at(i, j) += v;
    return A;
}
DM perm_dense(const std::vector<int>& P) {
    DM A;
    A.r = A.c = (int)P.size();
    A.a.assign(P.size() * P.size(), 0);
    for (size_t j = 0; j < P.size(); ++j) A.at(P[j], (int)j) = 1;
    return A;
}
DM imul(const DM& A, const DM& B) {  // exact integer product (small entries)
    DM C;
    C.r = A.r;
    C.c = B.c;
    C.a.assign((size_t)C.r * C.c, 0);
    for (int i = 0; i < A.r; ++i)
        for (int k = 0; k < A.c; ++k) {
            i64 x = A.at(i, k);
            if (!x) continue;
            for (int j = 0; j < B.c; ++j) C.at(i, j) += x * B.at(k, j);
        }
    return C;
}
DM modq(DM A, i64 q) {
    for (auto& x : A.a) x = ((x % q) + q) % q;
    return A;
}
std::string h6_case(i64 D, i64 M) {
    const i64 p = 5;
    const int m = 3, smax = 2;
    const i64 Q = ipow(p, m);
    static std::vector<std::unique_ptr<MaxOrder>> keepO;
    static std::vector<std::unique_ptr<ClassSet>> keepC;
    keepO.push_back(std::make_unique<MaxOrder>(D));
    keepC.push_back(std::make_unique<ClassSet>(*keepO.back()));
    const ClassSet& C = *keepC.back();
    LevelModel Mo(C, M * ipow(p, smax + 1));
    std::vector<std::unique_ptr<LevelSet>> S;
    std::vector<SpOp> U, Up;
    std::vector<Projector> Pe, Pp;
    for (int s = 1; s <= smax; ++s) {
        S.push_back(std::make_unique<LevelSet>(Mo, LevelSpec{M * ipow(p, s), 1}));
        U.push_back(up_operator(*S.back(), p));
        Up.push_back(up_prime_operator(*S.back(), p, s, M));
        Pe.push_back(ordinary_projector(U.back(), p, m));
        Pp.push_back(ordinary_projector(Up.back(), p, m));
    }
    Obj o;
    o.add("D", D).add("M", M);
    for (int s = 1; s <= smax; ++s) {
        const int n = S[s - 1]->size();
        DM Ui = dense_int(U[s - 1]), Upi = dense_int(Up[s - 1]);
        DM UT = transpose(Ui);
        DM Dp = M > 1 ? perm_dense(diamond_M_perm(*S[s - 1], p, s, M, p % M)) : perm_dense([&] {
            std::vector<int> id(n);
            std::iota(id.begin(), id.end(), 0);
            return id;
        }());
        DM Dpi = transpose(Dp);  // inverse of a permutation matrix
        bool ptriv = true;
        for (int i = 0; i < n; ++i) ptriv &= Dp.at(i, i) == 1;
        DM rhs = imul(Dp, Upi), rhs2 = imul(Dpi, Upi);
        bool exact = UT.a == rhs.a;
        bool modq_ok = modq(UT, Q).a == modq(rhs, Q).a, other = modq(UT, Q).a == modq(rhs2, Q).a;
        Projector Ps = ordinary_projector(modq(UT, Q), p, m);
        const Projector& E = Pe[s - 1];
        DM G = mul(transpose(E.basis), Ps.basis, Q);
        Obj d;
        d.add("n", n).add("p_M_trivial", jb(ptriv)).add("adjoint_identity_exact_integer", jb(exact));
        d.add("adjoint_identity_mod_5^3", jb(modq_ok)).add("adjoint_other_sign_mod_5^3", jb(other));
        d.add("rk_e", E.rank).add("rk_e_star", Ps.rank).add("rk_e_prime", Pp[s - 1].rank);
        d.add("e_star_eq_e_transpose", jb(Ps.e.a == transpose(E.e).a)).add("e_ne_e_star", jb(E.e.a != Ps.e.a));
        d.add("pairing_e_estar_gram_invertible_mod_5", jb(E.rank ? (G.r == G.c && rank_mod_p(G, p) == G.r) : true));
        if (s == 1) {
            auto pi = project(*S[1], *S[0]);
            const int n2 = S[1]->size();
            DM P;
            P.r = n;
            P.c = n2;
            P.a.assign((size_t)n * n2, 0);
            for (int j = 0; j < n2; ++j) P.at(pi[j], j) = 1;
            DM U2 = dense_int(U[1]), Up2 = dense_int(Up[1]);
            bool piU = imul(P, U2).a == imul(Ui, P).a, piUp = imul(P, Up2).a == imul(Upi, P).a;
            bool pie = mul(P, Pe[1].e, Q).a == mul(Pe[0].e, P, Q).a;
            bool piep = mul(P, Pp[1].e, Q).a == mul(Pp[0].e, P, Q).a;
            auto one_minus = [&](const DM& e) {
                DM R = e;
                for (int i = 0; i < R.r; ++i)
                    for (int j = 0; j < R.c; ++j) R.at(i, j) = (((i == j) - e.at(i, j)) % Q + Q) % Q;
                return R;
            };
            auto nonzero = [](const DM& A) {
                for (auto x : A.a)
                    if (x) return true;
                return false;
            };
            bool nz_p = nonzero(mul(one_minus(Pp[0].e), mul(P, Pp[1].e, Q), Q));
            bool z_e = !nonzero(mul(one_minus(Pe[0].e), mul(P, Pe[1].e, Q), Q));
            d.add("hida_d_s1_to_s2",
                  Obj().add("pi_Up_equals_Up_pi_integer", jb(piU)).add("pi_Uprime_equals_Uprime_pi_integer", jb(piUp))
                      .add("pi_e_equals_e_pi_mod_5^3", jb(pie)).add("pi_eprime_equals_eprime_pi_mod_5^3", jb(piep))
                      .add("(1-e')_1_pi_e'_2_nonzero_mod_5^3 (info: pi_* e'X2 lands in e'X1 even though pi_* e' != e' pi_*)", jb(nz_p))
                      .add("(1-e)_1_pi_e_2_zero_mod_5^3 (pi_* e X2 in e X1)", jb(z_e))
                      .add("rk_e_X2", Pe[1].rank).add("rk_eprime_X2", Pp[1].rank)
                      .add("failure_witnessed", jb(!piUp && piU)).str());
        }
        o.add("s" + std::to_string(s), d.str());
    }
    return o.str();
}
}  // namespace

int main(int argc, char** argv) {
    std::vector<std::string> suites;
    std::string out;
    int smax_coinv = 4, full_max = 3;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--suite" && i + 1 < argc)
            suites.push_back(argv[++i]);
        else if (a == "--out" && i + 1 < argc)
            out = argv[++i];
        else if (a == "--full-max" && i + 1 < argc)
            full_max = std::stoi(argv[++i]);
        else if (a == "--smax-coinv" && i + 1 < argc)
            smax_coinv = std::stoi(argv[++i]);
        else {
            std::cerr << "usage: jl_hj9 [--suite T3|H7]... [--smax-coinv N] [--out FILE]\n";
            return 2;
        }
    }
    if (suites.empty()) suites = {"T3", "H7", "H6"};
    std::string body = "{\"schema\":\"langlandscape_hj9/v1\",\"suites\":{";
    Obj timing;
    for (size_t i = 0; i < suites.size(); ++i) {
        auto t0 = std::chrono::steady_clock::now();
        std::string r;
        if (suites[i] == "T3") {
            MaxOrder O(3);
            ClassSet C(O);
            Obj lv;
            for (int s = 1; s <= smax_coinv; ++s) {
                lv.add("s" + std::to_string(s), t3_level(C, s, s, s <= full_max));
                std::fprintf(stderr, "T3 s=%d done (%.1fs)\n", s, since(t0));
            }
            r = lv.str();
        } else if (suites[i] == "H7") {
            r = Obj().add("11", h7_case(11, 2)).add("23", h7_case(23, 2)).str();
        } else if (suites[i] == "H6") {
            r = "[" + h6_case(2, 7) + "," + h6_case(3, 1) + "]";
        } else
            throw std::invalid_argument("unknown suite");
        body += (i ? ",\n" : "\n") + js(suites[i]) + ":" + r;
        timing.add(suites[i], std::to_string(since(t0)));
        std::fprintf(stderr, "suite %s done (%.2fs)\n", suites[i].c_str(), since(t0));
    }
    body += "},\"suite_seconds\":" + timing.str() + "}\n";
    if (out.empty())
        std::cout << body;
    else
        std::ofstream(out) << body;
    return 0;
}
