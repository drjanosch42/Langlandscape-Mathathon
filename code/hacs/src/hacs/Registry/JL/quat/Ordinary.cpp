// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-9): U_p at the level prime, the ordinary projector, ranks over Z/p^m[Delta]. See Ordinary.h.
#include "Ordinary.h"

#include <map>
#include <stdexcept>

namespace hacs_jl {

namespace {
i64 mdq(i128 x, i64 m) {
    i128 r = x % m;
    return (i64)(r < 0 ? r + m : r);
}
i64 invq(i64 a, i64 m) {
    i128 r0 = mdq(a, m), r1 = m, s0 = 1, s1 = 0;
    while (r1) {
        i128 qq = r0 / r1, t = r0 - qq * r1;
        r0 = r1;
        r1 = t;
        t = s0 - qq * s1;
        s0 = s1;
        s1 = t;
    }
    if (r0 != 1) throw std::logic_error("hacs_jl::ordinary: not a unit");
    return mdq(s0, m);
}
}  // namespace

SpOp up_operator(const LevelSet& L, i64 p) {
    const LevelModel& Mo = L.model();
    const ClassSet& C = Mo.class_set();
    const MaxOrder& O = C.order();
    const LevelSpec U = L.spec();
    if (U.N1 % p) throw std::invalid_argument("up_operator: p must divide N1");
    struct Tr {
        int c2;
        Mat2 A1, A0;
    };
    std::map<std::pair<int, int>, Tr> cache;
    auto transport = [&](int c, i64 al, i64 be, int lam) -> const Tr& {
        auto key = std::make_pair(c, lam);
        auto it = cache.find(key);
        if (it != cache.end()) return it->second;
        const ClassRep& r = C.classes()[c];
        Vec4 w = Mo.element(c, Mo.lift(c, al, be, p));
        std::vector<Vec4> gens;
        for (int s = 0; s < 4; ++s) {
            Vec4 u{{0, 0, 0, 0}};
            u[s] = 1;
            gens.push_back(O.mul(u, w));
            Vec4 h = r.I.h[s];
            for (auto& x : h) x = mul_chk(x, p);
            gens.push_back(h);
        }
        const i64 NJ = p * r.N;
        Lat J = hnf(gens, 1, (i128)NJ * NJ);
        int c2 = C.identify(J, NJ, true);
        if (c2 < 0) throw std::logic_error("up_operator: p-neighbour in no class");
        Vec4 mu = find_mu(C, C.classes()[c2].I, C.classes()[c2].N, J, NJ);
        Tr t;
        t.c2 = c2;
        t.A1 = Mo.move(c, c2, O.conj(mu), r.N, U.N1);
        t.A0 = U.N0 > 1 ? Mo.move(c, c2, O.conj(mu), r.N, U.N0) : Mat2{{0, 0, 0, 0}};
        return cache.emplace(key, t).first->second;
    };
    SpOp R;
    R.n = L.size();
    R.cols.resize(R.n);
    for (int j = 0; j < R.n; ++j) {
        const LevelCell& cell = L.cells()[j];
        if (cell.stab != 1) throw std::logic_error("up_operator: non-trivial stabiliser");
        const LevelPoint& x = cell.rep;
        const i64 a = mdq(x.v0, p), b = mdq(x.v1, p);
        for (int lam = 0; lam <= (int)p; ++lam) {
            const i64 al = lam < p ? 1 : 0, be = lam < p ? lam : 1;
            if (mdq((i128)a * be - (i128)b * al, p) == 0) continue;  // lam = <v mod p> excluded
            const Tr& t = transport(x.c, al, be, lam);
            LevelPoint y = x;
            y.c = t.c2;
            y = L.act(y, t.A1, t.A0);
            int i = L.locate(y);
            if (i < 0) throw std::logic_error("up_operator: image point not found");
            bool found = false;
            for (auto& pr : R.cols[j])
                if (pr.first == i) {
                    pr.second += 1;
                    found = true;
                }
            if (!found) R.cols[j].push_back({i, 1});
        }
    }
    return R;
}

std::vector<int> diamond_perm(const LevelSet& L, i64 p, int s, i64 M, i64 d) {
    i64 ps = 1;
    for (int t = 0; t < s; ++t) ps *= p;
    const i64 N = L.spec().N1;
    if (N != M * ps) throw std::invalid_argument("diamond_perm: N1 != M p^s");
    const i64 di = invq(d, ps);
    i64 u = di;
    if (M > 1) {  // CRT: u = di mod p^s, 1 mod M
        for (i64 t = di; t < N; t += ps)
            if (t % M == 1 % M) {
                u = t;
                break;
            }
    }
    std::vector<int> out;
    for (const auto& c : L.cells()) {
        LevelPoint r = c.rep;
        r.v0 = mdq((i128)u * r.v0, N);
        r.v1 = mdq((i128)u * r.v1, N);
        int t = L.locate(r);
        if (t < 0) throw std::logic_error("diamond_perm: image not found");
        out.push_back(t);
    }
    return out;
}

namespace {
i64 crt2(i64 a, i64 m1, i64 b, i64 m2) {  // x = a mod m1, b mod m2 (coprime)
    for (i64 k = 0; k < m2; ++k) {
        i64 x = a + m1 * k;
        if (mdq(x, m2) == mdq(b, m2)) return x;
    }
    throw std::logic_error("crt2: no solution");
}
}  // namespace

SpOp up_prime_operator(const LevelSet& L, i64 p, int s, i64 M) {
    const LevelModel& Mo = L.model();
    const ClassSet& C = Mo.class_set();
    const MaxOrder& O = C.order();
    i64 ps = 1;
    for (int t = 0; t < s; ++t) ps *= p;
    const i64 ps1 = ps * p, N1 = L.spec().N1;
    if (N1 != M * ps || Mo.modulus() % (M * ps1)) throw std::invalid_argument("up_prime_operator: level / model modulus");
    struct Tr {
        int c2;
        Mat2 AP, AM;
    };
    std::map<std::pair<int, std::pair<i64, i64>>, Tr> cache;
    SpOp R;
    R.n = L.size();
    R.cols.resize(R.n);
    for (int jx = 0; jx < R.n; ++jx) {
        const LevelCell& cell = L.cells()[jx];
        if (cell.stab != 1) throw std::logic_error("up_prime_operator: non-trivial stabiliser");
        const LevelPoint& x = cell.rep;
        const int c = x.c;
        i64 a = mdq(x.v0, p), b = mdq(x.v1, p);
        // normalised line key
        std::pair<i64, i64> lk = a ? std::make_pair((i64)1, mdq((i128)b * invq(a, p), p)) : std::make_pair((i64)0, (i64)1);
        auto key = std::make_pair(c, lk);
        auto it = cache.find(key);
        if (it == cache.end()) {
            const ClassRep& r = C.classes()[c];
            Vec4 w = Mo.element(c, Mo.lift(c, lk.first, lk.second, p));
            std::vector<Vec4> gens;
            for (int t = 0; t < 4; ++t) {
                Vec4 u{{0, 0, 0, 0}};
                u[t] = 1;
                gens.push_back(O.mul(u, w));
                Vec4 h = r.I.h[t];
                for (auto& z : h) z = mul_chk(z, p);
                gens.push_back(h);
            }
            const i64 NJ = p * r.N;
            Lat J = hnf(gens, 1, (i128)NJ * NJ);
            int c2 = C.identify(J, NJ, true);
            if (c2 < 0) throw std::logic_error("up_prime_operator: neighbour in no class");
            Vec4 mu = find_mu(C, C.classes()[c2].I, C.classes()[c2].N, J, NJ);
            Tr t;
            t.c2 = c2;
            t.AP = Mo.move(c, c2, O.conj(mu), r.N, ps1);
            t.AM = M > 1 ? Mo.move(c, c2, O.conj(mu), r.N, M) : Mat2{{0, 0, 0, 0}};
            it = cache.emplace(key, t).first;
        }
        const Tr& t = it->second;
        const i64 r10 = mdq(x.v1, p) ? 1 : 0, r11 = mdq(x.v1, p) ? 0 : 1;  // complement of v mod p
        const i64 vp0 = mdq(x.v0, ps), vp1 = mdq(x.v1, ps);
        const i64 vm0 = M > 1 ? mdq(x.v0, M) : 0, vm1 = M > 1 ? mdq(x.v1, M) : 0;
        i64 wm0 = 0, wm1 = 0;
        if (M > 1) {
            wm0 = mdq((i128)vm0 * t.AM[0] + (i128)vm1 * t.AM[2], M);
            wm1 = mdq((i128)vm0 * t.AM[1] + (i128)vm1 * t.AM[3], M);
        }
        for (i64 j = 0; j < p; ++j) {
            const i64 z0 = mdq((i128)vp0 - (i128)ps * j * r10, ps1), z1 = mdq((i128)vp1 - (i128)ps * j * r11, ps1);
            const i64 y0 = mdq((i128)z0 * t.AP[0] + (i128)z1 * t.AP[2], ps1);
            const i64 y1 = mdq((i128)z0 * t.AP[1] + (i128)z1 * t.AP[3], ps1);
            if (y0 % p || y1 % p) throw std::logic_error("up_prime_operator: datum not divisible by p");
            LevelPoint y = x;
            y.c = t.c2;
            y.v0 = M > 1 ? crt2(y0 / p, ps, wm0, M) : y0 / p;
            y.v1 = M > 1 ? crt2(y1 / p, ps, wm1, M) : y1 / p;
            int i = L.locate(y);
            if (i < 0) throw std::logic_error("up_prime_operator: image not found");
            bool found = false;
            for (auto& pr : R.cols[jx])
                if (pr.first == i) {
                    pr.second += 1;
                    found = true;
                }
            if (!found) R.cols[jx].push_back({i, 1});
        }
    }
    return R;
}

std::vector<int> diamond_M_perm(const LevelSet& L, i64 p, int s, i64 M, i64 d) {
    i64 ps = 1;
    for (int t = 0; t < s; ++t) ps *= p;
    const i64 N = L.spec().N1;
    std::vector<int> out;
    const i64 u = M > 1 ? crt2(1, ps, invq(mdq(d, M), M), M) : 1;
    for (const auto& c : L.cells()) {
        LevelPoint r = c.rep;
        r.v0 = mdq((i128)u * r.v0, N);
        r.v1 = mdq((i128)u * r.v1, N);
        int t = L.locate(r);
        if (t < 0) throw std::logic_error("diamond_M_perm: image not found");
        out.push_back(t);
    }
    return out;
}

// ---------------------------------------------------------------- dense mod q
DM dense(const SpOp& U, i64 q) {
    DM A;
    A.r = A.c = U.n;
    A.a.assign((size_t)U.n * U.n, 0);
    for (int j = 0; j < U.n; ++j)
        for (auto& [i, v] : U.cols[j]) A.at(i, j) = mdq((i128)A.at(i, j) + v, q);
    return A;
}
DM transpose(const DM& A) {
    DM T;
    T.r = A.c;
    T.c = A.r;
    T.a.assign(A.a.size(), 0);
    for (int i = 0; i < A.r; ++i)
        for (int j = 0; j < A.c; ++j) T.at(j, i) = A.at(i, j);
    return T;
}
DM mul(const DM& A, const DM& B, i64 q) {
    DM C;
    C.r = A.r;
    C.c = B.c;
    C.a.assign((size_t)C.r * C.c, 0);
    for (int i = 0; i < A.r; ++i) {
        i64* ci = &C.a[(size_t)i * C.c];
        for (int k = 0; k < A.c; ++k) {
            const i64 x = A.at(i, k);
            if (!x) continue;
            const i64* bk = &B.a[(size_t)k * B.c];
            for (int j = 0; j < B.c; ++j) ci[j] += x * bk[j];
        }
        for (int j = 0; j < C.c; ++j) ci[j] = mdq(ci[j], q);
    }
    return C;
}
DM sp_mul(const SpOp& U, const DM& A, i64 q) {
    DM C;
    C.r = U.n;
    C.c = A.c;
    C.a.assign((size_t)C.r * C.c, 0);
    for (int i = 0; i < U.n; ++i) {
        const i64* ai = &A.a[(size_t)i * A.c];
        for (auto& [t, v] : U.cols[i]) {
            i64* ct = &C.a[(size_t)t * C.c];
            for (int j = 0; j < A.c; ++j) ct[j] += v * ai[j];
        }
    }
    for (auto& x : C.a) x = mdq(x, q);
    return C;
}

namespace {
// full-pivoting elimination mod p: pivot rows I and columns J
void pivots(const DM& A, i64 p, std::vector<int>& I, std::vector<int>& J) {
    DM W = A;
    for (auto& x : W.a) x = mdq(x, p);
    I.clear();
    J.clear();
    std::vector<char> rowdead(W.r, 0);
    for (int col = 0; col < W.c; ++col) {
        int piv = -1;
        for (int i = 0; i < W.r; ++i)
            if (!rowdead[i] && W.at(i, col)) {
                piv = i;
                break;
            }
        if (piv < 0) continue;
        I.push_back(piv);
        J.push_back(col);
        rowdead[piv] = 1;
        const i64 iv = invq(W.at(piv, col), p);
        for (int i = 0; i < W.r; ++i) {
            if (rowdead[i] || !W.at(i, col)) continue;
            const i64 f = mdq((i128)W.at(i, col) * iv, p);
            i64* wi = &W.a[(size_t)i * W.c];
            const i64* wp = &W.a[(size_t)piv * W.c];
            for (int j = col; j < W.c; ++j) wi[j] = mdq(wi[j] - f * wp[j], p);
        }
    }
}
DM inv_mod(const DM& A, i64 p, i64 q) {
    const int n = A.r;
    DM W;
    W.r = n;
    W.c = 2 * n;
    W.a.assign((size_t)n * 2 * n, 0);
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) W.at(i, j) = mdq(A.at(i, j), q);
        W.at(i, n + i) = 1;
    }
    for (int c = 0; c < n; ++c) {
        int pv = -1;
        for (int r = c; r < n; ++r)
            if (W.at(r, c) % p) {
                pv = r;
                break;
            }
        if (pv < 0) throw std::logic_error("inv_mod: not invertible mod p");
        for (int j = 0; j < 2 * n; ++j) std::swap(W.at(c, j), W.at(pv, j));
        const i64 iv = invq(W.at(c, c), q);
        for (int j = 0; j < 2 * n; ++j) W.at(c, j) = mdq((i128)W.at(c, j) * iv, q);
        for (int r = 0; r < n; ++r) {
            if (r == c || !W.at(r, c)) continue;
            const i64 f = W.at(r, c);
            for (int j = 0; j < 2 * n; ++j) W.at(r, j) = mdq(W.at(r, j) - (i128)f * W.at(c, j), q);
        }
    }
    DM R;
    R.r = R.c = n;
    R.a.assign((size_t)n * n, 0);
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j) R.at(i, j) = W.at(i, n + j);
    return R;
}
// test stability of A (= T^k); fills P on success
bool try_stable(const DM& A, i64 p, i64 q, Projector& P) {
    std::vector<int> I, J;
    pivots(A, p, I, J);
    const int r = (int)J.size(), n = A.r;
    if (r == 0) {
        P.rank = 0;
        P.e.r = P.e.c = n;
        P.e.a.assign((size_t)n * n, 0);
        P.basis.r = n;
        P.basis.c = 0;
        P.coord.r = 0;
        P.coord.c = n;
        return true;
    }
    DM AJ, AIJ, AI;
    AJ.r = n;
    AJ.c = r;
    AJ.a.resize((size_t)n * r);
    for (int i = 0; i < n; ++i)
        for (int t = 0; t < r; ++t) AJ.at(i, t) = A.at(i, J[t]);
    AIJ.r = AIJ.c = r;
    AIJ.a.resize((size_t)r * r);
    AI.r = r;
    AI.c = n;
    AI.a.resize((size_t)r * n);
    for (int s = 0; s < r; ++s) {
        for (int t = 0; t < r; ++t) AIJ.at(s, t) = A.at(I[s], J[t]);
        for (int j = 0; j < n; ++j) AI.at(s, j) = A.at(I[s], j);
    }
    DM Cm = mul(inv_mod(AIJ, p, q), AI, q);
    DM AJC = mul(AJ, Cm, q);
    if (AJC.a != A.a) return false;
    DM R = mul(Cm, AJ, q);
    std::vector<int> I2, J2;
    pivots(R, p, I2, J2);
    if ((int)J2.size() != r) return false;
    P.coord = mul(inv_mod(R, p, q), Cm, q);
    P.basis = AJ;
    P.e = mul(AJ, P.coord, q);
    P.rank = r;
    return true;
}
}  // namespace

int rank_mod_p(const DM& A, i64 p) {
    std::vector<int> I, J;
    pivots(A, p, I, J);
    return (int)J.size();
}

Projector ordinary_projector(const DM& T, i64 p, int m) {
    i64 q = 1;
    for (int i = 0; i < m; ++i) q *= p;
    DM A = T;
    for (auto& x : A.a) x = mdq(x, q);
    Projector P;
    for (int k = 1; k <= (1 << 20); k *= 2) {
        if (try_stable(A, p, q, P)) {
            P.k = k;
            return P;
        }
        A = mul(A, A, q);
    }
    throw std::runtime_error("ordinary_projector: no stabilisation");
}

Projector ordinary_projector(const SpOp& U, i64 p, int m) {
    i64 q = 1;
    for (int i = 0; i < m; ++i) q *= p;
    DM A = dense(U, q);
    Projector P;
    int k = 1;
    for (; k <= 256; k *= 2) {
        if (try_stable(A, p, q, P)) {
            P.k = k;
            return P;
        }
        for (int t = 0; t < k; ++t) A = sp_mul(U, A, q);  // A = U^{2k}
    }
    // fall back to dense squaring
    for (; k <= (1 << 20); k *= 2) {
        if (try_stable(A, p, q, P)) {
            P.k = k;
            return P;
        }
        A = mul(A, A, q);
    }
    throw std::runtime_error("ordinary_projector: no stabilisation");
}

GroupRank group_ring_rank(const Projector& P, const std::vector<int>& D, int order, i64 p) {
    GroupRank g;
    g.rank_Zp = P.rank;
    g.order = order;
    if (P.rank == 0) {
        g.generators = 0;
        g.free = true;
        return g;
    }
    const int n = P.basis.r, r = P.basis.c;
    DM B;
    B.r = n;
    B.c = r;
    B.a.assign((size_t)n * r, 0);
    // (D x)[D[c]] = x[c]
    for (int c = 0; c < n; ++c)
        for (int t = 0; t < r; ++t) B.at(D[c], t) = mdq(B.at(D[c], t) + P.basis.at(c, t), p);
    for (int c = 0; c < n; ++c)
        for (int t = 0; t < r; ++t) B.at(c, t) = mdq(B.at(c, t) - P.basis.at(c, t), p);
    g.generators = r - rank_mod_p(B, p);
    g.free = r == g.generators * order;
    return g;
}

CoinvRank coinvariant_rank(const SpOp& U, const std::vector<int>& D, i64 p, int order) {
    const int n = U.n;
    std::vector<int> orb(n, -1);
    std::vector<int> reps;
    CoinvRank R;
    for (int i = 0; i < n; ++i) {
        if (orb[i] >= 0) continue;
        int o = (int)reps.size(), len = 0;
        reps.push_back(i);
        for (int t = i; orb[t] < 0; t = D[t]) {
            orb[t] = o;
            ++len;
        }
        if (len != order) R.delta_free = false;  // review m3: length = |Delta|
    }
    R.orbits = (int)reps.size();
    SpOp Ub;
    Ub.n = R.orbits;
    Ub.cols.resize(Ub.n);
    for (int o = 0; o < Ub.n; ++o) {
        std::map<int, i64> col;
        for (auto& [t, v] : U.cols[reps[o]]) col[orb[t]] += v;
        for (auto& [t, v] : col) Ub.cols[o].push_back({t, v});
    }
    R.e_bar = ordinary_projector(Ub, p, 1);
    R.generators = R.e_bar.rank;
    R.orbit_of = orb;
    return R;
}

bool commutes_with_perm(const SpOp& U, const std::vector<int>& D) {
    // (U D) e_j = U e_{D j};  (D U) e_j = sum_{(t, v) in U e_j} v e_{D t}
    for (int j = 0; j < U.n; ++j) {
        std::map<int, i64> a, b;
        for (auto& [t, v] : U.cols[D[j]]) a[t] += v;
        for (auto& [t, v] : U.cols[j]) b[D[t]] += v;
        if (a != b) return false;
    }
    return true;
}

}  // namespace hacs_jl
