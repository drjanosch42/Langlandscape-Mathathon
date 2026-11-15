// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-3): level structures. Conventions: Level.h (L1)-(L6).
#include "Level.h"

#include <algorithm>
#include <map>
#include <numeric>
#include <stdexcept>

namespace hacs_jl {

namespace {
std::string ctx(const char* f) { return std::string("hacs_jl::Level: ") + f; }
i64 md(i128 a, i64 m) { return (i64)mod128(a, m); }
i64 inv_mod(i64 a, i64 m) {  // a invertible mod m (extended Euclid)
    if (m == 1) return 0;
    i128 r0 = m, r1 = md(a, m), s0 = 0, s1 = 1;
    while (r1 != 0) {
        i128 q = r0 / r1, t = r0 - q * r1;
        r0 = r1;
        r1 = t;
        t = s0 - q * s1;
        s0 = s1;
        s1 = t;
    }
    if (r0 != 1) throw std::logic_error(ctx("inv_mod: not invertible"));
    return md(s0, m);
}
std::vector<std::pair<i64, i64>> prime_powers(i64 N) {
    std::vector<std::pair<i64, i64>> out;
    for (i64 l : prime_factors(N)) {
        i64 lk = 1;
        while (N % (lk * l) == 0) lk *= l;
        out.push_back({l, lk});
    }
    return out;
}
// x = r_i mod m_i (pairwise coprime)
i64 crt(const std::vector<std::pair<i64, i64>>& rm) {
    i128 x = 0, m = 1;
    for (auto [r, mi] : rm) {
        if (mi == 1) continue;
        i128 t = mod128((i128)(r - (i64)mod128(x, mi)) * inv_mod((i64)mod128(m, mi), mi), mi);
        x += m * t;
        m *= mi;
    }
    return (i64)mod128(x, (i64)m);
}
}  // namespace

std::string LevelSpec::str() const {
    if (N1 == 1 && N0 == 1) return "O^x";
    std::string s;
    if (N1 > 1) s += "U1(" + std::to_string(N1) + ")";
    if (N0 > 1) s += std::string(s.empty() ? "" : "*") + "U0(" + std::to_string(N0) + ")";
    return s;
}

// ===================================================================================================== LevelModel
LevelModel::LevelModel(const ClassSet& C, i64 Nbig) : C_(C), Nbig_(Nbig) {
    const MaxOrder& O = C.order();
    if (Nbig < 1 || std::gcd(Nbig, O.D()) != 1) throw std::invalid_argument(ctx("model modulus must be prime to D"));
    for (int c = 0; c < C.h(); ++c) units_.push_back(class_units(C, c));
    basis_.resize(C.h());
    piv_.resize(C.h());
    if (Nbig == 1) return;
    auto pp = prime_powers(Nbig);
    for (auto [l, lk] : pp) pps_.push_back(PP{l, lk});
    // e by CRT of the prime-power idempotents
    std::vector<Vec4> es;
    for (auto [l, lk] : pp) es.push_back(idempotent_mod(O, lk));
    for (int s = 0; s < 4; ++s) {
        std::vector<std::pair<i64, i64>> rm;
        for (size_t k = 0; k < pp.size(); ++k) rm.push_back({(i64)es[k][s], pp[k].second});
        e_[s] = crt(rm);
    }
    {
        Vec4 e2 = O.mul(e_, e_);
        for (int s = 0; s < 4; ++s)
            if (mod128(e2[s] - e_[s], Nbig) != 0) throw std::logic_error(ctx("CRT idempotent is not idempotent"));
    }
    for (int c = 0; c < C.h(); ++c) {
        const Lat& I = C.classes()[c].I;
        std::vector<std::array<i64, 4>> ys;
        for (int s = 0; s < 4; ++s) {
            Vec4 y = coords_in(I, O.mul(e_, I.h[s]));
            std::array<i64, 4> r;
            for (int t = 0; t < 4; ++t) r[t] = md(y[t], Nbig);
            ys.push_back(r);
        }
        std::vector<std::pair<i64, i64>> b1r[4], b2r[4];
        piv_[c].resize(pp.size());
        for (size_t k = 0; k < pp.size(); ++k) {
            const i64 l = pp[k].first;
            bool found = false;
            for (int a = 0; a < 4 && !found; ++a)
                for (int b = a + 1; b < 4 && !found; ++b)
                    for (int i = 0; i < 4 && !found; ++i)
                        for (int j = i + 1; j < 4 && !found; ++j)
                            if (mod128((i128)ys[a][i] * ys[b][j] - (i128)ys[a][j] * ys[b][i], l)) {
                                for (int t = 0; t < 4; ++t) {
                                    b1r[t].push_back({md(ys[a][t], pp[k].second), pp[k].second});
                                    b2r[t].push_back({md(ys[b][t], pp[k].second), pp[k].second});
                                }
                                piv_[c][k] = {i, j};
                                found = true;
                            }
            if (!found) throw std::logic_error(ctx("e I_c / l I_c is not free of rank 2"));
        }
        for (int t = 0; t < 4; ++t) {
            basis_[c][0][t] = crt(b1r[t]);
            basis_[c][1][t] = crt(b2r[t]);
        }
    }
}

std::array<i64, 4> LevelModel::lift(int c, i64 a, i64 b, i64 N) const {
    std::array<i64, 4> y{{0, 0, 0, 0}};
    if (N == 1) return y;
    for (int t = 0; t < 4; ++t) y[t] = md((i128)a * basis_[c][0][t] + (i128)b * basis_[c][1][t], N);
    return y;
}

std::array<i64, 2> LevelModel::coords(int c, const std::array<i64, 4>& y, i64 N) const {
    if (N == 1) return {0, 0};
    if (Nbig_ % N) throw std::invalid_argument(ctx("coords: N does not divide the model modulus"));
    std::vector<std::pair<i64, i64>> ra, rb;
    for (size_t k = 0; k < pps_.size(); ++k) {
        const i64 l = pps_[k].l;
        i64 m = 1;
        while (N % (m * l) == 0) m *= l;
        if (m == 1) continue;
        auto [i, j] = piv_[c][k];
        const auto& b1 = basis_[c][0];
        const auto& b2 = basis_[c][1];
        // [y_i y_j] = [a b] [[b1_i, b1_j], [b2_i, b2_j]]
        i64 det = md((i128)b1[i] * b2[j] - (i128)b1[j] * b2[i], m);
        i64 di = inv_mod(det, m);
        i64 a = md(((i128)y[i] * b2[j] - (i128)y[j] * b2[i]) % m * di, m);
        i64 b = md(((i128)b1[i] * y[j] - (i128)b1[j] * y[i]) % m * di, m);
        for (int t = 0; t < 4; ++t)
            if (md((i128)a * b1[t] + (i128)b * b2[t] - y[t], m) != 0)
                throw std::logic_error(ctx("coords: vector not in e I_c / N I_c"));
        ra.push_back({a, m});
        rb.push_back({b, m});
    }
    return {crt(ra), crt(rb)};
}

Vec4 LevelModel::element(int c, const std::array<i64, 4>& y) const {
    const Lat& I = C_.classes()[c].I;
    Vec4 v{{0, 0, 0, 0}};
    for (int s = 0; s < 4; ++s)
        if (y[s])
            for (int m = 0; m < 4; ++m) v[m] = add_chk(v[m], mul_chk(y[s], I.h[s][m]));
    return v;
}

Mat2 LevelModel::move(int c, int c2, const Vec4& x, i128 div, i64 N) const {
    Mat2 A{{0, 0, 0, 0}};
    if (N == 1) return A;
    const MaxOrder& O = C_.order();
    for (int r = 0; r < 2; ++r) {
        Vec4 z = O.mul(element(c, lift(c, r == 0, r == 1, N)), x);
        for (auto& t : z) t = exact_div(t, div);
        Vec4 y = coords_in(C_.classes()[c2].I, z);
        std::array<i64, 4> ym;
        for (int t = 0; t < 4; ++t) ym[t] = md(y[t], N);
        auto ab = coords(c2, ym, N);
        A[2 * r] = ab[0];
        A[2 * r + 1] = ab[1];
    }
    return A;
}

// ===================================================================================================== LevelSet
u64 LevelSet::key(const LevelPoint& p) const {
    const u64 n1 = (u64)U_.N1, n0 = (u64)U_.N0;
    return (((((u64)p.c * n1 + (u64)p.v0) * n1 + (u64)p.v1) * n0 + (u64)p.l0) * n0 + (u64)p.l1);
}

LevelPoint LevelSet::canon(LevelPoint p) const {
    p.v0 = md(p.v0, U_.N1);
    p.v1 = md(p.v1, U_.N1);
    if (U_.N0 > 1) {
        auto cl = canon0_[(size_t)(md(p.l0, U_.N0) * U_.N0 + md(p.l1, U_.N0))];
        p.l0 = cl[0];
        p.l1 = cl[1];
    } else {
        p.l0 = p.l1 = 0;
    }
    return p;
}

LevelPoint LevelSet::act(const LevelPoint& p, const Mat2& A1, const Mat2& A0) const {
    LevelPoint r = p;
    if (U_.N1 > 1) {
        r.v0 = md((i128)p.v0 * A1[0] + (i128)p.v1 * A1[2], U_.N1);
        r.v1 = md((i128)p.v0 * A1[1] + (i128)p.v1 * A1[3], U_.N1);
    }
    if (U_.N0 > 1) {
        r.l0 = md((i128)p.l0 * A0[0] + (i128)p.l1 * A0[2], U_.N0);
        r.l1 = md((i128)p.l0 * A0[1] + (i128)p.l1 * A0[3], U_.N0);
    }
    return canon(r);
}

LevelSet::LevelSet(const LevelModel& Mo, LevelSpec U) : Mo_(Mo), U_(U) {
    const ClassSet& C = Mo.class_set();
    const i64 Nb = Mo.modulus();
    if (U.N1 < 1 || U.N0 < 1 || std::gcd(U.N1, U.N0) != 1 || Nb % (U.N1 * U.N0))
        throw std::invalid_argument(ctx("level: need gcd(N1, N0) = 1 and N1 N0 | model modulus"));
    // canonical lines mod N0
    std::vector<std::array<i64, 2>> lines;
    if (U.N0 > 1) {
        const i64 N = U.N0;
        std::vector<i64> us;
        for (i64 u = 1; u < N; ++u)
            if (std::gcd(u, N) == 1) us.push_back(u);
        canon0_.assign((size_t)(N * N), {-1, -1});
        for (i64 a = 0; a < N; ++a)
            for (i64 b = 0; b < N; ++b) {
                if (std::gcd(std::gcd(a, b), N) != 1) continue;
                std::array<i64, 2> best{N, N};
                for (i64 u : us) {
                    std::array<i64, 2> cand{md((i128)u * a, N), md((i128)u * b, N)};
                    if (cand < best) best = cand;
                }
                canon0_[(size_t)(a * N + b)] = best;
                if (best[0] == a && best[1] == b) lines.push_back(best);
            }
    } else {
        lines.push_back({0, 0});
    }
    std::vector<std::array<i64, 2>> vecs;
    if (U.N1 > 1) {
        for (i64 a = 0; a < U.N1; ++a)
            for (i64 b = 0; b < U.N1; ++b)
                if (std::gcd(std::gcd(a, b), U.N1) == 1) vecs.push_back({a, b});
    } else {
        vecs.push_back({0, 0});
    }
    index_ = (i64)(vecs.size() * lines.size());
    const int h = C.h();
    um1_.resize(h);
    um0_.resize(h);
    first_.assign(h + 1, 0);
    for (int c = 0; c < h; ++c) {
        const auto& un = Mo.units(c);
        const i64 Nc = C.classes()[c].N;
        int minus = -1;
        for (size_t u = 0; u < un.size(); ++u)
            if (un[u] == Vec4{{-Nc, 0, 0, 0}}) minus = (int)u;
        if (minus < 0) throw std::logic_error(ctx("-1 not among the units"));
        for (const auto& x : un) {
            um1_[c].push_back(Mo.move(c, c, x, Nc, U.N1));
            um0_[c].push_back(Mo.move(c, c, x, Nc, U.N0));
        }
        first_[c] = (int)cells_.size();
        for (const auto& v : vecs)
            for (const auto& l : lines) {
                LevelPoint p;
                p.c = c;
                p.v0 = v[0];
                p.v1 = v[1];
                p.l0 = l[0];
                p.l1 = l[1];
                if (where_.count(key(p))) continue;
                LevelCell cell;
                cell.rep = p;
                const int id = (int)cells_.size();
                bool m1 = false;
                for (size_t u = 0; u < un.size(); ++u) {
                    LevelPoint im = act(p, um1_[c][u], um0_[c][u]);
                    if (im == p) {
                        cell.stab_units.push_back((int)u);
                        if ((int)u == minus) m1 = true;
                    }
                    auto ins = where_.emplace(key(im), std::make_pair(id, (int)u));
                    if (ins.second) ++cell.orbit_size;
                    else if (ins.first->second.first != id) throw std::logic_error(ctx("orbits overlap"));
                }
                cell.stab = (int)cell.stab_units.size();
                cell.w = m1 ? cell.stab / 2 : cell.stab;
                if ((size_t)cell.stab * cell.orbit_size != un.size()) throw std::logic_error(ctx("orbit-stabiliser failed"));
                cells_.push_back(cell);
            }
    }
    first_[h] = (int)cells_.size();
}

std::pair<int, int> LevelSet::locate_unit(const LevelPoint& p0) const {
    if (p0.c < 0 || p0.c >= (int)first_.size() - 1) return {-1, -1};
    if (U_.N1 > 1 && std::gcd(std::gcd(md(p0.v0, U_.N1), md(p0.v1, U_.N1)), U_.N1) != 1) return {-1, -1};
    if (U_.N0 > 1 && std::gcd(std::gcd(md(p0.l0, U_.N0), md(p0.l1, U_.N0)), U_.N0) != 1) return {-1, -1};
    auto it = where_.find(key(canon(p0)));
    return it == where_.end() ? std::make_pair(-1, -1) : it->second;
}
int LevelSet::locate(const LevelPoint& p) const { return locate_unit(p).first; }

std::vector<int> LevelSet::stabs() const {
    std::vector<int> s;
    for (const auto& c : cells_) s.push_back(c.stab);
    return s;
}
std::vector<int> LevelSet::ws() const {
    std::vector<int> s;
    for (const auto& c : cells_) s.push_back(c.w);
    return s;
}
namespace {
std::pair<i128, i128> sum_inv(const std::vector<int>& d) {
    i128 n = 0;
    for (int x : d) {
        if (24 % x) throw std::logic_error(ctx("stabiliser does not divide 24"));
        n += 24 / x;
    }
    i128 g = gcd128(n, 24);
    return {n / g, 24 / g};
}
}  // namespace
std::pair<i128, i128> LevelSet::mass() const { return sum_inv(stabs()); }
std::pair<i128, i128> LevelSet::massW() const { return sum_inv(ws()); }

// ===================================================================================================== maps
LevelPoint reduce_point(const LevelPoint& p, LevelSpec f, LevelSpec t) {
    // U_1(N1f) cap U_0(N0f) subset U_1(N1t) cap U_0(N0t) iff N1t | N1f and N0t | N1f N0f
    if (f.N1 % t.N1 || (f.N1 * f.N0) % t.N0) throw std::invalid_argument(ctx("reduce_point: levels not nested"));
    LevelPoint r = p;
    r.v0 = md(p.v0, t.N1);
    r.v1 = md(p.v1, t.N1);
    if (t.N0 > 1) {  // per prime power of N0t: the line of v (if it divides N1f) or of l
        std::vector<std::pair<i64, i64>> r0, r1;
        for (auto [l, lk] : prime_powers(t.N0)) {
            const bool fv = f.N1 % lk == 0;
            r0.push_back({md(fv ? p.v0 : p.l0, lk), lk});
            r1.push_back({md(fv ? p.v1 : p.l1, lk), lk});
        }
        r.l0 = crt(r0);
        r.l1 = crt(r1);
    } else {
        r.l0 = r.l1 = 0;
    }
    return r;
}

std::vector<int> project(const LevelSet& from, const LevelSet& to) {
    if (&from.model() != &to.model()) throw std::invalid_argument(ctx("project: different models"));
    std::vector<int> out;
    for (const auto& c : from.cells()) {
        int k = to.locate(reduce_point(c.rep, from.spec(), to.spec()));
        if (k < 0) throw std::logic_error(ctx("project: image not found"));
        out.push_back(k);
    }
    return out;
}

Correspondence u0q_correspondence(const LevelSet& E, const LevelSet& X, i64 q) {
    const LevelModel& Mo = E.model();
    const ClassSet& C = Mo.class_set();
    const MaxOrder& O = C.order();
    const LevelSpec ue = E.spec(), ux = X.spec();
    if (!is_prime(q) || ue.N1 != ux.N1 || ue.N0 != ux.N0 * q || ux.N0 % q == 0 || ue.N1 % q == 0)
        throw std::invalid_argument(ctx("u0q_correspondence: need E = U cap U_0(q), X = U, q prime to the level"));
    Correspondence R;
    R.s0 = project(E, X);
    std::map<std::tuple<int, i64, i64>, std::pair<int, Vec4>> cache;
    for (const auto& cell : E.cells()) {
        const LevelPoint& p = cell.rep;
        const int c = p.c;
        const i64 Nc = C.classes()[c].N;
        // the q-line, canonical mod q (first nonzero coordinate 1)
        i64 a = md(p.l0, q), b = md(p.l1, q);
        i64 f = a ? a : b;
        i64 fi = inv_mod(f, q);
        a = md((i128)a * fi, q);
        b = md((i128)b * fi, q);
        auto keyq = std::make_tuple(c, a, b);
        auto it = cache.find(keyq);
        if (it == cache.end()) {
            Vec4 y = Mo.element(c, Mo.lift(c, a, b, q));
            const Lat& I = C.classes()[c].I;
            std::vector<Vec4> gens;
            for (int s = 0; s < 4; ++s) {
                Vec4 es{{0, 0, 0, 0}};
                es[s] = 1;
                gens.push_back(O.mul(es, y));
                Vec4 qi = I.h[s];
                for (auto& t : qi) t = mul_chk(t, q);
                gens.push_back(qi);
            }
            const i128 NJ = (i128)q * Nc;
            Lat J = hnf(gens, 1, NJ * NJ);
            int c1 = C.identify(J, (i64)NJ, true);
            if (c1 < 0) throw std::logic_error(ctx("u0q: J in no class"));
            Vec4 mu = find_mu(C, C.classes()[c1].I, C.classes()[c1].N, J, (i64)NJ);
            it = cache.emplace(keyq, std::make_pair(c1, mu)).first;
        }
        const int c1 = it->second.first;
        const Vec4 cmu = O.conj(it->second.second);
        LevelPoint r;
        r.c = c1;
        Mat2 A1 = Mo.move(c, c1, cmu, Nc, ux.N1), A0 = Mo.move(c, c1, cmu, Nc, ux.N0);
        if (ux.N1 > 1) {
            r.v0 = md((i128)p.v0 * A1[0] + (i128)p.v1 * A1[2], ux.N1);
            r.v1 = md((i128)p.v0 * A1[1] + (i128)p.v1 * A1[3], ux.N1);
        }
        if (ux.N0 > 1) {
            i64 l0 = md(p.l0, ux.N0), l1 = md(p.l1, ux.N0);
            r.l0 = md((i128)l0 * A0[0] + (i128)l1 * A0[2], ux.N0);
            r.l1 = md((i128)l0 * A0[1] + (i128)l1 * A0[3], ux.N0);
        }
        int t = X.locate(r);
        if (t < 0) throw std::logic_error(ctx("u0q: transported point not found"));
        R.s1.push_back(t);
        R.edge_class_target.push_back(c1);
    }
    return R;
}

bool fibre_sums_ok(const LevelSet& E, const LevelSet& X, const std::vector<int>& s, i64 q) {
    std::vector<i128> acc(X.size(), 0);  // 24 * sum stab_x / stab_e
    for (int e = 0; e < E.size(); ++e) {
        const int x = s[e];
        acc[x] += (i128)X.cells()[x].stab * (24 / E.cells()[e].stab);
    }
    for (auto v : acc)
        if (v != 24 * (i128)(q + 1)) return false;
    return true;
}

// ===================================================================================================== tower
Tower::Tower(const ClassSet& C, i64 p, int smax, i64 M) : model_(C, [&] {
    i64 N = M;
    for (int s = 0; s < smax; ++s) N *= p;
    return N;
}()), p_(p), M_(M), smax_(smax) {
    if (!is_prime(p) || M % p == 0) throw std::invalid_argument(ctx("tower: p prime, p not | M"));
    i64 N = M;
    for (int s = 1; s <= smax; ++s) {
        N *= p;
        S_.push_back(std::make_unique<LevelSet>(model_, LevelSpec{N, 1}));
    }
}

std::vector<int> Tower::pi(int s) const {
    if (s < 2 || s > smax_) throw std::invalid_argument(ctx("tower pi: 2 <= s <= smax"));
    return project(S(s), S(s - 1));
}

std::vector<int> Tower::diamond(int s, i64 d) const {
    const LevelSet& X = S(s);
    i64 ps = 1;
    for (int t = 0; t < s; ++t) ps *= p_;
    const i64 N = M_ * ps;
    i64 u = M_ > 1 ? crt({{inv_mod(d, ps), ps}, {1, M_}}) : inv_mod(d, ps);
    std::vector<int> out;
    for (const auto& c : X.cells()) {
        LevelPoint r = c.rep;
        r.v0 = md((i128)u * r.v0, N);
        r.v1 = md((i128)u * r.v1, N);
        int t = X.locate(r);
        if (t < 0) throw std::logic_error(ctx("diamond: image not found"));
        out.push_back(t);
    }
    return out;
}

bool Tower::delta_free(int s) const {
    i64 ps = 1;
    for (int t = 0; t < s; ++t) ps *= p_;
    for (i64 k = 1; k < ps / p_; ++k) {
        auto perm = diamond(s, 1 + p_ * k);
        for (size_t j = 0; j < perm.size(); ++j)
            if (perm[j] == (int)j) return false;
    }
    return true;
}

}  // namespace hacs_jl
