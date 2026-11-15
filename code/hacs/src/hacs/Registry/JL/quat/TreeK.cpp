// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-7b): weight-k two-term complexes on BG(U, q). See TreeK.h.
#include "TreeK.h"

#include <stdexcept>

namespace hacs_jl {

namespace {
i64 md(i128 x, i64 m) {
    i128 r = x % m;
    return (i64)(r < 0 ? r + m : r);
}
i64 inv_mod(i64 a, i64 m) {
    // extended Euclid
    i128 r0 = md(a, m), r1 = m, s0 = 1, s1 = 0;
    while (r1) {
        i128 qq = r0 / r1, t = r0 - qq * r1;
        r0 = r1;
        r1 = t;
        t = s0 - qq * s1;
        s0 = s1;
        s1 = t;
    }
    if (r0 != 1) throw std::logic_error("hacs_jl::inv_mod: not a unit");
    return md(s0, m);
}
int val(i64 x, i64 p, int m) {
    if (x == 0) return m;
    int v = 0;
    while (x % p == 0) {
        x /= p;
        ++v;
    }
    return v;
}
ModMat mm(const ModMat& A, const ModMat& B, i64 mod) {
    ModMat C;
    C.r = A.r;
    C.c = B.c;
    C.a.assign((size_t)C.r * C.c, 0);
    for (int i = 0; i < A.r; ++i)
        for (int k = 0; k < A.c; ++k) {
            i64 x = A.at(i, k);
            if (!x) continue;
            for (int j = 0; j < B.c; ++j) C.at(i, j) = md((i128)C.at(i, j) + (i128)x * B.at(k, j), mod);
        }
    return C;
}
std::vector<i64> mv(const ModMat& A, const std::vector<i64>& v, i64 mod) {
    std::vector<i64> o(A.r, 0);
    for (int i = 0; i < A.r; ++i) {
        i128 s = 0;
        for (int j = 0; j < A.c; ++j)
            if (v[j]) s = (s + (i128)A.at(i, j) * v[j]) % mod;
        o[i] = md(s, mod);
    }
    return o;
}
}  // namespace

std::vector<int> elem_divs_mod(ModMat A, i64 p, int m) {
    i64 mod = 1;
    for (int i = 0; i < m; ++i) mod *= p;
    for (auto& x : A.a) x = md(x, mod);
    std::vector<int> out;
    const int nr = A.r, nc = A.c;
    int r0 = 0;
    for (int it = 0; it < std::min(nr, nc); ++it) {
        int bv = m + 1, bi = -1, bj = -1;
        for (int i = r0; i < nr && bv > 0; ++i)
            for (int j = r0; j < nc; ++j) {
                i64 x = A.at(i, j);
                if (!x) continue;
                int v = val(x, p, m);
                if (v < bv) {
                    bv = v;
                    bi = i;
                    bj = j;
                    if (v == 0) break;
                }
            }
        if (bi < 0) break;
        for (int j = 0; j < nc; ++j) std::swap(A.at(r0, j), A.at(bi, j));
        for (int i = 0; i < nr; ++i) std::swap(A.at(i, r0), A.at(i, bj));
        i64 pv = 1;
        for (int t = 0; t < bv; ++t) pv *= p;
        const i64 unit = inv_mod(A.at(r0, r0) / pv, mod);
        for (int j = 0; j < nc; ++j) A.at(r0, j) = md((i128)A.at(r0, j) * unit, mod);
        for (int i = 0; i < nr; ++i) {
            if (i == r0 || !A.at(i, r0)) continue;
            const i64 f = A.at(i, r0) / pv;
            for (int j = 0; j < nc; ++j) A.at(i, j) = md((i128)A.at(i, j) - (i128)f * A.at(r0, j), mod);
        }
        for (int j = r0 + 1; j < nc; ++j) {
            if (!A.at(r0, j)) continue;
            const i64 f = A.at(r0, j) / pv;
            for (int i = 0; i < nr; ++i) A.at(i, j) = md((i128)A.at(i, j) - (i128)f * A.at(i, r0), mod);
        }
        out.push_back(bv);
        ++r0;
    }
    std::sort(out.begin(), out.end());
    return out;
}

std::vector<int> module_structure(const ModMat& R, int dim, i64 p, int m) {
    // R: rows = relation vectors (length dim); structure of (Z/p^m)^dim / span
    auto ed = R.r ? elem_divs_mod(R, p, m) : std::vector<int>{};
    std::vector<int> out(dim - (int)ed.size(), m);
    for (int v : ed)
        if (v > 0) out.push_back(v);
    return out;
}

// ---------------------------------------------------------------- 2x2
M2 m2mul(const M2& A, const M2& B, i64 mod) {
    return {md((i128)A[0] * B[0] + (i128)A[1] * B[2], mod), md((i128)A[0] * B[1] + (i128)A[1] * B[3], mod),
            md((i128)A[2] * B[0] + (i128)A[3] * B[2], mod), md((i128)A[2] * B[1] + (i128)A[3] * B[3], mod)};
}
M2 m2inv(const M2& A, i64 mod) {
    i64 di = inv_mod(md((i128)A[0] * A[3] - (i128)A[1] * A[2], mod), mod);
    return {md((i128)A[3] * di, mod), md(-(i128)A[1] * di, mod), md(-(i128)A[2] * di, mod), md((i128)A[0] * di, mod)};
}
M2 m2scale(const M2& A, i64 s, i64 mod) {
    return {md((i128)A[0] * s, mod), md((i128)A[1] * s, mod), md((i128)A[2] * s, mod), md((i128)A[3] * s, mod)};
}

// ---------------------------------------------------------------- coefficients
ModMat SymCoeff::act(const M2& g) const {
    const int n = n_;
    const i64 mod = mod_;
    auto pmul = [&](const std::vector<i64>& a, const std::vector<i64>& b) {
        std::vector<i64> o(a.size() + b.size() - 1, 0);
        for (size_t i = 0; i < a.size(); ++i)
            for (size_t j = 0; j < b.size(); ++j) o[i + j] = md((i128)o[i + j] + (i128)a[i] * b[j], mod);
        return o;
    };
    // (a X + c Y)^{n-t} (b X + d Y)^t, coefficient of X^{n-s} Y^s at index s
    std::vector<std::vector<i64>> p1{{1}}, p2{{1}};
    for (int i = 0; i < n; ++i) {
        p1.push_back(pmul(p1.back(), {md(g[0], mod), md(g[2], mod)}));
        p2.push_back(pmul(p2.back(), {md(g[1], mod), md(g[3], mod)}));
    }
    ModMat S;
    S.r = S.c = n + 1;
    S.a.assign((size_t)(n + 1) * (n + 1), 0);
    for (int t = 0; t <= n; ++t) {
        auto col = pmul(p1[n - t], p2[t]);
        for (int s = 0; s <= n; ++s) S.at(s, t) = col[s];
    }
    return S;
}

ShapiroSymCoeff::ShapiroSymCoeff(int n, i64 p, i64 mod) : n_(n), p_(p), mod_(mod), sym_(n, mod) {
    for (i64 a = 0; a < p; ++a)
        for (i64 b = 0; b < p; ++b)
            if (a || b) pts_.push_back({a, b});
}
ModMat ShapiroSymCoeff::act(const M2& g) const {
    const int d = n_ + 1, N = (int)pts_.size();
    ModMat S = sym_.act(g);
    M2 gi = m2inv(g, mod_);
    ModMat W;
    W.r = W.c = N * d;
    W.a.assign((size_t)W.r * W.c, 0);
    for (int i = 0; i < N; ++i) {
        auto [r0, r1] = pts_[i];
        i64 s0 = md((i128)r0 * gi[0] + (i128)r1 * gi[2], p_), s1 = md((i128)r0 * gi[1] + (i128)r1 * gi[3], p_);
        int j = (int)(s0 * p_ + s1) - 1;  // index of (s0, s1) in pts_ (lexicographic, (0,0) skipped)
        for (int s = 0; s < d; ++s)
            for (int t = 0; t < d; ++t) W.at(j * d + s, i * d + t) = S.at(s, t);
    }
    return W;
}

// ---------------------------------------------------------------- frames
namespace {
M2 frames_iota(const MaxOrder& O, const PadicFrames& F, const Vec4& x) {
    M2 r{};
    const Vec4* bs[2] = {&F.b1, &F.b2};
    const int i0 = F.pos[0], i1 = F.pos[1];
    const i64 mod = F.mod;
    const i64 det = md((i128)F.b1[i0] * F.b2[i1] - (i128)F.b2[i0] * F.b1[i1], mod);
    const i64 di = inv_mod(det, mod);
    for (int i = 0; i < 2; ++i) {
        Vec4 w = O.mul(*bs[i], x);
        i64 w0 = md(w[i0], mod), w1 = md(w[i1], mod);
        // (al, be) [b1; b2] = w at the coordinates i0, i1
        i64 al = md(((i128)w0 * md(F.b2[i1], mod) - (i128)w1 * md(F.b2[i0], mod)) % mod * di, mod);
        i64 be = md(((i128)w1 * md(F.b1[i0], mod) - (i128)w0 * md(F.b1[i1], mod)) % mod * di, mod);
        for (int s = 0; s < 4; ++s)
            if (md((i128)al * F.b1[s] + (i128)be * F.b2[s] - w[s], mod) != 0)
                throw std::logic_error("hacs_jl::iota: b_i x not in span(b1, b2)");
        r[2 * i] = al;
        r[2 * i + 1] = be;
    }
    return r;
}
}  // namespace

PadicFrames make_frames(const ClassSet& C, i64 p, int m) {
    const MaxOrder& O = C.order();
    PadicFrames F;
    F.p = p;
    F.m = m;
    F.mod = 1;
    for (int i = 0; i < m; ++i) F.mod *= p;
    F.e = idempotent_mod(O, F.mod);
    std::vector<Vec4> ys;
    for (int s = 0; s < 4; ++s) {
        Vec4 u{{0, 0, 0, 0}};
        u[s] = 1;
        Vec4 y = O.mul(F.e, u);
        for (auto& t : y) t = md(t, F.mod);
        ys.push_back(y);
    }
    bool ok = false;
    for (int i = 0; i < 4 && !ok; ++i)
        for (int j = i + 1; j < 4 && !ok; ++j)
            for (int a = 0; a < 4 && !ok; ++a)
                for (int b = a + 1; b < 4 && !ok; ++b)
                    if (md((i128)ys[i][a] * ys[j][b] - (i128)ys[j][a] * ys[i][b], p)) {
                        F.b1 = ys[i];
                        F.b2 = ys[j];
                        F.pos[0] = a;
                        F.pos[1] = b;
                        ok = true;
                    }
    if (!ok) throw std::logic_error("hacs_jl::make_frames: e O / p^m is not free of rank 2");
    for (int c = 0; c < C.h(); ++c) {
        const ClassRep& r = C.classes()[c];
        Reduced R = lll_reduce(r.I, O.embedding(), O.gram());
        Vec4 best{};
        bool found = false;
        for (i128 bound = 4 * (i128)r.N; !found; bound *= 2)
            fp_enumerate(R, bound, [&](const i64* x, i128 v2) {
                i128 n = v2 / 2;
                if ((n / r.N) % p) {
                    best = combine(R, x);
                    found = true;
                    return false;
                }
                return true;
            });
        F.a.push_back(best);
        F.na.push_back(md(exact_div(O.nrd(best), r.N), F.mod));
    }
    return F;
}

LocalTwist local_twist(const ClassSet& C, const TreeQuotient& T, const PadicFrames& F) {
    const MaxOrder& O = C.order();
    const i64 mod = F.mod;
    auto phi = [&](int c, const Vec4& x) {  // x = N_c gamma, gamma in O_r(I_c)
        const i64 N = C.classes()[c].N;
        Vec4 z = O.mul(O.mul(F.a[c], x), O.conj(F.a[c]));
        for (auto& t : z) t = exact_div(t, (i128)N * N);
        return m2scale(frames_iota(O, F, z), inv_mod(F.na[c], mod), mod);
    };
    LocalTwist L;
    for (const auto& cell : T.V) {
        std::vector<M2> H;
        for (int u : cell.stab_units) H.push_back(phi(cell.rep.c, T.units[cell.rep.c][u]));
        L.Hv.push_back(H);
    }
    for (size_t e = 0; e < T.E.size(); ++e) {
        const auto& cell = T.E[e];
        const int c = cell.rep.c;
        std::vector<M2> H;
        for (int u : cell.stab_units) H.push_back(phi(c, T.units[c][u]));
        L.He.push_back(H);
        const EdgeMove& mvv = T.moves[e];
        L.u0.push_back(phi(c, O.conj(T.units[c][mvv.unit0])));
        const int c1 = mvv.c1;
        const i64 N = C.classes()[c].N, N1 = C.classes()[c1].N;
        Vec4 z = O.mul(O.mul(O.mul(F.a[c1], O.conj(T.units[c1][mvv.unit1])), mvv.mu), O.conj(F.a[c]));
        for (auto& t : z) t = exact_div(t, (i128)N1 * N1 * N);
        L.u1.push_back(m2scale(frames_iota(O, F, z), inv_mod(md((i128)T.q * F.na[c], mod), mod), mod));
    }
    // conjugation check: u_j H_e u_j^{-1} subset H_{s_j e}
    for (size_t e = 0; e < T.E.size(); ++e)
        for (int j = 0; j < 2; ++j) {
            const M2& u = j ? L.u1[e] : L.u0[e];
            const M2 ui = m2inv(u, mod);
            const auto& Hv = L.Hv[j ? T.s1[e] : T.s0[e]];
            for (const auto& h : L.He[e]) {
                M2 g = m2mul(m2mul(u, h, mod), ui, mod);
                if (std::find(Hv.begin(), Hv.end(), g) == Hv.end()) L.conj_ok = false;
            }
        }
    return L;
}

// ---------------------------------------------------------------- the complexes
namespace {
struct Summand {
    ModMat P;                    // projector e_H
    std::vector<std::vector<i64>> basis;  // columns
    std::vector<int> rows;       // invertible minor rows
    ModMat Ainv;                 // inverse of the minor
};

Summand summand(const std::vector<M2>& H, const CoeffModel& W, i64 p) {
    const i64 mod = W.modulus();
    const int d = W.dim();
    Summand S;
    S.P.r = S.P.c = d;
    S.P.a.assign((size_t)d * d, 0);
    for (const auto& h : H) {
        ModMat A = W.act(h);
        for (size_t i = 0; i < A.a.size(); ++i) S.P.a[i] = md((i128)S.P.a[i] + A.a[i], mod);
    }
    const i64 hi = inv_mod((i64)H.size(), mod);
    for (auto& x : S.P.a) x = md((i128)x * hi, mod);
    // image basis: columns of P independent mod p (greedy echelon mod p)
    std::vector<std::vector<i64>> red;
    std::vector<int> piv;
    for (int j = 0; j < d; ++j) {
        std::vector<i64> v(d);
        for (int i = 0; i < d; ++i) v[i] = md(S.P.at(i, j), p);
        for (size_t t = 0; t < red.size(); ++t)
            if (v[piv[t]]) {
                i64 f = v[piv[t]];
                for (int i = 0; i < d; ++i) v[i] = md((i128)v[i] - (i128)f * red[t][i], p);
            }
        int nz = -1;
        for (int i = 0; i < d; ++i)
            if (v[i]) {
                nz = i;
                break;
            }
        if (nz < 0) continue;
        i64 iv = inv_mod(v[nz], p);
        for (auto& x : v) x = md((i128)x * iv, p);
        red.push_back(v);
        piv.push_back(nz);
        std::vector<i64> col(d);
        for (int i = 0; i < d; ++i) col[i] = S.P.at(i, j);
        S.basis.push_back(col);
    }
    const int r = (int)S.basis.size();
    if (r == 0) return S;
    // rows with an invertible r x r minor: greedy rank mod p on the rows of the basis matrix
    std::vector<std::vector<i64>> rr;
    std::vector<int> rp;
    for (int i = 0; i < d && (int)S.rows.size() < r; ++i) {
        std::vector<i64> v(r);
        for (int j = 0; j < r; ++j) v[j] = md(S.basis[j][i], p);
        for (size_t t = 0; t < rr.size(); ++t)
            if (v[rp[t]]) {
                i64 f = v[rp[t]];
                for (int j = 0; j < r; ++j) v[j] = md((i128)v[j] - (i128)f * rr[t][j], p);
            }
        int nz = -1;
        for (int j = 0; j < r; ++j)
            if (v[j]) {
                nz = j;
                break;
            }
        if (nz < 0) continue;
        i64 iv = inv_mod(v[nz], p);
        for (auto& x : v) x = md((i128)x * iv, p);
        rr.push_back(v);
        rp.push_back(nz);
        S.rows.push_back(i);
    }
    if ((int)S.rows.size() != r) throw std::logic_error("hacs_jl::summand: no invertible minor");
    // invert the minor mod p^m (Gauss-Jordan with unit pivots)
    ModMat A;
    A.r = r;
    A.c = 2 * r;
    A.a.assign((size_t)r * 2 * r, 0);
    for (int a = 0; a < r; ++a) {
        for (int b = 0; b < r; ++b) A.at(a, b) = S.basis[b][S.rows[a]];
        A.at(a, r + a) = 1;
    }
    for (int col = 0; col < r; ++col) {
        int pv = -1;
        for (int i = col; i < r; ++i)
            if (A.at(i, col) % p) {
                pv = i;
                break;
            }
        if (pv < 0) throw std::logic_error("hacs_jl::summand: singular minor");
        for (int j = 0; j < 2 * r; ++j) std::swap(A.at(col, j), A.at(pv, j));
        i64 iv = inv_mod(A.at(col, col), mod);
        for (int j = 0; j < 2 * r; ++j) A.at(col, j) = md((i128)A.at(col, j) * iv, mod);
        for (int i = 0; i < r; ++i) {
            if (i == col || !A.at(i, col)) continue;
            i64 f = A.at(i, col);
            for (int j = 0; j < 2 * r; ++j) A.at(i, j) = md((i128)A.at(i, j) - (i128)f * A.at(col, j), mod);
        }
    }
    S.Ainv.r = S.Ainv.c = r;
    S.Ainv.a.assign((size_t)r * r, 0);
    for (int a = 0; a < r; ++a)
        for (int b = 0; b < r; ++b) S.Ainv.at(a, b) = A.at(a, r + b);
    return S;
}

std::vector<i64> coords(const Summand& S, const std::vector<i64>& w, i64 mod) {
    const int r = (int)S.basis.size();
    std::vector<i64> c(r, 0);
    for (int a = 0; a < r; ++a) {
        i128 s = 0;
        for (int b = 0; b < r; ++b) s = (s + (i128)S.Ainv.at(a, b) * w[S.rows[b]]) % mod;
        c[a] = md(s, mod);
    }
    for (size_t i = 0; i < w.size(); ++i) {
        i128 s = 0;
        for (int j = 0; j < r; ++j) s = (s + (i128)c[j] * S.basis[j][i]) % mod;
        if (md(s - w[i], mod) != 0) throw std::logic_error("hacs_jl::coords: vector not in the summand");
    }
    return c;
}
}  // namespace

TwoTerm two_term(const TreeQuotient& T, const LocalTwist& L, const CoeffModel& W, i64 p) {
    const i64 mod = W.modulus();
    const int X = T.X(), E = T.nE();
    std::vector<Summand> SV, SE;
    for (const auto& H : L.Hv) SV.push_back(summand(H, W, p));
    for (const auto& H : L.He) SE.push_back(summand(H, W, p));
    TwoTerm R;
    R.off_v.assign(2 * X + 1, 0);
    for (int t = 0; t < 2 * X; ++t) R.off_v[t + 1] = R.off_v[t] + (int)SV[t % X].basis.size();
    R.off_e.assign(E + 1, 0);
    for (int e = 0; e < E; ++e) R.off_e[e + 1] = R.off_e[e] + (int)SE[e].basis.size();
    R.r0 = R.off_v[2 * X];
    R.r1 = R.off_e[E];
    auto init = [](ModMat& M, int r, int c) {
        M.r = r;
        M.c = c;
        M.a.assign((size_t)r * c, 0);
    };
    init(R.d_hom, R.r0, R.r1);
    init(R.d_coh, R.r0, R.r1);
    init(R.delta, R.r1, R.r0);
    std::vector<ModMat> Wu0, Wu1, Wu0i, Wu1i;
    for (int e = 0; e < E; ++e) {
        const int v[2] = {T.s0[e], T.s1[e]};
        const M2 u[2] = {L.u0[e], L.u1[e]};
        const int sg[2] = {-1, 1};
        for (int j = 0; j < 2; ++j) {
            ModMat Wu = W.act(u[j]);
            ModMat PWu = mm(SV[v[j]].P, Wu, mod);
            const i64 idx = (i64)(L.Hv[v[j]].size() / L.He[e].size());
            const int o = R.off_v[j * X + v[j]];
            for (size_t a = 0; a < SE[e].basis.size(); ++a) {
                auto w = mv(PWu, SE[e].basis[a], mod);
                auto co = coords(SV[v[j]], w, mod);
                for (size_t i = 0; i < co.size(); ++i) {
                    R.d_hom.at(o + (int)i, R.off_e[e] + (int)a) =
                        md((i128)R.d_hom.at(o + (int)i, R.off_e[e] + (int)a) + sg[j] * (i128)co[i], mod);
                    R.d_coh.at(o + (int)i, R.off_e[e] + (int)a) =
                        md((i128)R.d_coh.at(o + (int)i, R.off_e[e] + (int)a) + sg[j] * (i128)idx * co[i], mod);
                }
            }
            // coboundary: (s_j^* f)(e) = u_j^{-1} f(v)
            ModMat Wui = W.act(m2inv(u[j], mod));
            for (size_t a = 0; a < SV[v[j]].basis.size(); ++a) {
                auto w = mv(Wui, SV[v[j]].basis[a], mod);
                auto co = coords(SE[e], w, mod);
                for (size_t i = 0; i < co.size(); ++i)
                    R.delta.at(R.off_e[e] + (int)i, o + (int)a) =
                        md((i128)R.delta.at(R.off_e[e] + (int)i, o + (int)a) + sg[j] * (i128)co[i], mod);
            }
        }
    }
    return R;
}

}  // namespace hacs_jl
