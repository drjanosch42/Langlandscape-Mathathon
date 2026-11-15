// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-4a): integral Sym^n Brandt module. Conventions: BrandtSym.h (C1)-(C7).
#include "BrandtSym.h"

#include <algorithm>
#include <stdexcept>

namespace hacs_jl {

namespace {
const Z kZero(0), kOne(1);
bool is_int(const Q& x) { return x.den() == kOne; }
Z floor_div(const Z& x, const Z& m) {  // m > 0
    Z r = x.floor_mod(m);
    return (x - r) / m;
}
Z lcm(const Z& a, const Z& b) {
    if (a.is_zero()) return b;
    if (b.is_zero()) return a;
    return (a / Z::gcd(a, b)) * b;
}
std::string ctx(const char* f) { return std::string("hacs_jl::BrandtSym: ") + f; }

// echelon rows (rational) with pivots: coordinates of v, verified
std::vector<Q> solve_echelon(const QMat& rows, const std::vector<int>& piv, const std::vector<Q>& v, const char* what) {
    const size_t r = rows.size();
    std::vector<Q> y(r);
    for (size_t i = 0; i < r; ++i) {
        Q acc = v[piv[i]];
        for (size_t j = 0; j < i; ++j)
            if (!y[j].is_zero() && !rows[j][piv[i]].is_zero()) acc -= y[j] * rows[j][piv[i]];
        y[i] = acc / rows[i][piv[i]];
    }
    // verify
    for (size_t c = 0; c < v.size(); ++c) {
        Q acc(0);
        for (size_t i = 0; i < r; ++i)
            if (!y[i].is_zero() && !rows[i][c].is_zero()) acc += y[i] * rows[i][c];
        if (acc != v[c]) throw std::logic_error(ctx(what) + ": vector not in the span");
    }
    return y;
}

std::vector<int> pivots_of(const QMat& rows) {
    std::vector<int> p;
    for (const auto& r : rows) {
        int c = 0;
        while (c < (int)r.size() && r[c].is_zero()) ++c;
        if (c == (int)r.size()) throw std::logic_error(ctx("pivots_of: zero row"));
        if (!p.empty() && c <= p.back()) throw std::logic_error(ctx("pivots_of: not echelon"));
        p.push_back(c);
    }
    return p;
}

// HNF basis of the Z-span of rational generator rows (rows of the result: rational, echelon)
QMat lattice_basis(const QMat& gens) {
    if (gens.empty()) return {};
    Z s(1);
    for (const auto& r : gens)
        for (const auto& x : r) s = lcm(s, x.den());
    ZMat A;
    for (const auto& r : gens) {
        std::vector<Z> row;
        for (const auto& x : r) row.push_back(x.num() * (s / x.den()));
        A.push_back(row);
    }
    ZMat H = symz::hnf_rows(A);
    QMat out;
    for (const auto& r : H) {
        std::vector<Q> row;
        for (const auto& x : r) row.push_back(Q(x, s));
        out.push_back(row);
    }
    return out;
}

QMat qinverse(QMat A) {
    const int n = (int)A.size();
    QMat I(n, std::vector<Q>(n, Q(0)));
    for (int i = 0; i < n; ++i) I[i][i] = Q(1);
    for (int c = 0; c < n; ++c) {
        int p = c;
        while (p < n && A[p][c].is_zero()) ++p;
        if (p == n) throw std::logic_error(ctx("qinverse: singular"));
        std::swap(A[p], A[c]);
        std::swap(I[p], I[c]);
        Q inv = Q(1) / A[c][c];
        for (int j = 0; j < n; ++j) {
            A[c][j] *= inv;
            I[c][j] *= inv;
        }
        for (int r = 0; r < n; ++r)
            if (r != c && !A[r][c].is_zero()) {
                Q f = A[r][c];
                for (int j = 0; j < n; ++j) {
                    A[r][j] -= f * A[c][j];
                    I[r][j] -= f * I[c][j];
                }
            }
    }
    return I;
}

Z binom(int n, int k) {
    Z r(1);
    for (int i = 1; i <= k; ++i) r = r * Z(n - k + i) / Z(i);
    return r;
}

std::vector<Q> real_of(const KVec& v) {
    std::vector<Q> x;
    x.reserve(2 * v.size());
    for (const auto& e : v) {
        x.push_back(e.r);
        x.push_back(e.s);
    }
    return x;
}
KVec kvec_of_real(const std::vector<Q>& x) {
    KVec v(x.size() / 2);
    for (size_t t = 0; t < v.size(); ++t) v[t] = KElt{x[2 * t], x[2 * t + 1]};
    return v;
}

KElt kadd(const KElt& x, const KElt& y) { return KElt{x.r + y.r, x.s + y.s}; }
KElt kmul(i64 a, const KElt& x, const KElt& y) {
    return KElt{x.r * y.r + Q(a) * (x.s * y.s), x.r * y.s + x.s * y.r};
}
bool kzero(const KElt& x) { return x.r.is_zero() && x.s.is_zero(); }

// polynomial (in Y, coefficient list) product over K
KVec pmul(i64 a, const KVec& p, const KVec& q) {
    KVec out(p.size() + q.size() - 1, KElt{Q(0), Q(0)});
    for (size_t i = 0; i < p.size(); ++i) {
        if (kzero(p[i])) continue;
        for (size_t j = 0; j < q.size(); ++j)
            if (!kzero(q[j])) out[i + j] = kadd(out[i + j], kmul(a, p[i], q[j]));
    }
    return out;
}
}  // namespace

// ===================================================================================================== symz
namespace symz {
ZMat identity(int d) {
    ZMat I(d, std::vector<Z>(d, kZero));
    for (int i = 0; i < d; ++i) I[i][i] = kOne;
    return I;
}
ZMat mul(const ZMat& A, const ZMat& B) {
    const size_t n = A.size(), k = B.size(), m = k ? B[0].size() : 0;
    ZMat C(n, std::vector<Z>(m, kZero));
    for (size_t i = 0; i < n; ++i)
        for (size_t t = 0; t < k; ++t) {
            if (A[i][t].is_zero()) continue;
            for (size_t j = 0; j < m; ++j)
                if (!B[t][j].is_zero()) C[i][j] += A[i][t] * B[t][j];
        }
    return C;
}
QMat mul(const QMat& A, const QMat& B) {
    const size_t n = A.size(), k = B.size(), m = k ? B[0].size() : 0;
    QMat C(n, std::vector<Q>(m, Q(0)));
    for (size_t i = 0; i < n; ++i)
        for (size_t t = 0; t < k; ++t) {
            if (A[i][t].is_zero()) continue;
            for (size_t j = 0; j < m; ++j)
                if (!B[t][j].is_zero()) C[i][j] += A[i][t] * B[t][j];
        }
    return C;
}
ZMat transpose(const ZMat& A) {
    if (A.empty()) return {};
    ZMat T(A[0].size(), std::vector<Z>(A.size()));
    for (size_t i = 0; i < A.size(); ++i)
        for (size_t j = 0; j < A[0].size(); ++j) T[j][i] = A[i][j];
    return T;
}
bool equal(const ZMat& A, const ZMat& B) { return A == B; }
bool is_scalar(const ZMat& A, const Z& l) {
    for (size_t i = 0; i < A.size(); ++i)
        for (size_t j = 0; j < A.size(); ++j)
            if (A[i][j] != (i == j ? l : kZero)) return false;
    return true;
}
std::vector<Z> charpoly(const ZMat& A) {
    const int n = (int)A.size();
    std::vector<Z> c(n + 1, kZero);
    c[n] = kOne;
    ZMat Mk(n, std::vector<Z>(n, kZero));
    for (int k = 1; k <= n; ++k) {
        for (int i = 0; i < n; ++i) Mk[i][i] += c[n - k + 1];
        Mk = mul(A, Mk);
        Z tr(0);
        for (int i = 0; i < n; ++i) tr += Mk[i][i];
        Z q, r;
        Z::divmod(tr, Z(k), q, r);
        if (!r.is_zero()) throw std::logic_error(ctx("charpoly: inexact division"));
        c[n - k] = -q;
    }
    return c;
}
std::vector<std::vector<u64>> reduce_mod(const ZMat& A, u64 m) {
    std::vector<std::vector<u64>> R(A.size());
    const Z M = Z::from_u64(m);
    for (size_t i = 0; i < A.size(); ++i)
        for (const auto& x : A[i]) R[i].push_back((u64)x.floor_mod(M).to_int64());
    return R;
}
namespace {
// eliminate columns [0, ncols) of A (rows), integer row operations only; returns the rank r: rows [0, r) echelon
size_t echelonize(ZMat& A, size_t ncols, bool reduce_above) {
    size_t r = 0;
    for (size_t col = 0; col < ncols && r < A.size(); ++col) {
        while (true) {
            size_t best = A.size();
            for (size_t i = r; i < A.size(); ++i)
                if (!A[i][col].is_zero() && (best == A.size() || A[i][col].abs() < A[best][col].abs())) best = i;
            if (best == A.size()) break;
            std::swap(A[r], A[best]);
            bool done = true;
            for (size_t i = r + 1; i < A.size(); ++i) {
                if (A[i][col].is_zero()) continue;
                Z q = A[i][col] / A[r][col];
                if (!q.is_zero())
                    for (size_t j = col; j < A[i].size(); ++j)
                        if (!A[r][j].is_zero()) A[i][j] -= q * A[r][j];
                if (!A[i][col].is_zero()) done = false;
            }
            if (done) break;
        }
        if (r < A.size() && !A[r][col].is_zero()) {
            if (A[r][col].is_neg())
                for (auto& x : A[r]) x = -x;
            if (reduce_above)
                for (size_t i = 0; i < r; ++i) {
                    if (A[i][col].is_zero()) continue;
                    Z q = floor_div(A[i][col], A[r][col]);
                    if (!q.is_zero())
                        for (size_t j = col; j < A[i].size(); ++j)
                            if (!A[r][j].is_zero()) A[i][j] -= q * A[r][j];
                }
            ++r;
        }
    }
    return r;
}
}  // namespace
ZMat hnf_rows(ZMat A) {
    if (A.empty()) return {};
    size_t r = echelonize(A, A[0].size(), true);
    A.resize(r);
    return A;
}
ZMat left_kernel(const ZMat& A) {
    const size_t r = A.size();
    if (r == 0) return {};
    const size_t c = A[0].size();
    ZMat aug(r);
    for (size_t i = 0; i < r; ++i) {
        aug[i] = A[i];
        aug[i].resize(c + r, kZero);
        aug[i][c + i] = kOne;
    }
    size_t rk = echelonize(aug, c, false);
    ZMat K;
    for (size_t i = rk; i < r; ++i) {
        for (size_t j = 0; j < c; ++j)
            if (!aug[i][j].is_zero()) throw std::logic_error(ctx("left_kernel: residual"));
        K.emplace_back(aug[i].begin() + c, aug[i].end());
    }
    return hnf_rows(K);
}
ZMat restrict_to_eigenspace(const ZMat& T, const ZMat& A, const Z& lambda, ZMat* basis) {
    const size_t d = A.size();
    ZMat M = transpose(A);  // (A - lambda)^T
    for (size_t i = 0; i < d; ++i) M[i][i] -= lambda;
    ZMat K = left_kernel(M);  // rows v with (A - lambda) v = 0
    if (basis) *basis = K;
    QMat Kq;
    for (const auto& r : K) {
        std::vector<Q> row;
        for (const auto& x : r) row.push_back(Q(x));
        Kq.push_back(row);
    }
    std::vector<int> piv = Kq.empty() ? std::vector<int>{} : pivots_of(Kq);
    const size_t e = K.size();
    ZMat R(e, std::vector<Z>(e, kZero));
    for (size_t j = 0; j < e; ++j) {
        std::vector<Q> v(d, Q(0));
        for (size_t i = 0; i < d; ++i)
            for (size_t t = 0; t < d; ++t)
                if (!T[i][t].is_zero() && !K[j][t].is_zero()) v[i] += Q(T[i][t] * K[j][t]);
        auto y = solve_echelon(Kq, piv, v, "restrict_to_eigenspace");
        for (size_t i = 0; i < e; ++i) {
            if (!is_int(y[i])) throw std::logic_error(ctx("restrict_to_eigenspace: non-integral"));
            R[i][j] = y[i].num();
        }
    }
    return R;
}
std::string fnv_text(const ZMat& F) {
    std::string s;
    for (size_t i = 0; i < F.size(); ++i) {
        if (i) s += ';';
        for (size_t j = 0; j < F[i].size(); ++j) {
            if (j) s += ',';
            s += F[i][j].to_string();
        }
    }
    return s;
}
}  // namespace symz

// ===================================================================================================== quaternions, K
QB qb_mul(i64 a, i64 b, const QB& x, const QB& y) {
    const Q A(a), B(b), AB(a * b);
    QB z;
    z[0] = x[0] * y[0] + A * x[1] * y[1] + B * x[2] * y[2] - AB * x[3] * y[3];
    z[1] = x[0] * y[1] + x[1] * y[0] - B * x[2] * y[3] + B * x[3] * y[2];
    z[2] = x[0] * y[2] + x[2] * y[0] + A * x[1] * y[3] - A * x[3] * y[1];
    z[3] = x[0] * y[3] + x[3] * y[0] + x[1] * y[2] - x[2] * y[1];
    return z;
}
QB qb_conj(const QB& x) { return QB{x[0], -x[1], -x[2], -x[3]}; }
Q qb_nrd(i64 a, i64 b, const QB& x) {
    return x[0] * x[0] - Q(a) * x[1] * x[1] - Q(b) * x[2] * x[2] + Q(a * b) * x[3] * x[3];
}
Q qb_trd(const QB& x) { return Q(2) * x[0]; }
QB qb_from(const QElt& x) {
    QB q;
    Z den = Z::from_string(to_string128(x.den));
    for (int s = 0; s < 4; ++s) q[s] = Q(Z::from_string(to_string128(x.c[s])), den);
    return q;
}
std::array<std::array<KElt, 2>, 2> split(i64 /*a*/, i64 b, const QB& x) {
    std::array<std::array<KElt, 2>, 2> s;
    s[0][0] = KElt{x[0], x[1]};
    s[0][1] = KElt{Q(b) * x[2], Q(b) * x[3]};
    s[1][0] = KElt{x[2], -x[3]};
    s[1][1] = KElt{x[0], -x[1]};
    return s;
}
KMat rho_K(i64 a, i64 b, const QB& x, int n) {
    auto s = split(a, b, x);
    // column t: (s00 X + s10 Y)^{n-t} (s01 X + s11 Y)^t, as polynomials in Y (X = 1)
    KVec lin1{s[0][0], s[1][0]}, lin2{s[0][1], s[1][1]};
    std::vector<KVec> pw1{KVec{KElt{Q(1), Q(0)}}}, pw2{KVec{KElt{Q(1), Q(0)}}};
    for (int k = 0; k < n; ++k) {
        pw1.push_back(pmul(a, pw1.back(), lin1));
        pw2.push_back(pmul(a, pw2.back(), lin2));
    }
    KMat R(n + 1, std::vector<KElt>(n + 1));
    for (int t = 0; t <= n; ++t) {
        KVec col = pmul(a, pw1[n - t], pw2[t]);
        for (int u = 0; u <= n; ++u) R[u][t] = col[u];
    }
    return R;
}
KVec apply(i64 a, const KMat& R, const KVec& v) {
    KVec out(R.size(), KElt{Q(0), Q(0)});
    for (size_t t = 0; t < R.size(); ++t)
        for (size_t u = 0; u < v.size(); ++u)
            if (!kzero(v[u]) && !kzero(R[t][u])) out[t] = kadd(out[t], kmul(a, R[t][u], v[u]));
    return out;
}
KVec quad_form(i64 a, i64 b, const QB& x) {
    auto s = split(a, b, x);
    // Q_x = (X, Y) s(x) J (X, Y)^T, J = [[0, 1], [-1, 0]]:  -s01 X^2 + (s00 - s11) XY + s10 Y^2
    KElt m01{-s[0][1].r, -s[0][1].s};
    KElt mid{s[0][0].r - s[1][1].r, s[0][0].s - s[1][1].s};
    return KVec{m01, mid, s[1][0]};
}
KElt beta_n(i64 a, const KVec& P, const KVec& R, int n) {
    KElt acc{Q(0), Q(0)};
    for (int i = 0; i <= n; ++i) {
        if (kzero(P[i]) || kzero(R[n - i])) continue;
        KElt t = kmul(a, P[i], R[n - i]);
        Q f = Q((i % 2) ? -1 : 1) / Q(binom(n, i));
        acc = kadd(acc, KElt{t.r * f, t.s * f});
    }
    return acc;
}

// ===================================================================================================== the module
namespace {
// a Z-basis of (R^0)^# for an order R with Z-basis ob (standard coordinates)
std::array<QB, 3> dual_trace_zero(i64 a, i64 b, const std::array<QB, 4>& ob) {
    ZMat t(4, std::vector<Z>(1));
    for (int s = 0; s < 4; ++s) {
        Q tr = qb_trd(ob[s]);
        if (!is_int(tr)) throw std::logic_error(ctx("dual_trace_zero: trd not integral"));
        t[s][0] = tr.num();
    }
    ZMat K = symz::left_kernel(t);  // 3 rows
    if (K.size() != 3) throw std::logic_error(ctx("dual_trace_zero: rank"));
    std::array<QB, 3> x;
    for (int r = 0; r < 3; ++r) {
        x[r] = QB{Q(0), Q(0), Q(0), Q(0)};
        for (int s = 0; s < 4; ++s)
            for (int m = 0; m < 4; ++m) x[r][m] += Q(K[r][s]) * ob[s][m];
        if (!x[r][0].is_zero()) throw std::logic_error(ctx("dual_trace_zero: not trace zero"));
    }
    QMat G(3, std::vector<Q>(3));
    for (int r = 0; r < 3; ++r)
        for (int s = 0; s < 3; ++s) G[r][s] = qb_trd(qb_mul(a, b, x[r], x[s]));
    QMat Gi = qinverse(G);
    std::array<QB, 3> d;
    for (int r = 0; r < 3; ++r) {
        d[r] = QB{Q(0), Q(0), Q(0), Q(0)};
        for (int s = 0; s < 3; ++s)
            for (int m = 0; m < 4; ++m) d[r][m] += Gi[r][s] * x[s][m];
    }
    return d;
}

// all monomials Q_{d1}^{e1} Q_{d2}^{e2} Q_{d3}^{e3}, e1 + e2 + e3 = m, times scale
std::vector<KVec> lattice_generators(i64 a, i64 b, const std::array<QB, 3>& d, int m, const Q& scale) {
    std::array<std::vector<KVec>, 3> pw;
    for (int r = 0; r < 3; ++r) {
        pw[r].push_back(KVec{KElt{Q(1), Q(0)}});
        KVec q = quad_form(a, b, d[r]);
        for (int e = 1; e <= m; ++e) pw[r].push_back(pmul(a, pw[r].back(), q));
    }
    std::vector<KVec> out;
    for (int e1 = 0; e1 <= m; ++e1)
        for (int e2 = 0; e1 + e2 <= m; ++e2) {
            KVec p = pmul(a, pmul(a, pw[0][e1], pw[1][e2]), pw[2][m - e1 - e2]);
            for (auto& c : p) c = KElt{c.r * scale, c.s * scale};
            out.push_back(p);
        }
    return out;
}
}  // namespace

BrandtSym::BrandtSym(const ClassSet& C, int n, Options opt) : C_(C), n_(n), m_(n / 2) {
    if (n < 0) throw std::invalid_argument(ctx("n < 0"));
    const MaxOrder& O = C.order();
    const i64 A = a(), Bb = b();
    const int r = C.h();
    perm_.resize(r);
    for (int i = 0; i < r; ++i) perm_[i] = i;
    if (opt.canonical_order) perm_ = canonical_order_v2(C).perm;
    inv_perm_.assign(r, -1);
    for (int i = 0; i < r; ++i) inv_perm_[perm_[i]] = i;
    cl_.resize(r);
    for (int c = 0; c < r; ++c) {
        const ClassRep& rep = C.classes()[perm_[c]];
        SymClass& s = cl_[c];
        s.enum_index = perm_[c];
        s.I = rep.I;
        s.N = rep.N;
        s.gamma = rep.gamma;
        s.w = rep.gamma / 2;
        for (int t = 0; t < 4; ++t) s.order_basis[t] = qb_from(O.to_std(rep.RN.h[t], rep.N));
        Reduced R = lll_reduce(rep.RN, O.embedding(), O.gram());
        const i128 n2 = (i128)rep.N * rep.N;
        fp_enumerate(R, 2 * n2, [&](const i64* x, i128 v2) {
            if (v2 == 2 * n2) s.units.push_back(qb_from(O.to_std(combine(R, x), rep.N)));
            return true;
        });
        if ((int)s.units.size() != s.gamma) throw std::logic_error(ctx("unit enumeration != |Gamma|"));
        s.dual0 = dual_trace_zero(A, Bb, s.order_basis);
    }
    off_.assign(r + 1, 0);
    if (n % 2) {  // -1 in Gamma_c acts by -1: M = 0
        Bc_.assign(r, QMat{});
        return;
    }
    // ---- base lattice Lambda_O = Lambda'(O), N = 1
    {
        std::array<QB, 4> ob;
        for (int t = 0; t < 4; ++t) {
            Vec4 e{{0, 0, 0, 0}};
            e[t] = 1;
            ob[t] = qb_from(O.to_std(e));
        }
        auto gens = lattice_generators(A, Bb, dual_trace_zero(A, Bb, ob), m_, Q(1));
        QMat G;
        for (const auto& g : gens) G.push_back(real_of(g));
        Rreal_ = lattice_basis(G);
        if ((int)Rreal_.size() != n + 1) throw std::logic_error(ctx("base lattice rank != n+1"));
        Rpiv_ = pivots_of(Rreal_);
    }
    Hpiv_.resize(r);
    Zpiv_.resize(r);
    Bc_.resize(r);
    for (int c = 0; c < r; ++c) {
        SymClass& s = cl_[c];
        Q scale = Q(kOne, Z::pow(Z(s.N), (uint64_t)m_));
        auto gens = lattice_generators(A, Bb, s.dual0, m_, scale);
        QMat G;
        for (const auto& g : gens) G.push_back(base_coords(g));
        s.H = lattice_basis(G);
        if ((int)s.H.size() != n + 1) throw std::logic_error(ctx("class lattice rank != n+1"));
        Hpiv_[c] = pivots_of(s.H);
        // invariants: (A_u - 1) z = 0 for every unit u
        ZMat M(n + 1);
        for (const auto& u : s.units) {
            QMat Au = rho_class(c, u);
            for (int i = 0; i <= n; ++i)
                for (int j = 0; j <= n; ++j) {
                    Q v = Au[j][i] - Q(i == j ? 1 : 0);
                    if (!is_int(v)) throw std::logic_error(ctx("Gamma_c does not preserve Lambda_c"));
                    M[i].push_back(v.num());
                }
        }
        s.Zinv = symz::left_kernel(M);
        s.E.clear();
        s.EK.clear();
        for (const auto& z : s.Zinv) {
            std::vector<Q> y(n + 1, Q(0));
            for (int i = 0; i <= n; ++i)
                if (!z[i].is_zero())
                    for (int j = 0; j <= n; ++j) y[j] += Q(z[i]) * s.H[i][j];
            s.E.push_back(y);
            s.EK.push_back(base_vector(y));
        }
        if (!s.Zinv.empty()) {
            QMat Zq;
            for (const auto& z : s.Zinv) {
                std::vector<Q> row;
                for (const auto& x : z) row.push_back(Q(x));
                Zq.push_back(row);
            }
            Zpiv_[c] = pivots_of(Zq);
        }
        // Gram block N_c^n beta_n
        const int d = s.dim();
        Q Nn = Q(Z::pow(Z(s.N), (uint64_t)n));
        Bc_[c].assign(d, std::vector<Q>(d));
        for (int i = 0; i < d; ++i)
            for (int j = 0; j < d; ++j) {
                KElt v = beta_n(A, s.EK[i], s.EK[j], n);
                if (!v.s.is_zero()) throw std::logic_error(ctx("beta_n not rational on V_Q'"));
                Bc_[c][i][j] = v.r * Nn;
            }
        off_[c + 1] = off_[c] + d;
    }
    rank_ = off_[r];
}

std::vector<int> BrandtSym::gammas() const {
    std::vector<int> g;
    for (const auto& c : cl_) g.push_back(c.gamma);
    return g;
}
std::vector<int> BrandtSym::dims() const {
    std::vector<int> g;
    for (const auto& c : cl_) g.push_back(c.dim());
    return g;
}

std::vector<Q> BrandtSym::base_coords(const KVec& v) const {
    return solve_echelon(Rreal_, Rpiv_, real_of(v), "base_coords");
}
KVec BrandtSym::base_vector(const std::vector<Q>& y) const {
    std::vector<Q> x(2 * (n_ + 1), Q(0));
    for (size_t i = 0; i < y.size(); ++i)
        if (!y[i].is_zero())
            for (size_t j = 0; j < x.size(); ++j)
                if (!Rreal_[i][j].is_zero()) x[j] += y[i] * Rreal_[i][j];
    return kvec_of_real(x);
}
std::vector<Q> BrandtSym::class_coords(int c, const std::vector<Q>& y) const {
    return solve_echelon(cl_[c].H, Hpiv_[c], y, "class_coords");
}
std::vector<Q> BrandtSym::inv_coords(int c, const std::vector<Q>& z) const {
    QMat Zq;
    for (const auto& r : cl_[c].Zinv) {
        std::vector<Q> row;
        for (const auto& x : r) row.push_back(Q(x));
        Zq.push_back(row);
    }
    return solve_echelon(Zq, Zpiv_[c], z, "inv_coords");
}

QMat BrandtSym::rho_class(int c, const QB& g) const {
    KMat R = rho_K(a(), b(), g, n_);
    const SymClass& s = cl_[c];
    QMat M(n_ + 1, std::vector<Q>(n_ + 1));
    for (int j = 0; j <= n_; ++j) {
        auto z = class_coords(c, base_coords(apply(a(), R, base_vector(s.H[j]))));
        for (int i = 0; i <= n_; ++i) M[i][j] = z[i];
    }
    return M;
}
QMat BrandtSym::rho_base(const Vec4& gamma, i128 den) const {
    if (n_ % 2) throw std::invalid_argument(ctx("rho_base: odd n (no Q-form)"));
    KMat R = rho_K(a(), b(), qb_from(order().to_std(gamma, den)), n_);
    QMat M(n_ + 1, std::vector<Q>(n_ + 1));
    for (int j = 0; j <= n_; ++j) {
        std::vector<Q> e(n_ + 1, Q(0));
        e[j] = Q(1);
        auto y = base_coords(apply(a(), R, base_vector(e)));
        for (int i = 0; i <= n_; ++i) M[i][j] = y[i];
    }
    return M;
}
ZMat BrandtSym::rho_base_int(const Vec4& gamma) const {
    QMat M = rho_base(gamma);
    ZMat Zm(M.size());
    for (size_t i = 0; i < M.size(); ++i)
        for (const auto& x : M[i]) {
            if (!is_int(x)) throw std::logic_error(ctx("rho_base_int: not integral"));
            Zm[i].push_back(x.num());
        }
    return Zm;
}

BrandtSym::HeckeTerm BrandtSym::connect(int c, const Lat& J, i64 NJ) const {
    const MaxOrder& O = order();
    int e = C_.identify(J, NJ, true);
    if (e < 0) throw std::logic_error(ctx("connect: ideal in no class"));
    int cp = inv_perm_[e];
    const ClassRep& rp = C_.classes()[e];
    i128 nn = (i128)rp.N * NJ;
    Lat P = O.product(rp.Ic, J, nn * nn);
    Reduced R = lll_reduce(P, O.embedding(), O.gram());
    bool found = false;
    Vec4 delta{};
    fp_enumerate(R, 2 * nn, [&](const i64* x, i128 v2) {
        if (v2 == 2 * nn) {
            delta = combine(R, x);
            found = true;
            return false;
        }
        return true;
    });
    if (!found) throw std::logic_error(ctx("connect: no connecting element"));
    HeckeTerm t;
    t.src = cp;
    t.g = qb_from(O.to_std(O.conj(delta), cl_[c].N));
    return t;
}

std::vector<std::vector<BrandtSym::HeckeTerm>> BrandtSym::terms_T(i64 ell) const {
    if (D() % ell == 0 || !is_prime(ell)) throw std::invalid_argument(ctx("T: ell must be a prime not dividing D"));
    std::vector<std::vector<HeckeTerm>> out(h());
    for (int c = 0; c < h(); ++c) {
        const ClassRep& rep = C_.classes()[perm_[c]];
        for (const Lat& J : C_.neighbours(rep, ell)) out[c].push_back(connect(c, J, rep.N * ell));
    }
    return out;
}

Lat BrandtSym::two_sided_prime(i64 p) const {
    const MaxOrder& O = order();
    const i64 Dd = D();
    if (p != Dd && (Dd % p || !is_prime(p))) throw std::invalid_argument(ctx("Pi: p must be a prime divisor of D, or D"));
    // O^# = G^{-1} Z^4 (G = trd(e_s conj e_t)); P_D = D O^#
    QMat G(4, std::vector<Q>(4));
    for (int s = 0; s < 4; ++s)
        for (int t = 0; t < 4; ++t) G[s][t] = Q(Z::from_string(to_string128(O.gram().g[s][t])));
    QMat Gi = qinverse(G);
    std::vector<Vec4> gens;
    for (int s = 0; s < 4; ++s) {
        Vec4 v;
        for (int t = 0; t < 4; ++t) {
            Q x = Gi[s][t] * Q(Dd);
            if (!is_int(x)) throw std::logic_error(ctx("D O^# not integral"));
            v[t] = (i128)x.num().to_int64();
        }
        gens.push_back(v);
    }
    if (p != Dd)
        for (int s = 0; s < 4; ++s) {
            Vec4 v{{0, 0, 0, 0}};
            v[s] = p;
            gens.push_back(v);
        }
    Lat P = hnf(gens);
    if (P.index() != (i128)p * p) throw std::logic_error(ctx("two-sided prime has the wrong index"));
    return P;
}

std::vector<std::vector<BrandtSym::HeckeTerm>> BrandtSym::terms_Pi(i64 p) const {
    Lat P = two_sided_prime(p);
    const MaxOrder& O = order();
    std::vector<std::vector<HeckeTerm>> out(h());
    for (int c = 0; c < h(); ++c) {
        const ClassRep& rep = C_.classes()[perm_[c]];
        i128 nj = (i128)p * rep.N;
        Lat J = O.product(P, rep.I, nj * nj);
        out[c].push_back(connect(c, J, (i64)nj));
    }
    return out;
}

ZMat BrandtSym::assemble(const std::vector<std::vector<HeckeTerm>>& terms) const {
    ZMat T(rank_, std::vector<Z>(rank_, kZero));
    if (rank_ == 0) return T;
    for (int c = 0; c < h(); ++c) {
        // acc[c'][j] = sum over terms with src c' of the Lambda_c coordinates of rho(g) e_{c',j}
        std::vector<std::vector<std::vector<Q>>> acc(h());
        for (int cp = 0; cp < h(); ++cp) acc[cp].assign(cl_[cp].dim(), std::vector<Q>(n_ + 1, Q(0)));
        for (const auto& t : terms[c]) {
            const SymClass& sp = cl_[t.src];
            if (sp.dim() == 0 || cl_[c].dim() == 0) continue;
            KMat R = rho_K(a(), b(), t.g, n_);
            for (int j = 0; j < sp.dim(); ++j) {
                auto z = class_coords(c, base_coords(apply(a(), R, sp.EK[j])));
                for (int i = 0; i <= n_; ++i) {
                    if (!is_int(z[i])) throw std::logic_error(ctx("Hecke term not integral on the lattice"));
                    acc[t.src][j][i] += z[i];
                }
            }
        }
        for (int cp = 0; cp < h(); ++cp)
            for (int j = 0; j < cl_[cp].dim(); ++j) {
                auto y = inv_coords(c, acc[cp][j]);
                for (int i = 0; i < cl_[c].dim(); ++i) {
                    if (!is_int(y[i])) throw std::logic_error(ctx("Hecke image not integral on the invariants"));
                    T[off_[c] + i][off_[cp] + j] = y[i].num();
                }
            }
    }
    return T;
}

ZMat BrandtSym::T(i64 ell) const { return assemble(terms_T(ell)); }
ZMat BrandtSym::Pi(i64 p) const { return assemble(terms_Pi(p)); }

QMat BrandtSym::gram(Weight wt, bool divide) const {
    QMat G(rank_, std::vector<Q>(rank_, Q(0)));
    for (int c = 0; c < h(); ++c) {
        Q f = Q(wt == Weight::w ? cl_[c].w : cl_[c].gamma);
        if (divide) f = Q(1) / f;
        for (int i = 0; i < cl_[c].dim(); ++i)
            for (int j = 0; j < cl_[c].dim(); ++j) G[off_[c] + i][off_[c] + j] = Bc_[c][i][j] * f;
    }
    return G;
}
Z BrandtSym::denominator_lcm(const QMat& G) {
    Z s(1);
    for (const auto& r : G)
        for (const auto& x : r) s = lcm(s, x.den());
    return s;
}
ZMat BrandtSym::scale_to_int(const QMat& G, const Z& s) {
    ZMat out(G.size());
    for (size_t i = 0; i < G.size(); ++i)
        for (const auto& x : G[i]) {
            Q y = x * Q(s);
            if (!is_int(y)) throw std::logic_error(ctx("scale_to_int: not integral"));
            out[i].push_back(y.num());
        }
    return out;
}
bool BrandtSym::self_adjoint(const ZMat& A, Weight wt) const {
    QMat G = gram(wt, true);
    QMat Aq(A.size()), At(A.size());
    for (size_t i = 0; i < A.size(); ++i)
        for (size_t j = 0; j < A.size(); ++j) {
            Aq[i].push_back(Q(A[i][j]));
            At[i].push_back(Q(A[j][i]));
        }
    return symz::mul(At, G) == symz::mul(G, Aq);
}

}  // namespace hacs_jl
