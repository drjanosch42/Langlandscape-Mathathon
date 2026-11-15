// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
#include "Lattice.h"

#include <algorithm>
#include <cmath>

namespace hacs_jl {

i128 Lat::index() const {
    i128 d = 1;
    for (int c = 0; c < 4; ++c) d = mul_chk(d, h[c][c]);
    return d;
}

std::string Lat::key() const {
    std::string s = to_string128(den) + "|";
    bool first = true;
    for (int c = 0; c < 4; ++c)
        for (int m = 0; m <= c; ++m) {
            if (!first) s += ",";
            first = false;
            s += to_string128(h[c][m]);
        }
    return s;
}

static void sub_mult(Vec4& w, i128 q, const Vec4& p, int upto, i128 modulus) {
    for (int m = 0; m <= upto; ++m) {
        w[m] = add_chk(w[m], -mul_chk(q, p[m]));
        if (modulus) w[m] = mod128(w[m], modulus);
    }
}

Lat hnf(const std::vector<Vec4>& gens, i128 den, i128 modulus) {
    if (den <= 0) throw std::invalid_argument("hacs_jl::hnf: den must be positive");
    std::vector<Vec4> W;
    W.reserve(gens.size() + 4);
    for (auto g : gens) {
        if (modulus)
            for (auto& v : g) v = mod128(v, modulus);
        W.push_back(g);
    }
    Lat L;
    L.den = den;
    for (int c = 3; c >= 0; --c) {
        if (modulus) {
            Vec4 e{{0, 0, 0, 0}};
            e[c] = modulus;
            W.push_back(e);
        }
        for (;;) {
            int piv = -1;
            for (int i = 0; i < (int)W.size(); ++i) {
                if (W[i][c] == 0) continue;
                if (piv < 0) piv = i;
                else {
                    i128 a = W[i][c] < 0 ? -W[i][c] : W[i][c];
                    i128 b = W[piv][c] < 0 ? -W[piv][c] : W[piv][c];
                    if (a < b) piv = i;
                }
            }
            if (piv < 0) throw std::invalid_argument("hacs_jl::hnf: lattice is not of full rank");
            bool other = false;
            for (int i = 0; i < (int)W.size(); ++i) {
                if (i == piv || W[i][c] == 0) continue;
                i128 q = floordiv128(W[i][c], W[piv][c]);
                sub_mult(W[i], q, W[piv], c, 0);
                if (modulus)
                    for (int m = 0; m < c; ++m) W[i][m] = mod128(W[i][m], modulus);
                if (W[i][c] != 0) other = true;
            }
            if (!other) {
                Vec4 p = W[piv];
                if (p[c] < 0)
                    for (auto& v : p) v = -v;
                if (modulus)
                    for (int m = 0; m < c; ++m) p[m] = mod128(p[m], modulus);
                L.h[c] = p;
                W.erase(W.begin() + piv);
                break;
            }
        }
        // drop zero vectors
        W.erase(std::remove_if(W.begin(), W.end(),
                               [](const Vec4& w) { return w[0] == 0 && w[1] == 0 && w[2] == 0 && w[3] == 0; }),
                W.end());
    }
    for (int k = 1; k < 4; ++k)
        for (int m = k - 1; m >= 0; --m) {
            i128 q = floordiv128(L.h[k][m], L.h[m][m]);
            if (q) sub_mult(L.h[k], q, L.h[m], m, 0);
        }
    if (modulus && L.index() != modulus)
        throw std::logic_error("hacs_jl::hnf: modular HNF index mismatch (modulus is not the lattice index)");
    i128 g = L.den;
    for (auto& r : L.h)
        for (auto v : r) g = gcd128(g, v);
    if (g > 1) {
        L.den /= g;
        for (auto& r : L.h)
            for (auto& v : r) v /= g;
    }
    return L;
}

Lat lat_sum(const Lat& A, const Lat& B) {
    i128 l = mul_chk(A.den / gcd128(A.den, B.den), B.den);
    std::vector<Vec4> gens;
    for (auto r : A.h) {
        for (auto& v : r) v = mul_chk(v, l / A.den);
        gens.push_back(r);
    }
    for (auto r : B.h) {
        for (auto& v : r) v = mul_chk(v, l / B.den);
        gens.push_back(r);
    }
    return hnf(gens, l);
}

static i128 det3(const std::array<Vec4, 4>& M, int skipr, int skipc) {
    int r[3], c[3], nr = 0, nc = 0;
    for (int i = 0; i < 4; ++i) {
        if (i != skipr) r[nr++] = i;
        if (i != skipc) c[nc++] = i;
    }
    auto e = [&](int i, int j) { return M[r[i]][c[j]]; };
    i128 t1 = mul_chk(e(0, 0), add_chk(mul_chk(e(1, 1), e(2, 2)), -mul_chk(e(1, 2), e(2, 1))));
    i128 t2 = mul_chk(e(0, 1), add_chk(mul_chk(e(1, 0), e(2, 2)), -mul_chk(e(1, 2), e(2, 0))));
    i128 t3 = mul_chk(e(0, 2), add_chk(mul_chk(e(1, 0), e(2, 1)), -mul_chk(e(1, 1), e(2, 0))));
    return add_chk(add_chk(t1, -t2), t3);
}

Lat dual(const Lat& L) {
    // rows of L are h_s / den; dual basis rows = den * (H^{-1})^T = den * Cof(H) / det(H)
    i128 det = L.index();
    std::vector<Vec4> gens(4);
    for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 4; ++j) {
            i128 cof = det3(L.h, i, j);
            if ((i + j) % 2) cof = -cof;
            gens[i][j] = mul_chk(cof, L.den);
        }
    return hnf(gens, det);
}

Lat intersect(const Lat& A, const Lat& B) { return dual(lat_sum(dual(A), dual(B))); }

static bool coords_try(const Lat& L, Vec4 v, Vec4& y) {
    for (int c = 3; c >= 0; --c) {
        if (v[c] % L.h[c][c] != 0) return false;
        y[c] = v[c] / L.h[c][c];
        if (y[c]) sub_mult(v, y[c], L.h[c], c, 0);
    }
    return true;
}

Vec4 coords_in(const Lat& L, const Vec4& v) {
    if (L.den != 1) throw std::invalid_argument("hacs_jl::coords_in: den must be 1");
    Vec4 y;
    if (!coords_try(L, v, y)) throw std::logic_error("hacs_jl::coords_in: vector not in lattice");
    return y;
}

bool contains(const Lat& L, const Vec4& v) {
    Vec4 w, y;
    for (int m = 0; m < 4; ++m) w[m] = mul_chk(v[m], L.den);
    return coords_try(L, w, y);
}

bool sublattice(const Lat& A, const Lat& B) {
    for (const auto& r : A.h) {
        Vec4 w, y;
        for (int m = 0; m < 4; ++m) {
            i128 t = mul_chk(r[m], B.den);
            if (t % A.den) return false;
            w[m] = t / A.den;
        }
        if (!coords_try(B, w, y)) return false;
    }
    return true;
}

// ---------------------------------------------------------------- LLL
i128 qform(const Gram4& G, const Vec4& x) {
    i128 s = 0;
    for (int i = 0; i < 4; ++i) {
        if (!x[i]) continue;
        i128 t = 0;
        for (int j = 0; j < 4; ++j) t = add_chk(t, mul_chk(G.g[i][j], x[j]));
        s = add_chk(s, mul_chk(x[i], t));
    }
    return s;
}

static i128 bilin(const Gram4& G, const Vec4& x, const Vec4& y) {
    i128 s = 0;
    for (int i = 0; i < 4; ++i) {
        if (!x[i]) continue;
        i128 t = 0;
        for (int j = 0; j < 4; ++j) t = add_chk(t, mul_chk(G.g[i][j], y[j]));
        s = add_chk(s, mul_chk(x[i], t));
    }
    return s;
}

using LD = long double;

static void real_image(const Embedding& E, const Vec4& x, LD out[4]) {
    for (int m = 0; m < 4; ++m) out[m] = 0;
    for (int s = 0; s < 4; ++s) {
        if (!x[s]) continue;
        LD xs = (LD)x[s];
        for (int m = 0; m < 4; ++m) out[m] += xs * E.v[s][m];
    }
}

static void gso(const Embedding& E, const std::array<Vec4, 4>& b, LD mu[4][4], LD Bn[4]) {
    LD v[4][4], bs[4][4];
    for (int i = 0; i < 4; ++i) real_image(E, b[i], v[i]);
    for (int i = 0; i < 4; ++i) {
        for (int m = 0; m < 4; ++m) bs[i][m] = v[i][m];
        for (int j = 0; j < i; ++j) {
            // modified Gram-Schmidt: project the running vector
            LD d = 0;
            for (int m = 0; m < 4; ++m) d += bs[i][m] * bs[j][m];
            LD mij = Bn[j] > 0 ? d / Bn[j] : 0;
            // mu w.r.t. the original vector (classical) differs from MGS only by rounding; use the MGS value
            mu[i][j] = mij;
            for (int m = 0; m < 4; ++m) bs[i][m] -= mij * bs[j][m];
        }
        LD n = 0;
        for (int m = 0; m < 4; ++m) n += bs[i][m] * bs[i][m];
        Bn[i] = n;
    }
}

static i128 round_ld(LD x) {
    LD r = roundl(x);
    if (fabsl(r) > 1.0e30L) throw std::overflow_error("hacs_jl::lll: coefficient too large");
    // exact for |r| < 2^64; beyond that a nearby integer is still a valid (if suboptimal) reduction step
    bool neg = r < 0;
    LD a = neg ? -r : r;
    unsigned __int128 hi = (unsigned __int128)(a / 18446744073709551616.0L);
    LD rem = a - (LD)hi * 18446744073709551616.0L;
    unsigned __int128 u = (hi << 64) + (unsigned __int128)(uint64_t)rem;
    return neg ? -(i128)u : (i128)u;
}

Reduced lll_reduce(const Lat& L, const Embedding& E, const Gram4& G0) {
    if (L.den != 1) throw std::invalid_argument("hacs_jl::lll_reduce: den must be 1");
    Reduced R;
    R.b = L.h;
    LD mu[4][4], Bn[4];
    const LD delta = 0.99L;
    int k = 1;
    long iter = 0;
    while (k < 4) {
        if (++iter > 200000) throw std::runtime_error("hacs_jl::lll_reduce: no convergence");
        gso(E, R.b, mu, Bn);
        bool changed = false;
        for (int j = k - 1; j >= 0; --j) {
            if (fabsl(mu[k][j]) <= 0.5L) continue;
            i128 q = round_ld(mu[k][j]);
            if (!q) continue;
            sub_mult(R.b[k], q, R.b[j], 3, 0);
            for (int i = 0; i < j; ++i) mu[k][i] -= (LD)q * mu[j][i];
            mu[k][j] -= (LD)q;
            changed = true;
        }
        if (changed) gso(E, R.b, mu, Bn);
        if (Bn[k] < (delta - mu[k][k - 1] * mu[k][k - 1]) * Bn[k - 1]) {
            std::swap(R.b[k], R.b[k - 1]);
            k = std::max(1, k - 1);
        } else {
            ++k;
        }
    }
    for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 4; ++j) R.G.g[i][j] = bilin(G0, R.b[i], R.b[j]);
    // Cholesky (Cohen, Alg. 2.7.6 layout): q(x) = sum_i q_ii (x_i + sum_{j>i} q_ij x_j)^2
    LD a[4][4];
    for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 4; ++j) a[i][j] = (LD)R.G.g[i][j];
    for (int i = 0; i < 4; ++i) {
        if (!(a[i][i] > 0)) throw std::runtime_error("hacs_jl::lll_reduce: form not positive definite");
        for (int j = i + 1; j < 4; ++j) R.chol[i][j] = a[i][j] / a[i][i];
        for (int k2 = i + 1; k2 < 4; ++k2)
            for (int l = k2; l < 4; ++l) a[k2][l] -= R.chol[i][k2] * a[i][i] * R.chol[i][l];
        R.chol[i][i] = a[i][i];
    }
    return R;
}

Vec4 combine(const Reduced& R, const i64* x) {
    Vec4 v{{0, 0, 0, 0}};
    for (int s = 0; s < 4; ++s)
        if (x[s])
            for (int m = 0; m < 4; ++m) v[m] = add_chk(v[m], mul_chk((i128)x[s], R.b[s][m]));
    return v;
}

namespace {
struct Enum {
    const Reduced& R;
    i128 bound2;
    const std::function<bool(const i64*, i128)>& cb;
    i64 x[4];
    bool stopped = false;

    i128 exact_val() const {
        i128 s = 0;
        for (int i = 0; i < 4; ++i) {
            if (!x[i]) continue;
            i128 t = 0;
            for (int j = 0; j < 4; ++j) t += R.G.g[i][j] * (i128)x[j];
            s += (i128)x[i] * t;
        }
        return s;
    }
    void rec(int i, LD T) {
        LD c = 0;
        for (int j = i + 1; j < 4; ++j) c -= R.chol[i][j] * (LD)x[j];
        LD qii = R.chol[i][i];
        LD r = sqrtl((T > 0 ? T : 0) / qii);
        LD eps = 1e-9L * (1 + fabsl(c) + r);
        i64 lo = (i64)ceill(c - r - eps), hi = (i64)floorl(c + r + eps);
        for (i64 xi = lo; xi <= hi && !stopped; ++xi) {
            x[i] = xi;
            LD d = (LD)xi - c;
            LD t = T - qii * d * d;
            if (i == 0) {
                if (x[0] == 0 && x[1] == 0 && x[2] == 0 && x[3] == 0) continue;
                i128 v = exact_val();
                if (v <= bound2 && !cb(x, v)) stopped = true;
            } else {
                rec(i - 1, t);
            }
        }
        x[i] = 0;
    }
};
}  // namespace

bool fp_enumerate(const Reduced& R, i128 bound2, const std::function<bool(const i64*, i128)>& cb) {
    if (bound2 <= 0) return true;
    Enum e{R, bound2, cb, {0, 0, 0, 0}};
    LD T = (LD)bound2;
    T += T * 1e-12L + 1e-6L;
    e.rec(3, T);
    return !e.stopped;
}

std::vector<u64> count_values(const Reduced& R, i128 scale, i64 X) {
    std::vector<u64> cnt(X + 1, 0);
    fp_enumerate(R, mul_chk(2 * scale, X), [&](const i64*, i128 v2) {
        if (v2 % 2) throw std::logic_error("hacs_jl::count_values: odd value of 2*nrd");
        i128 n = v2 / 2;
        if (n % scale) throw std::logic_error("hacs_jl::count_values: nrd not divisible by the normalisation");
        cnt[(size_t)(n / scale)]++;
        return true;
    });
    return cnt;
}

}  // namespace hacs_jl
