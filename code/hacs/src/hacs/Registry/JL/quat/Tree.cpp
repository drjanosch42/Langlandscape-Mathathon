// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-7): tree quotients BG(U, q), Ribet and Ihara maps. See Tree.h.
#include "Tree.h"

#include <algorithm>
#include <chrono>
#include <numeric>
#include <random>
#include <set>
#include <stdexcept>

namespace hacs_jl {

// ================================================================ zlin
namespace zlin {
namespace {
void ext_gcd(const Z& a, const Z& b, Z& g, Z& s, Z& t) {
    Z r0 = a, r1 = b, s0 = 1, s1 = 0, t0 = 0, t1 = 1;
    while (!r1.is_zero()) {
        Z qq, r;
        Z::divmod(r0, r1, qq, r);
        r0 = r1;
        r1 = r;
        Z s2 = s0 - qq * s1;
        s0 = s1;
        s1 = s2;
        Z t2 = t0 - qq * t1;
        t0 = t1;
        t1 = t2;
    }
    if (r0.is_neg()) {
        r0 = -r0;
        s0 = -s0;
        t0 = -t0;
    }
    g = r0;
    s = s0;
    t = t0;
}
Z floor_div(const Z& a, const Z& b) {
    Z qq, r;
    Z::divmod(a, b, qq, r);
    if (!r.is_zero() && (r.is_neg() != b.is_neg())) qq -= 1;
    return qq;
}
// row echelon by unimodular row operations on columns [0, npiv); reduce above pivots. Returns the rank.
size_t echelon(ZM& M, size_t npiv, bool reduce) {
    size_t r = 0;
    const size_t m = M.size();
    for (size_t c = 0; c < npiv && r < m; ++c) {
        size_t piv = m;
        for (size_t i = r; i < m; ++i)
            if (!M[i][c].is_zero()) {
                piv = i;
                break;
            }
        if (piv == m) continue;
        std::swap(M[r], M[piv]);
        for (size_t i = r + 1; i < m; ++i) {
            if (M[i][c].is_zero()) continue;
            const Z a = M[r][c], b = M[i][c];
            Z g, s, t;
            ext_gcd(a, b, g, s, t);
            const Z ag = a / g, bg = b / g;
            for (size_t j = c; j < M[r].size(); ++j) {
                const Z x = M[r][j], y = M[i][j];
                M[r][j] = s * x + t * y;
                M[i][j] = ag * y - bg * x;
            }
        }
        if (M[r][c].is_neg())
            for (auto& x : M[r]) x = -x;
        if (reduce)
            for (size_t j = 0; j < r; ++j) {
                if (M[j][c].is_zero()) continue;
                const Z qq = floor_div(M[j][c], M[r][c]);
                if (qq.is_zero()) continue;
                for (size_t l = c; l < M[j].size(); ++l) M[j][l] -= qq * M[r][l];
            }
        ++r;
    }
    return r;
}
}  // namespace

ZM from_i64(const std::vector<std::vector<i64>>& A) {
    ZM out;
    out.reserve(A.size());
    for (const auto& r : A) {
        std::vector<Z> z;
        z.reserve(r.size());
        for (i64 x : r) z.emplace_back(x);
        out.push_back(std::move(z));
    }
    return out;
}

namespace {
// Phase 1 of smith(): sparse elimination on unit pivots (+-1). Each step clears the pivot's column by row operations
// and then drops the pivot row and column (the column operations clearing the pivot row touch nothing else), so it
// keeps the Smith invariants and contributes one invariant 1. Returns the number of unit pivots; A becomes the
// remaining dense matrix (rows without pivots, columns without pivots).
size_t unit_pivot_phase(ZM& A) {
    const size_t m = A.size(), n = m ? A[0].size() : 0;
    std::vector<std::map<size_t, Z>> rows(m);
    std::vector<std::set<size_t>> colrows(n);
    for (size_t i = 0; i < m; ++i)
        for (size_t j = 0; j < n; ++j)
            if (!A[i][j].is_zero()) {
                rows[i][j] = A[i][j];
                colrows[j].insert(i);
            }
    std::vector<char> row_dead(m, 0), col_dead(n, 0);
    size_t units = 0;
    const Z one(1), mone(-1);
    for (bool progress = true; progress;) {
        progress = false;
        for (size_t r = 0; r < m; ++r) {
            if (row_dead[r]) continue;
            // a unit entry of row r in the column with the fewest rows
            size_t c = n, best = SIZE_MAX;
            for (auto& [j, v] : rows[r])
                if ((v == one || v == mone) && colrows[j].size() < best) {
                    best = colrows[j].size();
                    c = j;
                }
            if (c == n) continue;
            const Z piv = rows[r][c];
            std::vector<size_t> others(colrows[c].begin(), colrows[c].end());
            for (size_t i : others) {
                if (i == r) continue;
                const Z f = rows[i][c] * piv;  // piv^{-1} = piv
                for (auto& [j, v] : rows[r]) {
                    Z nv = rows[i].count(j) ? rows[i][j] - f * v : -(f * v);
                    if (nv.is_zero()) {
                        rows[i].erase(j);
                        colrows[j].erase(i);
                    } else {
                        rows[i][j] = nv;
                        colrows[j].insert(i);
                    }
                }
            }
            for (auto& [j, v] : rows[r]) colrows[j].erase(r);
            rows[r].clear();
            row_dead[r] = 1;
            col_dead[c] = 1;
            ++units;
            progress = true;
        }
    }
    std::vector<size_t> rc;
    for (size_t j = 0; j < n; ++j)
        if (!col_dead[j]) rc.push_back(j);
    ZM R;
    for (size_t i = 0; i < m; ++i) {
        if (row_dead[i] || rows[i].empty()) continue;
        std::vector<Z> row(rc.size(), Z(0));
        for (size_t t = 0; t < rc.size(); ++t) {
            auto it = rows[i].find(rc[t]);
            if (it != rows[i].end()) row[t] = it->second;
        }
        R.push_back(std::move(row));
    }
    A = std::move(R);
    return units;
}
}  // namespace

std::vector<Z> smith(ZM A) {
    std::vector<Z> out;
    for (size_t u = unit_pivot_phase(A); u > 0; --u) out.push_back(Z(1));
    const size_t m = A.size(), n = m ? A[0].size() : 0;
    for (size_t t = 0; t < std::min(m, n); ++t) {
        for (;;) {
            size_t bi = m, bj = n;
            for (size_t i = t; i < m; ++i)
                for (size_t j = t; j < n; ++j)
                    if (!A[i][j].is_zero() && (bi == m || A[i][j].abs() < A[bi][bj].abs())) {
                        bi = i;
                        bj = j;
                    }
            if (bi == m) {
                std::sort(out.begin(), out.end());
                return out;
            }
            std::swap(A[t], A[bi]);
            for (size_t i = 0; i < m; ++i) std::swap(A[i][t], A[i][bj]);
            bool clean = true;
            const Z p = A[t][t];
            for (size_t i = t + 1; i < m; ++i) {
                if (A[i][t].is_zero()) continue;
                const Z qq = A[i][t] / p;
                if (!qq.is_zero())
                    for (size_t j = t; j < n; ++j) A[i][j] -= qq * A[t][j];
                if (!A[i][t].is_zero()) clean = false;
            }
            for (size_t j = t + 1; j < n; ++j) {
                if (A[t][j].is_zero()) continue;
                const Z qq = A[t][j] / p;
                if (!qq.is_zero())
                    for (size_t i = t; i < m; ++i) A[i][j] -= qq * A[i][t];
                if (!A[t][j].is_zero()) clean = false;
            }
            if (!clean) continue;
            bool divides = true;
            for (size_t i = t + 1; i < m && divides; ++i)
                for (size_t j = t + 1; j < n; ++j)
                    if (!(A[i][j] % p).is_zero()) {
                        for (size_t l = t; l < n; ++l) A[t][l] += A[i][l];
                        divides = false;
                        break;
                    }
            if (divides) break;
        }
        out.push_back(A[t][t].abs());
    }
    std::sort(out.begin(), out.end());
    return out;
}

ZM hermite_rows(ZM rows) {
    if (rows.empty()) return rows;
    const size_t r = echelon(rows, rows[0].size(), true);
    rows.resize(r);
    return rows;
}

ZM kernel_basis(const ZM& A, size_t n) {
    const size_t m = A.size();
    ZM W(n, std::vector<Z>(m + n, Z(0)));
    for (size_t j = 0; j < n; ++j) {
        for (size_t i = 0; i < m; ++i) W[j][i] = A[i][j];
        W[j][m + j] = 1;
    }
    const size_t r = echelon(W, m, false);
    ZM K;
    for (size_t j = r; j < n; ++j) K.emplace_back(W[j].begin() + (std::ptrdiff_t)m, W[j].end());
    return hermite_rows(K);
}

bool in_row_span(const ZM& H, std::vector<Z> v) {
    // H in row HNF (pivots strictly increasing, positive)
    for (const auto& row : H) {
        size_t c = 0;
        while (c < row.size() && row[c].is_zero()) ++c;
        if (c == row.size()) continue;
        for (size_t j = 0; j < c; ++j)
            if (!v[j].is_zero()) return false;
        Z qq, r;
        Z::divmod(v[c], row[c], qq, r);
        if (!r.is_zero()) return false;
        for (size_t j = c; j < v.size(); ++j) v[j] -= qq * row[j];
    }
    for (const auto& x : v)
        if (!x.is_zero()) return false;
    return true;
}

Z det(ZM A) {
    const size_t n = A.size();
    if (n == 0) return 1;
    Z prev = 1;
    int sign = 1;
    for (size_t k = 0; k + 1 < n; ++k) {
        if (A[k][k].is_zero()) {
            size_t p = k + 1;
            while (p < n && A[p][k].is_zero()) ++p;
            if (p == n) return 0;
            std::swap(A[k], A[p]);
            sign = -sign;
        }
        for (size_t i = k + 1; i < n; ++i)
            for (size_t j = k + 1; j < n; ++j) A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) / prev;
        prev = A[k][k];
    }
    return sign > 0 ? A[n - 1][n - 1] : -A[n - 1][n - 1];
}

ZM transpose(const ZM& A, size_t ncols) {
    ZM T(ncols, std::vector<Z>(A.size(), Z(0)));
    for (size_t i = 0; i < A.size(); ++i)
        for (size_t j = 0; j < ncols; ++j) T[j][i] = A[i][j];
    return T;
}

ZM mul(const ZM& A, const ZM& B, size_t bcols) {
    ZM C(A.size(), std::vector<Z>(bcols, Z(0)));
    for (size_t i = 0; i < A.size(); ++i)
        for (size_t k = 0; k < B.size(); ++k) {
            if (A[i][k].is_zero()) continue;
            for (size_t j = 0; j < bcols; ++j)
                if (!B[k][j].is_zero()) C[i][j] += A[i][k] * B[k][j];
        }
    return C;
}

Z prod(const std::vector<Z>& v) {
    Z p = 1;
    for (const auto& x : v) p *= x;
    return p;
}
}  // namespace zlin

// ================================================================ helpers
std::string TreeLevel::str() const {
    std::string s;
    if (N1 > 1) s += "U1(" + std::to_string(N1) + ")";
    if (N0 > 1) s += (s.empty() ? "" : "*") + std::string("U0(") + std::to_string(N0) + ")";
    return s.empty() ? "O^x" : s;
}

std::string frac_str(i128 num, i128 den) {
    if (den < 0) {
        num = -num;
        den = -den;
    }
    i128 g = gcd128(num, den);
    if (g > 1) {
        num /= g;
        den /= g;
    }
    return to_string128(num) + "/" + to_string128(den);
}

std::vector<Vec4> class_units(const ClassSet& C, int c) {
    const MaxOrder& O = C.order();
    const ClassRep& r = C.classes()[c];
    Reduced R = lll_reduce(r.RN, O.embedding(), O.gram());
    const i128 n2 = (i128)r.N * r.N;
    std::vector<Vec4> out;
    fp_enumerate(R, 2 * n2, [&](const i64* x, i128 v2) {
        if (v2 == 2 * n2) out.push_back(combine(R, x));
        return true;
    });
    if ((int)out.size() != r.gamma) throw std::logic_error("hacs_jl::class_units: unit count differs from |Gamma_c|");
    return out;
}

Vec4 find_mu(const ClassSet& C, const Lat& I, i64 NI, const Lat& J, i64 NJ) {
    const MaxOrder& O = C.order();
    const i128 n = (i128)NI * NJ;
    Lat P = O.product(O.conj(I), J, n * n);
    Reduced R = lll_reduce(P, O.embedding(), O.gram());
    Vec4 mu{};
    bool found = false;
    fp_enumerate(R, 2 * n, [&](const i64* x, i128 v2) {
        if (v2 == 2 * n) {
            mu = combine(R, x);
            found = true;
            return false;
        }
        return true;
    });
    if (!found) throw std::logic_error("hacs_jl::find_mu: J is not in the class of I");
    // check J = I mu / NI
    std::vector<Vec4> gens;
    for (int s = 0; s < 4; ++s) {
        Vec4 v = O.mul(I.h[s], mu);
        for (auto& t : v) t = exact_div(t, NI);
        gens.push_back(v);
    }
    if (!(hnf(gens, 1, (i128)NJ * NJ) == J)) throw std::logic_error("hacs_jl::find_mu: J != I mu / N_I");
    return mu;
}

namespace {
i64 modp(i128 a, i64 m) { return (i64)mod128(a, m); }

Vec4 mod_vec(const Vec4& x, i64 N) {
    Vec4 y;
    for (int s = 0; s < 4; ++s) y[s] = mod128(x[s], N);
    return y;
}

i64 prime_of_power(i64 N) {
    auto f = prime_factors(N);
    if (f.size() != 1) throw std::invalid_argument("hacs_jl::tree: level must be a prime power");
    return f[0];
}
}  // namespace

Vec4 idempotent_mod(const MaxOrder& O, i64 N) {
    const i64 l = prime_of_power(N);
    if (O.D() % l == 0) throw std::invalid_argument("hacs_jl::idempotent_mod: N must be prime to D");
    // x with nrd(x) = 0, trd(x) != 0 mod l (exists: O/l = M_2(F_l)); e = x / trd(x) mod l
    Vec4 e{};
    bool ok = false;
    const i64 B = std::min<i64>(std::max<i64>(2, l), 7);
    std::mt19937_64 rng(0x1dea7ULL ^ (u64)l);
    for (i64 it = 0; it < B * B * B * B + 400 * l && !ok; ++it) {
        {
            Vec4 x;
            if (it < B * B * B * B)
                x = Vec4{{it % B, (it / B) % B, (it / B / B) % B, (it / B / B / B) % B}};
            else
                x = Vec4{{(i64)(rng() % l), (i64)(rng() % l), (i64)(rng() % l), (i64)(rng() % l)}};
            {
                    if (mod128(O.nrd(x), l) != 0) continue;
                    i64 t = modp(O.trd(x), l);
                    if (t == 0) continue;
                    i64 ti = powmod(t, l - 2 > 0 ? l - 2 : 1, l);
                    if (l == 2) ti = 1;
                    for (int s = 0; s < 4; ++s) e[s] = mod128(x[s] * ti, l);
                    ok = true;
                }
        }
    }
    if (!ok) throw std::logic_error("hacs_jl::idempotent_mod: no idempotent mod l");
    // Hensel: e <- 3 e^2 - 2 e^3 (mod M^2)
    i128 M = l;
    while (M < N) {
        M = std::min<i128>(M * M, (i128)N);
        Vec4 e2 = mod_vec(O.mul(e, e), (i64)M);
        Vec4 e3 = mod_vec(O.mul(e2, e), (i64)M);
        for (int s = 0; s < 4; ++s) e[s] = mod128(3 * e2[s] - 2 * e3[s], M);
    }
    e = mod_vec(e, N);
    Vec4 e2 = mod_vec(O.mul(e, e), N);
    if (!(e2 == e)) throw std::logic_error("hacs_jl::idempotent_mod: Hensel lift failed");
    return e;
}

// ================================================================ the builder
namespace {

struct Builder {
    const ClassSet& C;
    const MaxOrder& O;
    i64 q;
    TreeLevel U;
    TreeQuotient T;
    Vec4 e1{}, e0{};
    i64 l1 = 0;
    // per class
    std::vector<std::vector<Lat>> qnb;
    std::vector<std::map<std::string, int>> qnb_idx;
    std::vector<std::pair<std::array<i64, 4>, std::array<i64, 4>>> basis1, basis0;  // e I_c basis mod N
    std::map<std::pair<int, int>, std::pair<int, Vec4>> trans;  // (c, jq) -> (c', mu)
    // vertex orbit lookup
    std::map<TreePoint, std::pair<int, int>> vloc;  // point -> (vertex, unit index moving point to rep)

    Builder(const ClassSet& C_, i64 q_, TreeLevel U_) : C(C_), O(C_.order()), q(q_), U(U_) {}

    std::array<i64, 4> coords_mod(int c, const Vec4& elt, i64 N) const {
        Vec4 y = coords_in(C.classes()[c].I, elt);
        std::array<i64, 4> r;
        for (int s = 0; s < 4; ++s) r[s] = modp(y[s], N);
        return r;
    }
    Vec4 lift(int c, const std::array<i64, 4>& y) const {
        const Lat& I = C.classes()[c].I;
        Vec4 v{{0, 0, 0, 0}};
        for (int s = 0; s < 4; ++s)
            if (y[s])
                for (int m = 0; m < 4; ++m) v[m] = add_chk(v[m], mul_chk(y[s], I.h[s][m]));
        return v;
    }
    std::array<i64, 4> norm_line(std::array<i64, 4> y) const {
        const i64 N = U.N0;
        int f = 0;
        while (f < 4 && y[f] == 0) ++f;
        if (f == 4) throw std::logic_error("hacs_jl::tree: zero line");
        i64 inv = powmod(y[f], N - 2, N);
        for (auto& t : y) t = modp((i128)t * inv, N);
        return y;
    }
    // x * (elt) / N_c for the right action (elt in I_c, x in conj(I_c) I_c)
    Vec4 rmul(int c, const Vec4& w, const Vec4& x) const {
        Vec4 z = O.mul(w, x);
        for (auto& t : z) t = exact_div(t, C.classes()[c].N);
        return z;
    }
    TreePoint act(const TreePoint& p, const Vec4& x) const {
        TreePoint r = p;
        const int c = p.c;
        if (U.N1 > 1) r.v = coords_mod(c, rmul(c, lift(c, p.v), x), U.N1);
        if (U.N0 > 1) r.l = norm_line(coords_mod(c, rmul(c, lift(c, p.l), x), U.N0));
        if (p.jq >= 0) {
            const Lat& J = qnb[c][p.jq];
            std::vector<Vec4> gens;
            for (int s = 0; s < 4; ++s) gens.push_back(rmul(c, J.h[s], x));
            const i128 NJ = (i128)q * C.classes()[c].N;
            Lat Jg = hnf(gens, 1, NJ * NJ);
            auto it = qnb_idx[c].find(Jg.key());
            if (it == qnb_idx[c].end()) throw std::logic_error("hacs_jl::tree: J gamma is not a q-neighbour");
            r.jq = it->second;
        }
        return r;
    }

    std::pair<std::array<i64, 4>, std::array<i64, 4>> e_basis(int c, const Vec4& e, i64 N) const {
        const i64 l = prime_of_power(N);
        const Lat& I = C.classes()[c].I;
        std::vector<std::array<i64, 4>> ys;
        for (int s = 0; s < 4; ++s) ys.push_back(coords_mod(c, O.mul(e, I.h[s]), N));
        auto nz = [&](const std::array<i64, 4>& y) {
            for (auto t : y)
                if (t % l) return true;
            return false;
        };
        auto indep = [&](const std::array<i64, 4>& a, const std::array<i64, 4>& b) {
            for (int i = 0; i < 4; ++i)
                for (int j = i + 1; j < 4; ++j)
                    if (mod128((i128)a[i] * b[j] - (i128)a[j] * b[i], l)) return true;
            return false;
        };
        for (size_t i = 0; i < ys.size(); ++i) {
            if (!nz(ys[i])) continue;
            for (size_t j = i + 1; j < ys.size(); ++j)
                if (indep(ys[i], ys[j])) return {ys[i], ys[j]};
        }
        throw std::logic_error("hacs_jl::tree: e I / N I is not free of rank 2");
    }

    std::vector<TreePoint> fibre(int c, bool edges) const {
        std::vector<std::array<i64, 4>> vs{{{0, 0, 0, 0}}}, ls{{{0, 0, 0, 0}}};
        if (U.N1 > 1) {
            vs.clear();
            const i64 N = U.N1;
            auto [b1, b2] = basis1[c];
            for (i64 a = 0; a < N; ++a)
                for (i64 b = 0; b < N; ++b) {
                    if (a % l1 == 0 && b % l1 == 0) continue;
                    std::array<i64, 4> y;
                    for (int s = 0; s < 4; ++s) y[s] = modp((i128)a * b1[s] + (i128)b * b2[s], N);
                    vs.push_back(y);
                }
        }
        if (U.N0 > 1) {
            ls.clear();
            const i64 N = U.N0;
            auto [b1, b2] = basis0[c];
            for (i64 t = 0; t <= N; ++t) {
                std::array<i64, 4> y;
                for (int s = 0; s < 4; ++s) y[s] = (t < N) ? modp((i128)b1[s] + (i128)t * b2[s], N) : b2[s];
                ls.push_back(norm_line(y));
            }
        }
        std::vector<TreePoint> out;
        const int nj = edges ? (int)q + 1 : 1;
        for (auto& v : vs)
            for (auto& l : ls)
                for (int j = 0; j < nj; ++j) {
                    TreePoint p;
                    p.c = c;
                    p.v = v;
                    p.l = l;
                    p.jq = edges ? j : -1;
                    out.push_back(p);
                }
        return out;
    }

    // orbits of Gamma_c on a fibre: (cells, point -> (cell index, unit index u with point * units[u] = rep))
    void orbits(int c, const std::vector<TreePoint>& pts, std::vector<TreeCell>& cells,
                std::map<TreePoint, std::pair<int, int>>* loc, std::vector<std::vector<TreePoint>>* members) {
        const auto& un = T.units[c];
        std::map<TreePoint, int> idx;
        for (size_t i = 0; i < pts.size(); ++i) idx[pts[i]] = (int)i;
        std::vector<int> seen(pts.size(), -1);
        // locate -1 (x = -N_c) among the units
        Vec4 minus{};
        for (int s = 0; s < 4; ++s) minus[s] = 0;
        minus[0] = -C.classes()[c].N;  // e_0 = 1
        for (size_t i = 0; i < pts.size(); ++i) {
            if (seen[i] >= 0) continue;
            TreeCell cell;
            cell.rep = pts[i];
            std::vector<TreePoint> orb;
            // rep * units[u] = image; the point image is moved to rep by units[u]^{-1}: we record, for each image,
            // an index u' with image * units[u'] = rep (the conjugate unit)
            for (size_t u = 0; u < un.size(); ++u) {
                TreePoint im = act(pts[i], un[u]);
                auto it = idx.find(im);
                if (it == idx.end()) throw std::logic_error("hacs_jl::tree: unit image outside the fibre");
                if (im == pts[i]) {
                    cell.stab_units.push_back((int)u);
                    if (un[u] == minus) cell.w = -1;  // marker: -1 fixes the point
                }
                if (seen[it->second] < 0) {
                    seen[it->second] = (int)cells.size();
                    orb.push_back(im);
                    if (loc) {
                        // find u' with im * units[u'] = rep: units[u'] = conj(units[u]) (as N gamma^{-1} = conj(N gamma)/N... )
                        Vec4 cj = O.conj(un[u]);
                        int found = -1;
                        for (size_t v = 0; v < un.size(); ++v)
                            if (un[v] == cj) found = (int)v;
                        if (found < 0) throw std::logic_error("hacs_jl::tree: inverse unit not in the list");
                        (*loc)[im] = {(int)cells.size(), found};
                    }
                }
            }
            cell.stab = (int)cell.stab_units.size();
            const bool m1 = (cell.w == -1);
            cell.w = m1 ? cell.stab / 2 : cell.stab;
            cell.orbit_size = (int)orb.size();
            if ((int)(cell.stab * orb.size()) != (int)un.size())
                throw std::logic_error("hacs_jl::tree: orbit-stabiliser failed");
            cells.push_back(cell);
            if (members) members->push_back(orb);
        }
    }

    // s1 of an edge point: (vertex index, EdgeMove partial)
    std::pair<int, EdgeMove> s1_of(const TreePoint& p) {
        const int c = p.c;
        auto key = std::make_pair(c, p.jq);
        auto it = trans.find(key);
        if (it == trans.end()) {
            const Lat& J = qnb[c][p.jq];
            const i64 NJ = q * C.classes()[c].N;
            int c1 = C.identify(J, NJ, true);
            if (c1 < 0) throw std::logic_error("hacs_jl::tree: q-neighbour in no class");
            Vec4 mu = find_mu(C, C.classes()[c1].I, C.classes()[c1].N, J, NJ);
            it = trans.emplace(key, std::make_pair(c1, mu)).first;
        }
        const int c1 = it->second.first;
        const Vec4& mu = it->second.second;
        const Vec4 cmu = O.conj(mu);
        TreePoint r;
        r.c = c1;
        if (U.N1 > 1) r.v = coords_mod(c1, rmul(c, lift(c, p.v), cmu), U.N1);
        if (U.N0 > 1) r.l = norm_line(coords_mod(c1, rmul(c, lift(c, p.l), cmu), U.N0));
        auto jt = vloc.find(r);
        if (jt == vloc.end()) throw std::logic_error("hacs_jl::tree: transported point outside the fibre");
        EdgeMove m;
        m.c1 = c1;
        m.mu = mu;
        m.unit1 = jt->second.second;
        return {jt->second.first, m};
    }

    std::pair<int, int> s0_of(const TreePoint& p) const {
        TreePoint r = p;
        r.jq = -1;
        auto it = vloc.find(r);
        if (it == vloc.end()) throw std::logic_error("hacs_jl::tree: s0 point outside the fibre");
        return it->second;
    }

    void run(bool check) {
        T.D = O.D();
        T.q = q;
        T.level = U;
        T.minus_one_in_U = U.N1 <= 2;
        T.h = C.h();
        if (O.D() % q == 0 || !is_prime(q)) throw std::invalid_argument("hacs_jl::tree: q must be a prime not dividing D");
        if (U.N1 > 1 && (std::gcd(U.N1, O.D() * q) != 1)) throw std::invalid_argument("hacs_jl::tree: gcd(N1, Dq) != 1");
        if (U.N0 > 1 && (!is_prime(U.N0) || std::gcd(U.N0, O.D() * q) != 1 || std::gcd(U.N0, U.N1) != 1))
            throw std::invalid_argument("hacs_jl::tree: N0 must be a prime prime to D q N1");
        if (U.N1 > 1) {
            l1 = prime_of_power(U.N1);
            e1 = idempotent_mod(O, U.N1);
        }
        if (U.N0 > 1) e0 = idempotent_mod(O, U.N0);
        const int h = C.h();
        for (int c = 0; c < h; ++c) {
            T.class_gamma.push_back(C.classes()[c].gamma);
            T.units.push_back(class_units(C, c));
            qnb.push_back(C.neighbours(C.classes()[c], q));
            std::map<std::string, int> m;
            for (size_t j = 0; j < qnb.back().size(); ++j) m[qnb.back()[j].key()] = (int)j;
            if ((i64)m.size() != q + 1) throw std::logic_error("hacs_jl::tree: q-neighbours not distinct");
            qnb_idx.push_back(m);
            basis1.push_back(U.N1 > 1 ? e_basis(c, e1, U.N1) : std::make_pair(std::array<i64, 4>{}, std::array<i64, 4>{}));
            basis0.push_back(U.N0 > 1 ? e_basis(c, e0, U.N0) : std::make_pair(std::array<i64, 4>{}, std::array<i64, 4>{}));
        }
        // vertices
        for (int c = 0; c < h; ++c) {
            auto pts = fibre(c, false);
            T.points_v += (long)pts.size();
            orbits(c, pts, T.V, &vloc, nullptr);
        }
        // edges
        for (int c = 0; c < h; ++c) {
            auto pts = fibre(c, true);
            T.points_e += (long)pts.size();
            std::vector<std::vector<TreePoint>> members;
            const size_t first = T.E.size();
            orbits(c, pts, T.E, nullptr, check ? &members : nullptr);
            for (size_t e = first; e < T.E.size(); ++e) {
                const TreePoint& y = T.E[e].rep;
                auto a = s0_of(y);
                auto b = s1_of(y);
                EdgeMove mv = b.second;
                mv.unit0 = a.second;
                T.s0.push_back(a.first);
                T.s1.push_back(b.first);
                T.moves.push_back(mv);
                if (check)
                    for (const auto& p : members[e - first]) {
                        if (s0_of(p).first != a.first) throw std::logic_error("hacs_jl::tree: s0 not constant on an orbit");
                        if (s1_of(p).first != b.first) throw std::logic_error("hacs_jl::tree: s1 not constant on an orbit");
                    }
            }
        }
        T.orbit_checks = check;
    }
};
}  // namespace

TreeQuotient build_tree(const ClassSet& C, i64 q, TreeLevel U, TreeOptions opt) {
    auto t0 = std::chrono::steady_clock::now();
    Builder b(C, q, U);
    b.run(opt.check_orbits);
    b.T.seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    return b.T;
}

// ================================================================ TreeQuotient accessors
std::vector<int> TreeQuotient::stab_v() const {
    std::vector<int> r;
    for (const auto& c : V) r.push_back(c.stab);
    return r;
}
std::vector<int> TreeQuotient::stab_e() const {
    std::vector<int> r;
    for (const auto& c : E) r.push_back(c.stab);
    return r;
}
std::vector<int> TreeQuotient::w_v() const {
    std::vector<int> r;
    for (const auto& c : V) r.push_back(c.w);
    return r;
}
std::vector<int> TreeQuotient::w_e() const {
    std::vector<int> r;
    for (const auto& c : E) r.push_back(c.w);
    return r;
}
int TreeQuotient::components() const {
    const int n = 2 * X();
    std::vector<int> par(n);
    std::iota(par.begin(), par.end(), 0);
    std::function<int(int)> f = [&](int a) { return par[a] == a ? a : par[a] = f(par[a]); };
    for (int e = 0; e < nE(); ++e) par[f(s0[e])] = f(X() + s1[e]);
    int k = 0;
    for (int i = 0; i < n; ++i) k += (f(i) == i);
    return k;
}
std::vector<std::vector<i64>> TreeQuotient::hecke() const {
    std::vector<std::vector<i64>> H(X(), std::vector<i64>(X(), 0));
    for (int e = 0; e < nE(); ++e) {
        if (V[s0[e]].stab % E[e].stab) throw std::logic_error("hacs_jl::tree: |Gamma_e| does not divide |Gamma_s0e|");
        H[s0[e]][s1[e]] += V[s0[e]].stab / E[e].stab;
    }
    return H;
}
std::vector<std::vector<i64>> TreeQuotient::hecke_prime() const {
    std::vector<std::vector<i64>> H(X(), std::vector<i64>(X(), 0));
    for (int e = 0; e < nE(); ++e) {
        if (V[s1[e]].w % E[e].w) throw std::logic_error("hacs_jl::tree: w_e does not divide w_s1e");
        H[s0[e]][s1[e]] += V[s1[e]].w / E[e].w;
    }
    return H;
}
std::vector<std::vector<i64>> TreeQuotient::adjacency() const {
    std::vector<std::vector<i64>> A(X(), std::vector<i64>(X(), 0));
    for (int e = 0; e < nE(); ++e) A[s0[e]][s1[e]] += 1;
    return A;
}

// ================================================================ weight 2
namespace tree2 {
ZM boundary(const TreeQuotient& T) {
    ZM M(2 * T.X(), std::vector<Z>(T.nE(), Z(0)));
    for (int e = 0; e < T.nE(); ++e) {
        M[T.s0[e]][e] -= 1;
        M[T.X() + T.s1[e]][e] += 1;
    }
    return M;
}
ZM pullback(const TreeQuotient& T, int j) {
    ZM M(T.nE(), std::vector<Z>(T.X(), Z(0)));
    for (int e = 0; e < T.nE(); ++e) M[e][j ? T.s1[e] : T.s0[e]] = 1;
    return M;
}
ZM pushforward(const TreeQuotient& T, int j) { return zlin::transpose(pullback(T, j), T.X()); }
ZM ihara(const TreeQuotient& T) {
    ZM M(T.nE(), std::vector<Z>(2 * T.X(), Z(0)));
    for (int e = 0; e < T.nE(); ++e) {
        M[e][T.s0[e]] += 1;
        M[e][T.X() + T.s1[e]] -= 1;
    }
    return M;
}
ZM alpha_alphadag(const TreeQuotient& T, bool weighted, int sign) {
    const int X = T.X(), n = 2 * X;
    ZM M(n, std::vector<Z>(n, Z(0)));
    for (int e = 0; e < T.nE(); ++e) {
        const int a = T.s0[e], b = T.s1[e];
        const i64 we = weighted ? T.E[e].w : 1;
        const int js[2] = {0, 1};
        const int ys[2] = {a, b};
        const int sy[2] = {-1, 1};
        for (int t = 0; t < 2; ++t) {
            const i64 wy = weighted ? T.V[ys[t]].w : 1;
            if (wy % we) throw std::logic_error("hacs_jl::alpha_alphadag: w_e does not divide w_x");
            const i64 cc = (wy / we) * sy[t];
            const int col = js[t] * X + ys[t];
            M[a][col] -= cc;
            M[X + b][col] += cc;
        }
    }
    if (sign == -1)
        for (int i = 0; i < n; ++i)
            for (int k = 0; k < n; ++k)
                if ((i < X) != (k < X)) M[i][k] = -M[i][k];
    return M;
}
ZM cycle_basis(const TreeQuotient& T) { return zlin::kernel_basis(boundary(T), (size_t)T.nE()); }

Phi phi_comb(const ZM& B, const std::vector<i64>& w, size_t nE) {
    Phi r;
    r.rank = (int)B.size();
    if (B.empty()) return r;
    ZM G(B.size(), std::vector<Z>(B.size(), Z(0)));
    for (size_t i = 0; i < B.size(); ++i)
        for (size_t j = 0; j < B.size(); ++j) {
            Z s = 0;
            for (size_t e = 0; e < nE; ++e)
                if (!B[i][e].is_zero() && !B[j][e].is_zero()) s += Z(w[e]) * B[i][e] * B[j][e];
            G[i][j] = s;
        }
    auto d = zlin::smith(G);
    if (d.size() != B.size()) throw std::logic_error("hacs_jl::phi_comb: Gram matrix singular");
    for (auto& x : d)
        if (x != Z(1)) r.divisors.push_back(x);
    r.order = zlin::prod(d);
    r.cyclic = r.divisors.size() <= 1;
    return r;
}

Phi phi_two_vertex(const std::vector<i64>& w) {
    const size_t n = w.size();
    // the two-vertex graph 0 -> 1, n edges: ker d = {a : sum a = 0}
    ZM d(2, std::vector<Z>(n, Z(0)));
    for (size_t e = 0; e < n; ++e) {
        d[0][e] = -1;
        d[1][e] = 1;
    }
    return phi_comb(zlin::kernel_basis(d, n), w, n);
}

std::vector<i64> integer_eigenvalues(const std::vector<std::vector<i64>>& H, i64 bound) {
    std::vector<i64> out;
    const size_t n = H.size();
    for (i64 lam = -bound; lam <= bound; ++lam) {
        ZM A = zlin::from_i64(H);
        for (size_t i = 0; i < n; ++i) A[i][i] -= Z(lam);
        if (zlin::det(A).is_zero()) out.push_back(lam);
    }
    return out;
}

std::vector<int> elem_div_vals(const ZM& A, i64 p, int m) {
    std::vector<int> out;
    if (A.empty() || A[0].empty()) return out;
    for (const auto& d : zlin::smith(A)) {
        int v = (int)d.valuation((uint32_t)p);
        if (v < m) out.push_back(v);
    }
    std::sort(out.begin(), out.end());
    return out;
}
}  // namespace tree2

}  // namespace hacs_jl
