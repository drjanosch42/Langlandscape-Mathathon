// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// jl_eta_def (WP HJ-8-def, Lane C): eta^B natively -- the definite side of the integral JL defect comparison.
// Standalone tool (not linked into hacs; it only links the library sources, unchanged).
//
// Definitions (= code/python/langlandscape/defect/gram.py, S06-C5; results s06/T5_def.json):
//   * M = BrandtSym(C, n) (HJ-4a; the intrinsic lattice, = Sym^n(Z_p^2) at p !| q), level O^x of B_q, n = k - 2 even;
//   * G_w = (+)_x w_x^{-1} <,>_V and G_Gamma = (+)_x |Gamma_x|^{-1} <,>_V  (BrandtSym::gram(Weight::w | gamma));
//   * a generic T = sum c_l T_l (l in {2,3,5,7,11} \ {q}, the coefficient choices of gram.py) with squarefree charpoly chi;
//   * orbits = Q_p-irreducible factors phi of chi. Computed as: chi = prod f_i over Z (nf::factor_monic_over_z), then for
//     each f_i its mod-p factorisation f_i = prod g^e (Cantor-Zassenhaus) and the Hensel lift of the coprime split; when
//     e = 1 the lift is the Q_p-factor phi with residue g (degree deg g); e > 1 is reported as an unresolved union;
//   * A_phi = ker phi(T) cap M (x) Z_p (saturated, p-adic elimination mod p^R), vp_det_gram_* = v_p det(A^T G A);
//   * blocks (= the maximal ideals m) = orbits with the same residual eigensystem (the irreducible residual factor of the
//     charpoly of every T_l on A_phi); old_congruent: the residual eigenvalues equal a_l(g) mod p for the level-one
//     eigenform g of weight k (dim S_k(1) = 1); vp_level_raising = v_p(a_q(g)^2 - q^{k-2}(q+1)^2);
//   * for deg phi = 1, v_p(eta^B) = vp_det_gram_w (if:s04-etaB, d = 1); for deg phi > 1 the number is the Z_p-length of
//     the orbit's congruence module (Hsieh Rem. 7.3). The pairing is perfect only for p > n (and p !| w_x); otherwise
//     the values are still computed but flagged (pairing_perfect = false).
//
//   jl_eta_def --suite t5 | h3 | census | shift [--only q,k,p] [--R 40] [--qmax 50] [--kmax 20] [--pmax 200] [--out FILE]
#include "../BrandtSym.h"
#include "../../../../NumberField/IntPolyFactor.h"

#include <chrono>
#include <cstdio>
#include <fstream>
#include <functional>
#include <iostream>
#include <map>
#include <memory>
#include <random>
#include <set>

using namespace hacs_jl;

namespace {
using ZPoly = std::vector<i64>;  // mod p, constant first, normalised (no trailing zeros)

// ================================================================ JSON
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

// ================================================================ polynomials mod p
i64 md(i64 a, i64 p) { return ((a % p) + p) % p; }
i64 pw(i64 b, i64 e, i64 p) {
    i64 r = 1;
    b = md(b, p);
    while (e) {
        if (e & 1) r = (i64)((i128)r * b % p);
        b = (i64)((i128)b * b % p);
        e >>= 1;
    }
    return r;
}
i64 inv(i64 a, i64 p) { return pw(a, p - 2, p); }
void trim(ZPoly& f) {
    while (!f.empty() && f.back() == 0) f.pop_back();
}
ZPoly pmul(const ZPoly& a, const ZPoly& b, i64 p) {
    if (a.empty() || b.empty()) return {};
    ZPoly c(a.size() + b.size() - 1, 0);
    for (size_t i = 0; i < a.size(); ++i)
        if (a[i])
            for (size_t j = 0; j < b.size(); ++j) c[i + j] = (i64)((c[i + j] + (i128)a[i] * b[j]) % p);
    trim(c);
    return c;
}
void pdivmod(ZPoly a, const ZPoly& b, i64 p, ZPoly& q, ZPoly& r) {
    trim(a);
    q.assign(a.size() >= b.size() ? a.size() - b.size() + 1 : 0, 0);
    const i64 ib = inv(b.back(), p);
    while (a.size() >= b.size() && !a.empty()) {
        const size_t s = a.size() - b.size();
        const i64 c = (i64)((i128)a.back() * ib % p);
        q[s] = c;
        for (size_t i = 0; i < b.size(); ++i) a[s + i] = md(a[s + i] - (i64)((i128)c * b[i] % p), p);
        trim(a);
    }
    r = a;
    trim(q);
}
ZPoly pmod(const ZPoly& a, const ZPoly& b, i64 p) {
    ZPoly q, r;
    pdivmod(a, b, p, q, r);
    return r;
}
ZPoly pdiv(const ZPoly& a, const ZPoly& b, i64 p) {
    ZPoly q, r;
    pdivmod(a, b, p, q, r);
    if (!r.empty()) throw std::logic_error("pdiv: not exact");
    return q;
}
ZPoly monic(ZPoly f, i64 p) {
    trim(f);
    if (f.empty()) return f;
    const i64 iv = inv(f.back(), p);
    for (auto& x : f) x = (i64)((i128)x * iv % p);
    return f;
}
ZPoly pgcd(ZPoly a, ZPoly b, i64 p) {
    trim(a);
    trim(b);
    while (!b.empty()) {
        ZPoly r = pmod(a, b, p);
        a = b;
        b = r;
    }
    return monic(a, p);
}
ZPoly deriv(const ZPoly& f, i64 p) {
    ZPoly d;
    for (size_t i = 1; i < f.size(); ++i) d.push_back((i64)((i128)f[i] * (i64)(i % p) % p));
    trim(d);
    return d;
}
ZPoly powmod_poly(ZPoly b, i64 e, const ZPoly& f, i64 p) {
    ZPoly r{1};
    b = pmod(b, f, p);
    while (e) {
        if (e & 1) r = pmod(pmul(r, b, p), f, p);
        b = pmod(pmul(b, b, p), f, p);
        e >>= 1;
    }
    return r;
}
ZPoly psub(ZPoly a, const ZPoly& b, i64 p) {
    if (a.size() < b.size()) a.resize(b.size(), 0);
    for (size_t i = 0; i < b.size(); ++i) a[i] = md(a[i] - b[i], p);
    trim(a);
    return a;
}
// equal-degree splitting (Cantor-Zassenhaus), f squarefree, all factors of degree d, p odd
void edf(const ZPoly& f, int d, i64 p, std::vector<ZPoly>& out, std::mt19937_64& rng) {
    const int n = (int)f.size() - 1;
    if (n == d) {
        out.push_back(f);
        return;
    }
    i128 e128 = 1;
    for (int i = 0; i < d; ++i) e128 *= p;
    e128 = (e128 - 1) / 2;
    for (;;) {
        ZPoly a(n, 0);
        for (auto& x : a) x = (i64)(rng() % (u64)p);
        trim(a);
        if (a.empty()) continue;
        // a^((p^d-1)/2) mod f, exponent may exceed i64: square-and-multiply on i128
        ZPoly r{1}, b = pmod(a, f, p);
        for (i128 e = e128; e > 0; e >>= 1) {
            if (e & 1) r = pmod(pmul(r, b, p), f, p);
            b = pmod(pmul(b, b, p), f, p);
        }
        ZPoly g = pgcd(f, psub(r, ZPoly{1}, p), p);
        if (g.size() > 1 && g.size() < f.size()) {
            edf(g, d, p, out, rng);
            edf(pdiv(f, g, p), d, p, out, rng);
            return;
        }
    }
}
// squarefree f -> irreducible factors
void factor_sqfree(ZPoly f, i64 p, std::vector<ZPoly>& out, std::mt19937_64& rng) {
    f = monic(f, p);
    ZPoly h{0, 1};  // x
    for (int d = 1; 2 * d <= (int)f.size() - 1; ++d) {
        h = powmod_poly(h, p, f, p);
        ZPoly g = pgcd(f, psub(h, ZPoly{0, 1}, p), p);
        if (g.size() > 1) {
            edf(g, d, p, out, rng);
            f = pdiv(f, g, p);
            h = pmod(h, f, p);
        }
    }
    if (f.size() > 1) out.push_back(monic(f, p));
}
// f -> list of (irreducible g, multiplicity)
std::vector<std::pair<ZPoly, int>> factor_mod_p(ZPoly f, i64 p, std::mt19937_64& rng) {
    std::vector<std::pair<ZPoly, int>> res;
    f = monic(f, p);
    std::function<void(ZPoly, int)> sff = [&](ZPoly g, int mult) {
        if (g.size() <= 1) return;
        ZPoly dg = deriv(g, p);
        if (dg.empty()) {  // g = h(x^p)
            ZPoly h;
            for (size_t i = 0; i < g.size(); i += (size_t)p) h.push_back(g[i]);
            sff(h, mult * (int)p);
            return;
        }
        ZPoly c = pgcd(g, dg, p), w = pdiv(g, c, p);
        int i = 1;
        while (w.size() > 1) {
            ZPoly y = pgcd(w, c, p), z = pdiv(w, y, p);
            if (z.size() > 1) {
                std::vector<ZPoly> irr;
                factor_sqfree(z, p, irr, rng);
                for (auto& u : irr) res.push_back({u, i * mult});
            }
            ++i;
            w = y;
            c = pdiv(c, y, p);
        }
        if (c.size() > 1) {
            ZPoly h;
            for (size_t j = 0; j < c.size(); j += (size_t)p) h.push_back(c[j]);
            sff(h, mult * (int)p);
        }
    };
    sff(f, 1);
    // merge equal factors
    std::map<ZPoly, int> mm;
    for (auto& [g, e] : res) mm[g] += e;
    res.assign(mm.begin(), mm.end());
    return res;
}
std::string ptext(const ZPoly& f) {  // PARI-like "x^2 + 3*x + 1"
    std::string o;
    for (int i = (int)f.size() - 1; i >= 0; --i) {
        if (!f[i]) continue;
        std::string mon = i == 0 ? "" : (i == 1 ? "x" : "x^" + std::to_string(i));
        std::string c = (f[i] == 1 && i > 0) ? "" : std::to_string(f[i]) + (i > 0 ? "*" : "");
        o += (o.empty() ? "" : " + ") + c + mon;
    }
    return o.empty() ? "0" : o;
}

// ================================================================ Z/p^R arithmetic (BigInt)
struct PR {
    i64 p;
    int R;
    Z P;  // p^R
    Z m(const Z& x) const { return x.floor_mod(P); }
};
using ZV = std::vector<Z>;
int vpz(const Z& x, i64 p, int cap) {
    if (x.is_zero()) return cap;
    return std::min<int>(cap, (int)x.valuation((uint32_t)p));
}
// Hensel: f = a b mod p (a monic, gcd(a, b) = 1 mod p) -> a, b mod p^R with f = a b (a monic, deg a fixed)
std::pair<ZV, ZV> hensel(const ZV& f, const ZPoly& a0, const ZPoly& b0, const PR& pr) {
    const i64 p = pr.p;
    // s a0 + t b0 = 1 mod p (extended Euclid on ZPoly)
    ZPoly r0 = a0, r1 = b0, s0{1}, s1{}, t0{}, t1{1};
    while (!r1.empty()) {
        ZPoly q, r;
        pdivmod(r0, r1, p, q, r);
        r0 = r1;
        r1 = r;
        ZPoly s2 = psub(s0, pmul(q, s1, p), p), t2 = psub(t0, pmul(q, t1, p), p);
        s0 = s1;
        s1 = s2;
        t0 = t1;
        t1 = t2;
    }
    if (r0.size() != 1) throw std::logic_error("hensel: factors not coprime mod p");
    const i64 ic = inv(r0[0], p);
    for (auto& x : s0) x = (i64)((i128)x * ic % p);
    for (auto& x : t0) x = (i64)((i128)x * ic % p);
    // linear lifting: a = a0 + p a1 + ..., b likewise
    ZV a(a0.begin(), a0.end()), b(b0.begin(), b0.end());
    Z pk = Z(p);
    auto zmul = [&](const ZV& x, const ZV& y) {
        ZV c(x.size() + y.size() - 1, Z(0));
        for (size_t i = 0; i < x.size(); ++i)
            if (!x[i].is_zero())
                for (size_t j = 0; j < y.size(); ++j) c[i + j] += x[i] * y[j];
        return c;
    };
    for (int k = 1; k < pr.R; ++k) {
        // e = (f - a b) / p^k mod p
        ZV ab = zmul(a, b);
        ZV e(std::max(f.size(), ab.size()), Z(0));
        for (size_t i = 0; i < e.size(); ++i) {
            Z v = (i < f.size() ? f[i] : Z(0)) - (i < ab.size() ? ab[i] : Z(0));
            Z q, r;
            Z::divmod(v, pk, q, r);
            if (!r.is_zero()) throw std::logic_error("hensel: not divisible");
            e[i] = q;
        }
        ZPoly em;
        for (auto& x : e) em.push_back((i64)x.floor_mod(Z(p)).to_int64());
        trim(em);
        // delta_a = (t e mod a0), delta_b = (s e mod b0)  [b0 da + a0 db = e]
        ZPoly da = pmod(pmul(t0, em, p), a0, p), db = pmod(pmul(s0, em, p), b0, p);
        // a0 db + b0 da should equal e (mod p) up to degree: fine since deg e < deg f
        for (size_t i = 0; i < da.size(); ++i) a[i] += pk * Z(da[i]);
        for (size_t i = 0; i < db.size(); ++i) b[i] += pk * Z(db[i]);
        pk *= Z(p);
    }
    for (auto& x : a) x = pr.m(x);
    for (auto& x : b) x = pr.m(x);
    return {a, b};
}

// dense matrices mod p^R
struct PM {
    int r = 0, c = 0;
    std::vector<Z> a;
    Z& at(int i, int j) { return a[(size_t)i * c + j]; }
    const Z& at(int i, int j) const { return a[(size_t)i * c + j]; }
};
PM pm_from(const ZMat& A, const PR& pr) {
    PM M;
    M.r = (int)A.size();
    M.c = M.r ? (int)A[0].size() : 0;
    M.a.resize((size_t)M.r * M.c);
    for (int i = 0; i < M.r; ++i)
        for (int j = 0; j < M.c; ++j) M.at(i, j) = pr.m(A[i][j]);
    return M;
}
PM pm_mul(const PM& A, const PM& B, const PR& pr) {
    PM C;
    C.r = A.r;
    C.c = B.c;
    C.a.assign((size_t)C.r * C.c, Z(0));
    for (int i = 0; i < A.r; ++i)
        for (int k = 0; k < A.c; ++k) {
            const Z& x = A.at(i, k);
            if (x.is_zero()) continue;
            for (int j = 0; j < B.c; ++j)
                if (!B.at(k, j).is_zero()) C.at(i, j) += x * B.at(k, j);
        }
    for (auto& x : C.a) x = pr.m(x);
    return C;
}
// p-adic Smith with column transforms: returns valuations of the pivots and V (c x c) with A V = [pivot cols | rest]
std::vector<int> pm_smith(PM A, const PR& pr, PM* Vout) {
    const int m = A.r, n = A.c;
    PM V;
    V.r = V.c = n;
    V.a.assign((size_t)n * n, Z(0));
    for (int i = 0; i < n; ++i) V.at(i, i) = 1;
    std::vector<int> vals;
    for (int t = 0; t < std::min(m, n); ++t) {
        int bv = pr.R + 1, bi = -1, bj = -1;
        for (int i = t; i < m && bv > 0; ++i)
            for (int j = t; j < n; ++j) {
                if (A.at(i, j).is_zero()) continue;
                int v = vpz(A.at(i, j), pr.p, pr.R);
                if (v < bv) {
                    bv = v;
                    bi = i;
                    bj = j;
                    if (v == 0) break;
                }
            }
        if (bi < 0) break;
        for (int j = 0; j < n; ++j) std::swap(A.at(t, j), A.at(bi, j));
        for (int i = 0; i < m; ++i) std::swap(A.at(i, t), A.at(i, bj));
        for (int i = 0; i < n; ++i) std::swap(V.at(i, t), V.at(i, bj));
        const Z pv = Z::pow(Z(pr.p), (uint64_t)bv);
        Z unit = A.at(t, t) / pv;  // exact
        // inverse of unit mod p^R
        Z g, s, tt;
        {
            Z r0 = unit.floor_mod(pr.P), r1 = pr.P, s0 = 1, s1 = 0;
            while (!r1.is_zero()) {
                Z q, r;
                Z::divmod(r0, r1, q, r);
                r0 = r1;
                r1 = r;
                Z s2 = s0 - q * s1;
                s0 = s1;
                s1 = s2;
            }
            s = s0.floor_mod(pr.P);
        }
        // scale column t by s (unimodular on V)
        for (int i = 0; i < m; ++i) A.at(i, t) = pr.m(A.at(i, t) * s);
        for (int i = 0; i < n; ++i) V.at(i, t) = pr.m(V.at(i, t) * s);
        // now A[t][t] = p^bv; clear row t (column ops) and column t (row ops)
        for (int j = t + 1; j < n; ++j) {
            if (A.at(t, j).is_zero()) continue;
            Z f = A.at(t, j) / pv;
            for (int i = 0; i < m; ++i) A.at(i, j) = pr.m(A.at(i, j) - f * A.at(i, t));
            for (int i = 0; i < n; ++i) V.at(i, j) = pr.m(V.at(i, j) - f * V.at(i, t));
        }
        for (int i = t + 1; i < m; ++i) {
            if (A.at(i, t).is_zero()) continue;
            Z f = A.at(i, t) / pv;
            for (int j = t; j < n; ++j) A.at(i, j) = pr.m(A.at(i, j) - f * A.at(t, j));
        }
        vals.push_back(bv);
    }
    if (Vout) *Vout = V;
    return vals;
}

// ================================================================ level-one eigenforms (dim S_k(1) = 1)
// q-expansion coefficients a_1..a_N of the normalised eigenform Delta E_4^a E_6^b (k = 12 + 4a + 6b), exact
std::vector<Z> level_one(int k, int N) {
    // dim S_k(1) = 1 iff k in {12, 16, 18, 20, 22, 26}
    if (!(k == 12 || k == 16 || k == 18 || k == 20 || k == 22 || k == 26)) return {};
    int a = -1, b = -1;
    for (int bb = 0; 6 * bb <= k - 12; ++bb)
        if ((k - 12 - 6 * bb) % 4 == 0) {
            a = (k - 12 - 6 * bb) / 4;
            b = bb;
            break;
        }
    auto sigma = [](int n, int r) {
        Z s = 0;
        for (int d = 1; d <= n; ++d)
            if (n % d == 0) s += Z::pow(Z(d), (uint64_t)r);
        return s;
    };
    auto mul = [&](const std::vector<Z>& x, const std::vector<Z>& y) {
        std::vector<Z> z(N + 1, Z(0));
        for (int i = 0; i <= N; ++i)
            for (int j = 0; i + j <= N; ++j) z[i + j] += x[i] * y[j];
        return z;
    };
    std::vector<Z> E4(N + 1), E6(N + 1);
    E4[0] = 1;
    E6[0] = 1;
    for (int n = 1; n <= N; ++n) {
        E4[n] = Z(240) * sigma(n, 3);
        E6[n] = Z(-504) * sigma(n, 5);
    }
    auto E43 = mul(mul(E4, E4), E4), E62 = mul(E6, E6);
    std::vector<Z> D(N + 1);
    for (int n = 0; n <= N; ++n) D[n] = (E43[n] - E62[n]) / Z(1728);
    std::vector<Z> f = D;
    for (int i = 0; i < a; ++i) f = mul(f, E4);
    for (int i = 0; i < b; ++i) f = mul(f, E6);
    return f;  // f[1] = 1
}

// ================================================================ one Brandt module (q, k)
struct Module {
    i64 q = 0;
    int k = 0, n = 0;
    std::unique_ptr<MaxOrder> O;
    std::unique_ptr<ClassSet> C;
    std::unique_ptr<BrandtSym> M;
    int rank = 0;
    std::vector<i64> ells;
    std::map<i64, ZMat> Tl;
    ZMat Tgen;
    std::vector<int> coefs;
    std::vector<Z> chi;  // charpoly of Tgen, constant first
    nf::ZFactorisation fac;
    QMat Gw, Gg;
    double seconds = 0;
    bool squarefree = false;
};

std::unique_ptr<Module> build_module(i64 q, int k) {
    auto t0 = std::chrono::steady_clock::now();
    auto R = std::make_unique<Module>();
    R->q = q;
    R->k = k;
    R->n = k - 2;
    R->O = std::make_unique<MaxOrder>(q);
    R->C = std::make_unique<ClassSet>(*R->O);
    R->M = std::make_unique<BrandtSym>(*R->C, R->n);
    R->rank = R->M->rank();
    for (i64 l : {2, 3, 5, 7, 11})
        if (l != q) R->ells.push_back(l);
    if (R->rank == 0) return R;
    for (i64 l : R->ells) R->Tl[l] = R->M->T(l);
    const std::vector<std::vector<int>> COEFS = {{1, 3, 7, 13, 17}, {1, 5, 2, 11, 3}, {2, 1, 9, 4, 19}};
    for (const auto& cf : COEFS) {
        ZMat T(R->rank, std::vector<Z>(R->rank, Z(0)));
        for (size_t t = 0; t < R->ells.size(); ++t)
            for (int i = 0; i < R->rank; ++i)
                for (int j = 0; j < R->rank; ++j) T[i][j] += Z(cf[t]) * R->Tl[R->ells[t]][i][j];
        auto cp = symz::charpoly(T);
        // squarefree over Q iff gcd(chi, chi') = 1 mod some prime (test two large primes)
        bool sf = false;
        for (i64 L : {1000003LL, 998244353LL}) {
            ZPoly f;
            for (auto& z : cp) f.push_back((i64)z.floor_mod(Z(L)).to_int64());
            trim(f);
            if (pgcd(f, deriv(f, L), L).size() == 1) sf = true;
        }
        if (sf) {
            R->Tgen = T;
            R->coefs.assign(cf.begin(), cf.begin() + (long)R->ells.size());
            R->chi = cp;
            R->squarefree = true;
            break;
        }
    }
    if (!R->squarefree) return R;
    R->fac = nf::factor_monic_over_z(R->chi);
    R->Gw = R->M->gram(BrandtSym::Weight::w, true);
    R->Gg = R->M->gram(BrandtSym::Weight::gamma, true);
    R->seconds = since(t0);
    return R;
}

// v_p det(A^T G A) for a rational G (exact denominators handled), A basis columns (r x d) mod p^R
int vp_det_restricted(const QMat& G, const PM& A, const PR& pr, bool& ok) {
    const int r = (int)G.size();
    // D = lcm of denominators; G' = D G integral
    Z D = 1;
    for (auto& row : G)
        for (auto& x : row) D = D / Z::gcd(D, x.den()) * x.den();
    PM Gp;
    Gp.r = Gp.c = r;
    Gp.a.resize((size_t)r * r);
    for (int i = 0; i < r; ++i)
        for (int j = 0; j < r; ++j) Gp.at(i, j) = pr.m(G[i][j].num() * (D / G[i][j].den()));
    PM At;
    At.r = A.c;
    At.c = A.r;
    At.a.resize(A.a.size());
    for (int i = 0; i < A.r; ++i)
        for (int j = 0; j < A.c; ++j) At.at(j, i) = A.at(i, j);
    PM H = pm_mul(pm_mul(At, Gp, pr), A, pr);
    auto vals = pm_smith(H, pr, nullptr);
    ok = (int)vals.size() == A.c;
    int s = 0;
    for (int v : vals) s += v;
    const int vD = D.is_zero() ? 0 : (int)D.valuation((uint32_t)pr.p);
    ok = ok && s < pr.R / 2 - 2;  // the kernel basis is exact to about p^{R/2}
    return s - A.c * vD;
}

// charpoly mod p of a small d x d matrix (Faddeev-LeVerrier needs p > d; else via determinant interpolation is not used)
ZPoly charpoly_small(const std::vector<std::vector<i64>>& X, i64 p) {
    const int d = (int)X.size();
    if (d >= p) throw std::runtime_error("charpoly_small: d >= p");
    std::vector<i64> c(d + 1, 0);
    c[d] = 1;
    std::vector<std::vector<i64>> Mk(d, std::vector<i64>(d, 0));
    auto mul = [&](const std::vector<std::vector<i64>>& A, const std::vector<std::vector<i64>>& B) {
        std::vector<std::vector<i64>> C(d, std::vector<i64>(d, 0));
        for (int i = 0; i < d; ++i)
            for (int k2 = 0; k2 < d; ++k2)
                for (int j = 0; j < d; ++j) C[i][j] = (C[i][j] + A[i][k2] * B[k2][j]) % p;
        return C;
    };
    for (int k2 = 1; k2 <= d; ++k2) {
        Mk = mul(X, Mk);
        for (int i = 0; i < d; ++i) Mk[i][i] = (Mk[i][i] + c[d - k2 + 1]) % p;
        auto AM = mul(X, Mk);
        i64 tr = 0;
        for (int i = 0; i < d; ++i) tr = (tr + AM[i][i]) % p;
        c[d - k2] = md(-(i64)((i128)tr * inv(k2, p) % p), p);
    }
    ZPoly f(c.begin(), c.end());
    trim(f);
    return f;
}


std::vector<int> indep_rows(const PM& A, i64 p) {
    const int r = A.r, deg = A.c;
    std::vector<int> I;
    std::vector<std::vector<i64>> red;
    std::vector<int> pivc;
    for (int x = 0; x < r && (int)I.size() < deg; ++x) {
        std::vector<i64> v(deg);
        for (int y = 0; y < deg; ++y) v[y] = (i64)A.at(x, y).floor_mod(Z(p)).to_int64();
        for (size_t t = 0; t < red.size(); ++t)
            if (v[pivc[t]]) {
                i64 f = v[pivc[t]];
                for (int y = 0; y < deg; ++y) v[y] = md(v[y] - f * red[t][y], p);
            }
        int nz = -1;
        for (int y = 0; y < deg; ++y)
            if (v[y]) {
                nz = y;
                break;
            }
        if (nz < 0) continue;
        i64 iv = inv(v[nz], p);
        for (auto& z : v) z = z * iv % p;
        red.push_back(v);
        pivc.push_back(nz);
        I.push_back(x);
    }
    return I;
}
PM sub_rows(const PM& A, const std::vector<int>& I) {
    PM B;
    B.r = (int)I.size();
    B.c = A.c;
    B.a.resize((size_t)B.r * B.c);
    for (int s = 0; s < B.r; ++s)
        for (int j = 0; j < B.c; ++j) B.at(s, j) = A.at(I[s], j);
    return B;
}
Z inv_z(const Z& a, const PR& pr) {
    Z r0 = a.floor_mod(pr.P), r1 = pr.P, s0 = 1, s1 = 0;
    while (!r1.is_zero()) {
        Z q, r;
        Z::divmod(r0, r1, q, r);
        r0 = r1;
        r1 = r;
        Z s2 = s0 - q * s1;
        s0 = s1;
        s1 = s2;
    }
    if (r0 != Z(1)) throw std::logic_error("inv_z: not a unit");
    return s0.floor_mod(pr.P);
}
PM inv_pm(const PM& A, const PR& pr) {
    const int n = A.r;
    PM W;
    W.r = n;
    W.c = 2 * n;
    W.a.assign((size_t)n * 2 * n, Z(0));
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) W.at(i, j) = A.at(i, j);
        W.at(i, n + i) = 1;
    }
    for (int c = 0; c < n; ++c) {
        int pv = -1;
        for (int i = c; i < n; ++i)
            if (!(W.at(i, c) % Z(pr.p)).is_zero()) {
                pv = i;
                break;
            }
        if (pv < 0) throw std::logic_error("inv_pm: singular mod p");
        for (int j = 0; j < 2 * n; ++j) std::swap(W.at(c, j), W.at(pv, j));
        Z iv = inv_z(W.at(c, c), pr);
        for (int j = 0; j < 2 * n; ++j) W.at(c, j) = pr.m(W.at(c, j) * iv);
        for (int i = 0; i < n; ++i) {
            if (i == c || W.at(i, c).is_zero()) continue;
            Z f = W.at(i, c);
            for (int j = 0; j < 2 * n; ++j) W.at(i, j) = pr.m(W.at(i, j) - f * W.at(c, j));
        }
    }
    PM R;
    R.r = R.c = n;
    R.a.resize((size_t)n * n);
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j) R.at(i, j) = W.at(i, n + j);
    return R;
}
// charpoly mod p^R (Faddeev-LeVerrier; needs d < p), constant first
ZV charpoly_pm(const PM& X, const PR& pr) {
    const int d = X.r;
    ZV c(d + 1, Z(0));
    c[d] = 1;
    PM Mk;
    Mk.r = Mk.c = d;
    Mk.a.assign((size_t)d * d, Z(0));
    for (int k2 = 1; k2 <= d; ++k2) {
        Mk = pm_mul(X, Mk, pr);
        for (int i = 0; i < d; ++i) Mk.at(i, i) = pr.m(Mk.at(i, i) + c[d - k2 + 1]);
        PM AM = pm_mul(X, Mk, pr);
        Z tr = 0;
        for (int i = 0; i < d; ++i) tr += AM.at(i, i);
        c[d - k2] = pr.m(-(tr * inv_z(Z(k2), pr)));
    }
    return c;
}

struct Orbit;
void finish_orbit(Orbit& o, const PM& A, const struct Module& Mo, const std::map<i64, PM>& Tl, const PR& pr, std::mt19937_64& rng);
struct Orbit {
    int qfactor = 0;      // index of the Q-factor
    int qdeg = 0;
    ZPoly g;              // residue of the generic T
    int e = 1;            // multiplicity of g in f_i mod p
    int degree = 0;       // = e deg g (rank of A)
    std::map<i64, std::string> residual;   // per T_l: irreducible residual factor (text)
    std::map<i64, std::vector<i64>> residual_poly;
    std::map<i64, i64> residual_eigen;     // when deg g = 1
    int vp_w = 0, vp_gamma = 0;
    bool det_ok = true, resolved = true;
    std::string separated_by;
};



void finish_orbit(Orbit& o, const PM& A, const Module& Mo, const std::map<i64, PM>& Tl, const PR& pr, std::mt19937_64& rng) {
    const i64 p = pr.p;
    const int deg = A.c;
    bool ok1 = true, ok2 = true;
    o.vp_w = vp_det_restricted(Mo.Gw, A, pr, ok1);
    o.vp_gamma = vp_det_restricted(Mo.Gg, A, pr, ok2);
    o.det_ok = o.det_ok && ok1 && ok2;
    std::vector<int> I = indep_rows(A, p);
    if ((int)I.size() != deg || deg >= p) {
        o.det_ok = false;
        return;
    }
    PM AIi = inv_pm(sub_rows(A, I), pr);
    for (auto& [l, T] : Tl) {
        PM X = pm_mul(AIi, sub_rows(pm_mul(T, A, pr), I), pr);
        std::vector<std::vector<i64>> Xm(deg, std::vector<i64>(deg, 0));
        for (int s2 = 0; s2 < deg; ++s2)
            for (int y = 0; y < deg; ++y) Xm[s2][y] = (i64)X.at(s2, y).floor_mod(Z(p)).to_int64();
        ZPoly cp = charpoly_small(Xm, p);
        auto fs = factor_mod_p(cp, p, rng);
        std::string txt;
        ZPoly irr;
        if (fs.size() == 1) {
            irr = fs[0].first;
            txt = ptext(irr);
        } else {
            for (auto& [gg, ee] : fs) txt += (txt.empty() ? "" : " * ") + std::string("(") + ptext(gg) + ")^" + std::to_string(ee);
            o.det_ok = false;  // an orbit has a single residual factor
        }
        o.residual[l] = txt;
        o.residual_poly[l] = irr;
        if (irr.size() == 2) o.residual_eigen[l] = md(-irr[0], p);
    }
}

// recursive coprime splitting of a block A (r x d) by the Hecke elements T' = T + c T_l
void split_block(const Orbit& o0, const PM& A, const Module& Mo, const std::map<i64, PM>& Tl, const PM& Tgen, const PR& pr,
                 std::mt19937_64& rng, std::vector<Orbit>& orbs, int depth) {
    const i64 p = pr.p;
    const int deg = A.c;
    std::vector<int> I = indep_rows(A, p);
    if ((int)I.size() == deg && deg < p && depth < 6) {
        PM AIi = inv_pm(sub_rows(A, I), pr);
        for (int c = 0; c <= 3; ++c)
            for (auto& [l, T] : Tl) {
                PM Tp = Tgen;
                for (size_t z = 0; z < Tp.a.size(); ++z) Tp.a[z] = pr.m(Tp.a[z] + Z(c + 1) * T.a[z] - Z(c == 0 ? 1 : 0) * Tgen.a[z]);
                PM X = pm_mul(AIi, sub_rows(pm_mul(Tp, A, pr), I), pr);
                ZV cx = charpoly_pm(X, pr);
                ZPoly cm;
                for (auto& zz : cx) cm.push_back((i64)zz.floor_mod(Z(p)).to_int64());
                trim(cm);
                auto hs = factor_mod_p(cm, p, rng);
                const bool sqfree = hs.size() == (size_t)0 || std::all_of(hs.begin(), hs.end(), [](const auto& x) { return x.second == 1; });
                if (hs.size() < 2 && !sqfree) continue;  // one factor with multiplicity: no information
                const std::string sep = "T + " + std::to_string(c + 1) + " T_" + std::to_string(l) + (c == 0 ? " - T" : "");
                for (auto& [h, eh] : hs) {
                    ZPoly he{1};
                    for (int t = 0; t < eh; ++t) he = pmul(he, h, p);
                    ZPoly rest = pdiv(cm, he, p);
                    ZV H = (rest.size() == 1) ? cx : hensel(cx, he, rest, pr).first;
                    PM KX;
                    KX.r = KX.c = deg;
                    KX.a.assign((size_t)deg * deg, Z(0));
                    for (int t = (int)H.size() - 1; t >= 0; --t) {
                        KX = pm_mul(KX, X, pr);
                        for (int d2 = 0; d2 < deg; ++d2) KX.at(d2, d2) = pr.m(KX.at(d2, d2) + H[t]);
                    }
                    PM VX;
                    auto vx = pm_smith(KX, pr, &VX);
                    int gx = 0;
                    for (int v : vx) gx += v < pr.R / 2;
                    const int dh = (int)H.size() - 1;
                    PM Bx;
                    Bx.r = deg;
                    Bx.c = deg - gx;
                    Bx.a.resize((size_t)deg * Bx.c);
                    for (int x = 0; x < deg; ++x)
                        for (int y = 0; y < Bx.c; ++y) Bx.at(x, y) = VX.at(x, gx + y);
                    PM Ab = pm_mul(A, Bx, pr);
                    Orbit so = o0;
                    so.degree = dh;
                    so.separated_by = (o0.separated_by.empty() ? "" : o0.separated_by + "; ") + sep;
                    if (Bx.c != dh) so.det_ok = false;
                    if (eh == 1) {
                        so.e = 1;
                        so.resolved = true;
                        finish_orbit(so, Ab, Mo, Tl, pr, rng);
                        orbs.push_back(so);
                    } else {
                        so.e = eh;
                        so.resolved = false;
                        split_block(so, Ab, Mo, Tl, Tgen, pr, rng, orbs, depth + 1);
                    }
                }
                return;
            }
    }
    Orbit so = o0;
    so.resolved = false;
    finish_orbit(so, A, Mo, Tl, pr, rng);
    orbs.push_back(so);
}

std::string run_cell(const Module& Mo, i64 p, int R, bool only_nontrivial, bool* nontrivial, int* nblocks_out,
                     const std::map<i64, i64>* target = nullptr, std::map<i64, i64>* m_eigen_out = nullptr) {
    auto t0 = std::chrono::steady_clock::now();
    PR pr{p, R, Z::pow(Z(p), (uint64_t)R)};
    std::mt19937_64 rng(0xe7a0ULL ^ (u64)p);
    const int r = Mo.rank;
    const bool perfect = p > Mo.n && p >= 5;
    std::vector<Orbit> orbs;
    PM Tgen = pm_from(Mo.Tgen, pr);
    std::map<i64, PM> Tl;
    for (auto& [l, T] : Mo.Tl) Tl[l] = pm_from(T, pr);
    for (size_t i = 0; i < Mo.fac.factors.size(); ++i) {
        const auto& fz = Mo.fac.factors[i];
        if (fz.multiplicity != 1) throw std::logic_error("chi not squarefree");
        ZPoly fm;
        for (auto& z : fz.poly) fm.push_back((i64)z.floor_mod(Z(p)).to_int64());
        trim(fm);
        auto parts = factor_mod_p(fm, p, rng);
        ZV fZ(fz.poly.begin(), fz.poly.end());
        for (auto& [g, e] : parts) {
            // a0 = g^e, b0 = fm / g^e
            ZPoly a0{1};
            for (int t = 0; t < e; ++t) a0 = pmul(a0, g, p);
            ZPoly b0 = pdiv(fm, a0, p);
            ZV F;
            if (b0.size() == 1 && b0[0] == 1)
                F = fZ;
            else {
                // make b0 monic-consistent: fm monic and a0 monic -> b0 monic
                F = hensel(fZ, a0, b0, pr).first;
            }
            // K = F(T) by Horner (deg F = e deg g, small)
            PM K;
            K.r = K.c = r;
            K.a.assign((size_t)r * r, Z(0));
            for (int t = (int)F.size() - 1; t >= 0; --t) {
                K = pm_mul(K, Tgen, pr);
                for (int d = 0; d < r; ++d) K.at(d, d) = pr.m(K.at(d, d) + F[t]);
            }
            PM V;
            auto vals = pm_smith(K, pr, &V);
            const int deg = (int)F.size() - 1;
            int good = 0;
            for (int v : vals) good += v < R / 2;
            Orbit o;
            o.qfactor = (int)i;
            o.qdeg = (int)fz.poly.size() - 1;
            o.g = g;
            o.e = e;
            o.degree = deg;
            o.resolved = e == 1;
            if (good != r - deg) {
                o.det_ok = false;
            }
            // kernel basis: columns good..r-1 of V
            PM A;
            A.r = r;
            A.c = r - good;
            A.a.resize((size_t)r * A.c);
            for (int x = 0; x < r; ++x)
                for (int y = 0; y < A.c; ++y) A.at(x, y) = V.at(x, good + y);
            if (A.c != deg) o.det_ok = false;
            if (!o.det_ok) {
                orbs.push_back(o);
                continue;
            }
            if (e == 1) {
                finish_orbit(o, A, Mo, Tl, pr, rng);
                orbs.push_back(o);
                continue;
            }
            // e > 1 for the generic T: split the block on the COPRIME factors of the charpoly of other Hecke elements
            // T' = T + c T_l (review M2: a squarefree charpoly is not required), recursively; parts that no T' splits
            // further are single blocks (a ramified orbit, or a non-maximal Z_p[T]) and are reported unresolved.
            split_block(o, A, Mo, Tl, Tgen, pr, rng, orbs, 0);
        }
    }
    // blocks by residual eigensystem
    std::map<std::string, std::vector<int>> blocks;
    for (size_t i = 0; i < orbs.size(); ++i) {
        std::string key;
        for (auto& [l, t] : orbs[i].residual) key += std::to_string(l) + ":" + t + ";";
        blocks[key].push_back((int)i);
    }
    // level-one form (old congruence)
    auto lo = level_one(Mo.k, 50);
    int vlr = -1;
    if (!lo.empty()) {
        Z aq = lo[Mo.q];
        Z x = aq * aq - Z::pow(Z(Mo.q), (uint64_t)(Mo.k - 2)) * Z((Mo.q + 1) * (Mo.q + 1));
        vlr = x.is_zero() ? -2 : (int)x.valuation((uint32_t)p);
    }
    bool nontriv = false;
    std::string bl = "[";
    int nb = 0;
    std::string mjson = "null", mfromk = "null";
    int n_matches = 0;
    for (auto& [key, ids] : blocks) {
        int rank = 0;
        bool any_eta = false, all_ok = true, all_res = true;
        for (int i : ids) {
            rank += orbs[i].degree;
            any_eta |= orbs[i].vp_w != 0;
            all_ok &= orbs[i].det_ok;
            all_res &= orbs[i].resolved;
        }
        bool old = false;
        std::string oldj = "null";
        if (!lo.empty()) {
            bool deg1 = true, eq = true;
            for (int i : ids) deg1 &= orbs[i].degree == 1 && orbs[i].resolved;
            if (deg1)
                for (auto& [l, ev] : orbs[ids[0]].residual_eigen) eq &= md(lo[l].floor_mod(Z(p)).to_int64(), p) == ev;
            old = deg1 && eq && orbs[ids[0]].residual_eigen.size() == Mo.ells.size();
            oldj = jb(old);
        }
        const bool congr = ids.size() > 1 || any_eta || !all_res;
        nontriv |= congr || old;
        Obj b;
        b.add("rank", rank).add("n_orbits", (long long)ids.size()).add("congruence", jb(congr));
        b.add("old_congruent", oldj);
        std::string residual = "{", reseig = "{";
        int c1 = 0, c2 = 0;
        for (auto& [l, t] : orbs[ids[0]].residual) residual += (c1++ ? "," : "") + js(std::to_string(l)) + ":" + js(t);
        for (auto& [l, ev] : orbs[ids[0]].residual_eigen) reseig += (c2++ ? "," : "") + js(std::to_string(l)) + ":" + std::to_string(ev);
        b.add("residual", residual + "}").add("residual_eigenvalues", orbs[ids[0]].residual_eigen.size() == Mo.ells.size() ? reseig + "}" : std::string("null"));
        std::string ol = "[";
        std::vector<int> etas;
        for (size_t t = 0; t < ids.size(); ++t) {
            const Orbit& o = orbs[ids[t]];
            etas.push_back(o.vp_w);
            ol += std::string(t ? "," : "") +
                  Obj().add("degree", o.degree).add("residue_degree", o.resolved ? (long long)o.degree : (long long)o.g.size() - 1).add("e", o.e)
                      .add("separated_by", js(o.separated_by.empty() ? "generic T" : o.separated_by))
                      .add("resolved_Qp_orbit", jb(o.resolved)).add("Q_factor", o.qfactor).add("Q_factor_degree", o.qdeg)
                      .add("residue_of_generic_T", js(ptext(o.g))).add("vp_det_gram_w", o.vp_w)
                      .add("vp_det_gram_Gamma", o.vp_gamma).add("vp_ratio", o.vp_w - o.vp_gamma).add("det_ok", jb(o.det_ok)).str();
        }
        b.add("orbits", ol + "]").add("vp_etaB", jl(etas)).add("all_ok", jb(all_ok));
        if (old) {
            mjson = Obj().add("rank", rank).add("vp_etaB", jl(etas)).add("n_orbits", (long long)ids.size()).str();
            if (m_eigen_out) *m_eigen_out = orbs[ids[0]].residual_eigen;
        }
        if (target && !target->empty() && orbs[ids[0]].residual_eigen == *target && ids.size() >= 1) {
            ++n_matches;
            // review M1: the m of weight k, found at k + (p - 1) by its residual eigensystem (g E_{p-1} = g mod p).
            // eta^B is the ring-theoretic congruence ideal of the q-new algebra at m; rank 1 forces T^B_m = Z_p, eta^B = (1).
            mfromk = Obj().add("rank", rank).add("n_orbits", (long long)ids.size())
                         .add("etaB_ring_vp", rank == 1 ? std::string("0") : std::string("null"))
                         .add("etaB_ring", rank == 1 ? js(std::to_string(p) + "^0") : std::string("null"))
                         .add("method", js(rank == 1 ? "ring-theoretic: rank-1 block M_m, so T^B_m = Z_p and the congruence ideal is (1); no pairing used"
                                                     : "not determined: rank > 1 and the pairing is not perfect"))
                         .add("matched_by", js("residual eigenvalues a_l mod p (l in {2,3,5,7,11}, l != q) equal to those of m at weight k"))
                         .str();
        }
        if (!only_nontrivial || congr || old) {
            bl += std::string(nb ? "," : "") + b.str();
            ++nb;
        }
    }
    bl += "]";
    if (nontrivial) *nontrivial = nontriv;
    if (nblocks_out) *nblocks_out = (int)blocks.size();
    Obj o;
    o.add("q", Mo.q).add("k", Mo.k).add("p", p).add("dim_brandt", r).add("h", Mo.C->h());
    o.add("pairing_perfect", jb(perfect)).add("R", R).add("n_blocks", (long long)blocks.size());
    o.add("gram_weight", js("w (G_w = (+)_x w_x^{-1} <,>_V, w_x = |Gamma_x|/2); vp_det_gram_Gamma also given"));
    o.add("vp_level_raising", vlr == -1 ? std::string("null") : std::to_string(vlr));
    o.add("m_old_congruent", mjson).add("old_congruent_detection", js(lo.empty() ? "not detected (the tool detects old congruences only when dim S_k(1) = 1)" : "level-one eigenform g of weight k"));
    if (target) {
        // review guard: an empty target (no m at weight k) or more than one matching block gives no m
        if (target->empty())
            mfromk = Obj().add("status", js("not determined: no old-congruent m at weight k to match")).str();
        else if (n_matches == 0)
            mfromk = Obj().add("status", js("not determined: no block with the residual eigensystem of m")).str();
        else if (n_matches > 1)
            mfromk = Obj().add("status", js("not determined: " + std::to_string(n_matches) + " blocks match the residual eigensystem of m")).str();
        o.add("m_from_weight_k", mfromk).add("m_from_weight_k_matches", n_matches);
    }
    o.add("blocks", bl);
    o.add("seconds", std::to_string(since(t0)));
    return o.str();
}

std::string module_info(const Module& Mo) {
    Obj o;
    o.add("q", Mo.q).add("k", Mo.k).add("rank", Mo.rank).add("squarefree", jb(Mo.squarefree));
    std::string c = "{";
    for (size_t t = 0; t < Mo.coefs.size(); ++t) c += (t ? "," : "") + js(std::to_string(Mo.ells[t])) + ":" + std::to_string(Mo.coefs[t]);
    o.add("generic_T", c + "}").add("Q_factors_degrees", [&] {
        std::vector<int> d;
        for (auto& f : Mo.fac.factors) d.push_back((int)f.poly.size() - 1);
        return jl(d);
    }());
    o.add("Q_factorisation_complete", jb(Mo.fac.complete)).add("build_seconds", std::to_string(Mo.seconds));
    return o.str();
}

// ---------------------------------------------------------------- the m-block rank at k' = k + (p - 1) without chi (cheap)
// M_m (x) F_p = the joint generalized eigenspace of the T_l mod p at the residual eigenvalues a_l of m (Hecke algebra
// generated by the T_l used). Computed by successive restriction: W_0 = F_p^r, W_{j+1} = generalized kernel of
// (T_{l_j} - a_{l_j}) on W_j (W_j is stable, the T_l commute). If dim = 1 after some l, then rk M_m = 1 (it is >= 1 when
// the final space is nonzero), T^B_m = Z_p and eta^B = (1).
namespace {
using FMat = std::vector<std::vector<i64>>;
// kernel basis (columns as rows) of A (n x n) mod p
std::vector<std::vector<i64>> kernel_mod(FMat A, i64 p) {
    const int n = (int)A.size();
    std::vector<int> pivcol(n, -1);
    int r = 0;
    std::vector<int> where(n, -1);
    for (int c = 0; c < n && r < n; ++c) {
        int pv = -1;
        for (int i = r; i < n; ++i)
            if (A[i][c]) {
                pv = i;
                break;
            }
        if (pv < 0) continue;
        std::swap(A[pv], A[r]);
        i64 iv = inv(A[r][c], p);
        for (auto& x : A[r]) x = x * iv % p;
        for (int i = 0; i < n; ++i)
            if (i != r && A[i][c]) {
                i64 f = A[i][c];
                for (int j = 0; j < n; ++j) A[i][j] = md(A[i][j] - f * A[r][j], p);
            }
        where[c] = r++;
    }
    std::vector<std::vector<i64>> K;
    for (int c = 0; c < n; ++c) {
        if (where[c] >= 0) continue;
        std::vector<i64> v(n, 0);
        v[c] = 1;
        for (int c2 = 0; c2 < n; ++c2)
            if (where[c2] >= 0) v[c2] = md(-A[where[c2]][c], p);
        K.push_back(v);
    }
    return K;
}
FMat fmul(const FMat& A, const FMat& B, i64 p) {
    const int n = (int)A.size(), m = (int)B[0].size(), k = (int)B.size();
    FMat C(n, std::vector<i64>(m, 0));
    for (int i = 0; i < n; ++i)
        for (int t = 0; t < k; ++t)
            if (A[i][t])
                for (int j = 0; j < m; ++j) C[i][j] = (C[i][j] + A[i][t] * B[t][j]) % p;
    return C;
}
}  // namespace

std::string m_rank_shift(i64 q, int k, i64 p, const std::map<i64, i64>& target, double* secs) {
    auto t0 = std::chrono::steady_clock::now();
    Obj o;
    o.add("q", q).add("k", k).add("p", p);
    MaxOrder O(q);
    ClassSet C(O);
    BrandtSym M(C, k - 2);
    const int r = M.rank();
    o.add("dim_brandt", r).add("build_seconds", std::to_string(since(t0)));
    // current subspace W (basis: columns of a d x r matrix stored as rows of length r)
    FMat Wb;  // rows = basis vectors of W in F_p^r
    for (int i = 0; i < r; ++i) {
        std::vector<i64> e(r, 0);
        e[i] = 1;
        Wb.push_back(e);
    }
    std::string steps = "[";
    int nsteps = 0, dim = r;
    for (auto& [l, a] : target) {
        if (dim <= 1) break;
        ZMat T = M.T(l);
        FMat Tp(r, std::vector<i64>(r));
        for (int i = 0; i < r; ++i)
            for (int j = 0; j < r; ++j) Tp[i][j] = (i64)T[i][j].floor_mod(Z(p)).to_int64();
        // restrict (T - a) to W: X with (T - a) w_j = sum_i X[i][j] w_i; solve via the reduced basis of W
        const int d = (int)Wb.size();
        // images (column vectors of length r)
        FMat Wc(r, std::vector<i64>(d));  // r x d
        for (int j = 0; j < d; ++j)
            for (int i = 0; i < r; ++i) Wc[i][j] = Wb[j][i];
        FMat Y = fmul(Tp, Wc, p);
        for (int j = 0; j < d; ++j)
            for (int i = 0; i < r; ++i) Y[i][j] = md(Y[i][j] - a * Wc[i][j], p);
        // coordinates: solve Wc X = Y (Wc full column rank) by Gauss on [Wc | Y]
        FMat Aug(r, std::vector<i64>(2 * d));
        for (int i = 0; i < r; ++i)
            for (int j = 0; j < d; ++j) {
                Aug[i][j] = Wc[i][j];
                Aug[i][d + j] = Y[i][j];
            }
        int row = 0;
        for (int c = 0; c < d; ++c) {
            int pv = -1;
            for (int i = row; i < r; ++i)
                if (Aug[i][c]) {
                    pv = i;
                    break;
                }
            if (pv < 0) throw std::logic_error("m_rank_shift: W not of full rank");
            std::swap(Aug[pv], Aug[row]);
            i64 iv = inv(Aug[row][c], p);
            for (auto& x : Aug[row]) x = x * iv % p;
            for (int i = 0; i < r; ++i)
                if (i != row && Aug[i][c]) {
                    i64 f = Aug[i][c];
                    for (int j = 0; j < 2 * d; ++j) Aug[i][j] = md(Aug[i][j] - f * Aug[row][j], p);
                }
            ++row;
        }
        for (int i = d; i < r; ++i)
            for (int j = d; j < 2 * d; ++j)
                if (Aug[i][j]) throw std::logic_error("m_rank_shift: W not stable");
        FMat X(d, std::vector<i64>(d));
        for (int i = 0; i < d; ++i)
            for (int j = 0; j < d; ++j) X[i][j] = Aug[i][d + j];
        // generalized kernel of X: kernel of X^d
        FMat Xp = X;
        for (int t = 1; t < d; t *= 2) Xp = fmul(Xp, Xp, p);
        auto K = kernel_mod(Xp, p);  // vectors in coordinates of W
        FMat nW;
        for (auto& v : K) {
            std::vector<i64> w(r, 0);
            for (int j = 0; j < d; ++j)
                if (v[j])
                    for (int i = 0; i < r; ++i) w[i] = (w[i] + v[j] * Wb[j][i]) % p;
            nW.push_back(w);
        }
        Wb = nW;
        dim = (int)Wb.size();
        steps += std::string(nsteps++ ? "," : "") + Obj().add("l", l).add("a_l_mod_p", a).add("dim_after", dim)
                                                         .add("seconds", std::to_string(since(t0))).str();
        if (dim == 0) break;
    }
    steps += "]";
    o.add("steps", steps).add("rank_M_m", dim);
    o.add("etaB_ring_vp", dim == 1 ? std::string("0") : std::string("null"));
    o.add("etaB_ring", dim == 1 ? js(std::to_string(p) + "^0") : std::string("null"));
    o.add("method", js(dim == 1 ? "ring-theoretic: the joint generalized eigenspace of the T_l mod p at the residual "
                                  "eigenvalues of m is 1-dimensional, so rk M_m = 1, T^B_m = Z_p, congruence ideal (1)"
                                : (dim == 0 ? "m does not occur at this weight" : "not determined: rank > 1")));
    o.add("seconds", std::to_string(since(t0)));
    if (secs) *secs = since(t0);
    return o.str();
}

}  // namespace

int main(int argc, char** argv) {
    std::string suite = "t5", out, only;
    int R = 40, qmax = 50, kmax = 20, pmax = 200;
    double kp_budget = 600;  // seconds allowed for one k+(p-1) module build
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        auto nxt = [&] { return std::string(argv[++i]); };
        if (a == "--suite") suite = nxt();
        else if (a == "--out") out = nxt();
        else if (a == "--R") R = std::stoi(nxt());
        else if (a == "--qmax") qmax = std::stoi(nxt());
        else if (a == "--kmax") kmax = std::stoi(nxt());
        else if (a == "--pmax") pmax = std::stoi(nxt());
        else if (a == "--kp-budget") kp_budget = std::stod(nxt());
        else if (a == "--only") only = nxt();
        else {
            std::cerr << "usage: jl_eta_def --suite t5|h3|census [--R N] [--qmax N] [--kmax N] [--pmax N] [--out FILE]\n";
            return 2;
        }
    }
    auto t0 = std::chrono::steady_clock::now();
    std::string body = "{\"schema\":\"langlandscape_eta_def/v1\",\"suite\":" + js(suite) + ",\"R\":" + std::to_string(R) + ",";
    if (suite == "t5" || suite == "h3") {
        std::vector<std::array<int, 3>> cases;  // (q, k, p)
        if (suite == "t5")
            cases = {{13, 18, 19}, {5, 18, 23}, {5, 16, 31}, {13, 12, 31}, {3, 18, 53}, {3, 18, 61}, {13, 16, 101}};
        else  // H3 triples are (q, p, k)
            cases = {{13, 4, 7}, {13, 6, 7}, {19, 4, 5}, {29, 4, 5}};
        std::string cells = "[";
        int nc = 0;
        for (auto& c : cases) {
            std::map<i64, i64> m_eigen_k;
            std::vector<int> ks{c[1]};
            if (suite == "t5") ks.push_back(c[1] + c[2] - 1);
            for (int k : ks) {
                // predicted cost of the k + (p - 1) module (BrandtSym build ~ k^7 at q = 13: 1.4 s at k = 36, 53 s at k = 60)
                const double pred = (c[0] == 13 ? 53.0 : (c[0] == 5 ? 8.0 : 1.0)) * std::pow(k / 60.0, 7.0);
                Obj o;
                o.add("q", c[0]).add("k", k).add("p", c[2]).add("weight_role", js(k == c[1] ? "k" : "k+(p-1)"));
                if (k != c[1] && pred > kp_budget) {
                    o.add("status", js("not computed")).add("reason", js("predicted BrandtSym build time " +
                                                                        std::to_string((int)pred) + " s exceeds the budget"));
                    cells += std::string(nc++ ? "," : "") + o.str();
                    std::fprintf(stderr, "skip q=%d k=%d p=%d (pred %.0f s)\n", c[0], k, c[2], pred);
                    continue;
                }
                auto Mo = build_module(c[0], k);
                std::string cell = !Mo->squarefree || Mo->rank == 0 ? std::string("null")
                                   : (k == c[1] ? run_cell(*Mo, c[2], R, false, nullptr, nullptr, nullptr, &m_eigen_k)
                                                : run_cell(*Mo, c[2], R, false, nullptr, nullptr, &m_eigen_k, nullptr));
                o.add("status", js("computed")).add("module", module_info(*Mo)).add("cell", cell);
                cells += std::string(nc++ ? "," : "") + o.str();
                std::fprintf(stderr, "q=%d k=%d p=%d rank=%d (%.1fs)\n", c[0], k, c[2], Mo->rank, since(t0));
            }
        }
        body += "\"cells\":" + cells + "]";
    } else if (suite == "shift") {
        // the m of weight k at k + (p - 1) by the cheap route (m_rank_shift), all T5 triples or --only q,k,p
        std::vector<std::array<int, 3>> cases = {{13, 18, 19}, {5, 18, 23}, {5, 16, 31}, {13, 12, 31}, {3, 18, 53}, {3, 18, 61}, {13, 16, 101}};
        std::string cells = "[";
        int nc = 0;
        for (auto& c : cases) {
            if (!only.empty() && only != std::to_string(c[0]) + "," + std::to_string(c[1]) + "," + std::to_string(c[2])) continue;
            auto Mo = build_module(c[0], c[1]);
            std::map<i64, i64> mk;
            run_cell(*Mo, c[2], R, false, nullptr, nullptr, nullptr, &mk);
            std::string cell;
            if (mk.empty())
                cell = Obj().add("status", js("not determined: no old-congruent m at weight k")).str();
            else
                cell = m_rank_shift(c[0], c[1] + c[2] - 1, c[2], mk, nullptr);
            std::string me = "{";
            int t = 0;
            for (auto& [l, a] : mk) me += (t++ ? "," : "") + js(std::to_string(l)) + ":" + std::to_string(a);
            cells += std::string(nc++ ? "," : "") + Obj().add("q", c[0]).add("k", c[1]).add("p", c[2])
                                                       .add("k_shift", c[1] + c[2] - 1).add("m_residual_eigenvalues_weight_k", me + "}")
                                                       .add("shift", cell).str();
            std::fprintf(stderr, "shift q=%d k=%d p=%d done (%.1fs)\n", c[0], c[1], c[2], since(t0));
        }
        body += "\"cells\":" + cells + "]";
    } else if (suite == "census") {
        std::string cells = "[";
        int nc = 0;
        long n_cells = 0, n_nontrivial = 0, n_trivial_sqfree = 0, n_mod = 0;
        Obj per;
        for (i64 q = 2; q <= qmax; ++q) {
            if (!is_prime(q)) continue;
            for (int k = 2; k <= kmax; k += 2) {
                auto Mo = build_module(q, k);
                ++n_mod;
                if (Mo->rank == 0 || !Mo->squarefree) {
                    std::fprintf(stderr, "census q=%lld k=%d rank=%d skip\n", (long long)q, k, Mo->rank);
                    continue;
                }
                // level raising candidates (old congruence) need dim S_k(1) = 1
                auto lo = level_one(k, 50);
                for (i64 p = k + 1; p < pmax; ++p) {
                    if (!is_prime(p) || p < 5 || p == q || ((q * q - 1) % p) == 0) continue;
                    ++n_cells;
                    // prefilter: chi mod p squarefree and no level raising -> every block is one orbit with eta = 0
                    ZPoly f;
                    for (auto& z : Mo->chi) f.push_back((i64)z.floor_mod(Z(p)).to_int64());
                    trim(f);
                    bool sqf = pgcd(f, deriv(f, p), p).size() == 1;
                    bool lr = false;
                    if (!lo.empty()) {
                        Z x = lo[q] * lo[q] - Z::pow(Z(q), (uint64_t)(k - 2)) * Z((q + 1) * (q + 1));
                        lr = x.is_zero() || (x % Z(p)).is_zero();
                    }
                    if (sqf && !lr) {
                        ++n_trivial_sqfree;
                        continue;
                    }
                    bool nt = false;
                    int nb = 0;
                    std::string cell;
                    try {
                        cell = run_cell(*Mo, p, R, true, &nt, &nb);
                    } catch (const std::exception& ex) {
                        nt = true;
                        cell = Obj().add("q", q).add("k", k).add("p", p).add("error", js(ex.what())).str();
                    }
                    if (nt) {
                        ++n_nontrivial;
                        cells += std::string(nc++ ? ",\n" : "\n") + cell;
                    }
                }
                std::fprintf(stderr, "census q=%lld k=%d rank=%d done (%.1fs)\n", (long long)q, k, Mo->rank, since(t0));
            }
        }
        body += "\"census\":" + Obj().add("qmax", qmax).add("kmax", kmax).add("pmax", pmax).add("modules", n_mod)
                                     .add("cells_total", n_cells).add("cells_trivial_by_squarefree_chi_mod_p", n_trivial_sqfree)
                                     .add("cells_nontrivial", n_nontrivial).str();
        body += ",\"cells\":" + cells + "]";
    } else {
        std::cerr << "unknown suite\n";
        return 2;
    }
    body += ",\"seconds\":" + std::to_string(since(t0)) + "}\n";
    if (out.empty())
        std::cout << body;
    else
        std::ofstream(out) << body;
    return 0;
}
