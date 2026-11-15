// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception

// Langlandscape JL extension (WP HJ-6b): integral congruence modules of a definite Brandt lattice.  See JlCongruence.h.
#include "JlCongruence.h"

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <limits>
#include <sstream>

#include "../../../ModArithmetic/EngineCheck.h"
#include "../../NumberField/IntPolyFactor.h"

namespace hacs_jl {
namespace {

using nf::BigInt;

BigInt FloorDiv(const BigInt& a, const BigInt& b) {   // b != 0
    BigInt q, r;
    BigInt::divmod(a, b, q, r);
    if (!r.is_zero() && (r.is_neg() != b.is_neg())) q -= 1;
    return q;
}

// g = s a + t b, g = gcd(a, b) >= 0
void ExtGcd(const BigInt& a, const BigInt& b, BigInt& g, BigInt& s, BigInt& t) {
    BigInt r0 = a, r1 = b, s0 = 1, s1 = 0, t0 = 0, t1 = 1;
    while (!r1.is_zero()) {
        BigInt q, r;
        BigInt::divmod(r0, r1, q, r);
        r0 = r1; r1 = r;
        BigInt s2 = s0 - q * s1; s0 = s1; s1 = s2;
        BigInt t2 = t0 - q * t1; t0 = t1; t1 = t2;
    }
    if (r0.is_neg()) { r0 = -r0; s0 = -s0; t0 = -t0; }
    g = r0; s = s0; t = t0;
}

// Row echelon by unimodular row operations, pivots searched in columns [0, npiv); reduce: the entries above each pivot into [0, p).
// Returns the rank (the first `rank` rows are the pivot rows; the rest are zero on [0, npiv)).
size_t Echelon(ZMat& M, size_t npiv, bool reduce) {
    size_t r = 0;
    const size_t m = M.size();
    for (size_t c = 0; c < npiv && r < m; ++c) {
        size_t piv = m;
        for (size_t i = r; i < m; ++i)
            if (!M[i][c].is_zero()) { piv = i; break; }
        if (piv == m) continue;
        std::swap(M[r], M[piv]);
        for (size_t i = r + 1; i < m; ++i) {
            if (M[i][c].is_zero()) continue;
            const BigInt a = M[r][c], b = M[i][c];
            BigInt g, s, t;
            ExtGcd(a, b, g, s, t);
            const BigInt ag = a / g, bg = b / g;
            for (size_t j = c; j < M[r].size(); ++j) {
                const BigInt x = M[r][j], y = M[i][j];
                M[r][j] = s * x + t * y;
                M[i][j] = ag * y - bg * x;
            }
        }
        if (M[r][c].is_neg())
            for (auto& x : M[r]) x = -x;
        if (reduce)
            for (size_t j = 0; j < r; ++j) {
                if (M[j][c].is_zero()) continue;
                const BigInt q = FloorDiv(M[j][c], M[r][c]);
                if (q.is_zero()) continue;
                for (size_t l = c; l < M[j].size(); ++l) M[j][l] -= q * M[r][l];
            }
        ++r;
    }
    return r;
}

ZMat MatMul(const ZMat& A, const ZMat& B) {
    const size_t n = A.size(), k = B.size(), m = k ? B[0].size() : 0;
    ZMat C(n, std::vector<BigInt>(m, BigInt(0)));
    for (size_t i = 0; i < n; ++i)
        for (size_t l = 0; l < k; ++l) {
            if (A[i][l].is_zero()) continue;
            for (size_t j = 0; j < m; ++j) C[i][j] += A[i][l] * B[l][j];
        }
    return C;
}
ZMat Ident(size_t n) {
    ZMat I(n, std::vector<BigInt>(n, BigInt(0)));
    for (size_t i = 0; i < n; ++i) I[i][i] = 1;
    return I;
}
ZMat PolyAt(const std::vector<BigInt>& f, const ZMat& A) {   // Horner
    const size_t n = A.size();
    ZMat R(n, std::vector<BigInt>(n, BigInt(0)));
    for (size_t d = f.size(); d-- > 0;) {
        R = MatMul(R, A);
        for (size_t i = 0; i < n; ++i) R[i][i] += f[d];
    }
    return R;
}
std::vector<BigInt> PolyDivMonic(std::vector<BigInt> a, const std::vector<BigInt>& b) {   // exact: b monic, b | a
    const size_t db = b.size() - 1;
    if (a.size() < b.size()) return {BigInt(1)};
    std::vector<BigInt> q(a.size() - db, BigInt(0));
    for (size_t i = a.size(); i-- > db;) {
        const BigInt c = a[i];
        q[i - db] = c;
        for (size_t j = 0; j <= db; ++j) a[i - db + j] -= c * b[j];
    }
    for (size_t i = 0; i < db; ++i) ENGINE_CHECK_MSG(a[i].is_zero(), "PolyDivMonic: not exact");
    return q;
}

// The coordinates of v in the row-echelon basis B (exact; ENGINE_CHECK that v lies in the Z-span of B).
std::vector<BigInt> Coords(std::vector<BigInt> v, const ZMat& B) {
    std::vector<BigInt> c(B.size(), BigInt(0));
    for (size_t r = 0; r < B.size(); ++r) {
        size_t pc = 0;
        while (B[r][pc].is_zero()) ++pc;
        BigInt q, rem;
        BigInt::divmod(v[pc], B[r][pc], q, rem);
        ENGINE_CHECK_MSG(rem.is_zero(), "Coords: not in the lattice");
        c[r] = q;
        if (!q.is_zero())
            for (size_t j = 0; j < v.size(); ++j) v[j] -= q * B[r][j];
    }
    for (const BigInt& x : v) ENGINE_CHECK_MSG(x.is_zero(), "Coords: not in the span");
    return c;
}
// A restricted to the A-stable sublattice with row-echelon basis B: column a = the coordinates of A B[a].
ZMat Restrict(const ZMat& A, const ZMat& B) {
    const size_t h = A.size(), m = B.size();
    ZMat X(m, std::vector<BigInt>(m, BigInt(0)));
    for (size_t a = 0; a < m; ++a) {
        std::vector<BigInt> v(h, BigInt(0));
        for (size_t i = 0; i < h; ++i)
            for (size_t j = 0; j < h; ++j) v[i] += A[i][j] * B[a][j];
        const std::vector<BigInt> c = Coords(std::move(v), B);
        for (size_t r = 0; r < m; ++r) X[r][a] = c[r];
    }
    return X;
}
std::vector<BigInt> vec2(const ZMat& A) {
    std::vector<BigInt> v;
    for (const auto& row : A) v.insert(v.end(), row.begin(), row.end());
    return v;
}

ZMat OfRecord(const BrandtRecord& R, size_t o) {
    const uint32_t r = R.r;
    ZMat A(r, std::vector<BigInt>(r));
    for (uint32_t i = 0; i < r; ++i)
        for (uint32_t j = 0; j < r; ++j) A[i][j] = R.F[o][size_t(i) * r + j];
    return A;
}

uint64_t Fnv1a(const std::string& s) {
    uint64_t h = 0xcbf29ce484222325ULL;
    for (unsigned char c : s) { h ^= c; h *= 0x100000001b3ULL; }
    return h;
}
std::string Hex(uint64_t v) {
    char b[32];
    std::snprintf(b, sizeof b, "0x%016llx", static_cast<unsigned long long>(v));
    return b;
}

const std::vector<uint32_t>& SmallPrimes() {
    static const std::vector<uint32_t> P = [] {
        const uint32_t B = 1u << 20;
        std::vector<char> s(B + 1, 1);
        std::vector<uint32_t> out;
        for (uint32_t i = 2; i <= B; ++i) {
            if (!s[i]) continue;
            out.push_back(i);
            for (uint64_t j = uint64_t(i) * i; j <= B; j += i) s[j] = 0;
        }
        return out;
    }();
    return P;
}

BigInt PowMod(BigInt b, BigInt e, const BigInt& m) {
    BigInt r = 1;
    b = b.floor_mod(m);
    while (!e.is_zero()) {
        if (e.mod_u32(2) == 1) r = (r * b) % m;
        b = (b * b) % m;
        e = e / BigInt(2);
    }
    return r;
}
bool MillerRabin(const BigInt& n) {
    if (n < BigInt(2)) return false;
    BigInt d = n - 1;
    unsigned s = 0;
    while (d.mod_u32(2) == 0) { d = d / BigInt(2); ++s; }
    for (int a : {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53}) {
        if (BigInt(a) >= n) continue;
        BigInt x = PowMod(BigInt(a), d, n);
        if (x == BigInt(1) || x == n - 1) continue;
        bool comp = true;
        for (unsigned i = 1; i < s && comp; ++i) {
            x = (x * x) % n;
            if (x == n - 1) comp = false;
        }
        if (comp) return false;
    }
    return true;
}

std::string Q(const std::string& s) {
    std::string r = "\"";
    for (char c : s) {
        if (c == '"' || c == '\\') r += '\\';
        r += c;
    }
    return r + "\"";
}
std::string StrList(const std::vector<BigInt>& v) {
    std::string o = "[";
    for (size_t i = 0; i < v.size(); ++i) o += (i ? "," : "") + Q(v[i].to_string());
    return o + "]";
}
std::string FactJson(const Factored& f) {
    std::string o = "{\"pp\":[";
    for (size_t i = 0; i < f.pp.size(); ++i) o += (i ? "," : "") + std::string("[") + f.pp[i].p.to_string() + "," + std::to_string(f.pp[i].e) + "]";
    o += "],\"cofactor\":" + Q(f.cofactor.to_string()) + ",\"cofactor_prp\":" + (f.cofactor_prp ? "true" : "false") + ",\"text\":" + Q(f.text()) + "}";
    return o;
}
std::string Frac(BigInt a, BigInt b) {   // b > 0
    const BigInt g = BigInt::gcd(a, b);
    if (!g.is_zero() && g != BigInt(1)) { a = a / g; b = b / g; }
    return b == BigInt(1) ? a.to_string() : a.to_string() + "/" + b.to_string();
}

}  // namespace

std::vector<BigInt> CharpolyZ(const ZMat& A) {
    const size_t n = A.size();
    std::vector<BigInt> c(n + 1, BigInt(0));
    c[n] = 1;
    ZMat M(n, std::vector<BigInt>(n, BigInt(0)));
    for (size_t k = 1; k <= n; ++k) {
        M = MatMul(A, M);
        for (size_t i = 0; i < n; ++i) M[i][i] += c[n - k + 1];
        const ZMat AM = MatMul(A, M);
        BigInt tr = 0;
        for (size_t i = 0; i < n; ++i) tr += AM[i][i];
        BigInt q, r;
        BigInt::divmod(tr, BigInt(static_cast<int64_t>(k)), q, r);
        ENGINE_CHECK_MSG(r.is_zero(), "CharpolyZ: Faddeev-LeVerrier division not exact");
        c[n - k] = -q;
    }
    return c;
}

ZMat HermiteRows(ZMat rows) {
    if (rows.empty()) return rows;
    const size_t r = Echelon(rows, rows[0].size(), true);
    rows.resize(r);
    return rows;
}

ZMat KernelZ(const ZMat& A) {
    const size_t m = A.size(), n = m ? A[0].size() : 0;
    ZMat W(n, std::vector<BigInt>(m + n, BigInt(0)));
    for (size_t j = 0; j < n; ++j) {
        for (size_t i = 0; i < m; ++i) W[j][i] = A[i][j];
        W[j][m + j] = 1;
    }
    const size_t r = Echelon(W, m, false);
    ZMat K;
    for (size_t j = r; j < n; ++j) K.emplace_back(W[j].begin() + static_cast<std::ptrdiff_t>(m), W[j].end());
    return HermiteRows(K);
}

std::vector<BigInt> SmithInvariants(ZMat A) {
    std::vector<BigInt> out;
    const size_t m = A.size(), n = m ? A[0].size() : 0;
    for (size_t t = 0; t < std::min(m, n); ++t) {
        while (true) {
            // the nonzero entry of least |.| in the submatrix -> (t, t)
            size_t bi = m, bj = n;
            for (size_t i = t; i < m; ++i)
                for (size_t j = t; j < n; ++j)
                    if (!A[i][j].is_zero() && (bi == m || A[i][j].abs() < A[bi][bj].abs())) { bi = i; bj = j; }
            if (bi == m) return out;
            std::swap(A[t], A[bi]);
            for (size_t i = 0; i < m; ++i) std::swap(A[i][t], A[i][bj]);
            bool clean = true;
            const BigInt p = A[t][t];
            for (size_t i = t + 1; i < m; ++i) {
                if (A[i][t].is_zero()) continue;
                const BigInt q = A[i][t] / p;
                if (!q.is_zero())
                    for (size_t j = t; j < n; ++j) A[i][j] -= q * A[t][j];
                if (!A[i][t].is_zero()) clean = false;
            }
            for (size_t j = t + 1; j < n; ++j) {
                if (A[t][j].is_zero()) continue;
                const BigInt q = A[t][j] / p;
                if (!q.is_zero())
                    for (size_t i = t; i < m; ++i) A[i][j] -= q * A[i][t];
                if (!A[t][j].is_zero()) clean = false;
            }
            if (!clean) continue;
            // row t and column t are clear: the pivot must divide the rest
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
    return out;
}

std::string Factored::text() const {
    std::string o;
    for (const auto& x : pp) {
        if (!o.empty()) o += "*";
        o += x.p.to_string();
        if (x.e > 1) o += "^" + std::to_string(x.e);
    }
    if (cofactor != BigInt(1)) {
        if (!o.empty()) o += "*";
        o += "[" + cofactor.to_string() + (cofactor_prp ? ":prp]" : ":composite]");
    }
    return o.empty() ? "1" : o;
}

Factored FactorTrial(const BigInt& n0) {
    Factored F;
    BigInt n = n0.abs();
    if (n.is_zero()) { F.cofactor = 0; return F; }
    for (uint32_t p : SmallPrimes()) {
        if (n == BigInt(1)) break;
        if (n.bit_length() <= 40 && BigInt(int64_t(p) * p) > n) {   // what is left is prime
            break;
        }
        unsigned e = 0;
        while (n.mod_u32(p) == 0) { n = n.div_exact_u32(p); ++e; }
        if (e) F.pp.push_back({BigInt(int64_t(p)), e});
    }
    if (n != BigInt(1)) {
        if (n.bit_length() <= 40) {   // < p_max^2: prime
            F.pp.push_back({n, 1});
            std::sort(F.pp.begin(), F.pp.end(), [](const PrimePower& a, const PrimePower& b) { return a.p < b.p; });
        } else {
            F.cofactor = n;
            F.cofactor_prp = MillerRabin(n);
        }
    }
    return F;
}

BigInt PrimeTo6(BigInt n) {
    n = n.abs();
    if (n.is_zero()) return n;
    while (n.mod_u32(2) == 0) n = n.div_exact_u32(2);
    while (n.mod_u32(3) == 0) n = n.div_exact_u32(3);
    return n;
}

CongCell RunJlCongruence(const BrandtRecord& R) {
    const auto t0 = std::chrono::steady_clock::now();
    CongCell C;
    C.where = R.where;
    C.D = R.D; C.M = R.M; C.k = R.k; C.N = R.N; C.h = R.r;
    if (R.M == 1 && R.N >= 2) C.mazur_num = MazurNumber(R.N);
    auto done = [&](const std::string& st) {
        C.status = st;
        C.seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        return C;
    };
    if (R.r == 0) return done("rank0");
    const size_t h = R.r, no = R.ops.size();
    std::vector<ZMat> T(no);
    for (size_t o = 0; o < no; ++o) T[o] = OfRecord(R, o);

    // --- theta: T_p (p prime to N first), then T_a + c T_b, then T_a + T_b + T_c; charpoly squarefree and fully factored -------------
    std::vector<size_t> order;
    for (size_t o = 0; o < no; ++o)
        if (R.N % R.ops[o] != 0) order.push_back(o);
    for (size_t o = 0; o < no; ++o)
        if (R.N % R.ops[o] == 0) order.push_back(o);
    std::vector<std::vector<std::pair<size_t, int>>> cands;
    for (size_t a : order) cands.push_back({{a, 1}});
    for (size_t ia = 0; ia < order.size(); ++ia)
        for (size_t ib = ia + 1; ib < order.size(); ++ib)
            for (int c : {1, -1, 2, -2, 3, -3}) cands.push_back({{order[ia], 1}, {order[ib], c}});
    for (size_t ia = 0; ia < order.size(); ++ia)
        for (size_t ib = ia + 1; ib < order.size(); ++ib)
            for (size_t ic = ib + 1; ic < order.size(); ++ic) cands.push_back({{order[ia], 1}, {order[ib], 1}, {order[ic], 1}});
    ZMat theta;
    std::vector<BigInt> chi;
    nf::ZFactorisation fac;
    bool found = false;
    for (const auto& cand : cands) {
        ++C.theta_tries;
        ZMat X(h, std::vector<BigInt>(h, BigInt(0)));
        for (auto [o, c] : cand)
            for (size_t i = 0; i < h; ++i)
                for (size_t j = 0; j < h; ++j) X[i][j] += BigInt(c) * T[o][i][j];
        std::vector<BigInt> f = CharpolyZ(X);
        nf::ZFactorisation z = nf::factor_monic_over_z(f);
        bool sqf = z.verified && z.complete;
        for (const auto& g : z.factors) sqf = sqf && g.multiplicity == 1;
        if (!sqf) continue;
        theta = std::move(X);
        chi = std::move(f);
        fac = std::move(z);
        for (auto [o, c] : cand) C.theta.emplace_back(R.ops[o], c);
        found = true;
        break;
    }
    if (found) {
        std::ostringstream t;
        for (size_t i = 0; i < C.theta.size(); ++i) {
            const int c = C.theta[i].second;
            if (i) t << (c < 0 ? " - " : " + ");
            else if (c < 0) t << "-";
            const int ac = c < 0 ? -c : c;
            if (ac != 1) t << ac;
            t << "T_" << C.theta[i].first;
        }
        C.theta_text = t.str();
    }

    // --- the Hecke ring Z[T_p : p in ops] in End(L): closure of Z*1 under the generators, vectorised row-major ------------------------
    auto vec = [&](const ZMat& A) {
        std::vector<BigInt> v;
        v.reserve(h * h);
        for (const auto& row : A) v.insert(v.end(), row.begin(), row.end());
        return v;
    };
    auto mat = [&](const std::vector<BigInt>& v) {
        ZMat A(h, std::vector<BigInt>(h));
        for (size_t i = 0; i < h; ++i)
            for (size_t j = 0; j < h; ++j) A[i][j] = v[i * h + j];
        return A;
    };
    ZMat basis = HermiteRows({vec(Ident(h))});
    for (bool changed = true; changed;) {
        changed = false;
        const ZMat snap = basis;
        for (const auto& b : snap)
            for (size_t o = 0; o < no; ++o) {
                ZMat nb = basis;
                nb.push_back(vec(MatMul(T[o], mat(b))));
                nb = HermiteRows(std::move(nb));
                if (nb != basis) { basis = std::move(nb); changed = true; }
            }
    }
    C.hecke_rank = static_cast<uint32_t>(basis.size());
    for (const BigInt& d : SmithInvariants(basis)) {
        C.hecke_index *= d;
        if (d != BigInt(1)) C.hecke_smith.push_back(d);
    }
    C.hecke_index_f = FactorTrial(C.hecke_index);

    // --- k = 2: the weights w_c = |Gamma_c| / 2 and the self-adjointness F_ij w_j = F_ji w_i ------------------------------------------
    std::vector<BigInt> w;
    if (R.gammas.size() == h) {
        bool even = true;
        for (uint64_t g : R.gammas) even = even && g % 2 == 0 && g > 0;
        if (even) {
            for (uint64_t g : R.gammas) w.push_back(BigInt::from_u64(g / 2));
            C.gram_possible = true;
            C.selfadjoint = true;
            for (size_t o = 0; o < no; ++o)
                for (size_t i = 0; i < h; ++i)
                    for (size_t j = 0; j < h; ++j)
                        if (T[o][i][j] * w[j] != T[o][j][i] * w[i]) C.selfadjoint = false;
        }
    }
    BigInt Wl = 1;
    for (const BigInt& x : w) Wl = Wl / BigInt::gcd(Wl, x) * x;

    if (!found) return done("no_squarefree_theta");

    // --- the orbits ------------------------------------------------------------------------------------------------------------------
    bool bad = false;
    for (const auto& g : fac.factors) {
        CongOrbit O;
        O.f = g.poly;
        const size_t deg = O.f.size() - 1;
        const ZMat Ki = KernelZ(PolyAt(O.f, theta));
        const ZMat Kc = KernelZ(PolyAt(PolyDivMonic(chi, O.f), theta));
        O.rank_i = static_cast<uint32_t>(Ki.size());
        O.rank_ic = static_cast<uint32_t>(Kc.size());
        if (O.rank_i != deg || O.rank_i + O.rank_ic != h) bad = true;
        if (R.k == 2 && deg == 1) {   // the constant vector: theta * 1 = (sum c_p (p+1)) * 1 at k = 2
            const ZMat Fi = PolyAt(O.f, theta);
            bool kills = true;
            for (size_t i = 0; i < h && kills; ++i) {
                BigInt s = 0;
                for (size_t j = 0; j < h; ++j) s += Fi[i][j];
                kills = s.is_zero();
            }
            O.eisenstein = kills;
        }
        // C_i = Z^h / (row span of Ki and Kc)
        ZMat B = Ki;
        B.insert(B.end(), Kc.begin(), Kc.end());
        if (!B.empty()) {
            const std::vector<BigInt> s = SmithInvariants(B);
            if (s.size() == h) {
                for (const BigInt& d : s) {
                    O.order *= d;
                    if (d != BigInt(1)) O.smith.push_back(d);
                }
            } else {
                bad = true;
                O.order = 0;
            }
        }
        O.order_f = FactorTrial(O.order);
        // T_p on L_i in the HNF basis Ki (Ki is T-stable and saturated, so the coordinates are integral)
        if (!bad && !Ki.empty())
            for (size_t oi = 0, used = 0; oi < order.size() && used < 3; ++oi) {
                const size_t o = order[oi];
                if (R.N % R.ops[o] == 0) continue;
                ++used;
                O.tp_on_Li.emplace_back(R.ops[o], CharpolyZ(Restrict(T[o], Ki)));
            }
        // the ring congruence module (T_i x T_i^c) / T, T = Z[T_p : p in ops] (the Z-basis `basis` above), T_i its image in End(L_i):
        // an invariant of the abstract ring T in End_Q(V), independent of the lattice L
        if (!bad && !Ki.empty() && !Kc.empty()) {
            ZMat Ii, Ic;
            for (const auto& b : basis) {
                Ii.push_back(vec2(Restrict(mat(b), Ki)));
                Ic.push_back(vec2(Restrict(mat(b), Kc)));
            }
            const ZMat Bi = HermiteRows(Ii), Bc = HermiteRows(Ic);
            ZMat Y;   // rows: the coordinates of (t|L_i, t|L_i^c) in Bi (+) Bc
            for (size_t a = 0; a < basis.size(); ++a) {
                std::vector<BigInt> y = Coords(Ii[a], Bi);
                const std::vector<BigInt> yc = Coords(Ic[a], Bc);
                y.insert(y.end(), yc.begin(), yc.end());
                Y.push_back(std::move(y));
            }
            O.ring_ran = true;
            O.ring_rank_i = static_cast<uint32_t>(Bi.size());
            O.ring_rank_ic = static_cast<uint32_t>(Bc.size());
            const std::vector<BigInt> sy = SmithInvariants(Y);
            if (sy.size() == Bi.size() + Bc.size()) {
                for (const BigInt& d : sy) {
                    O.ring_order *= d;
                    if (d != BigInt(1)) O.ring_smith.push_back(d);
                }
            } else {
                O.ring_order = 0;   // T -> T_i x T_i^c not of full rank: ops do not generate T (x) Q
            }
            O.ring_order_f = FactorTrial(O.ring_order);
        } else if (!bad && !Ki.empty()) {
            O.ring_ran = true;   // a single orbit: T_i = T, trivial
            O.ring_rank_i = C.hecke_rank;
        }
        // Gram on L_i of <x, y> = sum x_c y_c / w_c, scaled by W = lcm w_c (integral), unscaled on print
        if (C.gram_possible && !Ki.empty()) {
            ZMat G(Ki.size(), std::vector<BigInt>(Ki.size(), BigInt(0)));
            for (size_t a = 0; a < Ki.size(); ++a)
                for (size_t b = 0; b < Ki.size(); ++b)
                    for (size_t c = 0; c < h; ++c) G[a][b] += Ki[a][c] * Ki[b][c] * (Wl / w[c]);
            BigInt det = 1;
            for (const BigInt& d : SmithInvariants(G)) {
                O.gram_smith.push_back(Frac(d, Wl));
                det *= d;
            }
            O.gram_det = Frac(det, BigInt::pow(Wl, Ki.size()));
            BigInt num = det / BigInt::gcd(det, BigInt::pow(Wl, Ki.size()));
            O.gram_det_num_f = FactorTrial(num);
            O.gram_ran = true;
        }
        C.orbits.push_back(std::move(O));
    }
    return done(bad ? "bad_decomposition" : "ok");
}

std::string CongCell::json(size_t i) const {
    std::ostringstream o;
    o << "{\"schema\":\"jl_congruence/v1\",\"tag\":\"computed (HACS-native JL module)\",\"D\":" << D << ",\"M\":" << M << ",\"k\":" << k
      << ",\"N\":" << N << ",\"h\":" << h << ",\"status\":" << Q(status) << ",\"file\":" << Q(where);
    o << ",\"theta\":" << Q(theta_text) << ",\"theta_tries\":" << theta_tries << ",\"n_orbits\":" << orbits.size();
    o << ",\"hecke_ring\":{\"gens\":\"ops\",\"rank\":" << hecke_rank << ",\"smith\":" << StrList(hecke_smith)
      << ",\"index\":" << Q(hecke_index.to_string()) << ",\"index_factor\":" << FactJson(hecke_index_f) << "}";
    o << ",\"mazur_num\":" << mazur_num << ",\"selfadjoint_w\":" << (gram_possible ? (selfadjoint ? "true" : "false") : "null");
    if (i < orbits.size()) {
        const CongOrbit& O = orbits[i];
        const size_t deg = O.f.size() - 1;
        std::string ftxt;
        for (size_t j = 0; j < O.f.size(); ++j) ftxt += (j ? "," : "") + O.f[j].to_string();
        o << ",\"tp_on_Li\":{";
        for (size_t j = 0; j < O.tp_on_Li.size(); ++j) o << (j ? "," : "") << "\"" << O.tp_on_Li[j].first << "\":" << StrList(O.tp_on_Li[j].second);
        o << "}";
        o << ",\"orbit\":" << i << ",\"deg\":" << deg << ",\"f\":" << (deg <= 6 ? StrList(O.f) : "null") << ",\"f_fnv\":" << Q(Hex(Fnv1a(ftxt)))
          << ",\"f_text\":" << Q(deg <= 6 ? nf::zpoly_text(O.f, "x") : "") << ",\"eisenstein\":" << (O.eisenstein ? "true" : "false")
          << ",\"rank_i\":" << O.rank_i << ",\"rank_ic\":" << O.rank_ic << ",\"smith\":" << StrList(O.smith) << ",\"order\":" << Q(O.order.to_string())
          << ",\"order_factor\":" << FactJson(O.order_f);
        if (O.ring_ran)
            o << ",\"ring_cong\":{\"what\":\"(T_i x T_i^c)/T, T = Z[T_p : p in ops], lattice-independent\",\"rank_i\":" << O.ring_rank_i
              << ",\"rank_ic\":" << O.ring_rank_ic << ",\"smith\":" << StrList(O.ring_smith) << ",\"order\":" << Q(O.ring_order.to_string())
              << ",\"order_factor\":" << FactJson(O.ring_order_f) << "}";
        else
            o << ",\"ring_cong\":null";
        if (O.gram_ran) {
            o << ",\"gram\":{\"pairing\":\"sum x_c y_c / w_c, w_c = |Gamma_c|/2\",\"smith\":[";
            for (size_t j = 0; j < O.gram_smith.size(); ++j) o << (j ? "," : "") << Q(O.gram_smith[j]);
            o << "],\"det\":" << Q(O.gram_det) << ",\"det_num_factor\":" << FactJson(O.gram_det_num_f) << "}";
        } else {
            o << ",\"gram\":null";
        }
    } else {
        o << ",\"orbit\":null";
    }
    char b[32];
    std::snprintf(b, sizeof b, "%.3f", seconds);
    o << ",\"wall_s\":" << b << "}";
    return o.str();
}

}  // namespace hacs_jl
