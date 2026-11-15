// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
#include "Quat.h"

#include <algorithm>
#include <set>

namespace hacs_jl {

i128 mul_chk(i128 a, i128 b) {
    i128 r;
    if (__builtin_mul_overflow(a, b, &r)) throw std::overflow_error("hacs_jl: i128 multiplication overflow");
    return r;
}
i128 add_chk(i128 a, i128 b) {
    i128 r;
    if (__builtin_add_overflow(a, b, &r)) throw std::overflow_error("hacs_jl: i128 addition overflow");
    return r;
}
i128 gcd128(i128 a, i128 b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        i128 t = a % b;
        a = b;
        b = t;
    }
    return a;
}
i128 floordiv128(i128 a, i128 b) {
    i128 q = a / b, r = a % b;
    if (r != 0 && ((r < 0) != (b < 0))) --q;
    return q;
}
i128 mod128(i128 a, i128 m) {
    i128 r = a % m;
    return r < 0 ? r + m : r;
}
i128 exact_div(i128 a, i128 b) {
    if (b == 0 || a % b != 0) throw std::logic_error("hacs_jl: inexact division");
    return a / b;
}
std::string to_string128(i128 v) {
    if (v == 0) return "0";
    bool neg = v < 0;
    unsigned __int128 u = neg ? (unsigned __int128)(-(v + 1)) + 1 : (unsigned __int128)v;
    std::string s;
    while (u) {
        s.push_back(char('0' + int(u % 10)));
        u /= 10;
    }
    if (neg) s.push_back('-');
    std::reverse(s.begin(), s.end());
    return s;
}
i64 to_i64(i128 v) {
    if (v > (i128)INT64_MAX || v < (i128)INT64_MIN) throw std::overflow_error("hacs_jl: value exceeds int64");
    return (i64)v;
}

std::vector<i64> prime_factors(i64 n) {
    std::vector<i64> out;
    if (n < 0) n = -n;
    for (i64 p = 2; p * p <= n; ++p) {
        if (n % p == 0) {
            out.push_back(p);
            while (n % p == 0) n /= p;
        }
    }
    if (n > 1) out.push_back(n);
    return out;
}
bool is_prime(i64 n) {
    if (n < 2) return false;
    for (i64 p = 2; p * p <= n; ++p)
        if (n % p == 0) return false;
    return true;
}
bool is_squarefree(i64 n) {
    if (n < 1) return false;
    for (i64 p = 2; p * p <= n; ++p) {
        if (n % (p * p) == 0) return false;
        if (n % p == 0) n /= p;
    }
    return true;
}
i64 powmod(i64 b, i64 e, i64 m) {
    i128 r = 1, x = mod128(b, m);
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (i64)r;
}
int legendre(i64 a, i64 p) {
    i64 r = powmod(a, (p - 1) / 2, p);
    if (r == 0) return 0;
    return r == 1 ? 1 : -1;
}
int kronecker(i64 a, i64 n) {
    // (a/n) for n > 0, via factorisation (n small in our uses)
    int res = 1;
    i64 m = n;
    for (i64 p : prime_factors(n)) {
        int e = 0;
        while (m % p == 0) {
            m /= p;
            ++e;
        }
        int s;
        if (p == 2) {
            if (a % 2 == 0) s = 0;
            else {
                i64 r = ((a % 8) + 8) % 8;
                s = (r == 1 || r == 7) ? 1 : -1;
            }
        } else {
            s = legendre(a, p);
        }
        for (int t = 0; t < e; ++t) res *= s;
    }
    return res;
}
i64 sqrt_mod(i64 a, i64 p) {
    a = (i64)mod128(a, p);
    if (a == 0) return 0;
    if (p == 2) return a;
    if (legendre(a, p) != 1) throw std::logic_error("hacs_jl: sqrt_mod of a non-residue");
    i64 q = p - 1;
    int s = 0;
    while (q % 2 == 0) {
        q /= 2;
        ++s;
    }
    i64 z = 2;
    while (legendre(z, p) != -1) ++z;
    i64 m = s, c = powmod(z, q, p), t = powmod(a, q, p), r = powmod(a, (q + 1) / 2, p);
    while (t != 1) {
        i64 i = 0, tt = t;
        while (tt != 1) {
            tt = (i64)((i128)tt * tt % p);
            ++i;
        }
        i64 b = c;
        for (i64 j = 0; j < m - i - 1; ++j) b = (i64)((i128)b * b % p);
        m = i;
        c = (i64)((i128)b * b % p);
        t = (i64)((i128)t * c % p);
        r = (i64)((i128)r * b % p);
    }
    return r;
}

int hilbert_symbol(i64 a, i64 b, i64 p) {
    int alpha = 0, beta = 0;
    while (a % p == 0) {
        a /= p;
        ++alpha;
    }
    while (b % p == 0) {
        b /= p;
        ++beta;
    }
    if (p == 2) {
        auto eps = [](i64 u) { return (int)((((u % 4) + 4) % 4 == 3) ? 1 : 0); };   // (u-1)/2 mod 2
        auto omg = [](i64 u) {
            i64 r = ((u % 8) + 8) % 8;
            return (int)((r == 3 || r == 5) ? 1 : 0);                                // (u^2-1)/8 mod 2
        };
        int e = eps(a) * eps(b) + alpha * omg(b) + beta * omg(a);
        return (e % 2) ? -1 : 1;
    }
    int s = ((alpha * beta) % 2 && ((p - 1) / 2) % 2) ? -1 : 1;
    if (beta % 2) s *= legendre(a, p);
    if (alpha % 2) s *= legendre(b, p);
    return s;
}

static bool ramifies_exactly(i64 a, i64 b, const std::set<i64>& target) {
    std::set<i64> ram;
    for (i64 p : prime_factors(2 * a * b))
        if (hilbert_symbol(a, b, p) == -1) ram.insert(p);
    return ram == target;
}

std::pair<i64, i64> find_ab(i64 D) {
    if (D < 2 || !is_squarefree(D)) throw std::invalid_argument("hacs_jl::find_ab: D must be squarefree >= 2");
    auto pf = prime_factors(D);
    if (pf.size() % 2 == 0) throw std::invalid_argument("hacs_jl::find_ab: omega(D) must be odd");
    std::set<i64> target(pf.begin(), pf.end());
    // An odd ramified prime divides ab (the Hilbert symbol is 1 at odd p not dividing ab), so |ab| runs over the
    // multiples of the odd part of D; skipping the other |ab| does not change the first hit of quat.py's order.
    i64 Dodd = D % 2 ? D : D / 2;
    for (i64 P = Dodd;; P += Dodd) {
        // pairs with (-a)(-b) = P, |b| <= |a|, ordered by a ascending (quat.py: sorted tuples (P, a, b)),
        // i.e. by B = |b| ascending
        for (i64 B = 1; B * B <= P; ++B) {
            if (P % B) continue;
            i64 A = P / B;
            if (ramifies_exactly(-A, -B, target)) return {-A, -B};
        }
        if (P > (i64)1 << 40) throw std::runtime_error("hacs_jl::find_ab: search exhausted");
    }
}

// ---------------------------------------------------------------- QElt / QuatAlgebra
void QElt::normalise() {
    if (den < 0) {
        den = -den;
        for (auto& v : c) v = -v;
    }
    i128 g = den;
    for (auto v : c) g = gcd128(g, v);
    if (g > 1) {
        den /= g;
        for (auto& v : c) v /= g;
    }
}

QuatAlgebra::QuatAlgebra(i64 D) : D_(D) {
    auto ab = find_ab(D);
    a_ = ab.first;
    b_ = ab.second;
}
QuatAlgebra::QuatAlgebra(i64 D, i64 a, i64 b) : D_(D), a_(a), b_(b) {
    auto pf = prime_factors(D);
    if (a >= 0 || b >= 0 || !ramifies_exactly(a, b, std::set<i64>(pf.begin(), pf.end())))
        throw std::invalid_argument("hacs_jl::QuatAlgebra: (a,b) not definite / not ramified exactly at D");
}

std::array<i128, 4> QuatAlgebra::mul_std(const std::array<i128, 4>& x, const std::array<i128, 4>& y) const {
    const i128 a = a_, b = b_;
    auto M = mul_chk;
    auto A = add_chk;
    // (x0 + x1 i + x2 j + x3 k)(y0 + y1 i + y2 j + y3 k);  i^2=a, j^2=b, k^2=-ab, ij=k, ji=-k,
    // ik = a j, ki = -a j, jk = -b i, kj = b i
    std::array<i128, 4> z;
    z[0] = A(A(M(x[0], y[0]), M(a, M(x[1], y[1]))), A(M(b, M(x[2], y[2])), -M(M(a, b), M(x[3], y[3]))));
    z[1] = A(A(M(x[0], y[1]), M(x[1], y[0])), A(-M(b, M(x[2], y[3])), M(b, M(x[3], y[2]))));
    z[2] = A(A(M(x[0], y[2]), M(x[2], y[0])), A(M(a, M(x[1], y[3])), -M(a, M(x[3], y[1]))));
    z[3] = A(A(M(x[0], y[3]), M(x[3], y[0])), A(M(x[1], y[2]), -M(x[2], y[1])));
    return z;
}
QElt QuatAlgebra::mul(const QElt& x, const QElt& y) const {
    QElt z;
    z.c = mul_std(x.c, y.c);
    z.den = mul_chk(x.den, y.den);
    z.normalise();
    return z;
}
QElt QuatAlgebra::conj(const QElt& x) const {
    QElt z = x;
    for (int t = 1; t < 4; ++t) z.c[t] = -z.c[t];
    return z;
}
std::pair<i128, i128> QuatAlgebra::trd(const QElt& x) const {
    i128 n = 2 * x.c[0], d = x.den, g = gcd128(n, d);
    return {n / g, d / g};
}
std::pair<i128, i128> QuatAlgebra::nrd(const QElt& x) const {
    const i128 a = a_, b = b_;
    i128 n = add_chk(add_chk(mul_chk(x.c[0], x.c[0]), -mul_chk(a, mul_chk(x.c[1], x.c[1]))),
                     add_chk(-mul_chk(b, mul_chk(x.c[2], x.c[2])), mul_chk(mul_chk(a, b), mul_chk(x.c[3], x.c[3]))));
    i128 d = mul_chk(x.den, x.den), g = gcd128(n, d);
    return {n / g, d / g};
}

}  // namespace hacs_jl
