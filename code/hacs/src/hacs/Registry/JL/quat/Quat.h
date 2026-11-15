// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl quaternion core (WP HJ-1): exact integer helpers and the definite quaternion algebra
// B = (a, b)_Q, a, b < 0, ramified exactly at the primes of a squarefree D with omega(D) odd (and at infinity).
//
// (a, b) rule: identical to code/python/langlandscape/quat.py::find_ab -- candidates ordered by (|ab|, a, b) with
// b >= a (|b| <= |a|), the first one whose ramification set {p | 2ab : (a,b)_p = -1} equals the primes of D.
// quat.py restricts the search to |a| <= 400 and |ab| <= 3200; we search without bound. Both rules return the same
// pair whenever quat.py returns one whose |ab| <= 401 (in particular for every D <= 400 checked by the self-test against
// code/results/s01/classsets.json); beyond quat.py's range the rule is its unbounded extension.
//
// Arithmetic is exact: int64 storage, __int128 intermediates, every potentially overflowing operation is checked and
// throws std::overflow_error (never silently wraps).
#pragma once

#include <array>
#include <cstdint>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace hacs_jl {

using i64 = int64_t;
using u64 = uint64_t;
using i128 = __int128;

// ---------------------------------------------------------------- checked integer helpers
i128 mul_chk(i128 a, i128 b);
i128 add_chk(i128 a, i128 b);
i128 gcd128(i128 a, i128 b);           // >= 0
i128 floordiv128(i128 a, i128 b);      // floor(a / b), b != 0
i128 mod128(i128 a, i128 m);           // in [0, m), m > 0
i128 exact_div(i128 a, i128 b);        // throws if b does not divide a
std::string to_string128(i128 v);
i64 to_i64(i128 v);                    // throws if out of range

std::vector<i64> prime_factors(i64 n);  // distinct, ascending
bool is_prime(i64 n);
bool is_squarefree(i64 n);
i64 powmod(i64 b, i64 e, i64 m);
int legendre(i64 a, i64 p);            // p odd prime
int kronecker(i64 a, i64 n);           // Kronecker symbol (a/n), n > 0
i64 sqrt_mod(i64 a, i64 p);            // a QR mod odd prime p (Tonelli-Shanks); returns r with r^2 = a
int hilbert_symbol(i64 a, i64 b, i64 p);  // (a,b)_p, p prime (p = 2 included), a, b nonzero

// quat.py::find_ab rule (see header comment); throws std::invalid_argument if D is not squarefree with odd omega(D).
std::pair<i64, i64> find_ab(i64 D);

// ---------------------------------------------------------------- rational quaternions in the standard basis 1, i, j, k
// x = (c[0] + c[1] i + c[2] j + c[3] k) / den, den > 0; i^2 = a, j^2 = b, ij = -ji = k.
struct QElt {
    std::array<i128, 4> c{{0, 0, 0, 0}};
    i128 den = 1;
    void normalise();
};

class QuatAlgebra {
public:
    explicit QuatAlgebra(i64 D);           // uses find_ab(D)
    QuatAlgebra(i64 D, i64 a, i64 b);      // explicit pair (checked: ramified exactly at D)
    i64 D() const { return D_; }
    i64 a() const { return a_; }
    i64 b() const { return b_; }

    // integral-coordinate product in the standard basis (no denominators)
    std::array<i128, 4> mul_std(const std::array<i128, 4>& x, const std::array<i128, 4>& y) const;
    QElt mul(const QElt& x, const QElt& y) const;
    QElt conj(const QElt& x) const;
    // reduced trace / norm as fractions num/den (den > 0, reduced)
    std::pair<i128, i128> trd(const QElt& x) const;
    std::pair<i128, i128> nrd(const QElt& x) const;

private:
    i64 D_, a_, b_;
};

}  // namespace hacs_jl
