// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
#include "ClassSet.h"

#include <chrono>
#include <cmath>
#include <deque>
#include <random>

namespace hacs_jl {

u64 fnv1a64(const std::string& s, u64 h) {
    for (unsigned char c : s) {
        h ^= c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

ThetaInfo ClassSet::qf_theta(const Lat& J, i64 N) const {
    Reduced R = lll_reduce(J, O_.embedding(), O_.gram());
    const double pi2 = 9.8696044010893586;
    i64 X = std::max<i64>(1, (i64)std::ceil(std::sqrt((double)opt_.theta_K * (double)O_.D() / (2 * pi2))));
    for (;;) {
        std::vector<u64> cnt(X + 1, 0);
        ThetaInfo t;
        i64 xbest[4] = {0, 0, 0, 0};
        fp_enumerate(R, mul_chk(2 * (i128)N, X), [&](const i64* x, i128 v2) {
            i128 n = v2 / 2;
            if (v2 % 2 || n % N) throw std::logic_error("hacs_jl::qf_theta: nrd not divisible by nrd(J)");
            cnt[(size_t)(n / N)]++;
            if (t.min_nrd == 0 || n < t.min_nrd) {
                t.min_nrd = n;
                for (int s = 0; s < 4; ++s) xbest[s] = x[s];
            }
            return true;
        });
        u64 cum = 0;
        for (i64 n = 1; n <= X; ++n) {
            cum += cnt[n];
            if (cum >= (u64)opt_.theta_K) {
                t.prefix.assign(cnt.begin() + 1, cnt.begin() + n + 1);
                std::string s;
                for (size_t k = 0; k < t.prefix.size(); ++k) {
                    if (k) s += ",";
                    s += std::to_string(t.prefix[k]);
                }
                t.hash = fnv1a64(s);
                t.min_vec = combine(R, xbest);
                return t;
            }
        }
        X *= 2;
    }
}

std::pair<Lat, i64> ClassSet::reduce(const Lat& J, i64 N, const ThetaInfo& t) const {
    i64 Np = to_i64(exact_div(t.min_nrd, N));
    Vec4 gc = O_.conj(t.min_vec);
    std::vector<Vec4> gens;
    for (int s = 0; s < 4; ++s) {
        Vec4 v = O_.mul(J.h[s], gc);
        for (auto& x : v) x = exact_div(x, N);
        gens.push_back(v);
    }
    return {hnf(gens, 1, (i128)Np * Np), Np};
}

bool ClassSet::equivalent(const Lat& I, i64 NI, const Lat& J, i64 NJ) const {
    ++st_.exact_tests;
    i128 n = (i128)NI * NJ;
    Lat P = O_.product(O_.conj(I), J, n * n);
    Reduced R = lll_reduce(P, O_.embedding(), O_.gram());
    bool found = !fp_enumerate(R, 2 * n, [](const i64*, i128) { return false; });
    if (found) ++st_.exact_tests_positive;
    return found;
}

int ClassSet::unit_count(const Lat& RN, i64 N) const {
    Reduced R = lll_reduce(RN, O_.embedding(), O_.gram());
    i128 n2 = (i128)N * N;
    int c = 0;
    fp_enumerate(R, 2 * n2, [&](const i64*, i128 v2) {
        if (v2 != 2 * n2) throw std::logic_error("hacs_jl::unit_count: element of nrd < nrd(I)^2 in conj(I) I");
        ++c;
        return true;
    });
    return c;
}

Lat ClassSet::pair_lattice(const ClassRep& a, const ClassRep& b) const {
    i128 n = (i128)a.N * b.N;
    return O_.product(a.Ic, b.I, n * n);
}

namespace {
// reduce the 4 x 4 matrix rows over F_p to row echelon form; return the nonzero rows
std::vector<std::array<i64, 4>> echelon_mod(std::vector<std::array<i64, 4>> rows, i64 p) {
    std::vector<std::array<i64, 4>> out;
    int col = 0;
    size_t r0 = 0;
    for (col = 0; col < 4 && r0 < rows.size(); ++col) {
        size_t piv = r0;
        while (piv < rows.size() && rows[piv][col] == 0) ++piv;
        if (piv == rows.size()) continue;
        std::swap(rows[piv], rows[r0]);
        i64 inv = powmod(rows[r0][col], p - 2, p);
        for (auto& v : rows[r0]) v = (i64)((i128)v * inv % p);
        for (size_t i = 0; i < rows.size(); ++i) {
            if (i == r0 || rows[i][col] == 0) continue;
            i64 f = rows[i][col];
            for (int m = 0; m < 4; ++m) rows[i][m] = (i64)mod128(rows[i][m] - (i128)f * rows[r0][m], p);
        }
        ++r0;
    }
    rows.resize(r0);
    return rows;
}
}  // namespace

std::vector<Lat> ClassSet::neighbours(const ClassRep& c, i64 p) const {
    if (O_.D() % p == 0 || !is_prime(p)) throw std::invalid_argument("hacs_jl::neighbours: p must be a prime not dividing D");
    const i128 N = c.N, N2 = N * N;
    // integral Gram of the norm form of R = O_r(I) in the basis RN.h[s] / N: Q_R(y) = y^T GR y / 2
    i128 GR[4][4];
    const Gram4& G0 = O_.gram();
    for (int s = 0; s < 4; ++s)
        for (int t = 0; t < 4; ++t) {
            i128 v = 0;
            for (int i = 0; i < 4; ++i) {
                if (!c.RN.h[s][i]) continue;
                i128 w = 0;
                for (int j = 0; j < 4; ++j) w = add_chk(w, mul_chk(G0.g[i][j], c.RN.h[t][j]));
                v = add_chk(v, mul_chk(c.RN.h[s][i], w));
            }
            GR[s][t] = mod128(exact_div(v, N2), 2 * (i128)p);  // only needed mod 2p
        }
    auto Qmod = [&](const i64 y[4]) -> i64 {  // Q_R(y) mod p
        i128 v = 0;
        for (int s = 0; s < 4; ++s)
            for (int t = 0; t < 4; ++t) v += GR[s][t] * y[s] % (2 * (i128)p) * y[t] % (2 * (i128)p);
        v = mod128(v, 2 * (i128)p);
        return (i64)(v / 2);  // v even
    };
    // 1. isotropic y0 (alpha_0 = sum y0_s RN_s / N has nrd = 0 mod p, alpha_0 not in pR)
    i64 y0[4] = {0, 0, 0, 0};
    bool ok = false;
    if (p <= 7) {
        for (i64 m = 1; m < p * p * p * p && !ok; ++m) {
            i64 y[4] = {m % p, (m / p) % p, (m / p / p) % p, (m / p / p / p) % p};
            if (Qmod(y) == 0) {
                for (int s = 0; s < 4; ++s) y0[s] = y[s];
                ok = true;
            }
        }
    } else {
        std::mt19937_64 rng(0x5eedULL ^ (u64)p ^ ((u64)c.N << 20));
        i64 A = (i64)mod128(GR[0][0] / 2, p);
        for (int tries = 0; tries < 100000 && !ok; ++tries) {
            i64 y[4] = {0, (i64)(rng() % p), (i64)(rng() % p), (i64)(rng() % p)};
            i64 Bc = (i64)mod128(GR[0][1] * y[1] + GR[0][2] * y[2] + GR[0][3] * y[3], p);
            i64 C = Qmod(y);
            i64 x;
            if (A == 0) {
                if (Bc == 0) continue;
                x = (i64)mod128(-(i128)C * powmod(Bc, p - 2, p), p);
            } else {
                i64 disc = (i64)mod128((i128)Bc * Bc - 4 * (i128)A * C, p);
                if (disc != 0 && legendre(disc, p) != 1) continue;
                i64 r = sqrt_mod(disc, p);
                x = (i64)mod128((i128)(r - Bc) * powmod(2 * A % p, p - 2, p), p);
            }
            y[0] = x;
            if (!y[0] && !y[1] && !y[2] && !y[3]) continue;
            if (Qmod(y) != 0) throw std::logic_error("hacs_jl::neighbours: isotropic solve failed");
            for (int s = 0; s < 4; ++s) y0[s] = y[s];
            ok = true;
        }
    }
    if (!ok) throw std::runtime_error("hacs_jl::neighbours: no zero divisor found");
    // 2. beta0 = N alpha_0 (O-coordinates); the right ideal alpha_0 R mod p in R-coordinates
    Vec4 beta0{{0, 0, 0, 0}};
    for (int s = 0; s < 4; ++s)
        for (int m = 0; m < 4; ++m) beta0[m] = add_chk(beta0[m], mul_chk(y0[s], c.RN.h[s][m]));
    std::vector<std::array<i64, 4>> rows;
    for (int t = 0; t < 4; ++t) {
        Vec4 v = O_.mul(beta0, c.RN.h[t]);  // = N^2 alpha_0 r_t
        for (auto& x : v) x = exact_div(x, N);  // = N alpha_0 r_t in RN
        Vec4 y = coords_in(c.RN, v);
        std::array<i64, 4> r;
        for (int m = 0; m < 4; ++m) r[m] = (i64)mod128(y[m], p);
        rows.push_back(r);
    }
    auto V = echelon_mod(rows, p);
    if (V.size() != 2) throw std::logic_error("hacs_jl::neighbours: alpha_0 R / p R is not 2-dimensional");
    // 3. the p+1 neighbours
    std::vector<Lat> out;
    out.reserve(p + 1);
    const i128 idx = (i128)p * p * N2;
    for (i64 s = 0; s <= p; ++s) {
        i64 y[4];
        for (int m = 0; m < 4; ++m) y[m] = (s < p) ? (i64)(((i128)V[0][m] + (i128)s * V[1][m]) % p) : V[1][m];
        Vec4 beta{{0, 0, 0, 0}};
        for (int u = 0; u < 4; ++u)
            if (y[u])
                for (int m = 0; m < 4; ++m) beta[m] = add_chk(beta[m], mul_chk(y[u], c.RN.h[u][m]));
        std::vector<Vec4> gens;
        gens.reserve(8);
        for (int u = 0; u < 4; ++u) {
            Vec4 v = O_.mul(c.I.h[u], beta);
            for (auto& x : v) x = exact_div(x, N);
            gens.push_back(v);
            Vec4 w = c.I.h[u];
            for (auto& x : w) x = mul_chk(x, p);
            gens.push_back(w);
        }
        out.push_back(hnf(gens, 1, idx));
    }
    return out;
}

int ClassSet::identify(const Lat& J, i64 NJ, bool complete) const {
    ++st_.identifications;
    ThetaInfo t = qf_theta(J, NJ);
    auto it = buckets_.find(t.hash);
    if (it == buckets_.end()) return -1;
    if (complete && it->second.size() == 1) {
        ++st_.single_bucket_shortcuts;
        return it->second[0];
    }
    auto red = reduce(J, NJ, t);
    for (int k : it->second)
        if (equivalent(reps_[k].I, reps_[k].N, red.first, red.second)) return k;
    return -1;
}

int ClassSet::add_class(const Lat& I, i64 N, const ThetaInfo& t) {
    ClassRep c;
    c.I = I;
    c.N = N;
    c.Ic = O_.conj(I);
    i128 n2 = (i128)N * N;
    c.RN = O_.product(c.Ic, I, n2 * n2);
    c.gamma = unit_count(c.RN, N);
    c.theta = t;
    if (c.gamma <= 0 || 24 % c.gamma) throw std::logic_error("hacs_jl::ClassSet: |Gamma_x| does not divide 24");
    reps_.push_back(c);
    sum24_ += 24 / c.gamma;
    auto& b = buckets_[t.hash];
    b.push_back((int)reps_.size() - 1);
    st_.max_bucket = std::max(st_.max_bucket, b.size());
    st_.buckets = buckets_.size();
    return (int)reps_.size() - 1;
}

ClassSet::ClassSet(const MaxOrder& O, Options opt) : O_(O), opt_(opt) {
    auto t0 = std::chrono::steady_clock::now();
    const i64 D = O.D();
    ell0_ = opt.ell0;
    if (!ell0_)
        for (i64 p = 2;; ++p)
            if (is_prime(p) && D % p) {
                ell0_ = p;
                break;
            }
    phi_ = 1;
    for (i64 p : prime_factors(D)) phi_ *= p - 1;
    Lat O1 = O.unit();
    {
        ThetaInfo t = qf_theta(O1, 1);
        // reduce O itself is a no-op (min nrd 1)
        add_class(O1, 1, t);
    }
    std::deque<int> queue{0};
    while (!queue.empty() && !(opt.mass_stop && sum24_ == phi_)) {
        int idx = queue.front();
        queue.pop_front();
        auto nb = neighbours(reps_[idx], ell0_);
        for (const Lat& J : nb) {
            if (opt.mass_stop && sum24_ == phi_) break;
            i64 NJ = reps_[idx].N * ell0_;
            ++st_.identifications;
            ThetaInfo t = qf_theta(J, NJ);
            auto red = reduce(J, NJ, t);
            bool known = false;
            auto it = buckets_.find(t.hash);
            if (it != buckets_.end())
                for (int k : it->second)
                    if (equivalent(reps_[k].I, reps_[k].N, red.first, red.second)) {
                        known = true;
                        break;
                    }
            if (!known) {
                // theta of the reduced rep equals t (class invariant); its min vector is recomputed for later use
                ThetaInfo tr = qf_theta(red.first, red.second);
                if (tr.hash != t.hash) throw std::logic_error("hacs_jl::ClassSet: qf_theta not a class invariant");
                queue.push_back(add_class(red.first, red.second, tr));
                if (sum24_ > phi_) throw std::logic_error("hacs_jl::ClassSet: mass exceeded (duplicate class)");
            }
        }
    }
    if (sum24_ != phi_) throw std::logic_error("hacs_jl::ClassSet: BFS exhausted before the mass was reached");
    st_.seconds = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}

}  // namespace hacs_jl
