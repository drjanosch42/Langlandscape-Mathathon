// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
#include "Brandt2.h"

#include <algorithm>
#include <functional>
#include <random>

namespace hacs_jl {

std::vector<int> gammas_of(const ClassSet& C) {
    std::vector<int> g;
    for (const auto& c : C.classes()) g.push_back(c.gamma);
    return g;
}

CanonOrder canonical_order_v2(const ClassSet& C, int L) {
    const auto& cl = C.classes();
    const MaxOrder& O = C.order();
    const int r = (int)cl.size();
    std::vector<std::vector<u64>> th(r);
    for (int i = 0; i < r; ++i) {
        // O_r(I) = RN / N, nrd on O_r(I) = nrd on RN / N^2
        Reduced R = lll_reduce(cl[i].RN, O.embedding(), O.gram());
        auto cnt = count_values(R, (i128)cl[i].N * cl[i].N, L);
        th[i].assign(cnt.begin() + 1, cnt.end());
        if (th[i][0] != (u64)cl[i].gamma) throw std::logic_error("hacs_jl::canonical_order_v2: r(1) != |Gamma|");
    }
    auto key_less = [&](int a, int b) {
        if (cl[a].gamma != cl[b].gamma) return cl[a].gamma < cl[b].gamma;
        return th[a] < th[b];
    };
    CanonOrder co;
    co.perm.resize(r);
    for (int i = 0; i < r; ++i) co.perm[i] = i;
    std::stable_sort(co.perm.begin(), co.perm.end(), key_less);
    for (int i = 0; i < r; ++i) co.theta.push_back(th[co.perm[i]]);
    for (int i = 0; i < r;) {
        int j = i + 1;
        while (j < r && !key_less(co.perm[i], co.perm[j])) ++j;
        if (j - i >= 2) {
            std::vector<int> g;
            for (int k = i; k < j; ++k) g.push_back(k);
            co.ties.push_back(g);
        }
        i = j;
    }
    return co;
}

Mat permute(const Mat& F, const std::vector<int>& perm) {
    const size_t r = perm.size();
    Mat G(r * r);
    for (size_t a = 0; a < r; ++a)
        for (size_t b = 0; b < r; ++b) G[a * r + b] = F[(size_t)perm[a] * r + perm[b]];
    return G;
}

Mat brandt_neighbours(const ClassSet& C, i64 p) {
    const int r = C.h();
    Mat F((size_t)r * r, 0);
    for (int i = 0; i < r; ++i) {
        const ClassRep& c = C.classes()[i];
        for (const Lat& J : C.neighbours(c, p)) {
            int k = C.identify(J, c.N * p, true);
            if (k < 0) throw std::logic_error("hacs_jl::brandt_neighbours: neighbour in no class (class set incomplete)");
            F[(size_t)i * r + k]++;
        }
    }
    return F;
}

std::map<i64, Mat> brandt_theta_pairs(const ClassSet& C, const std::vector<i64>& ns) {
    const int r = C.h();
    i64 X = 0;
    for (i64 n : ns) X = std::max(X, n);
    std::map<i64, Mat> out;
    for (i64 n : ns) out[n] = Mat((size_t)r * r, 0);
    const auto& cl = C.classes();
    const MaxOrder& O = C.order();
    for (int i = 0; i < r; ++i)
        for (int j = i; j < r; ++j) {
            Lat P = C.pair_lattice(cl[i], cl[j]);
            Reduced R = lll_reduce(P, O.embedding(), O.gram());
            auto cnt = count_values(R, (i128)cl[i].N * cl[j].N, X);
            for (i64 n : ns) {
                u64 v = cnt[n];
                if (v % cl[j].gamma || v % cl[i].gamma)
                    throw std::logic_error("hacs_jl::brandt_theta_pairs: count not divisible by |Gamma|");
                out[n][(size_t)i * r + j] = (i64)(v / cl[j].gamma);
                out[n][(size_t)j * r + i] = (i64)(v / cl[i].gamma);
            }
        }
    return out;
}

bool row_sums_ok(const Mat& F, int r, i64 value) {
    for (int i = 0; i < r; ++i) {
        i64 s = 0;
        for (int j = 0; j < r; ++j) s += F[(size_t)i * r + j];
        if (s != value) return false;
    }
    return true;
}

bool weighted_symmetric(const Mat& F, const std::vector<int>& g) {
    const int r = (int)g.size();
    for (int i = 0; i < r; ++i)
        for (int j = 0; j < r; ++j)
            if ((i128)g[j] * F[(size_t)i * r + j] != (i128)g[i] * F[(size_t)j * r + i]) return false;
    return true;
}

Mat matmul(const Mat& A, const Mat& B, int r) {
    Mat C((size_t)r * r, 0);
    for (int i = 0; i < r; ++i)
        for (int k = 0; k < r; ++k) {
            i64 a = A[(size_t)i * r + k];
            if (!a) continue;
            for (int j = 0; j < r; ++j) C[(size_t)i * r + j] = to_i64((i128)C[(size_t)i * r + j] + (i128)a * B[(size_t)k * r + j]);
        }
    return C;
}

bool commute(const Mat& A, const Mat& B, int r) { return matmul(A, B, r) == matmul(B, A, r); }

std::string matrix_text(const Mat& F, int r) {
    std::string s;
    for (int i = 0; i < r; ++i) {
        if (i) s += ";";
        for (int j = 0; j < r; ++j) {
            if (j) s += ",";
            s += std::to_string(F[(size_t)i * r + j]);
        }
    }
    return s;
}

u64 matrix_fnv(const Mat& F, int r) { return fnv1a64(matrix_text(F, r)); }

std::optional<std::vector<int>> match_permutation(const std::vector<Mat>& ours, const std::vector<Mat>& ref, int r,
                                                  const std::vector<int>& go, const std::vector<int>& gr, u64 max_nodes,
                                                  bool* exhausted) {
    if (exhausted) *exhausted = false;
    if (ours.size() != ref.size()) return std::nullopt;
    std::vector<int> pi(r, -1);
    std::vector<char> used(r, 0);
    u64 nodes = 0;
    bool stop = false;
    std::function<bool(int)> rec = [&](int i) -> bool {
        if (i == r) return true;
        for (int c = 0; c < r; ++c) {
            if (stop) return false;
            if (used[c] || go[c] != gr[i]) continue;
            if (max_nodes && ++nodes > max_nodes) {
                stop = true;
                if (exhausted) *exhausted = true;
                return false;
            }
            pi[i] = c;
            bool ok = true;
            for (size_t o = 0; o < ours.size() && ok; ++o)
                for (int k = 0; k <= i && ok; ++k) {
                    if (ours[o][(size_t)c * r + pi[k]] != ref[o][(size_t)i * r + k]) ok = false;
                    if (ours[o][(size_t)pi[k] * r + c] != ref[o][(size_t)k * r + i]) ok = false;
                }
            if (!ok) continue;
            used[c] = 1;
            if (rec(i + 1)) return true;
            used[c] = 0;
        }
        pi[i] = -1;
        return false;
    };
    if (!rec(0)) return std::nullopt;
    return pi;
}

AlgebraDim algebra_dim(const std::vector<Mat>& ops, int r) {
    const u64 P = 2147483647ULL;
    struct Sp {
        std::vector<std::vector<std::pair<int, u64>>> rows;
    };
    std::vector<Sp> sp(ops.size());
    for (size_t o = 0; o < ops.size(); ++o) {
        sp[o].rows.resize(r);
        for (int i = 0; i < r; ++i)
            for (int j = 0; j < r; ++j) {
                i64 v = ops[o][(size_t)i * r + j];
                if (v) sp[o].rows[i].push_back({j, (u64)((v % (i64)P + (i64)P) % (i64)P)});
            }
    }
    std::vector<std::vector<u64>> basis;
    std::vector<int> pivots;
    auto inv = [&](u64 a) { return (u64)powmod((i64)a, (i64)P - 2, (i64)P); };
    auto reduce_add = [&](std::vector<u64> v) -> bool {
        for (size_t b = 0; b < basis.size(); ++b) {
            u64 c = v[pivots[b]];
            if (!c) continue;
            const auto& bb = basis[b];
            for (int m = 0; m < r; ++m)
                if (bb[m]) v[m] = (v[m] + (P - c) * bb[m]) % P;
        }
        int piv = -1;
        for (int m = 0; m < r; ++m)
            if (v[m]) {
                piv = m;
                break;
            }
        if (piv < 0) return false;
        u64 iv = inv(v[piv]);
        for (auto& x : v) x = x * iv % P;
        // keep basis fully reduced at pivot columns of new vector
        for (auto& bb : basis) {
            u64 c = bb[piv];
            if (!c) continue;
            for (int m = 0; m < r; ++m)
                if (v[m]) bb[m] = (bb[m] + (P - c) * v[m]) % P;
        }
        basis.push_back(std::move(v));
        pivots.push_back(piv);
        return true;
    };
    std::mt19937_64 rng(12345);
    std::vector<u64> v0(r);
    for (auto& x : v0) x = rng() % P;
    std::vector<std::vector<u64>> queue;
    if (reduce_add(v0)) queue.push_back(v0);
    for (size_t o = 0; o < ops.size() && (int)basis.size() < r; ++o) {
        // apply op o to every vector found so far (and to new ones), then move on
        std::vector<std::vector<u64>> work = queue;
        for (size_t w = 0; w < work.size() && (int)basis.size() < r; ++w) {
            for (size_t o2 = 0; o2 <= o && (int)basis.size() < r; ++o2) {
                std::vector<u64> img(r, 0);
                for (int i = 0; i < r; ++i) {
                    u64 s = 0;
                    for (auto& e : sp[o2].rows[i]) s = (s + e.second * work[w][e.first]) % P;
                    img[i] = s;
                }
                if (reduce_add(img)) {
                    work.push_back(img);
                    queue.push_back(img);
                }
            }
        }
    }
    AlgebraDim d;
    d.dim = (int)basis.size();
    d.exact = d.dim == r;
    return d;
}

}  // namespace hacs_jl
