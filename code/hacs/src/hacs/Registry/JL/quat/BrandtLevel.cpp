// SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
// SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
//
// hacs_jl (WP HJ-4b): the Sym^n Brandt module at level. Conventions: BrandtLevel.h (B1)-(B8).
#include "BrandtLevel.h"

#include <map>
#include <numeric>
#include <stdexcept>

namespace hacs_jl {

namespace {
std::string ctx(const char* f) { return std::string("hacs_jl::BrandtLevel: ") + f; }
i64 md(i128 a, i64 m) { return (i64)mod128(a, m); }
i64 inv_mod(i64 a, i64 m) {
    if (m == 1) return 0;
    i128 r0 = m, r1 = md(a, m), s0 = 0, s1 = 1;
    while (r1 != 0) {
        i128 q = r0 / r1, t = r0 - q * r1;
        r0 = r1;
        r1 = t;
        t = s0 - q * s1;
        s0 = s1;
        s1 = t;
    }
    if (r0 != 1) throw std::logic_error(ctx("inv_mod"));
    return md(s0, m);
}
i64 crt2(i64 r1, i64 m1, i64 r2, i64 m2) {
    if (m1 == 1) return md(r2, m2);
    if (m2 == 1) return md(r1, m1);
    i128 t = mod128((i128)(r2 - r1) * inv_mod(m1, m2), m2);
    return (i64)mod128(r1 + (i128)m1 * t, (i128)m1 * m2);
}
std::vector<int> pivots(const ZMat& R) {
    std::vector<int> p;
    for (const auto& r : R) {
        int c = 0;
        while (c < (int)r.size() && r[c].is_zero()) ++c;
        p.push_back(c);
    }
    return p;
}
// coordinates of z w.r.t. HNF rows R (pivots piv), verified
std::vector<Q> solve_rows(const ZMat& R, const std::vector<int>& piv, const std::vector<Q>& z) {
    std::vector<Q> y(R.size());
    for (size_t i = 0; i < R.size(); ++i) {
        Q acc = z[piv[i]];
        for (size_t j = 0; j < i; ++j)
            if (!y[j].is_zero() && !R[j][piv[i]].is_zero()) acc -= y[j] * Q(R[j][piv[i]]);
        y[i] = acc / Q(R[i][piv[i]]);
    }
    for (size_t c = 0; c < z.size(); ++c) {
        Q acc(0);
        for (size_t i = 0; i < R.size(); ++i)
            if (!y[i].is_zero() && !R[i][c].is_zero()) acc += y[i] * Q(R[i][c]);
        if (acc != z[c]) throw std::logic_error(ctx("image not in the invariant lattice span"));
    }
    return y;
}
QMat qinv(QMat A) {
    const int n = (int)A.size();
    QMat I(n, std::vector<Q>(n, Q(0)));
    for (int i = 0; i < n; ++i) I[i][i] = Q(1);
    for (int c = 0; c < n; ++c) {
        int p = c;
        while (p < n && A[p][c].is_zero()) ++p;
        if (p == n) throw std::logic_error(ctx("singular Gram"));
        std::swap(A[p], A[c]);
        std::swap(I[p], I[c]);
        Q iv = Q(1) / A[c][c];
        for (int j = 0; j < n; ++j) {
            A[c][j] *= iv;
            I[c][j] *= iv;
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
// J = O y + q I_c for y in I_c (O-coordinates): the q-neighbour of the line of y (Level.h (L5))
Lat line_neighbour(const ClassSet& C, int c, const Vec4& y, i64 q) {
    const MaxOrder& O = C.order();
    const Lat& I = C.classes()[c].I;
    std::vector<Vec4> gens;
    for (int s = 0; s < 4; ++s) {
        Vec4 es{{0, 0, 0, 0}};
        es[s] = 1;
        gens.push_back(O.mul(es, y));
        Vec4 qi = I.h[s];
        for (auto& t : qi) t = mul_chk(t, q);
        gens.push_back(qi);
    }
    const i128 NJ = (i128)q * C.classes()[c].N;
    return hnf(gens, 1, NJ * NJ);
}
}  // namespace

BrandtLevel::BrandtLevel(const BrandtSym& M, const LevelSet& X) : M_(M), X_(X) {
    const int n = M.n();
    if (n % 2) throw std::invalid_argument(ctx("odd n is not supported (no Q-form of Sym^n; BrandtLevel.h (B1))"));
    if (&X.model().class_set() != &M.class_set()) throw std::invalid_argument(ctx("level and module use different class sets"));
    const ClassSet& C = M.class_set();
    enum2mod_.assign(C.h(), -1);
    for (int i = 0; i < M.h(); ++i) enum2mod_[M.classes()[i].enum_index] = i;
    const i64 a = M.a();
    off_.assign(X.size() + 1, 0);
    for (int y = 0; y < X.size(); ++y) {
        const LevelCell& cell = X.cells()[y];
        SymCell s;
        s.c_enum = cell.rep.c;
        s.c_mod = enum2mod_[s.c_enum];
        const SymClass& sc = M.classes()[s.c_mod];
        ZMat St(n + 1);
        for (int u : cell.stab_units) {
            QMat A = M.rho_class(s.c_mod, elt(s.c_enum, X.model().units(s.c_enum)[u], sc.N));
            for (int i = 0; i <= n; ++i)
                for (int j = 0; j <= n; ++j) {
                    Q v = A[j][i] - Q(i == j ? 1 : 0);
                    if (v.den() != Z(1)) throw std::logic_error(ctx("Stab_y does not preserve Lambda_c"));
                    St[i].push_back(v.num());
                }
        }
        if (cell.stab_units.empty()) throw std::logic_error(ctx("empty stabiliser (identity missing)"));
        s.Zinv = symz::left_kernel(St);
        s.piv = pivots(s.Zinv);
        for (const auto& z : s.Zinv) {
            std::vector<Q> yv(n + 1, Q(0));
            for (int i = 0; i <= n; ++i)
                if (!z[i].is_zero())
                    for (int j = 0; j <= n; ++j) yv[j] += Q(z[i]) * sc.H[i][j];
            s.EK.push_back(M.base_vector(yv));
        }
        const int d = s.dim();
        Q Nn(Z::pow(Z(sc.N), (uint64_t)n));
        s.B.assign(d, std::vector<Q>(d));
        for (int i = 0; i < d; ++i)
            for (int j = 0; j < d; ++j) {
                KElt v = beta_n(a, s.EK[i], s.EK[j], n);
                if (!v.s.is_zero()) throw std::logic_error(ctx("beta_n not rational"));
                s.B[i][j] = v.r * Nn;
            }
        off_[y + 1] = off_[y] + d;
        cells_.push_back(std::move(s));
    }
    rank_ = off_[X.size()];
}

QB BrandtLevel::elt(int c_enum, const Vec4& x, i128 div) const {
    (void)c_enum;
    return qb_from(M_.order().to_std(x, div));
}
QB BrandtLevel::unit_inv(int c_enum, int u) const {
    const Vec4& x = X_.model().units(c_enum)[u];
    return qb_from(M_.order().to_std(M_.order().conj(x), M_.class_set().classes()[c_enum].N));
}

BrandtLevel::Move BrandtLevel::connect(int c_enum, const Lat& J, i64 NJ) const {
    (void)c_enum;
    const ClassSet& C = M_.class_set();
    int c2 = C.identify(J, NJ, true);
    if (c2 < 0) throw std::logic_error(ctx("ideal in no class"));
    return Move{c2, find_mu(C, C.classes()[c2].I, C.classes()[c2].N, J, NJ)};
}

LevelPoint BrandtLevel::transport(const LevelPoint& p, int c2, const Vec4& cmu, i128 div) const {
    const LevelModel& Mo = X_.model();
    const LevelSpec U = X_.spec();
    LevelPoint r;
    r.c = c2;
    if (U.N1 > 1) {
        Mat2 A = Mo.move(p.c, c2, cmu, div, U.N1);
        r.v0 = md((i128)p.v0 * A[0] + (i128)p.v1 * A[2], U.N1);
        r.v1 = md((i128)p.v0 * A[1] + (i128)p.v1 * A[3], U.N1);
    }
    if (U.N0 > 1) {
        Mat2 A = Mo.move(p.c, c2, cmu, div, U.N0);
        r.l0 = md((i128)p.l0 * A[0] + (i128)p.l1 * A[2], U.N0);
        r.l1 = md((i128)p.l0 * A[1] + (i128)p.l1 * A[3], U.N0);
    }
    return r;
}

ZMat BrandtLevel::assemble(const BrandtLevel& dst, const BrandtLevel& src, const Terms& terms) {
    const BrandtSym& M = dst.M_;
    const int n = M.n();
    const i64 a = M.a(), b = M.b();
    ZMat A(dst.rank_, std::vector<Z>(src.rank_, Z(0)));
    for (int y = 0; y < (int)terms.size(); ++y) {
        const SymCell& ty = dst.cells_[y];
        if (ty.dim() == 0) continue;
        std::map<int, std::vector<std::vector<Q>>> acc;
        for (const auto& t : terms[y]) {
            const SymCell& sy = src.cells_[t.src];
            if (sy.dim() == 0) continue;
            auto& ac = acc[t.src];
            if (ac.empty()) ac.assign(sy.dim(), std::vector<Q>(n + 1, Q(0)));
            KMat R = rho_K(a, b, t.h, n);
            for (int j = 0; j < sy.dim(); ++j) {
                auto z = M.class_coords(ty.c_mod, M.base_coords(apply(a, R, sy.EK[j])));
                for (int i = 0; i <= n; ++i) {
                    if (z[i].den() != Z(1)) throw std::logic_error(ctx("Hecke term not integral on the lattice"));
                    ac[j][i] += z[i];
                }
            }
        }
        for (const auto& kv : acc)
            for (int j = 0; j < (int)kv.second.size(); ++j) {
                auto yv = solve_rows(ty.Zinv, ty.piv, kv.second[j]);
                for (int i = 0; i < ty.dim(); ++i) {
                    if (yv[i].den() != Z(1)) throw std::logic_error(ctx("image not integral on the invariants"));
                    A[dst.off_[y] + i][src.off_[kv.first] + j] = yv[i].num();
                }
            }
    }
    return A;
}

BrandtLevel::Terms BrandtLevel::terms_hecke(i64 ell) const {
    const ClassSet& C = M_.class_set();
    if (!is_prime(ell) || C.order().D() % ell == 0) throw std::invalid_argument(ctx("T/U_ell: ell prime, not dividing D"));
    const LevelSpec U = X_.spec();
    const bool at_level = (U.N1 % ell == 0) || (U.N0 % ell == 0);
    std::map<int, std::vector<Move>> mv;
    Terms out(X_.size());
    for (int y = 0; y < X_.size(); ++y) {
        const LevelPoint& p = X_.cells()[y].rep;
        const int c = p.c;
        const i64 Nc = C.classes()[c].N;
        auto it = mv.find(c);
        if (it == mv.end()) {
            std::vector<Move> ms;
            for (const Lat& J : C.neighbours(C.classes()[c], ell)) ms.push_back(connect(c, J, Nc * ell));
            it = mv.emplace(c, ms).first;
        }
        int used = 0;
        for (const auto& m : it->second) {
            const Vec4 cmu = M_.order().conj(m.mu);
            auto [y2, u] = X_.locate_unit(transport(p, m.c2, cmu, Nc));
            if (y2 < 0) {
                if (!at_level) throw std::logic_error(ctx("T_ell: transported point not found"));
                continue;
            }
            QB g = elt(c, cmu, Nc);
            out[y].push_back(Term{y2, qb_mul(M_.a(), M_.b(), g, unit_inv(m.c2, u))});
            ++used;
        }
        if (used != (at_level ? ell : ell + 1)) throw std::logic_error(ctx("T/U_ell: wrong number of terms"));
    }
    return out;
}

BrandtLevel::Terms BrandtLevel::terms_diamond(i64 d) const {
    const LevelSpec U = X_.spec();
    if (U.N1 <= 1 || std::gcd(d, U.N1) != 1) throw std::invalid_argument(ctx("<d>: need N1 > 1, d prime to N1"));
    const i64 di = inv_mod(d, U.N1);
    Terms out(X_.size());
    for (int y = 0; y < X_.size(); ++y) {
        LevelPoint p = X_.cells()[y].rep;
        p.v0 = md((i128)di * p.v0, U.N1);
        p.v1 = md((i128)di * p.v1, U.N1);
        auto [y2, u] = X_.locate_unit(p);
        if (y2 < 0) throw std::logic_error(ctx("<d>: point not found"));
        out[y].push_back(Term{y2, unit_inv(p.c, u)});
    }
    return out;
}

BrandtLevel::Terms BrandtLevel::terms_Pi(i64 p) const {
    const ClassSet& C = M_.class_set();
    const MaxOrder& O = C.order();
    Lat P = M_.two_sided_prime(p);
    Terms out(X_.size());
    for (int y = 0; y < X_.size(); ++y) {
        const LevelPoint& pt = X_.cells()[y].rep;
        const int c = pt.c;
        const i64 Nc = C.classes()[c].N;
        const i128 nj = (i128)p * Nc;
        Move m = connect(c, O.product(P, C.classes()[c].I, nj * nj), (i64)nj);
        const Vec4 cmu = O.conj(m.mu);
        auto [y2, u] = X_.locate_unit(transport(pt, m.c2, cmu, Nc));
        if (y2 < 0) throw std::logic_error(ctx("Pi: point not found"));
        out[y].push_back(Term{y2, qb_mul(M_.a(), M_.b(), elt(c, cmu, Nc), unit_inv(m.c2, u))});
    }
    return out;
}

BrandtLevel::Terms BrandtLevel::terms_W(i64 ell) const {
    const ClassSet& C = M_.class_set();
    const MaxOrder& O = C.order();
    const LevelModel& Mo = X_.model();
    const LevelSpec U = X_.spec();
    if (!is_prime(ell) || U.N0 % ell || (U.N0 / ell) % ell == 0 || U.N1 % ell == 0)
        throw std::invalid_argument(ctx("W_ell: need ell || N0, ell not | N1"));
    Terms out(X_.size());
    for (int y = 0; y < X_.size(); ++y) {
        const LevelPoint& p = X_.cells()[y].rep;
        const int c = p.c;
        const i64 Nc = C.classes()[c].N;
        Vec4 yl = Mo.element(c, Mo.lift(c, md(p.l0, ell), md(p.l1, ell), ell));
        Move m = connect(c, line_neighbour(C, c, yl, ell), Nc * ell);
        const Vec4 cmu = O.conj(m.mu);
        LevelPoint r = transport(p, m.c2, cmu, Nc);
        // the new ell-line: the line of e L g in e I_c' / ell I_c'
        Mat2 A = Mo.move(c, m.c2, cmu, Nc, ell);
        i64 n0 = A[0], n1 = A[1];
        if (n0 == 0 && n1 == 0) {
            n0 = A[2];
            n1 = A[3];
        }
        if ((n0 == 0 && n1 == 0) || md((i128)A[0] * A[3] - (i128)A[1] * A[2], ell) != 0)
            throw std::logic_error(ctx("W_ell: e L g is not a line mod ell"));
        const i64 rest = U.N0 / ell;
        r.l0 = crt2(n0, ell, md(r.l0, rest), rest);
        r.l1 = crt2(n1, ell, md(r.l1, rest), rest);
        auto [y2, u] = X_.locate_unit(r);
        if (y2 < 0) throw std::logic_error(ctx("W_ell: point not found"));
        out[y].push_back(Term{y2, qb_mul(M_.a(), M_.b(), elt(c, cmu, Nc), unit_inv(m.c2, u))});
    }
    return out;
}

BrandtLevel::Terms BrandtLevel::terms_Up_prime(i64 p) const {
    const ClassSet& C = M_.class_set();
    const MaxOrder& O = C.order();
    const LevelModel& Mo = X_.model();
    const LevelSpec U = X_.spec();
    if (!is_prime(p) || U.N1 % p || U.N0 % p == 0) throw std::invalid_argument(ctx("U'_p: need p | N1, p not | N0"));
    i64 ps = 1;
    while (U.N1 % (ps * p) == 0) ps *= p;
    const i64 M1 = U.N1 / ps;
    if (Mo.modulus() % (p * U.N1) != 0)
        throw std::invalid_argument(ctx("U'_p: the level model must be taken modulo p N1 (BrandtLevel.h (B3))"));
    const i64 Nb = Mo.modulus();
    Terms out(X_.size());
    for (int y = 0; y < X_.size(); ++y) {
        const LevelPoint& pt = X_.cells()[y].rep;
        const int c = pt.c;
        const i64 Nc = C.classes()[c].N;
        const i64 a = pt.v0, b = pt.v1;
        // complement w = (c0, d0): a d0 - b c0 = 1 mod p
        i64 c0 = -1, d0 = -1;
        for (i64 s = 0; s < p && c0 < 0; ++s)
            for (i64 t = 0; t < p; ++t)
                if (md((i128)a * t - (i128)b * s, p) == 1) {
                    c0 = s;
                    d0 = t;
                    break;
                }
        Vec4 vt = Mo.element(c, Mo.lift(c, a, b, Nb)), wt = Mo.element(c, Mo.lift(c, c0, d0, Nb));
        Vec4 yl = Mo.element(c, Mo.lift(c, md(a, p), md(b, p), p));
        Move m = connect(c, line_neighbour(C, c, yl, p), Nc * p);
        const Vec4 cmu = O.conj(m.mu);
        const Lat& I2 = C.classes()[m.c2].I;
        // the other primes: d g
        LevelPoint base = transport(pt, m.c2, cmu, Nc);
        for (i64 j = 0; j < p; ++j) {
            Vec4 d;
            for (int s = 0; s < 4; ++s) d[s] = add_chk(vt[s], -mul_chk(mul_chk(ps, j), wt[s]));
            Vec4 z = O.mul(d, cmu);
            for (auto& t : z) t = exact_div(t, (i128)Nc * p);
            Vec4 yc = coords_in(I2, z);
            std::array<i64, 4> ym;
            for (int s = 0; s < 4; ++s) ym[s] = md(yc[s], ps);
            auto abp = Mo.coords(m.c2, ym, ps);
            LevelPoint r = base;
            r.v0 = crt2(abp[0], ps, md(base.v0, M1), M1);
            r.v1 = crt2(abp[1], ps, md(base.v1, M1), M1);
            auto [y2, u] = X_.locate_unit(r);
            if (y2 < 0) throw std::logic_error(ctx("U'_p: point not found"));
            out[y].push_back(Term{y2, qb_mul(M_.a(), M_.b(), elt(c, cmu, Nc), unit_inv(m.c2, u))});
        }
    }
    return out;
}

ZMat BrandtLevel::pullback(const BrandtLevel& fine, const BrandtLevel& coarse) {
    const LevelSet &F = fine.X_, &Xc = coarse.X_;
    Terms t(F.size());
    for (int y = 0; y < F.size(); ++y) {
        auto [x, u] = Xc.locate_unit(reduce_point(F.cells()[y].rep, F.spec(), Xc.spec()));
        if (x < 0) throw std::logic_error(ctx("pullback: point not found"));
        t[y].push_back(Term{x, coarse.unit_inv(F.cells()[y].rep.c, u)});
    }
    return assemble(fine, coarse, t);
}

ZMat BrandtLevel::trace(const BrandtLevel& fine, const BrandtLevel& coarse) {
    const LevelSet &F = fine.X_, &Xc = coarse.X_;
    const LevelSpec f = F.spec(), c = Xc.spec();
    if (f.N0 != c.N0 || f.N1 % c.N1) throw std::invalid_argument(ctx("trace: only N1 refinements (same N0)"));
    const i64 r = f.N1 / c.N1;
    Terms t(Xc.size());
    for (int x = 0; x < Xc.size(); ++x) {
        const LevelPoint& p = Xc.cells()[x].rep;
        for (i64 s0 = 0; s0 < r; ++s0)
            for (i64 s1 = 0; s1 < r; ++s1) {
                LevelPoint q = p;
                q.v0 = p.v0 + c.N1 * s0;
                q.v1 = p.v1 + c.N1 * s1;
                if (f.N1 > 1 && std::gcd(std::gcd(q.v0, q.v1), f.N1) != 1) continue;
                auto [y, u] = F.locate_unit(q);
                if (y < 0) throw std::logic_error(ctx("trace: lift not found"));
                t[x].push_back(Term{y, fine.unit_inv(p.c, u)});
            }
    }
    return assemble(coarse, fine, t);
}

ZMat BrandtLevel::degeneracy_s1(const BrandtLevel& E, const BrandtLevel& X, i64 q) {
    const LevelSet &Le = E.X_, &Lx = X.X_;
    const ClassSet& C = X.M_.class_set();
    const MaxOrder& O = C.order();
    const LevelModel& Mo = Le.model();
    const LevelSpec ue = Le.spec(), ux = Lx.spec();
    if (!is_prime(q) || ue.N1 != ux.N1 || ue.N0 != ux.N0 * q || ux.N0 % q == 0 || ue.N1 % q == 0)
        throw std::invalid_argument(ctx("s1: need E = X cap U_0(q)"));
    Terms t(Le.size());
    for (int e = 0; e < Le.size(); ++e) {
        const LevelPoint& p = Le.cells()[e].rep;
        const int c = p.c;
        const i64 Nc = C.classes()[c].N;
        Vec4 yl = Mo.element(c, Mo.lift(c, md(p.l0, q), md(p.l1, q), q));
        Move m = X.connect(c, line_neighbour(C, c, yl, q), Nc * q);
        const Vec4 cmu = O.conj(m.mu);
        LevelPoint r = X.transport(reduce_point(p, ue, ux), m.c2, cmu, Nc);
        auto [x, u] = Lx.locate_unit(r);
        if (x < 0) throw std::logic_error(ctx("s1: point not found"));
        t[e].push_back(Term{x, qb_mul(X.M_.a(), X.M_.b(), X.elt(c, cmu, Nc), X.unit_inv(m.c2, u))});
    }
    return assemble(E, X, t);
}

QMat BrandtLevel::gram(bool weights_w) const {
    QMat G(rank_, std::vector<Q>(rank_, Q(0)));
    for (int y = 0; y < (int)cells_.size(); ++y) {
        const LevelCell& lc = X_.cells()[y];
        Q f = Q(1) / Q(weights_w ? lc.w : lc.stab);
        for (int i = 0; i < cells_[y].dim(); ++i)
            for (int j = 0; j < cells_[y].dim(); ++j) G[off_[y] + i][off_[y] + j] = cells_[y].B[i][j] * f;
    }
    return G;
}

QMat BrandtLevel::adjoint(const ZMat& A) const {
    QMat G = gram(true), At(rank_, std::vector<Q>(rank_));
    for (int i = 0; i < rank_; ++i)
        for (int j = 0; j < rank_; ++j) At[i][j] = Q(A[j][i]);
    return symz::mul(qinv(G), symz::mul(At, G));
}

}  // namespace hacs_jl
