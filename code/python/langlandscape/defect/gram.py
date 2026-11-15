# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06-C5 (T5, definite side): integral Brandt module of ``B_q`` with ``Sym^{k-2}``, its Gram matrix and ``eta^B``.

Tex: ``plan/staged/stage-06-integral-defect.tex``, computation T5, seam items (S1), (S3); interface ``if:s04-etaB``
(``thm:s04-etaB``; the eta-principle ``prop:s04-etaprinciple``, Hsieh Rem. 7.3: ``C(lambda)^d = det <e_i, e_j>``).

Setting.  ``B = B_q`` definite of discriminant ``q``, maximal order ``O`` (level ``U = O^^x``, ``-1 in U``),
``V_k = Sym^n``, ``n = k - 2`` (``k`` even), the Brandt module ``M = (+)_x V^{Gamma_x}`` of :mod:`langlandscape.symn`
(Gross form, ``Gamma_x = O_r(L_x)^x`` including ``-1``, ``w_x = |Gamma_x| / 2``), Hecke operators ``T_l``, ``l != q``,
by ``symn.SymBrandt.apply_formula``.  For the T5 triples ``(q, k, p)``: ``p >= 5``, ``p > n``, ``p`` prime to
``2 a b q |Gamma_x|`` (asserted).

Integral structure (``Z_(p)``).  ``s : O -> M_2(Q(sqrt a))`` lands in ``M_2(Z_(p)[sqrt a])`` (asserted on the order
basis), so ``Lambda = Sym^n(Z_(p)[sqrt a]^2)`` is ``s(O)``-stable; ``Z_(p)[sqrt a]`` is ``p``-maximal as ``p`` does not
divide ``4a``.  The ``sigma``-semilinear involution ``phi`` of ``symn`` (``phi(P) = b^{n/2} rho(s(j))^{-1} sigma(P)``)
maps ``e_t = X^{n-t} Y^t`` to ``c_t e_{n-t}`` with ``c_t`` a ``p``-unit (asserted), hence preserves ``Lambda``; by
unramified Galois descent ``Lambda = Lambda^phi (x) Z_(p)[sqrt a]``, and ``Lambda^phi`` has the explicit
``Z_(p)``-basis ``e_t + phi(e_t)``, ``sqrt a e_t + phi(sqrt a e_t)`` (``t < n/2``) and ``e_{n/2}`` or
``sqrt a e_{n/2}`` (``t = n/2``).  The integral Brandt module is ``M_Z = (+)_x (Lambda^phi)^{Gamma_x}``; since
``p`` does not divide ``|Gamma_x|`` its ``Z_(p)``-basis is a set of columns of the projector
``|Gamma_x|^{-1} sum_{gamma in Gamma_x} rho(gamma)`` independent mod ``p`` (Nakayama).

Pairing.  ``<e_t, e_s>_V = delta_{s, n-t} (-1)^t / binom(n, t)`` (``<gP, gQ> = det(g)^n <P, Q>``, asserted on the
order basis; rational on ``Lambda^phi`` since ``n`` is even, asserted; perfect on ``Lambda`` as ``p > n``).  The two
Gram matrices of (S1):

* ``G_w      = (+)_x  w_x^{-1}       <,>_V`` (Hsieh's weight ``#Gamma_{N p^alpha, x} = w_x``, (4.1) p. 29),
* ``G_Gamma  = (+)_x  |Gamma_x|^{-1} <,>_V`` (the stage-1 import's ``|Gamma_x|``).

Both make every ``T_l`` self-adjoint (asserted: ``T^t G = G T``; at level ``O^^x`` with trivial character
``T_l^* = T_l``, so the adjoint issue of (S3) is vacuous here; Hsieh's Atkin--Lehner twist in ``B_N`` lives at
``M p^alpha`` and is a unit at this level, stage-04 D4).  Their determinants differ by ``2^{dim}``, so
``v_p(det G_w / det G_Gamma) = 0`` for ``p`` odd (checked on the full module and on every orbit lattice).

``eta^B``.  Over ``Z_p``: a generic ``T = sum c_l T_l`` has squarefree char-poly ``chi`` (asserted; ``chi`` equals the
char-poly on ``S_k(Gamma_0(q))^new``, cross-checked against PARI for ``T_2``).  For every ``Q_p``-irreducible factor
``phi`` of ``chi`` (``factorpadic``, precision ``p^PREC``) the orbit lattice ``A_phi = ker phi(T) cap M_Z (x) Z_p``
(saturated; ``p``-adic Smith form) has ``|det G_w|_{A_phi}| = |M / (A_phi (+) A_phi^perp)|``, the order of the
congruence module of the orbit (``G_w`` is perfect and ``T``-equivariant).  For ``deg phi = 1`` this is the
eta-principle of ``if:s04-etaB`` with ``d = 1``: ``eta^B_f = (<m_0, m_0>)``, ``m_0`` a generator of the eigenline,
so ``v_p(eta^B_f) = v_p(det G_w|_{A_phi})``.  For ``deg phi = d > 1`` the recorded number is the ``Z_p``-length of the
congruence module (Hsieh Rem. 7.3 with the orbit as ``H``); it equals ``f * v_varpi(eta^B)`` when the coefficient
ring is the maximal order of residue degree ``f`` (not checked here, see the JSON field ``note``).

Localisation at ``m``.  Orbits are grouped by their residual eigensystem (the irreducible factor mod ``p`` of the
char-poly of each ``T_l`` restricted to ``A_phi``); a group is a block ``M_m`` (its rank is ``rk_{Z_p} M_m``).  The
block is ``old-congruent`` if its residual eigenvalues equal those of the level-1 eigenform ``g in S_k(SL_2(Z))``
mod ``p`` for every ``l`` used; for that block we also record ``v_p(a_q(g)^2 - q^{k-2}(q+1)^2)`` (level raising).
Status of every number: *computed*.
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from math import comb

import flint

from .. import results, symn
from ..pari import get_pari

TRIPLES = ((13, 18, 19), (5, 18, 23), (5, 16, 31), (13, 12, 31), (3, 18, 53), (3, 18, 61), (13, 16, 101))
ELLS = (2, 3, 5, 7, 11)
PREC = 60
COEFS = ((1, 3, 7, 13, 17), (1, 5, 2, 11, 3), (2, 1, 9, 4, 19))


# ---------------------------------------------------------------- p-adic linear algebra mod p^R
def vp(x: int, p: int, cap: int) -> int:
    """``v_p(x)`` capped at ``cap`` (``x = 0`` gives ``cap``)."""
    if x == 0:
        return cap
    v = 0
    while x % p == 0 and v < cap:
        x //= p
        v += 1
    return v


def vp_frac(x: Fraction, p: int) -> int:
    assert x != 0
    return vp(abs(x.numerator), p, 10**9) - vp(x.denominator, p, 10**9)


def to_mod(x, P: int) -> int:
    x = Fraction(x)
    return x.numerator * pow(x.denominator, -1, P) % P


def mat_mod(A, P: int):
    return [[to_mod(x, P) for x in r] for r in A]


def mmul(A, B, P: int):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(r, c)) % P for c in Bt] for r in A]


def transpose(A):
    return [list(r) for r in zip(*A)]


def smith(A, p: int, R: int):
    """``p``-adic Smith form of ``A`` mod ``p^R``: returns ``(vals, V)`` with ``U A V = diag(p^vals)``, ``V`` unimodular.

    ``vals`` lists the valuations of the pivots found (in order); entries ``>= R`` are not included (zero mod ``p^R``).
    """
    P = p**R
    A = [list(r) for r in A]
    m, n = len(A), len(A[0]) if A else 0
    V = [[int(i == j) for j in range(n)] for i in range(n)]
    vals = []
    for s in range(min(m, n)):
        best = None
        for i in range(s, m):
            for j in range(s, n):
                v = vp(A[i][j], p, R)
                if best is None or v < best[0]:
                    best = (v, i, j)
                    if v == 0:
                        break
            if best and best[0] == 0:
                break
        v, i, j = best
        if v >= R:
            break
        A[s], A[i] = A[i], A[s]
        for r in A:
            r[s], r[j] = r[j], r[s]
        for r in V:
            r[s], r[j] = r[j], r[s]
        u = A[s][s] // p**v
        ui = pow(u, -1, P)
        A[s] = [x * ui % P for x in A[s]]
        for r in range(s + 1, m):
            if A[r][s]:
                f = A[r][s] // p**v
                A[r] = [(x - f * y) % P for x, y in zip(A[r], A[s])]
        for c in range(s + 1, n):
            if A[s][c]:
                f = A[s][c] // p**v
                for r in A:
                    r[c] = (r[c] - f * r[s]) % P
                for r in V:
                    r[c] = (r[c] - f * r[s]) % P
        vals.append(v)
    return vals, V


def det_val(A, p: int, R: int) -> int:
    """``v_p(det A)`` for a square ``A`` mod ``p^R`` (asserts ``det A != 0`` at this precision)."""
    vals, _ = smith(A, p, R)
    assert len(vals) == len(A), "determinant vanishes mod p^R"
    return sum(vals)


def kernel(A, p: int, R: int, expected: int, zero_at: int):
    """Saturated ``Z_p``-kernel of ``A`` mod ``p^R`` (columns): Smith pivots of valuation ``>= zero_at`` count as zero.

    With full pivoting the pivot valuations are non-decreasing, so the trailing columns of ``V`` are annihilated by ``A``
    mod ``p^zero_at``; the gap between the last nonzero pivot and ``zero_at`` is asserted to be large.
    """
    vals, V = smith(A, p, R)
    r = next((i for i, v in enumerate(vals) if v >= zero_at), len(vals))
    n = len(V)
    assert n - r == expected, f"kernel rank {n - r}, expected {expected} (pivot valuations {vals})"
    assert not vals[:r] or max(vals[:r]) < zero_at // 2, f"precision too low: pivot valuations {vals}"
    return [[V[i][j] for j in range(r, n)] for i in range(n)]


def rank_mod_p(A, p: int) -> tuple[int, list[int]]:
    """Rank and pivot rows of ``A`` (integer rows) mod ``p``."""
    A = [[x % p for x in r] for r in A]
    rows = []
    basis: list[tuple[list[int], int]] = []
    for idx, r in enumerate(A):
        r = list(r)
        for b, piv in basis:
            if r[piv]:
                f = r[piv]
                r = [(x - f * y) % p for x, y in zip(r, b)]
        piv = next((c for c, x in enumerate(r) if x), None)
        if piv is None:
            continue
        inv = pow(r[piv], -1, p)
        r = [x * inv % p for x in r]
        basis = [([(x - b[piv] * y) % p for x, y in zip(b, r)], pv) for b, pv in basis]
        basis.append((r, piv))
        rows.append(idx)
    return len(rows), rows


def inv_mod(A, P: int):
    n = len(A)
    M = [list(A[i]) + [int(i == j) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] % P and _is_unit(M[r][c], P))
        M[c], M[piv] = M[piv], M[c]
        iv = pow(M[c][c], -1, P)
        M[c] = [x * iv % P for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]
                M[r] = [(x - f * y) % P for x, y in zip(M[r], M[c])]
    return [r[n:] for r in M]


def _is_unit(x: int, P: int) -> bool:
    try:
        pow(x, -1, P)
        return True
    except ValueError:
        return False


def restrict(T, Bcols, p: int, P: int):
    """Matrix ``X`` of ``T`` on the saturated column span of ``Bcols`` (``T B = B X``), mod ``P``."""
    _, piv = rank_mod_p(Bcols, p)  # rows of B forming an invertible-mod-p minor
    TB = mmul(T, Bcols, P)
    Bi = inv_mod([Bcols[i] for i in piv], P)
    X = mmul(Bi, [TB[i] for i in piv], P)
    assert mmul(Bcols, X, P) == [[x % P for x in r] for r in TB], "span not T-stable"
    return X


# ---------------------------------------------------------------- the integral Brandt module
class IntegralBrandt:
    """``M_Z = (+)_x (Lambda^phi)^{Gamma_x}`` over ``Z_(p)`` with exact rational ``T_l`` and the two Gram matrices."""

    def __init__(self, q: int, k: int, p: int, ells=ELLS):
        assert k % 2 == 0 and k > 2
        self.q, self.k, self.p, self.n = q, k, p, k - 2
        self.SB = SB = symn.sym_brandt(q, k)
        S = self.S = SB.S
        n = self.n
        self.ells = tuple(l for l in ells if l != q and l != p)
        assert p >= 5 and p > n, "need p >= 5 and p > k - 2"
        assert (2 * S.a * S.b * q) % p, "p must be prime to 2abq"
        assert all(g % p for g in SB.gammas), "p divides some |Gamma_x|"
        self.gammas = list(SB.gammas)
        self.ws = [g // 2 for g in self.gammas]
        # s(O) is p-integral (order basis)
        es = [tuple(Fraction(int(i == j)) for j in range(4)) for i in range(4)]
        for e in es:
            for x in (c for r in S.split(e) for c in r):
                assert x.r.denominator % p and x.s.denominator % p, "s(O) not p-integral"
        # Z_(p)-basis of Lambda^phi
        dim = n + 1
        E = [[S.one if i == t else S.zero for i in range(dim)] for t in range(dim)]
        cols = []
        for t in range(n // 2):
            pe = SB.phi(E[t])
            ct = pe[n - t]
            assert all(pe[i].is_zero() for i in range(dim) if i != n - t) and ct.is_rational() and vp_frac(ct.r, p) == 0
            cols.append([x + y for x, y in zip(E[t], pe)])
            se = [S.sqa * x for x in E[t]]
            cols.append([x + y for x, y in zip(se, SB.phi(se))])
        mid = SB.phi(E[n // 2])
        if mid == E[n // 2]:
            cols.append(E[n // 2])
        else:
            assert mid == [-x for x in E[n // 2]]
            cols.append([S.sqa * x for x in E[n // 2]])
        for v in cols:
            assert SB.phi(v) == v
        self.Cm = [[cols[j][i] for j in range(dim)] for i in range(dim)]
        Rr, piv = symn.rref([self.Cm[i] + [S.one if i == j else S.zero for j in range(dim)] for i in range(dim)])
        assert piv == list(range(dim))
        self.Cinv = [r[dim:] for r in Rr]
        # rho in Q-coordinates, p-integral on the order basis
        self._rq: dict = {}
        for e in es:
            assert all(x.denominator % p for r in self.rho_q(e) for x in r), "rho(s(O)) not p-integral on Lambda^phi"
        # pairing on V, in Q-coordinates
        JK = [[S.zero] * dim for _ in range(dim)]
        for t in range(dim):
            JK[t][n - t] = QSc(S, Fraction((-1) ** t, comb(n, t)))
        GK = symn.mat_mul(transpose(self.Cm), symn.mat_mul(JK, self.Cm))
        assert all(x.is_rational() for r in GK for x in r), "pairing not rational on Lambda^phi"
        self.GV = [[x.r for x in r] for r in GK]
        assert vp_frac(Fraction(flint_det(self.GV)), p) == 0, "<,>_V not perfect on Lambda^phi"
        for e in es:  # <gP, gQ> = nrd(g)^n <P, Q>
            Rg = self.rho_q(e)
            lhs = matmul_q(transpose(Rg), matmul_q(self.GV, Rg))
            nr = S.B.nrd(e) ** n
            assert lhs == [[nr * x for x in r] for r in self.GV], "pairing not equivariant"
        # invariants per class: projector columns independent mod p
        self.blocks = []  # per class: list of Q-coordinate vectors
        for c, U in enumerate(SB.units):
            Pc = [[Fraction(0)] * dim for _ in range(dim)]
            for g in U:
                Rg = self.rho_q(g)
                Pc = [[x + y for x, y in zip(r1, r2)] for r1, r2 in zip(Pc, Rg)]
            Pc = [[x / len(U) for x in r] for r in Pc]
            assert matmul_q(Pc, Pc) == Pc
            colsP = transpose(Pc)
            rk, pv = rank_mod_p([[to_mod(x, p) for x in col] for col in colsP], p)
            assert rk == SB.dims[c], (rk, SB.dims[c])
            self.blocks.append([colsP[j] for j in pv])
        self.basis = [(c, w) for c, W in enumerate(self.blocks) for w in W]
        self.dim = len(self.basis)
        assert self.dim == SB.dim
        # Gram matrices
        self.G = {}
        for name, wt in (("w", self.ws), ("Gamma", self.gammas)):
            G = [[Fraction(0)] * self.dim for _ in range(self.dim)]
            for i, (ci, wi) in enumerate(self.basis):
                for j, (cj, wj) in enumerate(self.basis):
                    if ci == cj:
                        G[i][j] = sum(wi[a] * self.GV[a][b] * wj[b] for a in range(dim) for b in range(dim)) / wt[ci]
            self.G[name] = G
        self._T: dict = {}

    def rho_q(self, g):
        if g not in self._rq:
            R = self.S.rho(g, self.n)
            M = symn.mat_mul(self.Cinv, symn.mat_mul(R, self.Cm))
            assert all(x.is_rational() for r in M for x in r)
            self._rq[g] = [[x.r for x in r] for r in M]
        return self._rq[g]

    def T(self, ell: int):
        """Exact rational matrix of ``T_ell`` on the ``Z_(p)``-basis ``self.basis`` (asserted ``p``-integral)."""
        if ell in self._T:
            return self._T[ell]
        S, SB, dim = self.S, self.SB, self.n + 1
        cols = []
        for c, w in self.basis:
            Phi = [[S.zero] * dim for _ in range(SB.h)]
            Phi[c] = symn.mat_vec(self.Cm, [QSc(S, x) for x in w], S.zero)
            TPhi = SB.apply_formula(ell, Phi)
            col = []
            for cc, W in enumerate(self.blocks):
                v = symn.mat_vec(self.Cinv, TPhi[cc], S.zero)
                assert all(x.is_rational() for x in v)
                col += symn.solve_in_span(W, [x.r for x in v], Fraction(0)) if W else []
            cols.append(col)
        M = transpose(cols)
        assert all(x.denominator % self.p for r in M for x in r), f"T_{ell} not p-integral"
        self._T[ell] = M
        return M


def QSc(S, x):
    return symn.QS(x, 0, S.a)


def matmul_q(A, B):
    Bt = list(zip(*B))
    return [[sum((a * b for a, b in zip(r, c)), Fraction(0)) for c in Bt] for r in A]


def flint_det(A) -> Fraction:
    n = len(A)
    if n == 0:
        return Fraction(1)
    m = flint.fmpq_mat(n, n, [flint.fmpq(x.numerator, x.denominator) for r in A for x in r])
    d = m.det()
    return Fraction(int(d.p), int(d.q))


def flint_charpoly(A) -> list[int]:
    n = len(A)
    m = flint.fmpq_mat(n, n, [flint.fmpq(x.numerator, x.denominator) for r in A for x in r])
    cs = [Fraction(int(c.p), int(c.q)) for c in m.charpoly().coeffs()]
    assert all(c.denominator == 1 for c in cs), "Hecke char-poly not integral"
    return [int(c) for c in cs]


# ---------------------------------------------------------------- PARI side
def mf_new(q: int, k: int, ell: int):
    pari = get_pari()
    mf = pari.mfinit([q, k], 0)
    d = int(pari.mfdim(mf))
    cp = [int(c) for c in reversed(list(pari.Vec(pari.charpoly(pari.mfheckemat(mf, ell)))))] if d else [1]
    return d, cp


def level_one(k: int, ells) -> dict | None:
    """``a_l(g)`` for the level-1 eigenform of weight ``k`` (only if ``dim S_k(SL_2(Z)) = 1``)."""
    pari = get_pari()
    mf = pari.mfinit([1, k], 1)
    if int(pari.mfdim(mf)) != 1:
        return None
    return {l: int(pari.mfheckemat(mf, l)[0, 0]) for l in ells}


def _pol(coeffs_const_first):
    return get_pari().Pol([int(c) for c in reversed(coeffs_const_first)])


def _coeffs_mod(pol, P: int) -> list[int]:
    """Integer coefficients mod ``P`` (constant first) of a polynomial with ``p``-adic integer coefficients."""
    pari = get_pari()
    out = []
    for c in reversed(list(pari.Vec(pol))):
        t = pari.truncate(c)
        out.append(int(pari.numerator(t)) * pow(int(pari.denominator(t)), -1, P) % P)
    return out


def poly_at(cs, T, P: int):
    n = len(T)
    acc = [[0] * n for _ in range(n)]
    for c in reversed(cs):  # Horner, cs constant first
        acc = mmul(acc, T, P)
        for i in range(n):
            acc[i][i] = (acc[i][i] + c) % P
    return acc


# ---------------------------------------------------------------- one triple
def triple(q: int, k: int, p: int, prec: int = PREC) -> dict:
    pari = get_pari()
    IB = IntegralBrandt(q, k, p)
    P = p**prec
    ells = IB.ells
    Ts = {l: IB.T(l) for l in ells}
    out = {"q": q, "k": k, "p": p, "a": IB.S.a, "b": IB.S.b, "h": IB.SB.h, "gammas": IB.gammas, "w": IB.ws,
           "dim_brandt": IB.dim, "ells": list(ells), "prec": prec}
    # checks: dimension, char-polys vs PARI newspace, commutativity, self-adjointness
    dnew, _ = mf_new(q, k, 2)
    out["dim_mf_new"] = dnew
    out["dim_equal"] = IB.dim == dnew
    out["charpoly_vs_pari"] = {}
    for l in ells[:2]:
        out["charpoly_vs_pari"][str(l)] = flint_charpoly(Ts[l]) == mf_new(q, k, l)[1]
    out["commutative"] = all(matmul_q(Ts[a], Ts[b]) == matmul_q(Ts[b], Ts[a]) for a, b in itertools.combinations(ells, 2))
    out["self_adjoint"] = {nm: all(matmul_q(transpose(T), G) == matmul_q(G, T) for T in Ts.values())
                           for nm, G in IB.G.items()}
    dw, dg = flint_det(IB.G["w"]), flint_det(IB.G["Gamma"])
    out["det_gram"] = {"w": dw, "Gamma": dg, "ratio_w_over_Gamma": dw / dg,
                       "vp_w": vp_frac(dw, p), "vp_Gamma": vp_frac(dg, p), "vp_ratio": vp_frac(dw / dg, p)}
    # a generic T with squarefree char-poly
    for co in COEFS:
        Tg = [[sum(c * Ts[l][i][j] for c, l in zip(co, ells)) for j in range(IB.dim)] for i in range(IB.dim)]
        chi_cs = flint_charpoly(Tg)
        chi = _pol(chi_cs)
        if int(pari.poldegree(pari.gcd(chi, pari.deriv(chi)))) == 0:
            break
    else:
        raise RuntimeError("no generic T with squarefree char-poly")
    out["generic_T"] = {"coefficients": dict(zip(map(str, ells), co)), "charpoly_squarefree": True}
    Tm = mat_mod(Tg, P)
    Tsm = {l: mat_mod(T, P) for l, T in Ts.items()}
    Gm = {nm: mat_mod(G, P) for nm, G in IB.G.items()}
    fa = pari.factorpadic(chi, p, prec)
    g1 = level_one(k, ells + (q,))
    orbits = []
    for i in range(int(pari.matsize(fa)[0])):
        phi = fa[0][i]
        assert int(fa[1][i]) == 1
        deg = int(pari.poldegree(phi))
        A = poly_at(_coeffs_mod(phi, P), Tm, P)
        Bc = kernel(A, p, prec, deg, zero_at=prec // 2)
        Pm = p ** (prec // 2)  # precision kept for kernel-derived quantities
        sig = {}
        for l in ells:
            X = restrict(Tsm[l], [[x % Pm for x in r] for r in Bc], p, Pm)
            cp = pari.charpoly(pari.matrix(deg, deg, [X[a][b] % p for a in range(deg) for b in range(deg)]))
            fm = pari.factormod(cp, p)
            assert int(pari.matsize(fm)[0]) == 1, "orbit not residually a single eigensystem"
            sig[str(l)] = str(pari.lift(fm[0][0]))
        Bt = transpose(Bc)
        vw = det_val(mmul(mmul(Bt, Gm["w"], Pm), Bc, Pm), p, prec // 2)
        vg = det_val(mmul(mmul(Bt, Gm["Gamma"], Pm), Bc, Pm), p, prec // 2)
        o = {"degree": deg, "residual": sig, "vp_det_gram_w": vw, "vp_det_gram_Gamma": vg, "vp_ratio": vw - vg}
        if deg == 1:
            # independent upper bound: Z_p[T] is contained in T_m, so v_p(eta^B) <= v_p(chi'(lambda)) (= the
            # congruence exponent of the monogenic order Z_p[x]/(chi)); equality iff Z_p[T] is the full algebra at m
            lam = -_coeffs_mod(phi, P)[0] % P
            dchi = [i * c for i, c in enumerate(chi_cs)][1:]
            o["vp_monogenic_bound"] = vp(sum(c * pow(lam, i, P) for i, c in enumerate(dchi)) % P, p, prec // 2)
            o["bound_ok"] = vw <= o["vp_monogenic_bound"]
        orbits.append(o)
    # blocks M_m
    groups: dict = {}
    for o in orbits:
        groups.setdefault(tuple(sorted(o["residual"].items())), []).append(o)
    blocks = []
    for key, os_ in groups.items():
        res = dict(key)
        lin = all(pari.poldegree(pari(v)) == 1 for v in res.values())
        ev = {l: (-int(pari.polcoef(pari(v), 0))) % p for l, v in res.items()} if lin else None
        old = bool(lin and g1 is not None and all((g1[int(l)] - ev[l]) % p == 0 for l in res))
        blocks.append({"residual": res, "residual_eigenvalues": ev, "rank": sum(o["degree"] for o in os_),
                       "orbits": os_, "old_congruent": old})
    blocks.sort(key=lambda b: (-b["old_congruent"], -b["rank"]))
    out["blocks"] = blocks
    out["n_blocks"] = len(blocks)
    out["orbits_total_degree"] = sum(o["degree"] for o in orbits)
    out["vp_ratio_all_zero"] = out["det_gram"]["vp_ratio"] == 0 and all(o["vp_ratio"] == 0 for o in orbits)
    if g1 is not None:
        lr = g1[q] ** 2 - q ** (k - 2) * (q + 1) ** 2
        out["level_one_form"] = {"a_l": {str(l): v for l, v in g1.items()},
                                 "vp_level_raising": vp(abs(lr), p, 10**6)}
    old = [b for b in blocks if b["old_congruent"]]
    if old:
        b = old[0]
        out["m"] = {"rank": b["rank"], "orbits": [(o["degree"], o["vp_det_gram_w"]) for o in b["orbits"]],
                    "vp_etaB": [o["vp_det_gram_w"] for o in b["orbits"] if o["degree"] == 1]}
    out["all_ok"] = bool(out["dim_equal"] and all(out["charpoly_vs_pari"].values()) and out["commutative"]
                         and all(out["self_adjoint"].values()) and out["vp_ratio_all_zero"]
                         and out["det_gram"]["vp_w"] == 0 and out["orbits_total_degree"] == IB.dim
                         and all(o.get("bound_ok", True) for o in orbits))
    return out


def compute_all(triples=TRIPLES) -> dict:
    data = {f"{q},{k},{p}": triple(q, k, p) for q, k, p in triples}
    return {
        "conventions": {
            "module": "M = (+)_x Sym^{k-2}(Z_(p)[sqrt a]^2)^{phi, Gamma_x}, level O^x of B_q (maximal order), symn Gross form",
            "pairing_V": "<e_t,e_s> = delta_{s,n-t} (-1)^t / binom(n,t), e_t = X^{n-t} Y^t",
            "gram_w": "G_w = (+)_x w_x^{-1} <,>_V, w_x = |Gamma_x|/2 (Hsieh's weight, S1)",
            "gram_Gamma": "G_Gamma = (+)_x |Gamma_x|^{-1} <,>_V (import's |Gamma_x|, S1)",
            "orbit": "Q_p-irreducible factor phi of the char-poly of a generic T = sum c_l T_l; A_phi = ker phi(T) saturated",
            "eta_B": "v_p(eta^B) = v_p(det G_w|A_phi) for deg phi = 1 (if:s04-etaB, d = 1); for deg phi > 1 the "
                     "number is the Z_p-length of the orbit's congruence module (Hsieh Rem. 7.3)",
            "m": "block = orbits with equal residual eigensystem of all T_l used; old_congruent = residual "
                 "eigenvalues equal a_l(g) mod p, g the level-1 eigenform of weight k",
            "status": "computed",
        },
        "triples": data,
        "all_ok": all(v["all_ok"] for v in data.values()),
    }


def main() -> None:
    with results.Timer() as t:
        data = compute_all()
    results.write(
        "s06/T5_def.json", data, script="code/python/langlandscape/defect/gram.py",
        params={"triples": [list(x) for x in TRIPLES], "ells": list(ELLS), "prec": PREC,
                "generic_T_coefficient_choices": [list(c) for c in COEFS]},
        runtime_s=t.seconds,
        notes="S06-C5: T5 definite side; Gram matrices with w_x and |Gamma_x|, eta^B from the Gram determinant",
    )
    assert data["all_ok"], "S06-C5 check failed for some triple"


if __name__ == "__main__":
    main()
