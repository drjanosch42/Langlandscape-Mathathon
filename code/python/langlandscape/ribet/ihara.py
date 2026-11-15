"""S03-C4: test T6 -- ``coker alpha = H_0`` with ``V_k`` coefficients, the map ``epsilon`` and the Hecke action.

Tex labels (``mathematics/chapters/s03/4-ihara.tex`` unless stated): conventions ``ss:s03-conv`` (C1)--(C6),
``thm:s03-iharaH0`` (a), (b), ``rem:s03-pm`` and its exponent table, ``rem:s03-T6``; ``thm:s03-ribet``,
``cor:s03-ihara`` (``3-ribet.tex``).  Stage-02 code reused (not modified): :func:`langlandscape.twoterm.tree_data`
and :class:`langlandscape.twoterm.LocalModel` (quotient graph ``BG(U, q)`` with the transport elements ``u_0, u_1``
and the stabilisers ``H_x = x_p^{-1} Gamma_x x_p`` in ``GL_2(Z/p^m)``), the linear algebra of
:mod:`langlandscape.twoterm` (``sym`` = ``Sym^n`` with the action ``(g.P)(X, Y) = P((X, Y) g)`` of ``eq:s01-Vk``,
``projector``, ``image_basis``, ``elementary_divisors``), and the splitting ``phi_c`` of
:class:`langlandscape.levels.ClassData`.

Setting (T6, ``rem:s03-T6`` (c)): ``B = B_3`` (``D = 3``), ``q = 2``, ``U = O^^x`` (``U_p = GL_2(Z_p)``), ``p in {5, 7}``,
coefficients over ``Z/p^m``.  For ``B_3`` the class set ``X_B(O^^x)`` is one point ``x_0`` (``|Gamma_{x_0}| = 12``) and
``X_B(U_0(2))`` is one edge (``|Gamma_e| = 4``), so ``BG(U, 2)`` is a single edge joining the two vertices.

Levels.
* ``level = "max"``: ``V = V_k = Sym^{k-2}((Z/p^m)^2)``, ``U^1_p = SL_2(Z_p)``.
* ``level = "U1p"``: the level ``U_1(p)_p x O^^{x,(p)}`` is realised by Shapiro's lemma: at the maximal level ``O^^x`` we take
  ``W = Ind_{U_1(p)_p}^{GL_2(Z_p)} V_k = V_k (x) Z[P]``, ``P = (Z/p)^2 - 0`` (the coset ``g U_1(p)`` <-> the row
  ``(0, 1) g^{-1}``), with ``g (v (x) [r]) = g v (x) [r g^{-1}]``.  Then ``M(O^^x; W) = M(U_1(p); V_k)`` and
  ``thm:s03-iharaH0`` applies verbatim to ``W`` at maximal level; ``W_{SL_2(Z_p)} = (V_k)_{U_1(p)^1}`` (Shapiro), realised by
  ``pi(v (x) [r]) = Sym(M_r) v`` with ``M_r in SL_2(Z/p^m)`` of second row ``= r mod p`` (equivariance is checked).

Complexes (both presentations of the exponent table after ``rem:s03-pm``).
* *Cohomological* ((C1), (C3)): ``P = M(U; W)^2 = (W^{H_x})^2``, ``alpha = (-s_{0*}, s_{1*})`` with the traces
  ``(s_{j*} g)(x) = sum_{h in H_x / u_j H_e u_j^{-1}} h u_j g(e) = [H_x : H_e] e_{H_x}(u_j g(e))`` (stage 02's ``tr_j``,
  ``prop:s02-Mhomprops`` (d)); ``epsilon(f_0, f_1) = sum_x w_x^{-1} ([tau(x)] f_0(x) + [q tau(x)] f_1(x))`` in ``W_{U^1_p}``
  (``thm:s03-iharaH0`` (a)); Hecke (C4): ``(T_l f)(x_0) = sum_i f(x_0 g_i) = sum_{gamma} phi_0(gamma) f(x_0)``, ``gamma`` over
  ``{gamma in O : nrd gamma = l} / O^x`` (right cosets; ``x_0 g_i = gamma_i x_0 u_i`` gives ``u_{i,p}^{-1} = phi_0(gamma_i)``).
* *Homological* (normative, ``if:s02-indef``; ``rem:s03-pm``): ``P_* = (W_{H_x})^2`` modelled on ``e_H W``, ``d = (-s_{0*}, s_{1*})``
  with ``s_{j*}(v) = e_{H_x}(u_j v)`` (exactly :meth:`twoterm.LocalModel.boundary`), ``epsilon_*(c_0, c_1) = [tau] c_0 + [q tau] c_1``
  (``= epsilon o nu``), and ``T_l^hom([x] (x) v) = sum_i [x g_i] (x) v``, i.e. ``v -> e_H sum_gamma phi_0(gamma)^{-1} v``.

``[t]`` (C6) is the action of ``u_t = diag(t, 1)`` (``det = t``; ``u_t in U_1(p)_p`` too).  ``tau(x_0)`` (C5): with one vertex
class we normalise ``tau(x_0) = 1``; another value composes ``epsilon`` with the automorphism ``[tau(x_0)]``, which changes none
of the checked statements (checked with ``tau(x_0) = 2``).  (C5) ``tau(y alpha) = q^{-1} tau(y)`` is checked on the edge as
``det u_1 = q^{-1} det u_0`` (``tau_transport``).

Checks per case (``p, m, k, level``): ``H_0 = coker alpha`` (invariants), ``V_{U^1_p}`` (invariants, computed from generators of
``U^1_p mod p^m``), ``epsilon`` well defined (representative change ``x -> x u``, random ``u``), ``epsilon alpha = 0``, onto,
``|coker alpha| = |V_{U^1_p}|`` (hence ``ker epsilon = im alpha``); for each ``l`` the induced ``T_l`` on ``H_0`` compared with
``(1+l)[l]^{+1}`` and ``(1+l)[l]^{-1}`` in both conventions; ``distinguishes`` records whether the two candidates differ on
``H_0`` (when they agree the exponent is not observable); ``S_l`` (:meth:`IharaCase.central`) against ``[l]^{+-2}``; at maximal
level the Hecke matrices against PARI ``mf`` (:meth:`IharaCase.hecke_vs_mf`).  Acceptance as changed after the M7 audit
(``mathematics/chapters/s03/NOTES.md`` M7.1, M7.3; ``ACCEPTANCE_CHANGE``): the exponent is only observable at ``U_1(p)``.
Further checks: ``S_l = T_{z_l}`` is derived with :meth:`IharaCase.hecke_from` and checked against ``T_l^2 - T_{l^2} = l S_l``
(:meth:`IharaCase.hecke_relation`; at ``U_1(p)`` only while ``dim W <= 240``); at ``U_1(p)`` the cohomological ``T_l`` is checked
against PARI ``mf`` on the 3-new forms of ``Gamma_0(3) cap Gamma_1(p)`` (:meth:`IharaCase.hecke_vs_mf_U1p`, ``EXPONENT_CASES``).
Limitations: the Hecke primes ``l = 11`` at ``p = 5`` (``l = 1 mod p``) and ``l = 13`` at ``p = 7`` (``1 + l = 0 mod p``) carry no
sign information (:func:`uninformative`); ``U_1(p)`` cases run at ``m = 1`` except one ``m = 2`` case (``EXTRA_CASES``).

Run ``python3 -m langlandscape.ribet.ihara`` (from ``code/python``) to write ``code/results/s03/T6.json``.
"""

from __future__ import annotations

import random
from functools import lru_cache

from .. import results
from .. import twoterm as tt
from ..twoterm import _Coords, elementary_divisors, image_basis, mat_inv2, projector, sym

D, Q = 3, 2
PS = (5, 7)
ELLS = (5, 7, 11, 13)
# Hecke primes that carry no sign information (recorded per row as ``uninformative_prime``): l = 1 mod p ([l] = 1 mod p;
# here l = 11 at p = 5) and l = -1 mod p (1 + l = 0 mod p, T_l = 0 on H_0 at m = 1; here l = 13 at p = 7).


def uninformative(ell: int, p: int):
    """Why ``l`` cannot separate the exponents mod ``p`` (``None`` if it can): ``l = 1`` or ``l = -1 mod p``."""
    if ell % p == 1:
        return "l = 1 mod p: [l] = 1 mod p"
    if ell % p == p - 1:
        return "l = -1 mod p: 1 + l = 0 mod p"
    return None


# ---------------------------------------------------------------- small linear algebra over Z/p^m
def _det(g, mod):
    return (g[0][0] * g[1][1] - g[0][1] * g[1][0]) % mod


def _diag(t, mod):
    return ((t % mod, 0), (0, 1))


def structure(cols, dim: int, p: int, m: int) -> list[int]:
    """``Z/p^m``-module structure of ``(Z/p^m)^dim / span(cols)``: sorted exponents ``e`` (a summand ``Z/p^e``)."""
    if dim == 0:
        return []
    if not cols:
        return [m] * dim
    A = [[c[i] for c in cols] for i in range(dim)]
    ed = elementary_divisors(A, p, m)
    return sorted([m] * (dim - len(ed)) + [v for v in ed if v > 0])


def in_span(R, cols, dim, p, m) -> bool:
    """``span(cols) subseteq span(R)`` (equal quotient structures, as ``span R subseteq span(R + cols)``)."""
    return structure(R + list(cols), dim, p, m) == structure(R, dim, p, m)


def _matvec(S, v, mod):
    return [sum(a * b for a, b in zip(row, v)) % mod for row in S]


# ---------------------------------------------------------------- coefficient modules W = V_k (x) Z[P]
class Coeff:
    """``W = V_k (x) Z[P]`` over ``Z/p^m`` (``P = {*}`` for ``level = "max"``, ``(Z/p)^2 - 0`` for ``"U1p"``), see module doc.

    Vectors are lists indexed by ``r * (n+1) + t`` (``r`` the index of the point, ``t`` the monomial ``X^{n-t} Y^t``)."""

    def __init__(self, k: int, p: int, m: int, level: str):
        assert level in ("max", "U1p")
        self.k, self.n, self.p, self.m, self.mod, self.level = k, k - 2, p, m, p**m, level
        self.d = k - 1
        if level == "max":
            self.P = [None]
        else:
            self.P = [(a, b) for a in range(p) for b in range(p) if (a, b) != (0, 0)]
        self.idx = {r: i for i, r in enumerate(self.P)}
        self.dim = len(self.P) * self.d
        self._sym: dict = {}

    # -- the GL_2(Z/p^m)-action
    def S(self, g):
        if g not in self._sym:
            self._sym[g] = sym(g, self.n, self.mod)
        return self._sym[g]

    def pt(self, r, g):
        """``r g^{-1} mod p`` (the point of ``g . [r]``)."""
        if r is None:
            return None
        p = self.p
        gi = mat_inv2(g, self.mod)
        return ((r[0] * gi[0][0] + r[1] * gi[1][0]) % p, (r[0] * gi[0][1] + r[1] * gi[1][1]) % p)

    def act(self, g, vec):
        d, mod, S = self.d, self.mod, self.S(g)
        out = [0] * self.dim
        for i, r in enumerate(self.P):
            blk = vec[i * d:(i + 1) * d]
            if not any(blk):
                continue
            j = self.idx[self.pt(r, g)]
            w = _matvec(S, blk, mod)
            out[j * d:(j + 1) * d] = [(a + b) % mod for a, b in zip(out[j * d:(j + 1) * d], w)]
        return out

    def average(self, H, vec):
        """``e_H vec = |H|^{-1} sum_h h vec``."""
        mod = self.mod
        tot = [0] * self.dim
        for h in H:
            tot = [(a + b) % mod for a, b in zip(tot, self.act(h, vec))]
        inv = pow(len(H), -1, mod)
        return [x * inv % mod for x in tot]

    # -- invariants W^H = (+)_{H-orbits on P} V^{H_r}
    def invariants(self, H):
        """Basis (full vectors) of ``W^H`` and the coordinate map ``W^H -> (Z/p^m)^r`` (``|H|`` prime to ``p``)."""
        d, p, mod = self.d, self.p, self.mod
        seen, basis, parts = set(), [], []
        for r0 in self.P:
            if r0 in seen:
                continue
            orbit = {}
            for h in H:
                orbit.setdefault(self.pt(r0, h), h)
            seen |= set(orbit)
            stab = [h for h in H if self.pt(r0, h) == r0]
            b0s = image_basis(projector(stab, self.n, p, mod), p, mod)
            parts.append((self.idx[r0], _Coords(b0s, p, mod) if b0s else None, len(b0s)))
            for b0 in b0s:
                v = [0] * self.dim
                for r, h in orbit.items():
                    j = self.idx[r]
                    v[j * d:(j + 1) * d] = _matvec(self.S(h), b0, mod)
                basis.append(v)

        def coords(vec):
            out = []
            for i, C, r in parts:
                blk = vec[i * d:(i + 1) * d]
                out += C(blk) if r else []
                if not r:
                    assert not any(x % mod for x in blk)
            return out

        return basis, coords

    # -- the coinvariants W_{U^1_p}, realised in V_k
    def coinv_relations(self):
        """Columns ``(h - 1) e_i`` spanning the relations of ``V_{U^1}`` in ``V = (Z/p^m)^{n+1}`` for generators ``h`` of
        ``U^1 mod p^m``: ``SL_2`` (``level = max``; elementary matrices) resp. ``U_1(p) cap SL_2`` (``U1p``; ``[[1,1],[0,1]]``,
        ``[[1,0],[p,1]]``, ``diag(1+p, (1+p)^{-1})``, see ``rem:s03-T6`` (b))."""
        p, mod, d = self.p, self.mod, self.d
        gens = [((1, 1), (0, 1)), ((1, 0), (1, 1))] if self.level == "max" else \
            [((1, 1), (0, 1)), ((1, 0), (p % mod, 1)), ((1 + p, 0), (0, pow(1 + p, -1, mod)))]
        R = []
        for g in gens:
            S = self.S(g)
            for i in range(d):
                R.append([(S[t][i] - (t == i)) % mod for t in range(d)])
        return R

    def M_r(self, r):
        """``M_r in SL_2(Z/p^m)`` with second row ``r`` (lifted)."""
        mod = self.mod
        c, dd = r
        if dd % self.p:
            return ((pow(dd, -1, mod), 0), (c, dd))
        return ((0, -pow(c, -1, mod) % mod), (c, dd))

    def pi(self, vec):
        """Shapiro: ``W -> V``, ``v (x) [r] -> Sym(M_r) v`` (identity for ``level = max``); induces ``W_{SL_2} = V_{U^1}``."""
        if self.level == "max":
            return list(vec)
        d, mod = self.d, self.mod
        out = [0] * d
        for i, r in enumerate(self.P):
            blk = vec[i * d:(i + 1) * d]
            if any(blk):
                out = [(a + b) % mod for a, b in zip(out, _matvec(self.S(self.M_r(r)), blk, mod))]
        return out


# ---------------------------------------------------------------- the elements of norm l
@lru_cache(maxsize=None)
def norm_l_cosets(ell: int):
    """Right-coset representatives ``gamma O^x`` of ``{gamma in O : nrd gamma = ell}`` (coordinates in the basis of ``O``).

    There are ``ell + 1`` of them (one class, ``deg(U g U) = ell + 1``, ``def:s01-hecke``); asserted."""
    reps = norm_cosets(ell)
    assert len(reps) == ell + 1, "Hecke cosets: expected ell + 1"
    return reps


@lru_cache(maxsize=None)
def norm_cosets(N: int):
    """Right-coset representatives ``gamma O^x`` of ``{gamma in O : nrd gamma = N}`` (all of them, primitive or not); for
    ``N = l^2`` there are ``l^2 + l + 1`` (the lattices of index ``l^2``), i.e. the operator ``T_{l^2}`` with
    ``T_l^2 = T_{l^2} + l S_l``."""
    from ..pari import get_pari
    pari = get_pari()
    td = tt.tree_data(D, Q, 1, 1)
    cd = td._b.cd
    assert cd.h == 1 and cd.orders[0].basis == cd.B.O.basis
    G = cd.B.gram(cd.B.O)
    res = pari.qfminim(G, 2 * N, 10**6, 0)
    vecs = res[2]
    half = [[int(vecs[i, j]) for i in range(4)] for j in range(int(pari.matsize(vecs)[1]))]
    allv = [v for v in half + [[-t for t in v] for v in half]
            if sum(v[i] * int(G[i, j]) * v[j] for i in range(4) for j in range(4)) == 2 * N]
    units = cd.units(0)
    reps, covered = [], set()
    for v in allv:
        if tuple(v) in covered:
            continue
        reps.append(v)
        covered |= {tuple(cd.mul(0, v, u)) for u in units}
    assert len(covered) == len(allv)
    return reps


# ---------------------------------------------------------------- one case
class IharaCase:
    """``thm:s03-iharaH0`` for ``B_3``, ``q = 2``, ``U = O^^x``, coefficients :class:`Coeff` ``(k, p, m, level)``."""

    def __init__(self, k: int, p: int, m: int, level: str = "max", tau0: int = 1):
        self.td = td = tt.tree_data(D, Q, 1, 1)
        assert td.T.X == 1, "epsilon is implemented for one vertex class (true for B_3)"
        self.lm = lm = tt.LocalModel(td, p, m)
        self.W = W = Coeff(k, p, m, level)
        self.k, self.p, self.m, self.mod, self.level, self.tau0 = k, p, m, p**m, level, tau0 % p**m
        self.cd = td._b.cd
        self.Hv, self.He = lm.Hv, lm.He  # lists of 2x2 matrices mod p^m
        self.inv_v = [W.invariants(H) for H in self.Hv]
        self.inv_e = [W.invariants(H) for H in self.He]
        self.wv = [len(H) // 2 if ((self.mod - 1, 0), (0, self.mod - 1)) in set(H) else len(H) for H in self.Hv]
        self.off = [0]
        for B_, _ in self.inv_v + self.inv_v:
            self.off.append(self.off[-1] + len(B_))
        self.R = W.coinv_relations()

    # -- complexes
    def boundary(self, cohomological: bool):
        """Columns of ``alpha`` (cohomological, traces ``[H_x:H_e] e_{H_x} u_j``) resp. ``d`` (homological, ``e_{H_x} u_j``)."""
        W, mod, X = self.W, self.mod, len(self.Hv)
        cols = []
        for k, tw in enumerate(self.td.tw):
            for b in self.inv_e[k][0]:
                col = [0] * self.off[-1]
                for j, (u, v, sg) in enumerate(((self.lm.u0[k], tw.v0, -1), (self.lm.u1[k], tw.v1, 1))):
                    w = W.average(self.Hv[v], W.act(u, b))
                    idx = len(self.Hv[v]) // len(self.He[k]) if cohomological else 1
                    co = self.inv_v[v][1](w)
                    o = self.off[j * X + v]
                    for i, x in enumerate(co):
                        col[o + i] = (col[o + i] + sg * idx * x) % mod
                cols.append(col)
        return cols

    def tau(self, v: int) -> int:
        return self.tau0

    def epsilon_cols(self, cohomological: bool, tau0=None):
        """Columns (in ``V``, before reduction mod the relations ``R``) of ``epsilon`` resp. ``epsilon_* = epsilon o nu``."""
        W, mod, X = self.W, self.mod, len(self.Hv)
        t0 = self.tau0 if tau0 is None else tau0
        cols = []
        for j in (0, 1):
            for v in range(X):
                t = t0 * (Q if j else 1) % mod
                c = pow(self.wv[v], -1, mod) if cohomological else 1
                for b in self.inv_v[v][0]:
                    cols.append([x * c % mod for x in W.pi(W.act(_diag(t, mod), b))])
        return cols

    def hecke(self, ell: int, cohomological: bool):
        """``T_l`` on ``P`` (columns in coordinates): ``sum_gamma phi_0(gamma)`` (C4) resp. ``e_H sum_gamma phi_0(gamma)^{-1}``."""
        return self.hecke_from(norm_l_cosets(ell), ell, cohomological)

    def hecke_from(self, gammas, N: int, cohomological: bool):
        """``T_g`` for the double coset whose right cosets are ``gamma O^x`` (``gamma`` in ``gammas``, ``nrd gamma = N``):
        ``(T f)(x_0) = sum_gamma phi_0(gamma) f(x_0)`` (C4), homologically ``v -> e_H sum_gamma phi_0(gamma)^{-1} v``."""
        W, mod, X = self.W, self.mod, len(self.Hv)
        mats = []
        for g in gammas:
            a, b, c, d = self.cd.phi(0, g, mod)
            M = ((a, b), (c, d))
            assert _det(M, mod) == N % mod
            mats.append(M if cohomological else mat_inv2(M, mod))
        cols = []
        for j in (0, 1):
            for v in range(X):
                for b in self.inv_v[v][0]:
                    tot = [0] * W.dim
                    for M in mats:
                        tot = [(x + y) % mod for x, y in zip(tot, W.act(M, b))]
                    if not cohomological:
                        tot = W.average(self.Hv[v], tot)
                    co = self.inv_v[v][1](tot)
                    col = [0] * self.off[-1]
                    o = self.off[j * X + v]
                    col[o:o + len(co)] = co
                    cols.append(col)
        return cols

    def central(self, ell: int, cohomological: bool):
        """``S_l = T_{z_l}`` (``z_l`` the central idele ``l`` at ``l``) on ``P``, derived with :meth:`hecke_from`: one coset,
        ``gamma = l in O`` (``x_0 z_l = l x_0 u`` with ``u_p = l^{-1}``).  Cohomologically ``f(x z_l) = phi_0(l) f(x)``
        (``= l^{k-2}`` on ``V_k``, (R1)); homologically ``[x z_l] (x) v = [x] (x) phi_0(l)^{-1} v`` (``= l^{2-k}``: the
        normative ``S_l`` of ``if:s02-indef`` is the classical ``S_l^{-1}``, NOTES M7.3).  The scalar values are *checked*
        (``S_scalar_on_P``), not assumed, and independently via ``T_l^2 - T_{l^2} = l S_l`` (:meth:`hecke_relation`)."""
        one = self.cd.one(0)
        return self.hecke_from([[ell * t for t in one]], ell * ell, cohomological)

    def hecke_relation(self, ell: int, cohomological: bool) -> bool:
        """``T_l o T_l - T_{l^2} = l S_l`` on ``P`` (``T_{l^2}`` over all ``l^2 + l + 1`` cosets of norm ``l^2``)."""
        mod = self.mod
        T, S = self.hecke(ell, cohomological), self.central(ell, cohomological)
        reps = norm_cosets(ell * ell)
        assert len(reps) == ell * ell + ell + 1
        T2 = self.hecke_from(reps, ell * ell, cohomological)
        TT = [self._apply(T, c) for c in T]
        return all((a - b - ell * c) % mod == 0 for x, y, z in zip(TT, T2, S) for a, b, c in zip(x, y, z))

    # -- checks
    def compose(self, E, A):
        """``E o A`` (``E``: columns in ``V``; ``A``: columns in ``P`` coordinates)."""
        mod = self.mod
        return [[sum(E[i][r] * a[i] for i in range(len(E))) % mod for r in range(self.W.d)] for a in A]

    def eps_well_defined(self, trials: int = 3, seed: int = 0) -> bool:
        """(a1): for ``x' = x u`` (``u in GL_2(Z/p^m)`` random), ``f(x') = u^{-1} f(x)`` and ``tau(x') = tau(x) det u``
        give the same summand ``[tau(x')] f(x') = [tau(x)] f(x)`` in ``W_{U^1}``, for every basis vector ``f(x)``."""
        rnd = random.Random(seed)
        W, mod, p = self.W, self.mod, self.p
        ok = True
        for _ in range(trials):
            while True:
                u = ((rnd.randrange(mod), rnd.randrange(mod)), (rnd.randrange(mod), rnd.randrange(mod)))
                if _det(u, mod) % p:
                    break
            ui, du = mat_inv2(u, mod), _det(u, mod)
            for v in range(len(self.Hv)):
                for c in (1, Q):
                    t = self.tau(v) * c % mod
                    diffs = []
                    for b in self.inv_v[v][0]:
                        lhs = W.pi(W.act(_diag(t * du, mod), W.act(ui, b)))
                        rhs = W.pi(W.act(_diag(t, mod), b))
                        diffs.append([(a - b_) % mod for a, b_ in zip(lhs, rhs)])
                    ok = ok and in_span(self.R, diffs, W.d, p, self.m)
        return ok

    def shapiro_check(self, trials: int = 2, seed: int = 1) -> bool:
        """``pi(h w) = pi(w)`` mod ``R`` for ``h in SL_2`` and ``pi(u_t w) = [t] pi(w)`` (``level = U1p``; trivial for max)."""
        if self.W.level == "max":
            return True
        rnd = random.Random(seed)
        W, mod, p = self.W, self.mod, self.p
        diffs = []
        for _ in range(trials):
            w = [rnd.randrange(mod) for _ in range(W.dim)]
            for h in (((1, 1), (0, 1)), ((1, 0), (1, 1))):
                diffs.append([(a - b) % mod for a, b in zip(W.pi(W.act(h, w)), W.pi(w))])
            t = 2
            diffs.append([(a - b) % mod for a, b in
                          zip(W.pi(W.act(_diag(t, mod), w)), _matvec(W.S(_diag(t, mod)), W.pi(w), mod))])
        return in_span(self.R, diffs, W.d, p, self.m)

    def scalar_on_H0(self, cols, target_cols):
        """The ``lam in Z/p^m`` with ``cols = lam * target_cols`` mod ``R`` (smallest), or ``None``; ``0`` if ``H_0 = 0``."""
        d, mod, p, m = self.W.d, self.mod, self.p, self.m
        for lam in range(mod):
            diffs = [[(a - lam * b) % mod for a, b in zip(c, t)] for c, t in zip(cols, target_cols)]
            if in_span(self.R, diffs, d, p, m):
                return lam
        return None

    def run(self, ells=ELLS) -> dict:
        p, m, mod, W = self.p, self.m, self.mod, self.W
        d = W.d
        Vcoinv = structure(self.R, d, p, m)
        out = {"p": p, "m": m, "k": self.k, "level": self.level, "D": D, "q": Q,
               "rank_P": self.off[-1], "rank_edge_module": sum(len(B_) for B_, _ in self.inv_e),
               "V_U1_coinvariants": Vcoinv, "shapiro_equivariance": self.shapiro_check()}
        out["tau_transport"] = all(
            _det(self.lm.u1[e], mod) * Q % mod == _det(self.lm.u0[e], mod) for e in range(len(self.td.tw)))
        out["eps_well_defined"] = self.eps_well_defined()
        I_d = [[int(i == j) for i in range(d)] for j in range(d)]
        conv = {}
        for name, coh in (("cohomological", True), ("homological", False)):
            A = self.boundary(coh)
            E = self.epsilon_cols(coh)
            H0 = structure(A, self.off[-1], p, m)
            EA = self.compose(E, A)
            c = {"H0": H0,
                 "eps_alpha_zero": in_span(self.R, EA, d, p, m),
                 "eps_onto": structure(self.R + E, d, p, m) == [],
                 "same_order": H0 == Vcoinv}
            c["ker_eps_eq_im_alpha"] = c["eps_alpha_zero"] and c["eps_onto"] and c["same_order"]
            if coh:
                E2 = self.epsilon_cols(coh, tau0=2)
                c["tau0_2_ok"] = in_span(self.R, self.compose(E2, A), d, p, m) and structure(self.R + E2, d, p, m) == []
            hk = {}
            for ell in ells:
                if ell == p or ell % 2 == 0 or ell % 3 == 0:
                    continue
                T = self.hecke(ell, coh)
                ET = self.compose(E, T)
                row = {"T_preserves_im": in_span(self.R, self.compose(E, [self._apply(T, a) for a in A]), d, p, m)}
                for e in (1, -1):
                    Sl = W.S(_diag(pow(ell, e, mod), mod))
                    target = [[(1 + ell) * x % mod for x in _matvec(Sl, col, mod)] for col in E]
                    diffs = [[(a - b) % mod for a, b in zip(x, y)] for x, y in zip(ET, target)]
                    row["acts_as_(1+l)[l]^%+d" % e] = in_span(self.R, diffs, d, p, m)
                Sp, Sm = W.S(_diag(ell, mod)), W.S(_diag(pow(ell, -1, mod), mod))
                row["distinguishes"] = not in_span(
                    self.R, [[(1 + ell) * (Sp[t][i] - Sm[t][i]) % mod for t in range(d)] for i in range(d)], d, p, m)
                row["exponent_observed"] = [e for e in (1, -1) if row["acts_as_(1+l)[l]^%+d" % e]] \
                    if row["distinguishes"] else "undetermined"
                row["vacuous"] = H0 == []  # H_0 = 0: every operator statement on H_0 holds trivially
                row["uninformative_prime"] = uninformative(ell, p)
                # S_l on H_0: [l]^2 cohomological, [l]^{-2} homological (exponent table + M7.3)
                ES = self.compose(E, self.central(ell, coh))
                for e in (2, -2):
                    Sl = W.S(_diag(pow(ell, e, mod), mod))
                    diffs = [[(a - b) % mod for a, b in zip(x, _matvec(Sl, y, mod))] for x, y in zip(ES, E)]
                    row["S_acts_as_[l]^%+d" % e] = in_span(self.R, diffs, d, p, m)
                S2p, S2m = W.S(_diag(pow(ell, 2, mod), mod)), W.S(_diag(pow(ell, -2, mod), mod))
                row["S_distinguishes"] = not in_span(
                    self.R, [[(S2p[t][i] - S2m[t][i]) % mod for t in range(d)] for i in range(d)], d, p, m)
                if self.level == "max":
                    # on the whole Brandt module P (not only H_0): S_l is the scalar l^{+-(k-2)}
                    sc = pow(ell, self.k - 2 if coh else 2 - self.k, mod)
                    Sc = self.central(ell, coh)
                    row["S_scalar_on_P"] = all(Sc[j][i] == (sc if i == j else 0) for j in range(len(Sc))
                                               for i in range(len(Sc)))
                if H0:
                    row["T_scalar_on_H0"] = self.scalar_on_H0(ET, E)
                    lam = self.scalar_on_H0([_matvec(Sp, col, mod) for col in I_d], I_d)
                    row["diamond_l_scalar_on_H0"] = lam
                hk[str(ell)] = row
            c["hecke"] = hk
            l0 = next((l for l in ells if l != p and l % 6 and not uninformative(l, p)), None)
            if l0 is not None and (self.level == "max" or W.dim <= 240):
                c["hecke_relation_T_l^2-T_l2=lS_l"] = {"l": l0, "ok": self.hecke_relation(l0, coh)}
            else:
                c["hecke_relation_T_l^2-T_l2=lS_l"] = "not computed (cost; W too large)"
            conv[name] = c
        out["conventions"] = conv
        out["H0"] = conv["cohomological"]["H0"]
        if self.level == "max":
            out["stage02_LocalModel_H0"] = sorted(self.lm.homology(self.k)["H0"])
            if self.k % 2 == 0:
                out["hecke_vs_mf"] = {str(l): self.hecke_vs_mf(l) for l in ells if l % p and l % 6}
        elif self.k >= 3 and (p, self.k) in EXPONENT_CASES:
            l0 = next(l for l in ells if l != p and l % 6 and not uninformative(l, p))
            out["hecke_vs_mf_U1p"] = self.hecke_vs_mf_U1p(l0)
        return out

    def hecke_vs_mf_U1p(self, ell: int) -> dict:
        """Independent check of the Hecke matrices at ``U_1(p)`` (``k >= 3``): the characteristic polynomial mod ``p^m`` of the
        cohomological ``T_l`` on ``M(O^^x; W) = M(U_1(p); V_k)`` equals that of the classical ``T_l`` on the 3-new part of
        ``S_k(Gamma_0(3) cap Gamma_1(p))`` (JL with nebentypus): the product over Galois orbits of characters ``chi mod p`` with
        ``chi(-1) = (-1)^k`` of ``N_{Q(chi)/Q} charpoly(T_l | S_k(3p, chi)^new)``, times ``charpoly(T_l | S_k(3)^new)^2`` for
        ``chi = 1`` (``p``-old forms, ``sigma_0(p) = 2``).  The homological charpoly is recorded, not compared."""
        from math import gcd
        from ..pari import get_pari
        pari = get_pari()
        p, k, mod = self.p, self.k, self.mod
        r = len(self.inv_v[0][0])

        def cp(cols):
            M = "[" + ";".join(",".join(str(cols[j][i]) for j in range(r)) for i in range(r)) + "]"
            return str(pari(f"lift(charpoly(Mod(Mat({M}), {mod})))"))

        tot, dim, seen = pari("1"), 0, set()
        for a in range(1, p):
            if a in seen:
                continue
            o = int(pari(f"znorder(Mod({a}, {p}))"))
            seen |= {pow(a, e, p) for e in range(1, o + 1) if gcd(e, o) == 1}
            if int(pari(f"zncharisodd(znstar({p}, 1), {a})")) != k % 2:
                continue
            for N, mult in ([(3, 2), (3 * p, 1)] if a == 1 else [(3 * p, 1)]):
                chi = "" if a == 1 else f", Mod({a}, {p})"
                mf = pari(f"mfinit([{N}, {k}{chi}], 0)")
                if int(pari.mfdim(mf)) == 0:
                    continue
                f = pari.liftall(pari.charpoly(pari.mfheckemat(mf, ell)))
                if o > 2:
                    f = pari.polresultant(f, pari(f"polcyclo({o}, t)"), "t")
                dim += mult * int(pari.poldegree(f))
                tot = tot * f**mult
        want = str(pari(f"lift(Mod(1, {mod}) * ({tot}))"))
        ours = cp(self.hecke(ell, True))
        assert dim == r, "rk M(U_1(p); V_k) != dim of the 3-new forms (JL)"
        return {"l": ell, "rank_M": r, "charpoly_cohom": ours, "charpoly_mf": want, "cohom_eq_mf": ours == want,
                "charpoly_hom": cp(self.hecke(ell, False))}

    def hecke_vs_mf(self, ell: int) -> dict:
        """Independent check of the Hecke matrices (maximal level, ``k`` even): the characteristic polynomial mod ``p^m`` of
        the cohomological ``T_l`` on ``M(O^^x; V_k)`` equals that of the classical ``T_l`` on ``S_k(Gamma_0(3))^new`` (PARI
        ``mf``; JL, plus the Eisenstein line ``1 + l`` at ``k = 2``), as (R1) predicts; the homological ``T_l`` has the
        characteristic polynomial of ``l^{2-k} T_l`` (``= S_l^{-1} T_l``, ``rem:s03-pm``)."""
        from ..pari import get_pari
        pari = get_pari()
        mod, k, n = self.mod, self.k, self.k - 2
        r = len(self.inv_v[0][0])

        def cp(cols):
            M = "[" + ";".join(",".join(str(cols[j][i]) for j in range(r)) for i in range(r)) + "]" if r else "matrix(0,0)"
            return str(pari(f"lift(charpoly(Mod(Mat({M}), {mod})))"))

        mf = pari(f"mfinit([3, {k}], 0)")
        dim = int(pari.mfdim(mf))
        H = pari.mfheckemat(mf, ell) if dim else None
        cls = [[int(H[i, j]) for j in range(dim)] for i in range(dim)] if dim else []
        if k == 2:
            cls = [[ell + 1]]
            dim = 1
        tot = len(cls)
        assert tot == r, "rk M(O^x; V_k) != dim S_k(3)^new + [k = 2] (JL)"
        sc = pow(ell, -n, mod)
        Mcl = "[" + ";".join(",".join(str(x) for x in row) for row in cls) + "]" if tot else "matrix(0,0)"
        want = str(pari(f"lift(charpoly(Mod(Mat({Mcl}), {mod})))"))
        want_h = str(pari(f"lift(charpoly(Mod({sc} * Mat({Mcl}), {mod})))"))
        Tc, Th = self.hecke(ell, True), self.hecke(ell, False)
        return {"rank_M": r, "charpoly_cohom": cp(Tc), "charpoly_mf": want, "cohom_eq_mf": cp(Tc) == want,
                "charpoly_hom": cp(Th), "charpoly_l^(2-k)mf": want_h, "hom_eq_l^(2-k)mf": cp(Th) == want_h}

    def _apply(self, T, a):
        mod = self.mod
        return [sum(T[j][i] * a[j] for j in range(len(a))) % mod for i in range(len(a))]


# ---------------------------------------------------------------- driver
def cases():
    """``(k, p, m, level)``: maximal level ``m = 2``, ``2 <= k <= 2p``; ``U_1(p)`` with ``m = 1``, ``2 <= k <= KMAX_U1[p]``
    (covers the exponent-distinguishing weights of NOTES M7.2: ``p = 5``: ``k in {7, 9}``; ``p = 7``: ``k in {9, 10}``)."""
    out = []
    for p in PS:
        out += [(k, p, 2, "max") for k in range(2, 2 * p + 1)]
        out += [(k, p, 1, "U1p") for k in range(2, KMAX_U1[p] + 1)]
    return out + list(EXTRA_CASES)


KMAX_U1 = {5: 9, 7: 10}
EXTRA_CASES = ((7, 5, 2, "U1p"),)  # one U_1(p) case over Z/p^2 (all other U_1(p) cases run at m = 1 for cost)
EXPONENT_CASES = ((5, 7), (5, 9), (7, 9), (7, 10))  # (p, k) at U_1(p), NOTES M7.1/M7.2

ACCEPTANCE_CHANGE = (
    "Acceptance changed by the S03 coordinator after the M7 maths audit (mathematics/chapters/s03/NOTES.md, "
    "wip-implementation 6ff60ad). M7.1: rem:s03-T6(c) is wrong at the level maximal at p: H_0 != 0 only if "
    "(p-1) | (k-2), and there [l] is trivial mod p, so the +-1 exponent is not observable at maximal level; the "
    "exponent test (cohomological (1+l)[l], homological (1+l)[l]^{-1}) is run at U_1(p) for p = 5, k in {7, 9} and "
    "p = 7, k in {9, 10} and must distinguish the conventions with exponent +1 cohomologically. At maximal level the "
    "asserted claim is 'H_0 = 0 unless (p-1) | (k-2)'. M7.3: the normative (homological) S_l is l^{2-k} (the classical "
    "S_l^{-1}); S_l is checked as [l]^2 (cohomological) / [l]^{-2} (homological) on H_0 and as the scalar "
    "l^{k-2} / l^{2-k} on the Brandt module. The original claims (H_0 = 0 for 3 <= k <= p+1; T_l = (1+l)[l]^{+-1} for "
    "p+3 <= k <= 2p) are still recorded: both hold, the second only non-discriminatingly.")


def acceptance(rows) -> dict:
    """PYCHK of S03-C4 as changed after M7 (``ACCEPTANCE_CHANGE``): at maximal level ``H_0 = 0`` unless ``(p-1) | (k-2)``;
    at ``U_1(p)`` (``EXPONENT_CASES``) the two conventions are distinguished, exponent ``+1`` cohomological, ``-1``
    homological; ``H_0 != 0`` at ``U_1(p)``; ``S_l = [l]^{+-2}``; all ``epsilon`` checks.  The original plan claims are kept
    as recorded (non-asserted-by-M7) flags."""
    acc = {"max_H0_zero_unless_(p-1)|(k-2)": True, "U1p_exponent_cases_distinguished": True,
           "U1p_exponent_cohom_+1_hom_-1": True, "S_l_cohom_[l]^2_hom_[l]^-2": True, "S_l_scalar_on_P_max": True,
           "original_H0_vanishes_3_le_k_le_p+1": True, "original_T_l_p+3_le_k_le_2p_holds_vacuous_or_nondiscriminating": True,
           "S_l_nonvacuous_discriminating_instances": 0, "hecke_relation_ok": True, "hecke_matches_mf_U1p": True,
           "H0_nonzero_U1p": True, "epsilon_checks": True, "exponent_distinguished_somewhere": False,
           "exponent_cohom_observed": set(), "exponent_hom_observed": set(), "hecke_matches_mf": True}
    for r in rows:
        p, k = r["p"], r["k"]
        cc, ch = r["conventions"]["cohomological"], r["conventions"]["homological"]
        for c in (cc, ch):
            acc["epsilon_checks"] &= c["ker_eps_eq_im_alpha"]
        acc["epsilon_checks"] &= r["eps_well_defined"] and r["tau_transport"] and r["shapiro_equivariance"] \
            and cc["tau0_2_ok"]
        if r["level"] == "max" and (k - 2) % (p - 1):
            acc["max_H0_zero_unless_(p-1)|(k-2)"] &= r["H0"] == []
        if r["level"] == "max" and 3 <= k <= p + 1:
            acc["original_H0_vanishes_3_le_k_le_p+1"] &= r["H0"] == []
        if r["level"] == "max" and p + 3 <= k <= 2 * p:
            # holds, but only vacuously (H_0 = 0, p+3 <= k < 2p) or non-discriminatingly (k = 2p, [l] = 1)
            for row in cc["hecke"].values():
                acc["original_T_l_p+3_le_k_le_2p_holds_vacuous_or_nondiscriminating"] &= row["acts_as_(1+l)[l]^+1"] and (row["vacuous"] or not row["distinguishes"])
            for row in ch["hecke"].values():
                acc["original_T_l_p+3_le_k_le_2p_holds_vacuous_or_nondiscriminating"] &= row["acts_as_(1+l)[l]^-1"] and (row["vacuous"] or not row["distinguishes"])
        if r["level"] == "U1p" and (p, k) in EXPONENT_CASES:
            hc, hh = cc["hecke"], ch["hecke"]
            acc["U1p_exponent_cases_distinguished"] &= any(row["distinguishes"] for row in hc.values())
            for l, row in hc.items():
                if row["distinguishes"]:
                    acc["U1p_exponent_cohom_+1_hom_-1"] &= row["exponent_observed"] == [1] \
                        and hh[l]["exponent_observed"] == [-1]
        for c in (cc, ch):
            rel = c["hecke_relation_T_l^2-T_l2=lS_l"]
            if isinstance(rel, dict):
                acc["hecke_relation_ok"] &= rel["ok"]
            for row in c["hecke"].values():
                acc["S_l_nonvacuous_discriminating_instances"] += (not row["vacuous"]) and row["S_distinguishes"]
        if "hecke_vs_mf_U1p" in r:
            acc["hecke_matches_mf_U1p"] &= r["hecke_vs_mf_U1p"]["cohom_eq_mf"]
        for row in cc["hecke"].values():
            acc["S_l_cohom_[l]^2_hom_[l]^-2"] &= row["S_acts_as_[l]^+2"]
            acc["S_l_scalar_on_P_max"] &= row.get("S_scalar_on_P", True)
        for row in ch["hecke"].values():
            acc["S_l_cohom_[l]^2_hom_[l]^-2"] &= row["S_acts_as_[l]^-2"]
            acc["S_l_scalar_on_P_max"] &= row.get("S_scalar_on_P", True)
        if r["level"] == "U1p":
            acc["H0_nonzero_U1p"] &= r["H0"] != []
        for h in r.get("hecke_vs_mf", {}).values():
            acc["hecke_matches_mf"] &= h["cohom_eq_mf"] and h["hom_eq_l^(2-k)mf"]
        for name, c in (("cohom", cc), ("hom", ch)):
            for row in c["hecke"].values():
                if row["distinguishes"]:
                    acc["exponent_distinguished_somewhere"] = True
                    acc["exponent_%s_observed" % name] |= set(row["exponent_observed"])
    return acc


FLAG_NOTES = {
    "original_H0_vanishes_3_le_k_le_p+1": "original plan claim (rem:s03-T6 (a)); holds and is consistent with M7.1",
    "original_T_l_p+3_le_k_le_2p_holds_vacuous_or_nondiscriminating":
        "original plan claim; for p+3 <= k < 2p it holds vacuously (H_0 = 0), at k = 2p non-discriminatingly ([l] = 1 on "
        "H_0 = Z/p); the flag also asserts that no row in this range distinguishes the exponents (M7.1/M7.2)",
    "S_l_cohom_[l]^2_hom_[l]^-2": "S_l = T_{z_l} derived from hecke_from (gamma = l); vacuous where H_0 = 0; the number "
        "of non-vacuous rows where [l]^2 != [l]^{-2} on H_0 is S_l_nonvacuous_discriminating_instances",
    "S_l_scalar_on_P_max": "maximal level: S_l is the scalar l^{k-2} (cohom.) / l^{2-k} (homol., M7.3) on the Brandt module",
    "hecke_relation_ok": "T_l^2 - T_{l^2} = l S_l on P, both conventions, first informative l (U_1(p): only if dim W <= 240)",
    "hecke_matches_mf": "maximal level, k even: charpoly of T_l = PARI mf on S_k(3)^new (cohom.), = l^{2-k} T_l (homol.)",
    "hecke_matches_mf_U1p": "U_1(p), EXPONENT_CASES: charpoly of cohom. T_l = classical T_l on the 3-new forms of "
        "Gamma_0(3) cap Gamma_1(p) (PARI mf, all characters mod p)",
    "uninformative primes": "l = 11 at p = 5 (l = 1 mod p) and l = 13 at p = 7 (1 + l = 0 mod p) carry no sign "
        "information; rows record uninformative_prime",
    "m": "maximal level m = 2; U_1(p) at m = 1 except EXTRA_CASES (p = 5, k = 7, m = 2)",
}


def compute_all() -> dict:
    rows = [IharaCase(*c).run() for c in cases()]
    acc = acceptance(rows)
    summary = [{"p": r["p"], "m": r["m"], "k": r["k"], "level": r["level"], "H0": r["H0"],
                "exp_cohom": {l: h["exponent_observed"] for l, h in r["conventions"]["cohomological"]["hecke"].items()},
                "exp_hom": {l: h["exponent_observed"] for l, h in r["conventions"]["homological"]["hecke"].items()}}
               for r in rows]
    obs = {"max_level_nonzero_H0_k_gt_2": [{"p": r["p"], "k": r["k"], "H0": r["H0"]} for r in rows
                                            if r["level"] == "max" and r["k"] > 2 and r["H0"]],
           "exponent_distinguishing_cases": [{"p": r["p"], "k": r["k"], "level": r["level"], "l": l,
                                              "cohom": h["exponent_observed"],
                                              "hom": r["conventions"]["homological"]["hecke"][l]["exponent_observed"]}
                                             for r in rows for l, h in r["conventions"]["cohomological"]["hecke"].items()
                                             if h["distinguishes"]]}
    return {"cases": rows, "summary": summary, "acceptance": acc, "observations": obs,
            "acceptance_change": ACCEPTANCE_CHANGE, "flag_notes": FLAG_NOTES}


def main() -> None:
    with results.Timer() as t:
        data = compute_all()
    path = results.write("s03/T6.json", data, script="code/python/langlandscape/ribet/ihara.py",
                         params={"D": D, "q": Q, "ps": PS, "ells": ELLS, "cases": cases(),
                                 "exponent_cases_U1p": EXPONENT_CASES},
                         runtime_s=round(t.seconds, 2),
                         notes="S03-C4 / T6 (rem:s03-T6): coker alpha with V_k over Z/p^m for B_3, q = 2; epsilon of "
                               "thm:s03-iharaH0 (a); T_l on H_0 in the cohomological (C4) and homological (if:s02-indef) "
                               "conventions (exponent table after rem:s03-pm); U_1(p) via Shapiro (W = Ind V_k). "
                               "H0 = list of exponents e (summand Z/p^e). 'undetermined' = (1+l)[l] and (1+l)[l]^{-1} "
                               "agree on H_0.")
    print(path)


if __name__ == "__main__":
    main()
