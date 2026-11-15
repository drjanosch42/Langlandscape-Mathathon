# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C1: the ``p``-tower ``X_s``, ``X'_s`` of ss:s04-notation with ``U_p``, ``U'_p``, diamonds and projections.

Setting.  ``B = B_D`` definite with ``h(D) = 1`` (``D`` in ``{2, 3, 5, 7, 13}``; the S01 :func:`levels.class_data`
order and splittings), a prime ``p`` not dividing ``D M N0``, the level prime to ``p``
``U = U_1(M) cap U_0(N0)`` and
``X_s = X_B(U^{(p)} K_s)``, ``K_s = U_1(p^s)_p``;  ``X'_s = X_B(U^{(p)} K'_s)``, ``K'_s = K_s cap U_0(p^{s+1})_p``.

Points (as in :mod:`langlandscape.up` / :mod:`.sign_pin`).  ``h = 1``: a point is ``O^x``-orbit of a pair
``(v, l)``: ``v = e_2 k^{-1}`` a primitive row vector mod ``Nf`` taken modulo the scalars ``lambda = 1 mod Nv``, and
``l`` a line mod ``N0`` (``()`` if ``N0 = 1``); ``O^x`` acts by ``v -> v phi(gamma)^{-1}``.  For ``X_s``:
``Nf = Nv = M p^s``.  For ``X'_s``: ``Nf = M p^{s+1}``, ``Nv = M p^s`` (``K'_s`` = stabiliser of the line of ``e_2``
mod ``p^{s+1}`` with scalar ``= 1 mod p^s``).  Stabilisers are trivial (N1) and asserted.

Operators (homological, columns = images, ``Mat[t, c]`` = coefficient of ``[x_t]`` in ``T[x_c]``).
* ``U_p[x] = sum_j [x varpi_j]``, ``varpi_j = [[p, j], [0, 1]]`` at ``p`` (the same ``varpi_j`` on ``X_{s+1}, X'_s,
  X_s``, lem:s04-hida(a)); ``U'_p[x] = sum_j [x [[1, 0], [p^s j, p]]]`` on ``X_s`` (lem:s01-Up(c)).
  ``[x g]``: ``x g = gamma y`` with ``Nrd gamma = p``, ``y`` integral; at ``p``: ``y = iota(gamma)^{-1} k g``, at the
  primes of ``M N0``: ``v -> v phi(gamma)``.
* ``<d>[x] = [x delta_d]``, ``delta_d = diag(1, d)`` at ``p``: ``v -> d^{-1} v`` mod ``p^a``; ``<d>_M``: the same at the
  primes of ``M`` (``v -> d^{-1} v`` mod ``M``), so ``<p>_M = diamond_M(p mod M)`` in the convention of
  ``results/s04/H6_sign.json`` (sign ``+1``: ``U_p^T = <p>_M U'_p``).
* ``Delta_s = (1 + pZ)/(1 + p^s Z)``, generator ``<1 + p>`` of order ``p^{s-1}``; acts on ``X_s`` and ``X'_s``.
* ``pi_*: Z[X_{s+1}] -> Z[X_s]``, ``pi'_*: Z[X'_s] -> Z[X_s]``, ``pi''_*: Z[X_{s+1}] -> Z[X'_s]`` (reduce ``v``);
  ``pi_* = pi'_* pi''_*``.

``h(D) > 1`` (e.g. ``B_11``, ``B_23``) is not implemented (would need the class transport at ``p`` of
:mod:`langlandscape.tree`).
"""

from __future__ import annotations

from functools import lru_cache
from math import gcd

import numpy as np

from .. import levels
from ..padic import _inv, mat_adj, mat_det, mat_mul
from . import proj


def _k_from_v(v, q: int, p: int):
    v1, v2 = v[0] % q, v[1] % q
    r = [_inv(v2, q), 0] if v2 % p else [0, (-_inv(v1, q)) % q]
    return mat_adj([r, [v1, v2]], q)  # inverse of [[r], [v]] (det 1)


def _v_of(y, q: int, p: int):
    d = mat_det(y, q)
    assert d % p
    di = _inv(d, q)
    return ((-y[1][0]) * di % q, y[0][0] * di % q)


def _rowmul(v, g, Q):
    a, b, c, d = g
    return ((v[0] * a + v[1] * c) % Q, (v[0] * b + v[1] * d) % Q)


@lru_cache(maxsize=None)
def norm_p_classes(D: int, p: int) -> tuple:
    """Representatives of ``{gamma in O : Nrd gamma = p} / O^x`` (right multiplication), order coordinates."""
    from ..pari import get_pari

    cd = levels.class_data(D)
    pari = get_pari()
    G = cd.B.gram(cd.orders[0])
    vecs = pari.qfminim(G, 2 * p, 10**6, 0)[2]
    els = []
    for t in range(int(pari.matsize(vecs)[1])):
        v = [int(vecs[r, t]) for r in range(4)]
        if sum(v[i] * int(G[i, j]) * v[j] for i in range(4) for j in range(4)) == 2 * p:
            els += [tuple(v), tuple(-c for c in v)]
    units = cd.units(0)
    seen, reps = set(), []
    for g in sorted(els):
        if g in seen:
            continue
        orb = {tuple(cd.mul(0, list(g), u)) for u in units}
        assert len(orb) == len(units)
        seen |= orb
        reps.append(g)
    assert len(reps) == p + 1
    return tuple(reps)


class Level:
    """Points of ``X_s`` (``prime=False``) or ``X'_s`` (``prime=True``)."""

    def __init__(self, T: "Tower", s: int, prime: bool):
        self.T, self.s, self.prime = T, s, prime
        p, M, N0 = T.p, T.M, T.N0
        self.a = s + 1 if prime else s           # p-adic depth of v
        self.qa = p**self.a
        self.Nf, self.Nv = M * self.qa, M * p**s
        Nf = self.Nf
        cd = T.cd
        umats = sorted({(cd.phi(0, u, Nf), cd.phi(0, u, N0)) for u in T.units})
        assert len(umats) == len(T.units)
        scal = [1 + self.Nv * t for t in range(Nf // self.Nv)]
        L = levels.lines(N0) if N0 > 1 else [()]
        self.points, self.index = [], {}
        for a_ in range(Nf):
            for b_ in range(Nf):
                if gcd(gcd(a_, b_), Nf) != 1:
                    continue
                for l in L:
                    if ((a_, b_), l) in self.index:
                        continue
                    orb = set()
                    for g1, g0 in umats:
                        w = _rowmul((a_, b_), g1, Nf)
                        l2 = levels.canon_line(_rowmul(l, g0, N0), N0) if N0 > 1 else ()
                        for lam in scal:
                            orb.add((((lam * w[0]) % Nf, (lam * w[1]) % Nf), l2))
                    assert len(orb) == len(umats) * len(scal), "non-trivial stabiliser"
                    idx = len(self.points)
                    self.points.append(min(orb))
                    for z in orb:
                        self.index[z] = idx
        self.n = len(self.points)

    def __len__(self):
        return self.n

    def idx(self, v, l=()) -> int:
        return self.index[((v[0] % self.Nf, v[1] % self.Nf), l)]

    # -- [x g] for g at p with det g in p Z_p^x ----------------------------------------------------------------
    @property
    def _gam(self):
        if not hasattr(self, "_gcache"):
            T, prec = self.T, self.T.p ** (self.a + 2)
            self._gcache = []
            for g in T.gammas:
                a, b, c, d = T.cd.phi(0, list(g), prec)
                Gp = [[a, b], [c, d]]
                self._gcache.append((mat_adj(Gp, prec), T.cd.phi(0, list(g), T.M), T.cd.phi(0, list(g), T.N0)))
        return self._gcache

    def translate(self, c: int, g) -> int:
        T, p = self.T, self.T.p
        prec = p ** (self.a + 2)
        (v, l) = self.points[c]
        k = _k_from_v((v[0] % self.qa, v[1] % self.qa), prec, p)
        kg = mat_mul(k, [[x % prec for x in r] for r in g], prec)
        hits = []
        for adjG, GM, G0 in self._gam:
            z = mat_mul(adjG, kg, prec)  # = p iota(gamma)^{-1} k g
            if all(x % p == 0 for r in z for x in r):
                hits.append(([[(x // p) % (prec // p) for x in r] for r in z], GM, G0))
        assert len(hits) == 1, f"expected one gamma, got {len(hits)}"
        y, GM, G0 = hits[0]
        vp = _v_of(y, self.qa, p)
        if T.M > 1:
            vM = _rowmul(v, GM, T.M)
            vp = tuple(levels._crt([(vp[i], self.qa), (vM[i], T.M)]) for i in range(2))
        l2 = levels.canon_line(_rowmul(l, G0, T.N0), T.N0) if T.N0 > 1 else ()
        return self.idx(vp, l2)

    def operator(self, mats) -> np.ndarray:
        Mat = np.zeros((self.n, self.n), dtype=np.int64)
        for c in range(self.n):
            for g in mats:
                Mat[self.translate(c, g), c] += 1
        return Mat

    def scale(self, u: int) -> np.ndarray:
        """``[(v, l)] -> [(u v, l)]`` for a unit ``u`` mod ``Nf``."""
        Mat = np.zeros((self.n, self.n), dtype=np.int64)
        for c, (v, l) in enumerate(self.points):
            Mat[self.idx((u * v[0], u * v[1]), l), c] = 1
        return Mat


class Tower:
    """The tower ``X_s``, ``X'_s`` for ``(D, p, M, N0)``; levels are built lazily and cached."""

    def __init__(self, D: int, p: int, M: int = 1, N0: int = 1):
        assert gcd(p, D * M * N0) == 1 and gcd(M * N0, D) == 1 and gcd(M, N0) == 1 and p >= 5
        self.D, self.p, self.M, self.N0 = D, p, M, N0
        self.cd = levels.class_data(D)
        if self.cd.h != 1:
            raise NotImplementedError("S04-C1 tower: only class number one (h(D) = 1)")
        self.units = self.cd.units(0)
        self.gammas = norm_p_classes(D, p)
        self._lv: dict = {}

    def level(self, s: int, prime: bool = False) -> Level:
        key = (s, prime)
        if key not in self._lv:
            self._lv[key] = Level(self, s, prime)
        return self._lv[key]

    def X(self, s: int) -> Level:
        return self.level(s, False)

    def Xp(self, s: int) -> Level:
        return self.level(s, True)

    # -- Hecke operators at p ---------------------------------------------------------------------------------
    def Up(self, s: int, prime: bool = False) -> np.ndarray:
        """``U_p = N_{U_p}`` on ``Z[X_s]`` (or ``Z[X'_s]``)."""
        p = self.p
        return self.level(s, prime).operator([[[p, j], [0, 1]] for j in range(p)])

    def Up_prime(self, s: int) -> np.ndarray:
        """``U'_p`` on ``Z[X_s]``: representatives ``[[1, 0], [p^s j, p]]``."""
        p = self.p
        return self.X(s).operator([[[1, 0], [p**s * j, p]] for j in range(p)])

    # -- diamonds ---------------------------------------------------------------------------------------------
    def _unit(self, lv: Level, at_p: int, at_M: int) -> int:
        return levels._crt([(at_p % lv.qa, lv.qa), (at_M % self.M, self.M)]) if self.M > 1 else at_p % lv.qa

    def diamond(self, s: int, d: int, prime: bool = False) -> np.ndarray:
        """``<d>``, ``d in (Z/p^s)^x``: ``v -> d^{-1} v`` mod ``p^a``, identity mod ``M``."""
        lv = self.level(s, prime)
        return lv.scale(self._unit(lv, pow(d, -1, lv.qa), 1))

    def diamond_M(self, s: int, d: int, prime: bool = False) -> np.ndarray:
        """``<d>_M``, ``d in (Z/M)^x``: ``v -> d^{-1} v`` mod ``M``, identity mod ``p^a``."""
        lv = self.level(s, prime)
        return lv.scale(self._unit(lv, 1, pow(d, -1, self.M)))

    def p_M(self, s: int, prime: bool = False) -> np.ndarray:
        """``<p>_M`` (lem:s01-Up(d), sign of results/s04/H6_sign.json): ``U_p^T = <p>_M U'_p``."""
        return self.diamond_M(s, self.p % self.M, prime) if self.M > 1 else np.eye(len(self.level(s, prime)), dtype=np.int64)

    def delta_gen(self, s: int, prime: bool = False) -> np.ndarray:
        """Generator ``<1 + p>`` of ``Delta_s`` (order ``p^{s-1}``)."""
        return self.diamond(s, 1 + self.p, prime)

    def delta_order(self, s: int) -> int:
        return self.p ** (s - 1)

    def delta_orbits(self, s: int, prime: bool = False) -> list[list[int]]:
        return proj.orbits([proj.perm_of(self.delta_gen(s, prime))], len(self.level(s, prime)))

    # -- projections ------------------------------------------------------------------------------------------
    def _push(self, src: Level, dst: Level) -> np.ndarray:
        Mat = np.zeros((dst.n, src.n), dtype=np.int64)
        for c, (v, l) in enumerate(src.points):
            Mat[dst.idx(v, l), c] += 1
        return Mat

    def pi_push(self, s: int) -> np.ndarray:
        """``pi_*: Z[X_{s+1}] -> Z[X_s]``."""
        return self._push(self.X(s + 1), self.X(s))

    def pi_prime_push(self, s: int) -> np.ndarray:
        """``pi'_*: Z[X'_s] -> Z[X_s]``."""
        return self._push(self.Xp(s), self.X(s))

    def pi_dprime_push(self, s: int) -> np.ndarray:
        """``pi''_*: Z[X_{s+1}] -> Z[X'_s]``."""
        return self._push(self.X(s + 1), self.Xp(s))

    # -- ordinary parts ---------------------------------------------------------------------------------------
    def e(self, s: int, m: int, prime: bool = False) -> proj.Projector:
        """``e = e_{U_p}`` on ``Z/p^m[X_s]`` (or ``[X'_s]``)."""
        return proj.ordinary_projector(self.Up(s, prime), self.p, m)

    def ordinary_delta_rank(self, s: int, m: int = 1, prime: bool = False) -> dict:
        """Freeness and rank of ``e Z/p^m[X_s]`` over ``Z/p^m[Delta_s]``."""
        return proj.group_ring_rank(self.e(s, m, prime), self.delta_gen(s, prime), self.delta_order(s))


@lru_cache(maxsize=None)
def tower(D: int, p: int, M: int = 1, N0: int = 1) -> Tower:
    return Tower(D, p, M, N0)
