# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C1: linear algebra over ``Z/p^m`` for the ordinary projector (def:s04-e) and group-ring freeness.

* :func:`ordinary_projector` -- ``e = e_T`` of an endomorphism ``T`` of ``(Z/p^m)^n`` by *image stabilisation*
  (Fitting): ``A = T^k`` with ``k = 1, 2, 4, ...`` until ``M = im A (+) ker A`` with ``im A`` free; then
  ``e = A_J (C A_J)^{-1} C`` where ``A_J`` = columns of ``A`` independent mod ``p`` (a basis of ``im A``) and
  ``A = A_J C``.  This is the projection onto ``im A`` along ``ker A = ker C``; by Fitting's lemma (def:s04-e, Step 2)
  ``T`` is invertible on ``im A`` and nilpotent on ``ker A``, so it is ``e_T mod p^m``.  It is the reduction mod
  ``p^m`` of ``e_T`` on the ``Z_p``-lattice (def:s04-e, Step 3: the ``e_m`` are compatible).
* :func:`group_ring_rank` -- for a ``Z/p^m[Delta]``-module ``eM`` (``Delta`` cyclic of ``p``-power order, generator
  acting by ``D``; ``Z/p^m[Delta]`` is local, prop:s04-freeA): number of generators
  ``g = dim_{F_p} eM/(p, D - 1) = r - rk_p((D - 1) A_J)`` (Nakayama), free iff ``r = g |Delta|`` (both sides are free
  ``Z/p^m``-modules, compare cardinalities), and then ``rk_{Z/p^m[Delta]} eM = g``.
* :func:`orbits` -- orbits of a permutation group given by generator permutations.

Matrices are numpy ``int64`` arrays with entries in ``[0, q)``; products use exact float64 BLAS when
``n (q-1)^2 < 2^53`` (else an exact split product).
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

_EXACT = 2**53


def mod(A, q: int) -> np.ndarray:
    return np.asarray(A, dtype=np.int64) % q


def mul(A, B, q: int) -> np.ndarray:
    """``A B mod q`` (exact)."""
    A, B = mod(A, q), mod(B, q)
    k = A.shape[1]
    if k * (q - 1) ** 2 < _EXACT:
        return np.rint(A.astype(np.float64) @ B.astype(np.float64)).astype(np.int64) % q
    b = int(np.ceil(np.sqrt(q)))
    assert k * (b - 1) ** 2 < _EXACT and q * b < 2**62, "modulus too large for the split product"
    A1, A0 = np.divmod(A, b)
    B1, B0 = np.divmod(B, b)
    f = lambda X, Y: np.rint(X.astype(np.float64) @ Y.astype(np.float64)).astype(np.int64) % q
    bb = (b * b) % q
    hi = f(A1, B1) * bb % q
    mid = (f(A1, B0) + f(A0, B1)) % q * b % q
    return (hi + mid + f(A0, B0)) % q


def power(T, k: int, q: int) -> np.ndarray:
    n = T.shape[0]
    R, X = np.eye(n, dtype=np.int64) % q, mod(T, q)
    while k:
        if k & 1:
            R = mul(R, X, q)
        k >>= 1
        if k:
            X = mul(X, X, q)
    return R


def pivots_mod_p(A, p: int):
    """Rows ``I`` and columns ``J`` with ``A[I, J]`` invertible mod ``p``, ``|I| = |J| = rk_{F_p} A`` (full pivoting;
    cost ``O(rank * size)``)."""
    W = mod(A, p).copy()
    I, J = [], []
    while True:
        nz = np.flatnonzero(W)
        if not len(nz):
            return I, J
        i, j = divmod(int(nz[0]), W.shape[1])
        I.append(i)
        J.append(j)
        f = W[:, j] * pow(int(W[i, j]), -1, p) % p
        W = (W - np.outer(f, W[i, :])) % p


def rank_mod_p(A, p: int) -> int:
    return len(pivots_mod_p(A, p)[1])


def inv(A, p: int, m: int) -> np.ndarray:
    """Inverse mod ``p^m`` of a square matrix invertible mod ``p`` (Gauss--Jordan with unit pivots)."""
    q = p**m
    A = mod(A, q)
    n = A.shape[0]
    W = np.concatenate([A, np.eye(n, dtype=np.int64)], axis=1)
    for c in range(n):
        piv = next((r for r in range(c, n) if W[r, c] % p), None)
        if piv is None:
            raise ValueError("matrix not invertible mod p")
        W[[c, piv]] = W[[piv, c]]
        W[c] = W[c] * pow(int(W[c, c]), -1, q) % q
        f = W[:, c].copy()
        f[c] = 0
        W = (W - np.outer(f, W[c]) % q) % q
    return W[:, n:]


def is_invertible_mod_p(A, p: int) -> bool:
    A = np.asarray(A)
    return A.shape[0] == A.shape[1] and rank_mod_p(A, p) == A.shape[0]


@dataclass
class Projector:
    """``e = e_T`` mod ``q = p^m``: ``e = basis @ coord`` with ``coord @ basis = id_r``; ``k`` = exponent with
    ``im T^k = eM``, ``ker T^k = (1 - e)M``."""

    e: np.ndarray
    basis: np.ndarray   # n x r, a Z/p^m-basis of eM (columns of T^k)
    coord: np.ndarray   # r x n, coordinates of e x in ``basis``
    rank: int           # rk_{Z/p^m} eM
    k: int
    p: int
    m: int

    @property
    def q(self) -> int:
        return self.p**self.m


def ordinary_projector(T, p: int, m: int, max_doublings: int = 40) -> Projector:
    """``e_T`` on ``(Z/p^m)^n`` by image stabilisation (see module docstring)."""
    q = p**m
    A = mod(T, q)
    n = A.shape[0]
    k = 1
    t = min(n, 64)
    sketch = np.random.default_rng(0).integers(0, p, size=(n, t))
    for _ in range(max_doublings):
        # Cheap skip: while rk_p(A sketch) = t the ordinary part may still be swamped by the nilpotent part; the full
        # (O(rank n^2)) pivot search runs once that rank drops below t, or from k >= n on (mod-p nilpotence index <= n).
        if t == n or k >= n or rank_mod_p(mul(A, sketch, p), p) < t:
            I, J = pivots_mod_p(A, p)
        else:
            A = mul(A, A, q)
            k *= 2
            continue
        r = len(J)
        if r == 0:  # A = 0 mod p: eM/p = 0, so eM = 0 (Nakayama)
            z = np.zeros((n, 0), dtype=np.int64)
            return Projector(np.zeros((n, n), dtype=np.int64), z, z.T.copy(), 0, k, p, m)
        AJ = A[:, J]
        C = mul(inv(A[np.ix_(I, J)], p, m), A[I, :], q)
        if (mul(AJ, C, q) == A).all():
            R = mul(C, AJ, q)
            if is_invertible_mod_p(R, p):
                coord = mul(inv(R, p, m), C, q)
                return Projector(mul(AJ, coord, q), AJ, coord, r, k, p, m)
        A = mul(A, A, q)
        k *= 2
    raise RuntimeError("image of T^k did not stabilise")


def ordinary_rank(T, p: int, m: int = 1) -> int:
    """``rk_{Z_p} e_T M`` (= ``rk`` mod ``p``; ``m = 1`` suffices)."""
    return ordinary_projector(T, p, m).rank


def restrict(P: Projector, T) -> np.ndarray:
    """Matrix (``r x r``) of an endomorphism ``T`` commuting with ``e`` on ``eM`` in the basis ``P.basis``."""
    return mul(P.coord, mul(T, P.basis, P.q), P.q)


def group_ring_rank(P: Projector, D_gen, order: int) -> dict:
    """Freeness of ``eM`` over ``Z/p^m[Delta]``, ``Delta`` cyclic of ``p``-power ``order`` generated by ``D_gen``."""
    p = P.p
    n = P.e.shape[0]
    if P.rank == 0:
        return {"rank_Zp": 0, "generators": 0, "order": order, "free": True, "rank": 0}
    B = mul(mod(D_gen, p) - np.eye(n, dtype=np.int64), P.basis % p, p)
    g = P.rank - rank_mod_p(B, p)
    free = P.rank == g * order
    return {"rank_Zp": P.rank, "generators": g, "order": order, "free": free, "rank": g if free else None}


def orbits(perms, n: int) -> list[list[int]]:
    """Orbits of the group generated by the permutations ``perms`` (lists ``i -> perm[i]``) on ``range(n)``."""
    seen = [False] * n
    out = []
    for i in range(n):
        if seen[i]:
            continue
        orb, stack = [i], [i]
        seen[i] = True
        while stack:
            j = stack.pop()
            for g in perms:
                t = g[j]
                if not seen[t]:
                    seen[t] = True
                    orb.append(t)
                    stack.append(t)
        out.append(sorted(orb))
    return out


def perm_of(Mat) -> list[int]:
    """The permutation ``c -> t`` of a 0/1 permutation matrix with columns = images."""
    Mat = np.asarray(Mat)
    assert (Mat.sum(axis=0) == 1).all() and (Mat.sum(axis=1) == 1).all()
    return [int(np.flatnonzero(Mat[:, c])[0]) for c in range(Mat.shape[1])]
