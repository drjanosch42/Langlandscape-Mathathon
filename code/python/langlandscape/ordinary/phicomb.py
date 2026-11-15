# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C5 (H7): ``Phi^comb`` of the DR graph of ``B_q`` at level ``U_1(p^s)`` with the ``U_p``-action, any class number.

Tex: ``lem:s04-ekills`` (c).  Level ``S_s = X_B(U_1(p^s))`` (``M = 1``), ``B = B_q`` definite of discriminant ``q``.

*Class transport at p* (the lattice model of :mod:`langlandscape.tree`): a point is ``(c, v)`` with ``v`` a primitive
vector of ``e_0 I_c / p^s`` (``psi_c`` coordinates).  For ``y = x_c h``, ``v = e_2 h^{-1}`` and ``g = varpi_j = [[p, j],
[0, 1]]``: ``L_{yg} = L_y + O p^{-1} u`` with ``u`` lifting the line ``<(1, -j) h^{-1}>`` of ``F_p^2``; as ``j`` runs
over ``0..p-1`` these are exactly the ``p`` lines **different from** ``<v mod p>``.  Row 2 of ``g^{-1}`` is ``(0, 1)``,
so the level datum is the *same* vector ``v``, now in the lattice ``L_{yg} = I_{c'} g'`` (``g' = gamma'/p``), i.e.
``[y g] = (c', psi_{c'}(w g'^{-1}))`` for ``w in I_c`` with ``psi_c(w) = v``.  Hence

    U_p (c, v) = sum_{lines lam != <v mod p>}  (c'(lam), v G_lam),     (homological, columns = images)

``G_lam`` the 2x2 matrix mod ``p^s`` of ``w -> psi_{c'}(w g'^{-1})`` (cached per ``(c, lam)``).

``Phi^comb`` of ``G_DR`` (two vertices, one edge per point of ``S_s``, all weights 1 by (N1)) is ``Z/|S_s|`` via
``sigma = sum`` on ``Z^E / (X + Z 1)``; the action ``phi -> phi o U_p^*`` on ``X^v = Z^E/Z 1`` is ``f -> A f``
(``A`` the homological matrix; ``phi_f(x) = <f, x>``, ``<f, A^T x> = <A f, x>``).
"""

from __future__ import annotations

from math import gcd

import numpy as np

from .. import levels
from ..levels import canon_line, class_data
from ..quat import Lattice
from ..ribet import graphs
from ..tree import _find_gamma, _index, _inv_elt, _local
from . import proj


class PTower:
    """``S_s = X_B(U_1(p^s))``, ``s = 1..smax``, with ``U_p`` and projections (any class number; ``p`` not dividing ``D``)."""

    def __init__(self, D: int, p: int, smax: int):
        assert D % p and p > 2
        self.D, self.p, self.smax = D, p, smax
        self.loc = _local(D)
        self.cd = class_data(D)
        self.X = {s: levels.XB(D, p**s, 1) for s in range(1, smax + 1)}
        self.elts = {s: self.X[s].elements() for s in self.X}
        self.idx = {s: {e: k for k, e in enumerate(self.elts[s])} for s in self.X}
        self._trans: dict = {}
        for s in self.X:
            assert all(o["stab"] == 1 for orbs in self.X[s].orbits for o in orbs), "non-trivial stabiliser (N1)"

    def size(self, s: int) -> int:
        return len(self.elts[s])

    def transport(self, c: int, lam: tuple):
        """``(c', g', G)`` with ``L_{y varpi} = I_{c'} g'``, ``G`` = 2x2 matrix mod ``p^smax`` of ``w -> psi_{c'}(w g'^{-1})``."""
        key = (c, lam)
        if key not in self._trans:
            B, loc, p = self.cd.B, self.loc, self.p
            I, N = self.cd.reps[c]
            wq = loc.preimage(c, lam, p)
            v = B.mul(loc.e0(p), wq)
            assert canon_line(loc.psi(c, v, p, 1), p) == lam
            qL = Lattice([tuple(p * x for x in b) for b in I.basis] + [B.mul(o, v) for o in B.O.basis])
            assert _index(I, qL) == p * p
            found = None
            for c2, (J, NJ) in enumerate(self.cd.reps):
                g = _find_gamma(B, J, NJ, qL, N * p)
                if g is not None:
                    found = (c2, g)
                    break
            assert found is not None, "p-neighbour lies in no known class"
            c2, gp = found
            g = tuple(x / p for x in gp)
            ginv = _inv_elt(B, g)
            Q = p**self.smax
            G = [loc.psi_mod(c2, B.mul(loc.preimage(c, r, Q), ginv), Q) for r in ((1, 0), (0, 1))]
            self._trans[key] = (c2, g, G)
        return self._trans[key]

    def Up(self, s: int) -> np.ndarray:
        """Homological ``U_p`` on ``Z[S_s]`` (``M[t, c]`` = coefficient of ``[x_t]`` in ``U_p[x_c]``)."""
        p, X, q = self.p, self.X[s], self.p**s
        n = self.size(s)
        M = np.zeros((n, n), dtype=np.int64)
        for col, (c, i) in enumerate(self.elts[s]):
            (v0, v1), _ = X.orbits[c][i]["rep"]
            for lam in levels.lines(p):
                if (v0 * lam[1] - v1 * lam[0]) % p == 0:  # lam = <v mod p> is excluded
                    continue
                c2, _, G = self.transport(c, lam)
                v2 = ((v0 * G[0][0] + v1 * G[1][0]) % q, (v0 * G[0][1] + v1 * G[1][1]) % q)
                t = self.idx[s][(c2, X.orbit_of[c2][(v2, ())])]
                M[t, col] += 1
        return M

    def projection(self, s: int) -> np.ndarray:
        """``pi_*: Z[S_s] -> Z[S_{s-1}]`` (matrix ``|S_{s-1}| x |S_s|``)."""
        X, Y, q = self.X[s], self.X[s - 1], self.p ** (s - 1)
        P = np.zeros((self.size(s - 1), self.size(s)), dtype=np.int64)
        for col, (c, i) in enumerate(self.elts[s]):
            (v0, v1), _ = X.orbits[c][i]["rep"]
            P[self.idx[s - 1][(c, Y.orbit_of[c][((v0 % q, v1 % q), ())])], col] = 1
        return P


def phicomb(D: int, p: int, s: int, A: np.ndarray) -> dict:
    """``Phi^comb(G_DR(UU_s))`` and the action of ``U_p^*`` on it (``A`` = homological ``U_p``)."""
    n = A.shape[0]
    G = graphs.two_vertex([1] * n)
    ph = graphs.phi_comb(G)
    # sigma = sum : Z^E -> Z/n identifies Z^E/(X + Z1) with Z/n (X = ker sum, sum 1 = n); (f -> A f) induces sigma(Af)
    sig_ok = all(int(A[:, c].sum()) % n == (p * 1) % n for c in range(n))  # sigma(A e_c) = p sigma(e_c) in Z/n
    N = ph["order"]
    mult = {int(A[:, c].sum()) for c in range(n)}
    vp = 0
    m = N
    while m % p == 0:
        m //= p
        vp += 1
    # e on Phi (x) Z_p = Z/p^vp with U_p^* = p: p^k = 0 for k >= vp  => e = lim p^{n!} = 0
    e_zero = (vp == 0) or pow(p, max(vp, 1), p**vp) == 0
    return {
        "order": N, "order_is_size": N == n, "cyclic": ph["cyclic"], "divisors": ph["divisors"], "v_p_order": vp,
        "v_p_size_ge_2s_minus_2": vp >= 2 * s - 2, "col_sums": sorted(mult), "Up_star_acts_as_p": sig_ok and mult == {p},
        "e_zero_on_phi_p": bool(e_zero),
    }


def run_case(D: int, p: int, smax: int) -> dict:
    T = PTower(D, p, smax)
    out = {"D": D, "p": p, "h": T.cd.h, "levels": {}}
    A = {s: T.Up(s) for s in range(1, smax + 1)}
    for s in range(1, smax + 1):
        n = T.size(s)
        r = phicomb(D, p, s, A[s])
        q = p ** min(s + 2, 4)
        ok = proj.ordinary_projector(A[s], p, 1)
        r["size"] = n
        r["ordinary_rank_Zp_XB"] = ok.rank  # rk e Z_p[S_s]
        if s >= 2:
            P = T.projection(s)
            r["Up_commutes_pi"] = bool((P @ A[s] == A[s - 1] @ P).all())
        r["colsum_p"] = bool((A[s].sum(axis=0) == p).all())
        out["levels"][str(s)] = r
    return out


def main() -> None:
    from .. import results

    with results.Timer() as t:
        data = {str(D): run_case(D, 5, 2) for D in (11, 23)}
    results.write(
        "s04/H7.json", data, script="code/python/langlandscape/ordinary/phicomb.py",
        params={"q": [11, 23], "p": 5, "s_max": 2, "command": "python3 -m langlandscape.ordinary.phicomb (cwd code/python)"},
        runtime_s=t.seconds,
        notes="H7: Phi^comb(G_DR(UU_s)) (x) Z_5 = Z/5^{v_5|S_s|}; U_p^* = 5 on it (hence e = 0); U_p commutes with pi_*.",
    )
    print(data)


if __name__ == "__main__":
    main()
