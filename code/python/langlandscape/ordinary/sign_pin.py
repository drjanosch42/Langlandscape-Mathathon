# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C3a: pin the sign in ``U_p^* = <p>_M U'_p`` (lem:s01-Up(d)) on ``S_1 = X_B(U_1(M p))``.

Example: ``D = 2`` (Hurwitz order, ``h = 1``), ``M = 7``, ``p = 5``, ``s = 1``.  (``M = 1`` gives no information:
``<p>_M`` is trivial, and for ``M = 3`` it is an involution so the sign is invisible; ``up.py`` only treats ``D = 3, M = 1``.  Same conventions as ``langlandscape.up``, with an
extra prime ``7`` in the level.)

Points.  ``h = 1``, ``S_s = O^x \\ (GL_2(Z_7) x GL_2(Z_5)) / U_1(7 5^s)``; ``k -> v(k) = e_2 k^{-1}`` mod ``N = 7 5^s``,
primitive row vectors modulo ``phi(O^x)`` acting on the right (``v -> v phi(gamma)^{-1}``).
Homological operators, columns = images (``M[t, c]`` = coefficient of ``[x_t]`` in ``T[x_c]``).
* ``U_p[x] = sum_j [x varpi_j]``, ``varpi_j = diag-type [[5, j], [0, 1]]`` at ``5``.
* ``U'_p[x] = sum_j [x [[1, 0], [5^s j, 5]]]`` at ``5``.
* ``<d>[x] = [x delta_d]``, ``delta_d = diag(1, d)`` at the primes dividing ``M`` (1 elsewhere): ``v -> d^{-1} v`` mod ``M``
  (identity mod ``p^s``).  ``<p>_M := <d>`` with ``d = p mod M``, ``d = 1 mod p^s`` (lem:s01-Up(d)).
* Brandt pairing ``<[x],[y]> = w_x delta_{xy}`` with ``w_x = 1`` (``Gamma_x`` trivial at ``s >= 1``), so ``T^* = T^T``.
"""

from __future__ import annotations

import sys
from math import gcd

import numpy as np

from .. import levels, results
from ..padic import mat_adj, mat_det, mat_mul, _inv

D, M, P, S = 2, 7, 5, 1


def _classes_norm_p(cd):
    """Representatives of ``{gamma in O : Nrd gamma = P} / O^x`` (right multiplication)."""
    from ..pari import get_pari

    pari = get_pari()
    G = cd.B.gram(cd.orders[0])
    res = pari.qfminim(G, 2 * P, 10**6, 0)
    vecs = res[2]
    els = []
    for t in range(int(pari.matsize(vecs)[1])):
        v = [int(vecs[r, t]) for r in range(4)]
        n = sum(v[i] * G[i][j] * v[j] for i in range(4) for j in range(4)) // 2
        if n == P:
            els += [v, [-c for c in v]]
    units = cd.units(0)
    seen, reps = set(), []
    for g in sorted(map(tuple, els)):
        if g in seen:
            continue
        orb = {tuple(cd.mul(0, list(g), u)) for u in units}
        assert len(orb) == len(units)
        seen |= orb
        reps.append(list(g))
    return reps


def _k_from_v(v, mod, ell):
    v1, v2 = v[0] % mod, v[1] % mod
    r = [_inv(v2, mod), 0] if v2 % ell else [0, (-_inv(v1, mod)) % mod]
    return mat_adj([r, [v1, v2]], mod)


def _v_of(y, q, ell):
    d = mat_det(y, q)
    assert d % ell
    di = _inv(d, q)
    return ((-y[1][0]) * di % q, y[0][0] * di % q)


class Setting:
    def __init__(self, s: int = S):
        self.s = s
        self.cd = levels.class_data(D)
        self.X = levels.XB(D, M * P**s, 1)
        assert len(self.X.orbits) == 1 and all(o["stab"] == 1 for o in self.X.orbits[0])
        self.n = len(self.X)
        self.q5 = P**s
        self.N = M * self.q5
        self.prec5 = P ** (s + 2)
        self.gam = _classes_norm_p(self.cd)
        self.g5 = [self._mat(g, self.prec5) for g in self.gam]
        self.g3 = [self._mat(g, M) for g in self.gam]

    def _mat(self, u, Q):
        a, b, c, d = self.cd.phi(0, u, Q)
        return [[a, b], [c, d]]

    def _crt(self, v3, v5):
        out = []
        for a, b in zip(v3, v5):
            out.append(next(x for x in range(self.N) if x % M == a % M and x % self.q5 == b % self.q5))
        return tuple(out)

    def _idx(self, v):
        return self.X.orbit_of[0][(tuple(c % self.N for c in v), ())]

    def points(self):
        reps = {}
        for k in range(self.n):
            reps[k] = self.X.orbits[0][k]["rep"][0]
        return reps

    def translate(self, v, g5):
        """Index of ``[x g]``, ``x = (k_3, k_5)`` with ``v(x) = v``, ``g`` at ``5`` of determinant in ``5 Z_5^x``."""
        m5 = self.prec5
        k5 = _k_from_v(v, m5, P)
        k3 = _k_from_v(v, M, M)
        kg = mat_mul(k5, [[c % m5 for c in r] for r in g5], m5)
        hits = []
        for G5, G3 in zip(self.g5, self.g3):
            z = mat_mul(mat_adj(G5, m5), kg, m5)  # = 5 iota(gamma)^{-1} k g
            if all(c % P == 0 for r in z for c in r):
                y5 = [[(c // P) % (m5 // P) for c in r] for r in z]
                z3 = mat_mul(mat_adj(G3, M), k3, M)
                y3 = [[(c * _inv(P, M)) % M for c in r] for r in z3]  # y_3 = phi_3(gamma)^{-1} k_3
                hits.append((y3, y5))
        assert len(hits) == 1
        y3, y5 = hits[0]
        return self._idx(self._crt(_v_of(y3, M, M), _v_of(y5, self.q5, P)))

    def operator(self, mats):
        M_ = np.zeros((self.n, self.n), dtype=np.int64)
        pts = self.points()
        for c in range(self.n):
            for g in mats:
                M_[self.translate(pts[c], g), c] += 1
        return M_

    def Up(self):
        return self.operator([[[P, j], [0, 1]] for j in range(P)])

    def Up_prime(self):
        return self.operator([[[1, 0], [P**self.s * j, P]] for j in range(P)])

    def diamond(self, d: int):
        """Homological ``<d>``: ``[x] -> [x delta_d]``, ``delta_d = diag(1, d)`` at ``M``, ``v -> d^{-1} v`` mod ``M``."""
        u = self._crt([pow(d, -1, M) * c for c in (1, 1)], [1, 1])[0]  # u = d^-1 mod M, 1 mod 5^s
        D_ = np.zeros((self.n, self.n), dtype=np.int64)
        for c, v in self.points().items():
            D_[self._idx(((u * v[0]) % self.N, (u * v[1]) % self.N)), c] += 1
        return D_


def run(write: bool = True) -> dict:
    with results.Timer() as tm:
        C = Setting()
        n = C.n
        U, Up, Dp = C.Up(), C.Up_prime(), C.diamond(P % M)  # <p>_M : d = p mod M
        Dm = C.diamond(pow(P, -1, M))  # <p>_M^{-1}
        assert (Dp @ Dm == np.eye(n, dtype=np.int64)).all()
        assert (U.sum(axis=0) == P).all() and (Up.sum(axis=0) == P).all()
        Ustar = U.T  # adjoint for <[x],[y]> = delta_{xy} (w_x = 1)
        mod = P**3
        plus = bool(((Ustar - Dp @ Up) % mod == 0).all())
        minus = bool(((Ustar - Dm @ Up) % mod == 0).all())
        plus_exact = bool((Ustar == Dp @ Up).all())
        minus_exact = bool((Ustar == Dm @ Up).all())
        assert Dp.tolist() != np.eye(n).tolist()  # nontrivial diamond: the test is informative
    assert plus != minus, "exactly one sign must hold"
    sign = "+1" if plus else "-1"
    data = {
        "sign": sign,
        "sign_meaning": '"+1": U_p^* = <p>_M U\'_p; "-1": U_p^* = <p>_M^{-1} U\'_p',
        "convention": (
            "<d>[x] = [x delta_d] (homological, adelic; T_delta with delta U delta^-1 = U), delta_{d,l} = diag(1,d) at l | M, 1 "
            "elsewhere; on X_B(U_1(M p^s)) = primitive row vectors v = e_2 k^-1 mod M p^s mod phi(O^x) it acts by "
            "v -> d^{-1} v mod M, identity mod p^s. <p>_M := <d> with d = p mod M, d = 1 mod p^s (lem:s01-Up(d)), "
            "i.e. v -> p^{-1} v mod M. Lean: diamondM with d := the unit of Z/(M p^s) with d = p mod M, 1 mod p^s, in the "
            "same one-prime diamond convention (right translation by diag(1,d)); exponent as in `sign`."),
        "example": {"D": D, "B": "Hurwitz quaternions (-1,-1)_Q", "M": M, "p": P, "s": S, "level": "U_1(M p^s) = U_1(35)",
                    "S_1_size": n, "Gamma_x": "trivial for all x", "w_x": 1},
        "checks": {"U_p_star_eq_<p>_M_U'_p_mod_5^3": plus, "U_p_star_eq_<p>_M^-1_U'_p_mod_5^3": minus,
                   "plus_exact_integer": plus_exact, "minus_exact_integer": minus_exact,
                   "<p>_M_nontrivial": True, "<p>_M_has_order": int(next(k for k in range(1, 20) if (np.linalg.matrix_power(Dp, k) == np.eye(n, dtype=np.int64)).all()))},
        "matrices": {"U_p": U.tolist(), "U_p_prime": Up.tolist(), "diamond_p_M": Dp.tolist()},
    }
    if write:
        results.write("s04/H6_sign.json", data, script="code/python/langlandscape/ordinary/sign_pin.py "
                      "(cd code/python && python -m langlandscape.ordinary.sign_pin)",
                      params={"D": D, "M": M, "p": P, "s": S}, runtime_s=round(tm.seconds, 3),
                      notes="S04-C3a: sign of <p>_M in U_p^* = <p>_M U'_p, exact mod 5^3")
    return data


if __name__ == "__main__":
    d = run()
    print(d["sign"], d["checks"])
