# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S03-C2 (test T1): Mazur check and Eisenstein property of Phi^comb for the DR graph of B_q at ``O^_^x``.

Tex: ``ex:s03-mazur``, ``prop:s03-mazur``, ``def:s03-DR``, ``prop:s03-phieis`` (``mathematics/chapters/s03``).

Conventions: classes from :func:`langlandscape.brandt.module` (D = q, M = 1); ``w_x = |Gamma_x| / 2`` (``|Gamma_x|``
includes -1; ``w_e = |Gamma_e / {+-1}|`` of def:s03-DR).  Brandt matrix ``B = T_l`` has row sums ``l+1`` and
``w_c' B[c][c'] = w_c B[c'][c]``.  On ``Z[E]`` the operator is ``x -> B^T x`` (``e_c -> sum_c' B[c][c'] e_c'``); it
preserves ``X = Z[E]^0`` and is self-adjoint for the weighted pairing ``<e,e'> = w_e delta``.  ``X^v = Hom(X, Z)
= Z^E / Z*1`` (restriction of functions), ``X -> X^v`` is ``x -> W x``, and the induced action on ``X^v`` is
``f -> B f`` (well defined as ``B 1 = (l+1) 1``).  *Eisenstein check* (prop:s03-phieis): ``(B - (l+1)) X^v``
lies in the image of ``X``, i.e. ``T_l`` acts on ``Phi^comb = X^v / X`` as ``1 + l``.
"""

from __future__ import annotations

from fractions import Fraction
from math import gcd

from .. import brandt, pari as _pari, results
from . import graphs

QS = (11, 23, 37, 101, 131)
ELLS = (2, 3, 5, 7, 11, 13)
EXPECTED = {11: (2, 5), 23: (3, 11), 37: (3, 3), 101: (9, 25), 131: (12, 65)}


def eisenstein_check(B: list, w: list, ell: int) -> bool:
    """``(B-(l+1)) Z^E  subset  W*X + Z*1`` (see module docstring); B = Brandt matrix of l, w = weights."""
    h = len(w)
    if h == 1:
        return True
    pari = _pari.get_pari()
    G = graphs.two_vertex(w)
    basis = graphs.X_basis(G)  # h-1 vectors in Z^h
    cols = [[w[e] * b[e] for e in range(h)] for b in basis] + [[1] * h]
    L = pari.matrix(h, h, [cols[j][i] for i in range(h) for j in range(h)])
    A = [[B[i][j] - (ell + 1) * (i == j) for j in range(h)] for i in range(h)]
    R = pari.matrix(h, h, [A[i][j] for i in range(h) for j in range(h)])
    Y = pari.matsolve(L, R)
    return all(int(pari.denominator(Y[i, j])) == 1 for i in range(h) for j in range(h))


def num_fraction(q: int) -> int:
    return (q - 1) // gcd(q - 1, 12)


def t1_row(q: int, ells=ELLS) -> dict:
    m = brandt.module(q, 1)
    gam = list(m.gammas)
    assert all(g % 2 == 0 for g in gam)
    w = [g // 2 for g in gam]
    G = graphs.two_vertex(tuple(w))
    phi = graphs.phi_comb(G)
    mass_w = sum(Fraction(1, x) for x in w)
    eis = {}
    for ell in ells:
        if ell == q:
            continue
        eis[str(ell)] = eisenstein_check(m.T(ell), w, ell)
    return {
        "q": q, "h": m.h, "weights": sorted(w), "gammas": sorted(gam),
        "n2": w.count(2), "n3": w.count(3),
        "mass_w": str(mass_w), "mass_w_ok": mass_w == Fraction(q - 1, 12),
        "mass_gamma_ok": m.mass == Fraction(q - 1, 24),
        "phi_order": phi["order"], "phi_divisors": phi["divisors"], "phi_cyclic": phi["cyclic"],
        "num_q_minus_1_over_12": num_fraction(q), "phi_order_ok": phi["order"] == num_fraction(q),
        "eisenstein": eis, "eisenstein_all": all(eis.values()),
    }


def compute_all() -> dict:
    return {str(q): t1_row(q) for q in QS}


def main() -> None:
    with results.Timer() as t:
        data = compute_all()
    results.write(
        "s03/T1.json", data, script="code/python/langlandscape/ribet/mazur.py",
        params={"q": list(QS), "ells": list(ELLS), "w": "|Gamma_x|/2", "level": "O^_^x (M=1)"},
        runtime_s=t.seconds,
        notes="Eisenstein check: (T_l-(1+l)) X^v subset im(X) for l != q, l <= 13 (X^v = Z^E/Z1, X -> W x, T_l acts as B)",
    )
    for q, r in data.items():
        print(q, r["h"], r["weights"], r["phi_order"], r["phi_cyclic"], r["eisenstein_all"])


if __name__ == "__main__":
    main()
