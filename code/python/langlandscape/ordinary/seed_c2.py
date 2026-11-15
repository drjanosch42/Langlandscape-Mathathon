# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C4 (seed C2): ordinary rank of ``Z_p[X_1]`` vs PARI newforms, and the diamond normalisation ``P^ad_k``.

Setting: ``B = B_3`` (definite, ``h = 1``), ``p = 5``, ``M = N0 = 1``; ``X_s = X_B(K_s)``, ``K_s = U_1(5^s)_5``
(:mod:`.tower`).  Classical side (JL, thm:s01-JLclassical / thm:s01-lambdaJL): weight-``k`` forms on
``Gamma_1(5) cap Gamma_0(3)`` that are new at 3, i.e. ``S_k(15, chi)^{3-new}`` for ``chi`` mod 15 trivial at 3
(Conrey labels 1, 4, 7, 13 mod 15) = ``S_k^new(15, chi)`` plus, for ``chi = 1``, the two 5-stabilisations of
``S_k^new(3)`` (U_5 charpoly ``x^2 - a_5 x + 5^{k-1}``).

(A) ``s = 1``, ``k = 2``: ``rk e Z/5^m[X_1]`` vs the number of 5-adic unit roots of the ``U_5``-charpolys
    (``chi`` even); the Eisenstein line (constants, ``U_p = p``) is killed by ``e``.
(B) ``s >= 2``: for each ``k <= 6``, ``chi`` and a convention ``(w, eps)``, the piece of ``e Z/5^s[X_s]`` on which the
    adelic diamond ``<2>`` (``2`` generates ``(Z/5^s)^x``) acts by ``lambda = iota(chi(2))^eps * 2^w``, with
    ``w = 2 - k`` (``P^ad_k``, def:s04-Pk) or ``w = k - 2`` (seed ``P_k``) and ``eps = +-1``.  Its ``Z/5^s``-rank and
    ``U_p``-charpoly mod ``5^s`` are compared with the ordinary part of ``U_5`` on ``S_k(15, chi)^{3-new}``.
    ``iota: Z[i] -> Z/5^s`` is a fixed root of ``t^2 + 1``; the comparison is embedding-independent because ``chi``
    and ``chi^{-1}`` are both tested.  The piece is the image of ``N_lambda = sum_j lambda^{-j} <2>^j`` (the kernel
    of ``<2> - lambda`` on a free ``Z/p^s[Delta_s]``-module, ``lambda^{|G|} = 1``), a free direct summand.

Run: ``cd code/python && python3 -m langlandscape.ordinary.seed_c2`` (writes ``code/results/s04/C2.json``).
"""

from __future__ import annotations

import numpy as np

from .. import results
from ..pari import get_pari
from . import proj, tower

D, P = 3, 5
CHARS = (1, 4, 7, 13)  # Conrey labels mod 15 of the characters trivial at 3
KS = tuple(range(2, 7))


# ------------------------------------------------------------------------------------------------ helpers

def sqrt_m1(q: int) -> int:
    """The root of ``t^2 + 1`` mod ``q = 5^s`` lifting ``2`` mod 5 (Hensel)."""
    r = 2
    while (r * r + 1) % q:
        r = next(x for x in range(r, q, 5) if (x * x + 1) % q == 0)
    return r


def charpoly_mod(X, q: int) -> list[int]:
    """Monic charpoly of an integer matrix mod ``q`` (coefficients, leading first)."""
    pari = get_pari()
    X = np.asarray(X, dtype=np.int64) % q
    n = X.shape[0]
    if n == 0:
        return [1]
    f = pari.charpoly(pari.matrix(n, n, [int(v) for v in X.flatten()]))
    return [int(c) % q for c in reversed(list(pari.Vecrev(f)))]


def ordinary_part(coeffs: list[int], q: int) -> list[int]:
    """Unit-root factor mod ``q = 5^m`` of a monic ``f`` in ``Z_5[x]`` (given mod ``q``): ``e_U`` on the companion."""
    n = len(coeffs) - 1
    if n == 0:
        return [1]
    C = np.zeros((n, n), dtype=np.int64)
    for i in range(1, n):
        C[i, i - 1] = 1
    for i in range(n):
        C[i, n - 1] = (-coeffs[n - i]) % q
    m = round(np.log(q) / np.log(P))
    E = proj.ordinary_projector(C, P, m)
    return charpoly_mod(proj.mul(proj.mul(E.coord, C, q), E.basis, q), q) if E.rank else [1]


def polmul(a, b, q):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % q
    return r


# ------------------------------------------------------------------------------------------------ PARI side

def chi_value_2(a: int):
    """``chi_a(2)`` as an element of ``Q(i)``, written ``(c0, c1)`` = ``c0 + c1 t`` with PARI's ``t`` of ``mfinit``."""
    pari = get_pari()
    G = pari.znstar(15, 1)
    c = pari.chareval(G, pari.znconreychar(G, a), 2)  # chi(2) = exp(2 pi i c)
    e = int(4 * c) % 4
    return {0: (1, 0), 1: (0, 1), 2: (-1, 0), 3: (0, -1)}[e]


def _to_modq(pol, ival: int, q: int) -> list[int]:
    """Polynomial in ``x`` with coefficients in ``Q(t)`` (``t -> ival``) reduced mod ``q``, leading first."""
    pari = get_pari()
    f = pari.subst(pari.lift(pol), "t", ival)
    assert pari.pollead(f) == 1, "monic expected"
    out = []
    for c in reversed(list(pari.Vecrev(f))):
        c = pari(c)
        num, den = int(pari.numerator(c)), int(pari.denominator(c))
        assert den % P
        out.append(num * pow(den, -1, q) % q)
    return out


def mf_charpoly_U5(k: int, a: int):
    """``U_5``-charpoly on ``S_k(15, chi_a)^{3-new}`` as a PARI polynomial and its dimension data."""
    pari = get_pari()
    x = pari("x")
    mf = pari.mfinit([15, k, pari.Mod(a, 15)], 0)
    d15 = int(pari.mfdim(mf))
    f = pari.charpoly(pari.mfheckemat(mf, 5)) if d15 else pari(1)
    d3 = 0
    if a == 1:
        mf3 = pari.mfinit([3, k], 0)
        d3 = int(pari.mfdim(mf3))
        if d3:
            Q = pari.subst(pari.charpoly(pari.mfheckemat(mf3, 5)), "x", pari("y"))
            R = pari.polresultant(x**2 - pari("y") * x + 5 ** (k - 1), Q, "y")
            f = f * R / pari.pollead(R)  # monic (the resultant has leading coefficient +-1)
    return f, {"dim_new_15": d15, "dim_new_3": d3, "dim_3new": d15 + 2 * d3,
               "charpoly_U5": str(f).replace(" ", "")}


def mf_ordinary(k: int, a: int, q: int, ival: int):
    f, info = mf_charpoly_U5(k, a)
    fo = ordinary_part(_to_modq(f, ival, q), q)
    return fo, info


# ------------------------------------------------------------------------------------------------ quaternion side

def rank_s1(m: int = 3) -> dict:
    T = tower.tower(D, P)
    U = T.Up(1)
    q = P**m
    E = T.e(1, m)
    ones = np.ones(len(T.X(1)), dtype=np.int64)
    return {"X1_size": len(T.X(1)), "U_p": U.tolist(), "rank_e": E.rank, "m": m,
            "deg_Up_eq_p": bool((U.sum(axis=0) == P).all()),
            "eisenstein_killed": bool((proj.mul(ones[None, :], E.e, q) % q == 0).all()),
            "U_p_charpoly_on_e_mod_q": charpoly_mod(proj.mul(proj.mul(E.coord, U, q), E.basis, q), q)}


class Pieces:
    """``e Z/5^s[X_s]`` with ``U_p`` and ``<2>`` restricted (``m = s``)."""

    def __init__(self, s: int):
        self.s, self.q = s, P**s
        T = tower.tower(D, P)
        q = self.q
        self.E = T.e(s, s)
        c, b = self.E.coord, self.E.basis
        self.U = proj.mul(proj.mul(c, T.Up(s), q), b, q)
        self.G = proj.mul(proj.mul(c, T.diamond(s, 2), q), b, q)
        self.order = 4 * P ** (s - 1)
        self.r = self.E.rank
        Gs, X = [], np.eye(self.r, dtype=np.int64)
        for _ in range(self.order):
            Gs.append(X)
            X = proj.mul(X, self.G, q)
        assert (X == np.eye(self.r, dtype=np.int64)).all()
        assert (proj.mul(self.U, self.G, q) == proj.mul(self.G, self.U, q)).all()
        self.Gs = Gs

    def piece(self, lam: int) -> dict:
        q, p = self.q, P
        assert pow(lam, self.order, q) == 1
        li = pow(lam, -1, q)
        N = np.zeros((self.r, self.r), dtype=np.int64)
        for j, X in enumerate(self.Gs):
            N = (N + pow(li, j, q) * X) % q
        _, J = proj.pivots_mod_p(N, p)
        if not J:
            return {"rank": 0, "charpoly": [1]}
        B = N[:, J]
        I, J2 = proj.pivots_mod_p(B, p)
        assert len(J2) == len(J)
        Binv = proj.inv(B[I, :], p, self.s)
        # B spans im N (free summand): N = B (Binv N[I]); invariance and eigen-relation
        assert (proj.mul(B, proj.mul(Binv, N[I, :], q), q) == N).all()
        assert ((proj.mul(self.G, B, q) - lam * B) % q == 0).all()
        UB = proj.mul(self.U, B, q)
        X = proj.mul(Binv, UB[I, :], q)
        assert (proj.mul(B, X, q) == UB).all()
        return {"rank": len(J), "charpoly": charpoly_mod(X, q)}


CONVENTIONS = {
    "Pad_k,chi^-1": (-1, -1),  # (sign of k - 2 in w, eps): lambda = chi(2)^-1 2^{2-k}
    "Pad_k,chi": (-1, 1),
    "P_k,chi^-1": (1, -1),
    "P_k,chi": (1, 1),
}


def diamond_test(s: int = 2) -> dict:
    q = P**s
    ival = sqrt_m1(q)
    Pc = Pieces(s)
    rows, verdict = [], {c: True for c in CONVENTIONS}
    for k in KS:
        for a in CHARS:
            c0, c1 = chi_value_2(a)
            chi2 = (c0 + c1 * ival) % q
            fo, info = mf_ordinary(k, a, q, ival)
            row = {"k": k, "chi_conrey_mod15": a, "chi(2)": [c0, c1], "iota(chi(2))": chi2, **info,
                   "mf_ord_rank": len(fo) - 1, "mf_ord_charpoly_mod_q": fo, "quat": {}}
            for name, (sw, eps) in CONVENTIONS.items():
                lam = pow(chi2, eps, q) * pow(2, sw * (k - 2), q) % q
                pc = Pc.piece(lam)
                ok = pc["rank"] == len(fo) - 1 and pc["charpoly"] == fo
                row["quat"][name] = {"lambda": lam, **pc, "match": ok}
                verdict[name] &= ok
            rows.append(row)
    return {"s": s, "q": q, "iota_i": ival, "rank_e_Zq_Xs": Pc.r, "X_s_size": len(tower.tower(D, P).X(s)),
            "rows": rows, "all_match": verdict}


def weight2_count(m: int = 3) -> dict:
    q = P**m
    ival = sqrt_m1(q)
    per = {}
    for a in CHARS:
        pari = get_pari()
        G = pari.znstar(15, 1)
        if pari.chareval(G, pari.znconreychar(G, a), -1) != 0:
            continue  # odd: no weight-2 forms
        fo, info = mf_ordinary(2, a, q, ival)
        per[a] = {**info, "ordinary": len(fo) - 1}
    return {"per_char": per, "dim_3new_total": sum(v["dim_3new"] for v in per.values()),
            "ordinary_total": sum(v["ordinary"] for v in per.values())}


def run(write: bool = True, s_list=(2, 3)) -> dict:
    with results.Timer() as tm:
        A = rank_s1()
        W = weight2_count()
        Bs = {f"s={s}": diamond_test(s) for s in s_list}
    data = {
        "setting": "B_3 (definite, h=1), p=5, X_s = X_B(U_1(5^s)_5), M=N0=1; classical: S_k(Gamma_1(5) cap Gamma_0(3))^{3-new}",
        "A_rank_s1": {**A, **W, "Eisenstein_line": "constants, U_p = p (deg U_p = p), killed by e",
                      "rank_check": A["rank_e"] == W["ordinary_total"]
                      and A["X1_size"] == W["dim_3new_total"] + 1},
        "B_diamonds": Bs,
        "conventions": {k: f"adelic <2> acts by iota(chi(2))^{e} * 2^{{{'2-k' if sw < 0 else 'k-2'}}}"
                        for k, (sw, e) in CONVENTIONS.items()},
        "diamond_convention": "<d>[x] = [x diag(1,d)] at p (adelic, homological; tower.diamond)",
    }
    ok = [c for c in CONVENTIONS if all(B["all_match"][c] for B in Bs.values())]
    data["verdict"] = {
        "rank_equal": data["A_rank_s1"]["rank_check"],
        "matching_conventions": ok,
        "statement": ("on the piece of e Z_p[X_s] matching ord S_k(Gamma_0(15), chi)^{3-new}, the adelic <d> = [x diag(1,d)] "
                      "acts by chi(d)^{-1} d^{2-k} = (classical chi(d) d^{k-2})^{-1}: weight point P^ad_k (not seed P_k) and "
                      "the classical nebentypus enters inverted (rem:s01-diamond, thm:s01-lambdaJL classical <d> -> seed <d>^{-1})")
        if ok == ["Pad_k,chi^-1"] else "UNEXPECTED",
    }
    if write:
        results.write("s04/C2.json", data,
                      script="code/python/langlandscape/ordinary/seed_c2.py "
                             "(cd code/python && python3 -m langlandscape.ordinary.seed_c2)",
                      params={"D": D, "p": P, "M": 1, "N0": 1, "k": list(KS), "s": list(s_list), "chars_mod15": list(CHARS)},
                      runtime_s=round(tm.seconds, 3),
                      notes="S04-C4 (seed C2): rk e Z_p[X_1] vs PARI ordinary 3-new weight-2 forms; diamond normalisation P^ad_k")
    return data


if __name__ == "__main__":
    d = run()
    print("rank", d["A_rank_s1"]["rank_e"], d["A_rank_s1"]["ordinary_total"], d["A_rank_s1"]["rank_check"])
    for s, B in d["B_diamonds"].items():
        print(s, B["all_match"])
