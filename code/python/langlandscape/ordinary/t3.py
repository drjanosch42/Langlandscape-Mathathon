# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C2 (T3): ekills (a),(d), Hida (d) and the Lambda-adic Ribet ranks for ``B_3``, ``q = 2``, ``p = 5``, mod ``5^3``.

Objects (``h(3) = 1``, all stabilisers trivial): ``S_s = X_B(U_1(5^s))`` = ``tower(3,5,1,1).X(s)`` (vertices of both
types of ``BG(U_1(5^s), 2)``) and ``E_s = X_B(U_1(5^s) cap U_0(2))`` = ``tower(3,5,1,2).X(s)`` (edges), with
``s_0 : E_s -> S_s`` forgetting the line and ``s_1 : E_s -> S_s`` the other end ``x -> x alpha_2``.  ``s_1`` is built here:
for a point ``(v, l)`` choose the class ``gamma`` of norm 2 in ``O`` (one of ``q + 1 = 3``) attached to the line ``l`` and
set ``y = iota_p(gamma)^{-1} k_v``, ``s_1 = [y]``; the attachment (left kernel / row space / right kernel / column space of
``phi(gamma) mod 2``) is *selected* by the requirement that ``s_1`` is well defined on ``O^x``-orbits (:func:`pick_variant`).
Ribet: ``0 -> H_1 -> Z[E] --alpha--> Z[S]^2 --eps--> Z -> 0``, ``alpha = (-s_0*, s_1*)``, all maps ``U_p``- and
``Delta``-equivariant.  ``e`` is exact, ``e Z = 0`` (``U_p = p``), hence ``rk e H_1 = rk e Z[E] - 2 rk e Z[S]``.

Run: ``cd code/python && python -m langlandscape.ordinary.t3`` -> ``code/results/s04/T3.json``.
"""

from __future__ import annotations

import json
import sys
from math import gcd

import numpy as np

from .. import levels, results
from ..padic import mat_adj, mat_mul
from . import proj, tower as tw

D, Q, P, M = 3, 2, 5, 3  # M = precision exponent (mod 5^3)
QM = P**M
VARIANTS = ("left_kernel", "row_space", "right_kernel", "column_space")


def _line_of(phi2, variant):
    a, b, c, d = phi2
    rows = [(a, b), (c, d)]
    cols = [(a, c), (b, d)]
    cand = {
        "left_kernel": [(x, y) for x in range(2) for y in range(2) if (x, y) != (0, 0) and ((x * a + y * c) % 2, (x * b + y * d) % 2) == (0, 0)],
        "row_space": [r for r in rows if r != (0, 0)],
        "right_kernel": [(x, y) for x in range(2) for y in range(2) if (x, y) != (0, 0) and ((a * x + b * y) % 2, (c * x + d * y) % 2) == (0, 0)],
        "column_space": [r for r in cols if r != (0, 0)],
    }[variant]
    lines = {levels.canon_line(v, 2) for v in cand}
    assert len(lines) == 1
    return lines.pop()


class Ribet:
    def __init__(self, s: int, variant: str | None = None):
        self.s = s
        self.TS, self.TE = tw.tower(D, P, 1, 1), tw.tower(D, P, 1, Q)
        self.LS, self.LE = self.TS.X(s), self.TE.X(s)
        self.gam = tw.norm_p_classes(D, Q)
        assert len(self.gam) == Q + 1
        self.variant = variant or pick_variant()
        qa = self.LE.qa
        cd = self.TE.cd
        self._gdat = []
        for g in self.gam:
            a, b, c, d = cd.phi(0, list(g), qa)
            ph2 = cd.phi(0, list(g), 2)
            self._gdat.append((mat_adj([[a, b], [c, d]], qa), _line_of(ph2, self.variant)))

    def s1_point(self, v, l):
        LE, qa, p = self.LE, self.LE.qa, P
        k = tw._k_from_v((v[0] % qa, v[1] % qa), qa, p)
        hits = [adj for adj, ln in self._gdat if ln == l]
        assert len(hits) == 1
        z = mat_mul(hits[0], k, qa)
        y = [[(x * pow(Q, -1, qa)) % qa for x in r] for r in z]
        return tw._v_of(y, qa, p)

    def maps(self):
        LE, LS = self.LE, self.LS
        s0, s1 = [], []
        for (v, l) in LE.points:
            s0.append(LS.idx(v))
            s1.append(LS.idx(self.s1_point(v, l)))
        return s0, s1


_PICK = None


def well_defined(s: int, variant: str) -> bool:
    """Is ``s_1`` constant on ``O^x``-orbits of ``E_s`` for this attachment of norm-2 classes to lines?"""
    R = Ribet(s, variant)
    LE, LS = R.LE, R.LS
    img = {}
    for z, c in LE.index.items():
        t = LS.idx(R.s1_point(*z))
        if img.setdefault(c, t) != t:
            return False
    return True


def pick_variant() -> str:
    global _PICK
    if _PICK is None:
        good = [v for v in VARIANTS if well_defined(1, v)]
        assert good, "no variant makes s_1 well defined"
        _PICK = good[0]
    return _PICK


def alpha_matrix(s0, s1, S):
    E = len(s0)
    A = np.zeros((2 * S, E), dtype=np.int64)
    for e in range(E):
        A[s0[e], e] -= 1
        A[S + s1[e], e] += 1
    return A


def cycle_basis(s0, s1, S):
    """Z-basis of ``H_1 = ker(alpha)`` of the bipartite graph (fundamental cycles of a BFS spanning tree), ``E x r``."""
    E, V = len(s0), 2 * S
    adj = [[] for _ in range(V)]
    for e in range(E):
        a, b = s0[e], S + s1[e]
        adj[a].append((b, e, +1))   # traverse e forwards: a -> b
        adj[b].append((a, e, -1))
    par = {0: None}
    order = [0]
    for u in order:
        for (w, e, sg) in adj[u]:
            if w not in par:
                par[w] = (u, e, sg)
                order.append(w)
    assert len(par) == V, "graph not connected"
    tree_edges = {pe[1] for pe in par.values() if pe}

    def path_to_root(u):
        out = []
        while par[u] is not None:
            pu, e, sg = par[u]
            out.append((e, sg))  # edge e traversed pu -> u with sign sg
            u = pu
        return out  # u <- ... <- root

    cols = []
    for e in range(E):
        if e in tree_edges:
            continue
        a, b = s0[e], S + s1[e]
        v = np.zeros(E, dtype=np.int64)
        v[e] = 1
        # cycle: root -> a, edge e a -> b, b -> root
        for (f, sg) in path_to_root(a):
            v[f] += sg
        for (f, sg) in path_to_root(b):
            v[f] -= sg
        cols.append(v)
    return np.array(cols, dtype=np.int64).T


def restrict_to(B, X, q):
    """Matrix of ``X`` on the saturated sublattice with basis columns ``B`` (``X B = B A``), mod ``q`` (``q = p^m``)."""
    _, I = proj.pivots_mod_p(B.T.copy(), P)  # rows I of B independent mod p (pivot columns of B^T)
    I = list(I)
    assert len(I) == B.shape[1]
    BI = B[I, :]
    XB = proj.mul(X, B, q)
    A = proj.mul(proj.inv(BI % q, P, M), XB[I, :], q)
    assert (proj.mul(B % q, A, q) == XB % q).all()
    return A


def ekills_pairing(Tw, s, prime_tower_up):
    """``det`` of the pairing ``e x e*`` (``<[x],[y]> = delta``, ``w_x = 1``): the Gram matrix of bases is invertible mod p."""
    Up = Tw.Up(s)
    Pe = proj.ordinary_projector(Up, P, M)
    Ps = proj.ordinary_projector(Up.T.copy(), P, M)
    assert Pe.rank == Ps.rank
    G = proj.mul(Pe.basis.T.copy(), Ps.basis, QM)
    r = Pe.rank
    return Pe, Ps, G, r


def run(write: bool = True, smax: int = 3) -> dict:
    out = {"variant_s1": pick_variant(), "variants_well_defined_s1": {v: well_defined(1, v) for v in VARIANTS}, "levels": {}}
    s02 = json.load(open(results.repo_root() / "code/results/s02/T3.json"))["data"]
    with results.Timer() as tm:
        for s in range(1, smax + 1):
            R = Ribet(s)
            S, E = len(R.LS), len(R.LE)
            assert len(R.TS.X(s)) == S
            s0, s1 = R.maps()
            A = alpha_matrix(s0, s1, S)
            US, UE = R.TS.Up(s), R.TE.Up(s)
            Z = np.zeros_like(US)
            U2 = np.block([[US, Z], [Z, US]])
            assert (A @ UE == U2 @ A).all(), "alpha is not U_p-equivariant"
            DS, DE = R.TS.delta_gen(s), R.TE.delta_gen(s)
            D2 = np.block([[DS, Z], [Z, DS]])
            assert (A @ DE == D2 @ A).all(), "alpha is not Delta-equivariant"
            assert (A.sum(axis=0) == 0).all()
            B = cycle_basis(s0, s1, S)
            assert (A @ B == 0).all()
            rkH1 = B.shape[1]
            d02 = s02[f"s{s}"]
            # ekills (a): e kills deg (deg U_p = p deg => deg e = 0 mod 5^3); (d): pairing e x e*
            PeS, PsS, G, r = ekills_pairing(R.TS, s, None)
            degU = US.sum(axis=0)
            assert (degU == P).all()
            ea_deg0 = bool((proj.mul(np.ones((1, S), dtype=np.int64), PeS.e, QM) % QM == 0).all())
            pair_unit = proj.is_invertible_mod_p(G, P)
            e_ne_estar = bool((PeS.e != PsS.e).any())
            hid = R.TS.ordinary_delta_rank(s, M)
            PeE = proj.ordinary_projector(UE, P, M)
            hidE = proj.group_ring_rank(PeE, DE, R.TE.delta_order(s))
            # Ribet: e H_1 directly
            UH, DH = restrict_to(B, UE, QM), restrict_to(B, DE, QM)
            PH = proj.ordinary_projector(UH, P, M)
            hidH = proj.group_ring_rank(PH, DH, R.TE.delta_order(s))
            # exactness: e alpha maps e Z[E] onto e Z[S]^2, kernel e H_1
            ealpha = proj.mul(A % QM, PeE.e, QM)
            im_rank = proj.rank_mod_p(ealpha, P)
            out["levels"][f"s{s}"] = {
                "S_s": S, "E_s": E, "S_s_expected": 2 * 25 ** (s - 1), "stage02_X_per_type": d02["X_per_type"],
                "stage02_edges": d02["n_edges"], "stage02_rk_H1": d02["rk_H1"],
                "rk_H1": rkH1, "rk_H1_eq_S_plus_1": rkH1 == S + 1, "E_eq_3S": E == 3 * S,
                "alpha_equivariant_U_p_Delta": True,
                "ekills_a": {"rk_e_ZS": r, "deg_e_zero_mod_5^3": ea_deg0, "deg_U_p_eq_p": True},
                "ekills_d": {"rk_e": PeS.rank, "rk_e_star": PsS.rank, "pairing_gram_invertible_mod_5": bool(pair_unit),
                             "pairing_gram_rank_mod_5": proj.rank_mod_p(G, P),
                             "e_ne_e_star": e_ne_estar},
                "hida_d_rank_Delta_ZS": {"rank_Zp": hid["rank_Zp"], "free": hid["free"], "rank_Delta": hid["rank"],
                                         "delta_order": hid["order"]},
                "ribet": {"rk_e_ZE": PeE.rank, "rk_e_ZS": PeS.rank, "rk_e_H1": PH.rank,
                          "identity_rk_eH1_eq_rkeZE_minus_2rkeZS": PH.rank == PeE.rank - 2 * PeS.rank,
                          "rank_Delta_e_ZE": hidE["rank"], "rank_Delta_e_H1": hidH["rank"], "free_E": hidE["free"],
                          "free_H1": hidH["free"],
                          "rank_Delta_identity": (hidH["rank"] == hidE["rank"] - 2 * hid["rank"]) if None not in (hidH["rank"], hidE["rank"], hid["rank"]) else None,
                          "e_alpha_image_rank_mod5": im_rank, "expected_2rk_e_ZS": 2 * PeS.rank,
                          "eps_e_zero": ea_deg0},
            }
        L = out["levels"]
        out["checks"] = {
            "S_s": [L[f"s{s}"]["S_s"] for s in range(1, smax + 1)],
            "rank_Delta_e_constant": len({L[k]["hida_d_rank_Delta_ZS"]["rank_Delta"] for k in L}) == 1,
            "rank_Delta_e_values": [L[k]["hida_d_rank_Delta_ZS"]["rank_Delta"] for k in L],
            "C4_cross_check_s1_value": L["s1"]["hida_d_rank_Delta_ZS"]["rank_Delta"],
        }
    if write:
        results.write("s04/T3.json", out, script="code/python/langlandscape/ordinary/t3.py "
                      "(cd code/python && python -m langlandscape.ordinary.t3)",
                      params={"D": D, "q": Q, "p": P, "m": M, "s": list(range(1, smax + 1))}, runtime_s=round(tm.seconds, 2),
                      notes="S04-C2: T3; E_s = X(U_1(5^s) cap U_0(2)); H_1 = ker(alpha) via spanning tree")
    return out


if __name__ == "__main__":
    d = run(smax=int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    print(json.dumps(d["checks"]))
    for k, v in d["levels"].items():
        print(k, v["S_s"], v["rk_H1"], v["ribet"], v["hida_d_rank_Delta_ZS"])
