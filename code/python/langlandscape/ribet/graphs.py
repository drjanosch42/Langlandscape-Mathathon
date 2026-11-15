# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S03-C1: weighted graphs, X(G), weighted Gram matrix, Phi^comb (Smith form), bipartite collapse (lem:s03-bip).

Tex: ``mathematics/chapters/s03/1-graphs.tex`` (``def:s03-graph``, ``prop:s03-phi``, ``lem:s03-cyclic``,
``rem:s03-kirchhoff``) and ``3-ribet.tex`` (``lem:s03-bip``).

Conventions (as in the tex): a graph has vertices ``0..nV-1``, edges ``0..nE-1`` with origin ``o[e]`` and target ``t[e]``;
``d e = t(e) - o(e)``; ``X(G) = ker d`` (saturated sublattice of Z^E); ``<e,e'>_w = w_e delta``;
``Phi^comb = coker(X -> X^v)`` has Gram matrix ``B^T W B`` for a basis ``B`` of X.  A bipartite graph (parts V0, V1,
maps s0, s1) is the graph with vertices ``V0 (+) V1`` (V1 shifted by ``n0``), ``o = s0``, ``t = n0 + s1``; then
``d = (-s0*, s1*)`` as in stage 02's ``twoterm.py``.  Smith forms and integer kernels use PARI (``pari.get_pari``).
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from math import prod
from typing import Sequence

from .. import pari as _pari


def _mat(rows: Sequence[Sequence[int]], nrows: int, ncols: int):
    """PARI integer matrix from a list of rows (handles empty shapes via explicit dimensions)."""
    pari = _pari.get_pari()
    return pari.matrix(nrows, ncols, [int(x) for r in rows for x in r])


@dataclass(frozen=True)
class WGraph:
    """Weighted graph (def:s03-graph): ``nV`` vertices, edges ``(o[e], t[e])`` with weights ``w[e] >= 1``."""

    nV: int
    o: tuple
    t: tuple
    w: tuple

    def __post_init__(self):
        assert len(self.o) == len(self.t) == len(self.w)
        assert all(0 <= v < self.nV for v in self.o + self.t)
        assert all(int(x) >= 1 for x in self.w)

    @property
    def nE(self) -> int:
        return len(self.w)

    def boundary_matrix(self):
        """``d`` as an ``nV x nE`` integer matrix (list of rows): column e is ``t(e) - o(e)``."""
        M = [[0] * self.nE for _ in range(self.nV)]
        for e in range(self.nE):
            M[self.t[e]][e] += 1
            M[self.o[e]][e] -= 1
        return M

    def is_connected(self) -> bool:
        if self.nV == 0:
            return False
        par = list(range(self.nV))

        def f(a):
            while par[a] != a:
                par[a] = par[par[a]]
                a = par[a]
            return a

        for a, b in zip(self.o, self.t):
            par[f(a)] = f(b)
        return len({f(v) for v in range(self.nV)}) == 1


def two_vertex(weights: Sequence[int]) -> WGraph:
    """Two-vertex graph with one edge ``0 -> 1`` per weight (prop:s03-phi)."""
    n = len(weights)
    return WGraph(2, (0,) * n, (1,) * n, tuple(int(x) for x in weights))


def bipartite(n0: int, n1: int, s0: Sequence[int], s1: Sequence[int], w: Sequence[int] | None = None) -> WGraph:
    """Bipartite multigraph (parts of sizes n0, n1; ``s_j : E -> V_j``) as a WGraph; V1 is shifted by ``n0``."""
    assert len(s0) == len(s1)
    w = tuple(w) if w is not None else (1,) * len(s0)
    return WGraph(n0 + n1, tuple(s0), tuple(n0 + b for b in s1), w)


def X_basis(G: WGraph) -> list:
    """Basis of ``X(G) = ker d`` (saturated, via PARI ``matkerint``): list of integer vectors of length nE."""
    if G.nE == 0:
        return []
    if G.nV == 0:
        return [[int(i == j) for j in range(G.nE)] for i in range(G.nE)]
    K = _pari.get_pari().matkerint(_mat(G.boundary_matrix(), G.nV, G.nE))
    ncols = int(K.ncols()) if hasattr(K, "ncols") else len(K)
    return [[int(K[i, j]) for i in range(G.nE)] for j in range(ncols)]


def gram(G: WGraph, basis: list | None = None) -> list:
    """Gram matrix ``(<b_i, b_j>_w)`` of the weighted pairing on a basis of X(G) (default :func:`X_basis`)."""
    B = X_basis(G) if basis is None else basis
    return [[sum(G.w[e] * bi[e] * bj[e] for e in range(G.nE)) for bj in B] for bi in B]


def smith_divisors(M: Sequence[Sequence[int]], nrows: int | None = None, ncols: int | None = None) -> list:
    """Nonzero elementary divisors of an integer matrix (PARI ``matsnf``), ascending, including 1's."""
    nrows = len(M) if nrows is None else nrows
    ncols = (len(M[0]) if M else 0) if ncols is None else ncols
    if nrows == 0 or ncols == 0:
        return []
    d = _pari.get_pari().matsnf(_mat(M, nrows, ncols))
    return sorted(int(x) for x in d if int(x) != 0)


def phi_comb(G: WGraph) -> dict:
    """Phi^comb(G) = coker(X -> X^v) by Smith form of the Gram matrix.

    Returns ``{"rank": g, "divisors": elementary divisors > 1 ascending (d_1 | d_2 | ...), "order": prod of all
    elementary divisors = det Gram, "cyclic": bool}``.  (Positive definiteness => Gram nonsingular, fact (2).)
    """
    B = X_basis(G)
    g = len(B)
    full = smith_divisors(gram(G, B), g, g)
    assert len(full) == g, "Gram matrix singular (impossible for positive weights)"
    divs = [d for d in full if d != 1]
    return {"rank": g, "divisors": divs, "order": prod(full), "cyclic": len(divs) <= 1}


def two_vertex_order(weights: Sequence[int]) -> int:
    """prop:s03-phi: ``sum_e prod_{e' != e} w_e'``."""
    return sum(prod(weights[:i] + tuple(weights[i + 1:])) for i in range(len(weights))) if weights else 0


def spanning_tree_weight_sum(G: WGraph) -> int:
    """rem:s03-kirchhoff: ``sum_T prod_{e not in T} w_e`` over spanning trees T (brute force; small graphs only)."""
    m = G.nV
    total = 0
    for T in itertools.combinations(range(G.nE), m - 1):
        par = list(range(m))

        def f(a):
            while par[a] != a:
                a = par[a]
            return a

        ok = True
        for e in T:
            a, b = f(G.o[e]), f(G.t[e])
            if a == b:
                ok = False
                break
            par[a] = b
        if ok:
            Ts = set(T)
            total += prod(G.w[e] for e in range(G.nE) if e not in Ts)
    return total


def collapse(G: WGraph, n0: int) -> WGraph:
    """lem:s03-bip(c): collapse a bipartite WGraph (V0 = first ``n0`` vertices) to two vertices, identity on edges,
    every edge oriented 0 -> 1 (same weights)."""
    return two_vertex(G.w) if G.nE == 0 else WGraph(2, (0,) * G.nE, (1,) * G.nE, G.w)


def check_bip(n0: int, n1: int, s0: Sequence[int], s1: Sequence[int]) -> dict:
    """Verify lem:s03-bip (a), (b), (c) for a connected bipartite multigraph; returns a dict of booleans.

    (a) ker d lies in Z[E]^0; d: Z[E]^0 -> Z[V0]^0 (+) Z[V1]^0 is onto (image has rank n0+n1-2 and all elementary
        divisors 1, i.e. is saturated, inside the saturated target of the same rank); rank H_1 = |E|-|V0|-|V1|+1.
    (b) ker of d^v : (f0,f1) -> s1^* f1 - s0^* f0 is the diagonal, over Z (matkerint) and over Q (rank of kernel = 1,
        spanned by the all-ones vector).
    (c) the collapse G -> G^(2) has H_1(G^(2)) = Z[E]^0 and the connecting map on Z[E]^0 is d|Z[E]^0, whose kernel is
        H_1(G): checked as ker d = ker (d restricted to Z[E]^0) and ker d^(2) = Z[E]^0.
    """
    G = bipartite(n0, n1, s0, s1)
    assert G.is_connected()
    nE, nV = G.nE, G.nV
    pari = _pari.get_pari()
    D = G.boundary_matrix()
    B = X_basis(G)
    res = {}
    # (a)
    res["a_ker_in_deg0"] = all(sum(b) == 0 for b in B)
    # Z[E]^0 basis e_i - e_{nE-1}; matrix of d on it
    Z0 = [[(1 if j == i else 0) - (1 if j == nE - 1 else 0) for j in range(nE)] for i in range(nE - 1)]
    cols = [[sum(D[v][e] * z[e] for e in range(nE)) for v in range(nV)] for z in Z0]  # images, as vectors in Z^V
    img_rows = [[cols[i][v] for i in range(nE - 1)] for v in range(nV)]
    div = smith_divisors(img_rows, nV, nE - 1)
    res["a_surjective"] = len(div) == n0 + n1 - 2 and all(x == 1 for x in div) and all(
        sum(c[:n0]) == 0 and sum(c[n0:]) == 0 for c in cols
    )
    res["a_rank"] = len(B) == nE - n0 - n1 + 1
    # (b) kernel of the transpose of d (matrix E x V: row e = (-[s0 e], [s1 e]))
    DT = [[D[v][e] for v in range(nV)] for e in range(nE)]
    K = pari.matkerint(_mat(DT, nE, nV))
    kc = int(K.ncols())
    kvecs = [[int(K[i, j]) for i in range(nV)] for j in range(kc)]
    res["b_ker_Z"] = kc == 1 and (kvecs[0] == [1] * nV or kvecs[0] == [-1] * nV)
    res["b_ker_Q"] = int(pari.matrank(_mat(DT, nE, nV))) == nV - 1
    # (c)
    G2 = collapse(G, n0)
    B2 = X_basis(G2)
    ker_collapse_is_deg0 = len(B2) == nE - 1 and all(sum(b) == 0 for b in B2)
    D2 = G2.boundary_matrix()
    # d(2) = deg-type map: d(2) y = (sum y)(v1 - v0); d|Z[E]^0 lands in ker of aug on each part; connecting map = d|Z[E]^0
    res["c_collapse_H1"] = ker_collapse_is_deg0 and all(D2[1][e] == 1 and D2[0][e] == -1 for e in range(nE))
    res["c_connecting_kernel"] = len(B) == nE - 1 - (n0 + n1 - 2)  # ker(d|Z[E]^0) = H_1(G) has rank |E|-1-(|V|-2)
    return res
