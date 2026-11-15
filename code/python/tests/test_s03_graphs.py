# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S03-C1: weighted graphs, Phi^comb via Smith form, matrix-tree count, lem:s03-bip checks."""

import random

import pytest

from langlandscape.ribet import graphs as g


def test_two_vertex_phi():
    r = g.phi_comb(g.two_vertex((2, 2, 2)))  # prop:s03-phi: Z/2 x Z/6
    assert r["divisors"] == [2, 6] and r["order"] == 12 and not r["cyclic"]
    r = g.phi_comb(g.two_vertex((2, 3)))  # Mazur q = 11
    assert r["divisors"] == [5] and r["order"] == 5 and r["cyclic"]
    assert g.phi_comb(g.two_vertex((1, 1, 1)))["divisors"] == [3]  # Z/|E| for unit weights
    assert g.phi_comb(g.two_vertex((7,)))["order"] == 1  # one edge: Phi = 0
    for w in [(1, 2, 3), (1, 1, 3, 4), (2, 2, 3, 3)]:
        assert g.phi_comb(g.two_vertex(w))["order"] == g.two_vertex_order(w)


def random_connected(rng):
    n = rng.randint(2, 5)
    o, t = [], []
    for v in range(1, n):  # random spanning tree, random orientations
        u = rng.randrange(v)
        o.append(u), t.append(v)
        if rng.random() < 0.5:
            o[-1], t[-1] = t[-1], o[-1]
    for _ in range(rng.randint(0, 4)):  # extra edges (multi-edges and loops allowed)
        o.append(rng.randrange(n)), t.append(rng.randrange(n))
    w = tuple(rng.randint(1, 4) for _ in o)
    return g.WGraph(n, tuple(o), tuple(t), w)


def test_matrix_tree_equals_smith_order():
    rng = random.Random(20261114)
    for _ in range(20):
        G = random_connected(rng)
        assert G.is_connected()
        r = g.phi_comb(G)
        assert r["rank"] == G.nE - G.nV + 1
        assert g.spanning_tree_weight_sum(G) == r["order"]


def test_orientation_independence():
    G = g.WGraph(3, (0, 1, 0, 2), (1, 2, 2, 0), (2, 3, 1, 2))
    H = g.WGraph(3, (1, 1, 2, 2), (0, 2, 0, 0), (2, 3, 1, 2))  # edges 0 and 2 reversed
    assert g.phi_comb(G)["divisors"] == g.phi_comb(H)["divisors"]


BIP = [
    (2, 2, (0, 0, 1, 1, 0), (0, 1, 0, 1, 0)),  # multi-edge
    (3, 2, (0, 1, 2, 2, 1, 0), (0, 0, 0, 1, 1, 1)),
    (1, 3, (0, 0, 0), (0, 1, 2)),  # tree: H_1 = 0
    (1, 1, (0, 0, 0), (0, 0, 0)),  # two-vertex, 3 parallel edges
]


@pytest.mark.parametrize("n0,n1,s0,s1", BIP)
def test_lemma_bip(n0, n1, s0, s1):
    res = g.check_bip(n0, n1, s0, s1)
    assert all(res.values()), res
    assert len(g.X_basis(g.bipartite(n0, n1, s0, s1))) == len(s0) - n0 - n1 + 1
