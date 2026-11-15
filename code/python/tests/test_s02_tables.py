"""S02-C3: T2 (H02.3) and T3 (H02.4) numbers."""

from fractions import Fraction

import pytest

from langlandscape import results, tables_s02 as ts

T2_MASS = {(2, 7): Fraction(8, 24), (2, 13): Fraction(14, 24), (11, 2): Fraction(30, 24)}


@pytest.fixture(scope="module")
def T2():
    return ts.t2()


@pytest.fixture(scope="module")
def T3():
    return ts.t3()


@pytest.mark.parametrize("case", ts.T2_CASES)
def test_t2(T2, case):
    d = T2[f"B{case[0]}_q{case[1]}"]
    rk, E = ts.T2_EXPECT[case]
    assert (d["rk_H1"], d["n_edges"]) == (rk, E)
    assert d["rk_H1"] == d["rk_H1_formula"] and d["components"] == 1
    assert d["edge_mass"] == (case[1] + 1) * d["vertex_mass"] == T2_MASS[case]
    if case == (11, 2):
        assert d["X_per_type"] == 2


def test_t3(T3):
    for s in (1, 2, 3):
        d = T3[f"s{s}"]
        S = 2 * 25 ** (s - 1)
        assert d["X_per_type"] == S and d["n_edges"] == 3 * S and d["rk_H1"] == S + 1 == d["rk_H1_formula"]
        assert d["components"] == 1


def test_t3_graph(T3):
    g = T3["s1"]["self_contained_graph"]
    assert len(g["vertices_type0"]) == len(g["vertices_type1"]) == 2 and len(g["edges"]) == 6
    assert sum(g["edge_multiplicities"].values()) == 6 and g["genus"] == 3


def test_committed_json_matches(T2, T3):
    """Read-only: the tracked result files agree with the in-memory computation."""
    a = results.read("s02/T2.json")["data"]
    b = results.read("s02/T3.json")["data"]
    for k, d in T2.items():
        assert a[k]["rk_H1"] == d["rk_H1"] and a[k]["n_edges"] == d["n_edges"]
        assert a[k]["X_per_type"] == d["X_per_type"]
    for k, d in T3.items():
        assert b[k]["rk_H1"] == d["rk_H1"] and b[k]["n_edges"] == d["n_edges"]
        assert b[k]["X_per_type"] == d["X_per_type"]
    assert b["s1"]["self_contained_graph"] == T3["s1"]["self_contained_graph"]
