"""S02-C2: validation of the tree-quotient builder (H02.2 (a)-(c)).  Never writes tracked files."""

import pytest

from langlandscape import results, tree, validate_s02 as v

FAST = [(2, 3, tree.Level.max()), (3, 2, tree.Level.max()), (5, 2, tree.Level.U0(3)), (7, 3, tree.Level.max()),
        (11, 2, tree.Level.max()), (2, 5, tree.Level.U1(3)), (30, 7, tree.Level.max())]


@pytest.mark.parametrize("D,q,lv", FAST)
def test_fast_cases(D, q, lv):
    r = v.check_case(D, q, lv)
    assert r["connected"] and r["fibre_sums"] and r["mass"] and r["rk_H1_ok"] and r["all_pass"]
    assert r["rk_H1"] == r["E"] - 2 * r["X"] + 1


def test_rank_Q():
    assert v.rank_Q([{0: 1, 1: 1}, {0: 1, 1: 1}, {1: 1}]) == 2


def test_committed_json_all_pass():
    d = results.read("s02/validation.json")["data"]
    assert d["all_pass"] and d["n_cases"] == len(d["cases"]) > 0
    assert all(c["all_pass"] for c in d["cases"])
    assert max(c["D"] for c in d["cases"]) >= 51 and max(c["q"] for c in d["cases"]) == 13
