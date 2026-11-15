"""S05-C1 / T05-1: a_q = +lambda(Pi_q) on every Brandt eigenline (fast cases + the committed JSON)."""

import json
import pathlib

import pytest

from langlandscape.comparison import sign

JSON = pathlib.Path(__file__).resolve().parents[2] / "results" / "s05" / "T05-1.json"


@pytest.mark.parametrize("q,k", [(11, 2), (11, 4), (23, 2), (23, 4), (37, 4)])
def test_small_cases(q, k):
    r = sign.compare(q, k)
    assert r["Pi_squared_equals_q^n"] and r["Pi_commutes_with_T"] and r["eigenvalues_exhaust"]
    assert r["eigenlines_checked"] == r["newform_dim"] > 0
    assert r["n_minus"] == 0 and r["n_unmatched"] == 0
    assert r["n_plus"] == r["eigenlines_checked"] and r["all_plus"]


def test_results_json():
    if not JSON.exists():
        pytest.skip("T05-1.json not generated")
    data = json.loads(JSON.read_text())["data"]
    assert {(r["q"], r["k"]) for r in data["rows"]} == {(q, k) for q in sign.QS for k in sign.KS}
    assert data["all_plus"] and data["total_minus"] == 0 and data["total_unmatched"] == 0
    assert data["total_plus"] == data["total_eigenlines"] == data["total_newforms_with_dimension"] > 0
    for r in data["rows"]:
        assert r["all_plus"] and r["T_charpolys_agree_per_sign"]
