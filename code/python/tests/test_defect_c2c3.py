# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06-C2 (seed C4(i) regression) and S06-C3 (T4 Hecke side) tests; fast, single-threaded."""

import math

import pytest

from langlandscape import results
from langlandscape.defect import c4i, t4_hecke


@pytest.mark.parametrize("k", [12, 28, 44, 60])
def test_t4_hecke_rows(k):
    """k <= 60: finite rank, length 1 = prediction = t_{G_k}(3) (computed independently via PARI mf)."""
    r = t4_hecke.row(k)
    assert math.isfinite(r["local_rank"]) and r["local_rank"] == 1
    assert r["length"] == 1 == t4_hecke.PREDICTION[k] == r["t_Gk_3"]["length"]
    assert r["m_values"]["T17"] == t4_hecke._tau_mod(17, 17) != 0   # ordinary


def test_t4_k12_ord17_is_one():
    r = t4_hecke.row(12)
    assert r["length"] == 1 and r["t_Gk_3"]["t"] == [1]


def test_t4_k124_recorded():
    """k = 124 (dimension 10, ~1 s): length 2, as predicted (\\stexp for k >= 17); not gating in the result file."""
    r = t4_hecke.row(124)
    assert r["length"] == r["t_Gk_3"]["length"] == 2 and r["length_equals_prediction"]


@pytest.mark.parametrize("q,N,k", [(2, 6, 14), (5, 10, 12), (3, 21, 4), (2, 58, 2)])
def test_c4i_small_cases(q, N, k):
    """v(h) = v(c_q) in scope (non-Eisenstein, p >= 5, p prime to N, q != +-1 mod p); (h) contains c_q at Eisenstein m."""
    c = {"q": q, "N": N, "k": k, "dim": 0, "dim_old_M": 0}
    r = c4i.run_case(c)
    assert r["rows"]
    for x in r["rows"]:
        if x["in_scope"] and not x["eisenstein"]:
            assert x["equal"], x
        if x["eisenstein"] and x["O_v_dvr"]:
            assert x["h_contains_c"], x


def test_c4i_case_enumeration():
    cs = c4i.cases()
    assert all(c["q"] in (2, 3, 5) and c["N"] <= 70 and c["k"] <= 16 for c in cs)
    assert len(cs) == 319


def test_results_files():
    """Provenance and gating content of the committed result files."""
    t = results.read("s06/T4_hecke.json")
    assert t["provenance"]["commit"] and t["provenance"]["script"].endswith("t4_hecke.py")
    rows = {r["k"]: r for r in t["data"]}
    assert rows[12]["length"] == 1 and all(math.isfinite(r["local_rank"]) for r in rows.values())
    c = results.read("s06/C4i.json")
    assert c["provenance"]["commit"]
    s = c["data"]["summary"]
    assert s["in_scope_non_eisenstein"]["violations"] == [] and s["eisenstein"]["violations_dvr"] == []
    assert c["data"]["n_cases_run"] + len(c["data"]["skipped"]) == c["data"]["n_cases_total"] == 319
    assert c["data"]["n_cases_run"] > 0
