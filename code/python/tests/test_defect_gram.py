# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06-C5: integral Brandt module with Sym^{k-2}, Gram matrices with w_x and |Gamma_x|, eta^B (T5 definite side)."""

from fractions import Fraction

import pytest

from langlandscape import results
from langlandscape.defect import gram


# ---------------------------------------------------------------- p-adic linear algebra
def test_smith_and_kernel_toy():
    p, R = 5, 12
    P = p**R
    A = [[25, 0, 0], [0, 1, 0], [0, 0, 0]]
    assert gram.det_val([[25, 0], [0, 7]], p, R) == 2
    K = gram.kernel(A, p, R, expected=1, zero_at=R // 2)
    assert len(K) == 3 and len(K[0]) == 1
    assert all(x % P == 0 for x in gram.mmul(A, K, P)[0] + gram.mmul(A, K, P)[1])
    assert gram.rank_mod_p([[x % p for x in col] for col in gram.transpose(K)], p)[0] == 1  # saturated


def test_vp_frac():
    assert gram.vp_frac(Fraction(50, 3), 5) == 2
    assert gram.vp_frac(Fraction(3, 125), 5) == -3


# ---------------------------------------------------------------- one T5 triple in full
@pytest.fixture(scope="module")
def t5_13_12_31():
    return gram.triple(13, 12, 31)


def test_dimension_is_q_new_dimension(t5_13_12_31):
    r = t5_13_12_31
    assert r["dim_brandt"] == r["dim_mf_new"] == 11
    assert all(r["charpoly_vs_pari"].values())


def test_hecke_relations(t5_13_12_31):
    r = t5_13_12_31
    assert r["commutative"]
    assert r["self_adjoint"] == {"w": True, "Gamma": True}


def test_gram_ratio_unit(t5_13_12_31):
    d = t5_13_12_31["det_gram"]
    assert d["vp_ratio"] == 0 and d["vp_w"] == 0
    assert d["ratio_w_over_Gamma"] == Fraction(2) ** 11  # h = 1, |Gamma| = 2 w
    assert t5_13_12_31["vp_ratio_all_zero"]


def test_old_congruent_block(t5_13_12_31):
    r = t5_13_12_31
    assert r["level_one_form"]["vp_level_raising"] >= 1  # 31 | a_13(Delta)^2 - 13^10 * 14^2
    assert r["blocks"][0]["old_congruent"]
    assert r["m"]["vp_etaB"] == [0]
    assert r["all_ok"]


def test_small_triple_q3():
    r = gram.triple(3, 18, 53)
    assert r["all_ok"] and r["dim_brandt"] == r["dim_mf_new"] == 3
    assert r["gammas"] == [12] and r["w"] == [6]


# ---------------------------------------------------------------- positive control: a new/new congruence
def test_positive_control_13_8_37():
    """S_8(Gamma_0(13))^new has two Q_37-rational newforms congruent mod 37: the Gram determinant sees it."""
    r = gram.triple(13, 8, 37)
    assert r["all_ok"]
    pair = [b for b in r["blocks"] if b["rank"] == 2 and all(o["degree"] == 1 for o in b["orbits"])]
    assert len(pair) == 1
    for o in pair[0]["orbits"]:
        assert o["vp_det_gram_w"] == 1 == o["vp_monogenic_bound"]
        assert o["vp_ratio"] == 0


def test_guards():
    with pytest.raises(AssertionError):
        gram.IntegralBrandt(13, 12, 7)  # p <= k - 2


# ---------------------------------------------------------------- committed result file
def test_result_file():
    try:
        res = results.read("s06/T5_def.json")
    except FileNotFoundError:
        pytest.skip("T5_def.json not generated yet")
    prov = res["provenance"]
    assert prov["script"] == "code/python/langlandscape/defect/gram.py"
    assert {"commit", "params", "runtime_s", "date"} <= set(prov)
    data = res["data"]
    assert data["all_ok"]
    assert set(data["triples"]) == {f"{q},{k},{p}" for q, k, p in gram.TRIPLES}
    for v in data["triples"].values():
        assert v["dim_brandt"] == v["dim_mf_new"]
        assert v["det_gram"]["vp_ratio"] == 0
