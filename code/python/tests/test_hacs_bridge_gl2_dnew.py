# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-A1: pure-maths unit tests and small integration tests (skipped without the HACS binary) for gl2_dnew."""

import json
import pathlib

import flint
import pytest

from langlandscape.hacs_bridge import gl2_dnew as g
from langlandscape.hacs_bridge import runner

ROOT = pathlib.Path(__file__).resolve().parents[3]
X = g.X

try:
    runner.find_hacs()
    HAVE = True
except runner.HacsError:
    HAVE = False
needs_hacs = pytest.mark.skipif(not HAVE, reason="no HACS binary")


@pytest.mark.parametrize("N,k,d", [
    (1, 12, 1), (1, 24, 2), (1, 10, 0), (11, 2, 1), (37, 2, 2), (23, 2, 2), (2, 8, 1), (13, 4, 3),
    (11, 4, 2), (11, 10, 8), (5, 2, 0), (30, 2, 3), (1, 2, 0), (11, 3, 0),
])
def test_dim_cusp_forms(N, k, d):
    assert g.dim_cusp_forms(N, k) == d


def test_dim_new():
    assert g.dim_new(11, 2) == 1 and g.dim_new(13, 4) == 3
    assert g.dim_new(11, 12) == g.dim_cusp_forms(11, 12) - 2 * g.dim_cusp_forms(1, 12)
    assert g.dim_new(30, 2) == 1 + 0 and g.dim_new(6, 2) == 0
    assert g.dim_H1(11, 2) == 3 and g.dim_H1(13, 4) == 8


def test_old_part_removal_synthetic():
    f1 = X ** 2 - 3 * X + 1          # "new at 1"
    fD = X ** 3 - X - 7              # "new at D"
    fM = X - 5
    fDM = X ** 2 + 4
    # N = 6: cusp = new_1^4 new_2^2 new_3^2 new_6
    new = {1: f1, 2: fD, 3: fM}
    cusp = f1 ** 4 * fD ** 2 * fM ** 2 * fDM
    assert g.remove_old(cusp, 6, new) == fDM
    with pytest.raises(AssertionError):      # wrong multiplicity of an old part: no exact division
        g.remove_old(f1 ** 3 * fD ** 2 * fM ** 2 * fDM, 6, new)


def test_cusp_from_h1_synthetic():
    p, k, N = 5, 4, 7
    chi = (X ** 2 - 3 * X + 1) * (X - 2)
    H1 = chi ** 2 * g.eis_poly(N, k, p)
    assert g.cusp_from_h1(H1, N, k, p) == chi
    with pytest.raises(AssertionError):
        g.cusp_from_h1(chi * g.eis_poly(N, k, p), N, k, p)  # not a square


def test_ramanujan():
    assert g.ramanujan_ok(X - 2, 2, 2) and g.ramanujan_ok(X ** 2 - 3 * X + 1, 2, 2)   # |root| <= 2 sqrt 2
    assert not g.ramanujan_ok(X - 3, 2, 2)
    assert not g.ramanujan_ok(X ** 2 + 1, 2, 2)   # non-real roots


def test_assign_signs():
    f, h = X ** 2 - 2, X ** 3 - X - 1
    st, fac = g.assign_signs(f * h, 2, 3)
    assert st == "unique" and {(d, jp) for _, d, _, jp, _ in fac} == {(2, 1), (3, 0)}
    assert g.assign_signs(f * h, 5, 0)[0] == "constant"
    assert g.assign_signs((X - 1) * (X + 1) * (X - 2) * (X + 2), 2, 2)[0] == "ambiguous"
    assert g.assign_signs(f * h, 1, 4)[0] == "inconsistent"


@needs_hacs
@pytest.mark.parametrize("D,k", [(11, 2), (11, 10), (13, 4)])
def test_symn_rhs(D, k):
    symn = json.load(open(ROOT / "code/results/s01/symn.json"))["data"]["grid"][f"{D},{k}"]
    rec = g.compute_cell(D, k)
    assert all(rec["checks"].values())
    for ell, e in symn["ell"].items():
        mine = flint.fmpz_poly(rec["charpoly_new"][ell])
        if k == 2:
            mine = mine * (X - int(ell) - 1)
        assert g.poly_list(mine) == [int(c) for c in e["rhs"]]


@needs_hacs
def test_pi_sign_13_4():
    pis = json.load(open(ROOT / "code/results/s01/pi_sign.json"))["data"]["grid"]["13,4"]
    rec = g.compute_cell(13, 4)
    assert g._pi_sign_match(rec, pis["mf"])
    assert (rec["U_D"]["n_plus"], rec["U_D"]["n_minus"]) == (1, 2)


def test_dnew_from_new_synthetic():
    # D = 5, M = 6: D-new part = new(5)^4 new(10)^2 new(15)^2 new(30)  (sigma_0(6/d) for d = 1, 2, 3, 6)
    f5, f10, f15, f30 = X - 2, X ** 2 - 5, X + 3, X ** 3 - X - 1
    junk = X ** 2 + 7                      # N-old but not D-new (levels 1, 2, 3, 6): must not enter
    new = {1: junk, 2: junk, 3: junk, 6: junk, 5: f5, 10: f10, 15: f15, 30: f30}
    assert g.dnew_from_new(5, 6, new) == f5 ** 4 * f10 ** 2 * f15 ** 2 * f30
    assert g.dnew_from_new(5, 1, new) == f5              # M = 1: the D-new = N-new charpoly
    assert g.dim_dnew(11, 2, 2) == 2 and g.dim_dnew(11, 1, 2) == 1
    assert g.dim_dnew(5, 6, 2) == 4 * 0 + 2 * 0 + 2 * 1 + 1 * 1    # dim new(15,2) = 1, dim new(30,2) = 1


def test_ext_levels():
    assert g.ext_levels(50) == [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 30, 31, 37, 41, 42, 43, 47]


def test_rule19_prediction_monotone():
    w1, r1 = g.predict_descent(13, 24)
    w2, r2 = g.predict_descent(47, 24)
    assert 0 < w1 < w2 and 0 < r1 < r2
    assert g.predict_cell(11, 2, 1, done={(11, 2), (1, 2)}) == (0.0, 0.0)


@needs_hacs
def test_dnew_11_2_level_22():
    # S_2(Gamma_0(22)) = 2 copies of 11a, no 22-new form: D-new part = (x - a_p(11a))^2, N-new part trivial
    rec = g.compute_cell(11, 2, M=2)
    assert rec["dim_new"] == 2 and rec["dim_new_formula"] == 2 and rec["dim_N_new"] == 0
    a = {3: -1, 5: 1, 7: -2}                  # 11a: a_3 = -1, a_5 = 1, a_7 = -2
    for p, ap in a.items():
        assert rec["charpoly_new"][str(p)] == g.poly_list((X - ap) ** 2)
        assert rec["charpoly_N_new"][str(p)] == [1]
    assert rec["U_D"] is None and "U_D_null_reason" in rec
    assert all(rec["checks"].values())


@needs_hacs
def test_dnew_m1_unchanged():
    old = json.load(open(ROOT / "code/results/s01/symn.json"))["data"]["grid"]["11,2"]
    rec = g.compute_cell(11, 2)
    assert "charpoly_N_new" not in rec and rec["M"] == 1
    for ell, e in old["ell"].items():
        assert g.poly_list(flint.fmpz_poly(rec["charpoly_new"][ell]) * (X - int(ell) - 1)) == [int(c) for c in e["rhs"]]


def test_ambiguous_factors_null():
    P = (X - 1) * (X + 1) * (X - 2) * (X + 2)
    st, facs = g.assign_signs(P, 2, 2)
    assert st == "ambiguous"
    rows = g.factor_rows(st, facs)
    assert all(r["n_plus"] is None and r["n_minus"] is None for r in rows) and sum(r["deg"] for r in rows) == 4
    st, facs = g.assign_signs((X ** 2 - 2) * (X ** 3 - X - 1), 2, 3)
    assert [r["n_plus"] for r in g.factor_rows(st, facs)] == [1, 0] or [r["n_plus"] for r in g.factor_rows(st, facs)] == [0, 1]
