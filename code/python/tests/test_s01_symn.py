"""S01-C4: Sym^n Brandt modules at level O^x vs S_k(Gamma_0(D))^new (classical JL, char-poly form).

The full grid (D in {2,3,5,7,11,13}, 2 <= k <= 12, ell in {2,3}, ell prime to D) runs in well under a minute,
so it is the default. Nothing is written into code/results here (``python -m langlandscape.symn`` does that).
"""

import itertools
from fractions import Fraction

import pytest

from langlandscape import brandt, symn


@pytest.mark.parametrize("D", symn.DS)
def test_splitting_and_left_action(D):
    S = symn.split_algebra(D)
    es = [tuple(Fraction(int(k == m)) for m in range(4)) for k in range(4)]
    for x, y in itertools.product(es + [S.I, S.J], repeat=2):
        xy = S.B.mul(x, y)
        assert symn.mat_mul(S.split(x), S.split(y)) == S.split(xy)
        for n in (1, 2, 3):  # eq:s01-Vk is a left action: rho(xy) = rho(x) rho(y)
            assert symn.mat_mul(S.rho(x, n), S.rho(y, n)) == S.rho(xy, n)
    a = S.a
    assert S.split(S.I) == [[symn.QS(0, 1, a), symn.QS(0, 0, a)], [symn.QS(0, 0, a), symn.QS(0, -1, a)]]
    assert S.split(S.J) == [[symn.QS(0, 0, a), symn.QS(S.b, 0, a)], [symn.QS(1, 0, a), symn.QS(0, 0, a)]]


@pytest.mark.parametrize("D", symn.DS)
def test_weight2_is_brandt_matrix(D):
    M = symn.sym_brandt(D, 2)
    for ell in symn.ells_for(D):
        T = [[x.r for x in r] for r in M.T(ell)]
        assert all(x.is_rational() for r in M.T(ell) for x in r)
        assert T == [[Fraction(x) for x in r] for r in brandt.module(D).T(ell)]


@pytest.mark.parametrize("D,k", [(D, k) for D in symn.DS for k in symn.KS])
def test_jl_charpoly(D, k):
    r = symn.check(D, k)
    assert r["dim_equal"], (r["dim_brandt"], r["dim_expected"])
    for ell, v in r["ell"].items():
        assert v["charpoly_in_Q"], (D, k, ell)
        assert v["charpoly_brandt"] == v["rhs"], (D, k, ell)
    q = r["Q_structure"]
    if k % 2 == 0:
        assert q["applicable"]
        assert all(q["phi_commutes_T"].values())
        assert all(q["rational_model_matches"].values())
    else:
        assert r["dim_brandt"] == 0
    assert r["all_ok"]
