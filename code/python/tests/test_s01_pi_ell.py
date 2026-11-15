"""S01-C7: Pi_D on M(O^x; V_k) vs a_D of the newforms (sign U_D -> +Pi_D). Nothing is written into code/results here."""

import itertools

import pytest

from langlandscape import pi_ell, symn

GRID = list(itertools.product(pi_ell.DS, pi_ell.KS))


@pytest.fixture(scope="module")
def cmp():
    return {(D, k): pi_ell.compare(D, k) for D, k in GRID}


@pytest.mark.parametrize("D,k", GRID)
def test_relations(cmp, D, k):
    r = cmp[(D, k)]
    assert r["Pi_squared_equals_D^n"]  # Pi^2 = S_D = D^{k-2}
    assert all(r["commutes_with_T"].values()) and set(r["commutes_with_T"]) == {"2", "3", "5"}
    assert r["brandt"]["eigenvalues_exhaust"] and r["mf"]["UD_semisimple_with_eigenvalues_pm"]


@pytest.mark.parametrize("D,k", GRID)
def test_sign_plus(cmp, D, k):
    r = cmp[(D, k)]
    assert not r["sign_contradiction"], "SIGN CONTRADICTION: Pi = -a_D"
    assert r["match_Pi_eq_plus_aD"]
    if r["no_newforms"]:
        assert (D, k) == (13, 2)  # S_2(Gamma_0(13)) = 0: only the Eisenstein line
    else:
        assert not r["match_Pi_eq_minus_aD"]  # the test does discriminate the sign


def test_pi11_identity_and_a11():
    D = 11
    P = pi_ell.pi_matrix(D, 2)
    assert all(c.s == 0 and c.r == (1 if i == j else 0) for i, r in enumerate(P) for j, c in enumerate(r))
    mf = pi_ell.mf_side(D, 2)
    assert mf["eigenspaces"]["+"]["dim"] == 1 and mf["eigenspaces"]["-"]["dim"] == 0  # a_11(11a) = +1


def test_weight4_eigenvalues_are_plus_minus_D():
    # no extra normalising power: Pi has eigenvalues +-D = +-D^{(k-2)/2} = a_D(f) for k = 4
    r = pi_ell.compare(11, 4)
    assert r["brandt"]["eigenspaces"]["-"]["lambda"] == "-11" and r["mf"]["eigenspaces"]["-"]["dim"] == 2
