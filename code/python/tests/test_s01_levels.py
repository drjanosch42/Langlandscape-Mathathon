"""S01-C2: class sets at U_0(M), U_1(N), U_0(q)U; mass level change; the p-tower S_s (does not write results)."""

from fractions import Fraction

import pytest

from langlandscape import levels as L

DS = [2, 3, 5, 7, 11, 13]


def test_tower_sizes_D3_p5():
    T = L.Tower(3, 5, 3)
    assert [T.size(s) for s in (1, 2, 3)] == [2, 50, 1250]
    for s in (1, 2, 3):
        assert T.size(s) == L.expected_Sizes(3, 5, s)


def test_u1_5_D2_single_point():
    assert len(L.XB(2, 5, 1)) == 1


@pytest.mark.parametrize("D", DS)
@pytest.mark.parametrize("p", [5, 7, 11])
def test_all_gamma_trivial_at_u1p(D, p):
    if D % p == 0:
        pytest.skip("p | D")
    X = L.XB(D, p, 1)
    assert X.gamma_multiset == [1] * len(X)
    assert Fraction(len(X)) == L.expected_Sizes(D, p, 1)  # thm:s01-mass(d)


def test_delta_acts_freely_and_projections():
    T = L.Tower(3, 5, 3)
    for s in (1, 2, 3):
        assert T.delta_free(s)
    # Delta_s is a group of order p^{s-1} acting through (1+pZ)/(1+p^sZ); d = 1 mod p^s acts trivially
    for s in (2, 3):
        n = T.size(s)
        assert T.diamond(s, 1) == list(range(n))
        pr = T.projection(s)
        assert len(set(pr)) == T.size(s - 1)  # surjective
        fibres = {}
        for j, t in enumerate(pr):
            fibres.setdefault(t, 0)
            fibres[t] += 1
        assert set(fibres.values()) == {25 if s == 3 else 25}  # [U_{s-1}:U_s] = p^2
        # diamond with d = 1 mod p^{s-1} preserves the fibres of the projection
        d = 1 + 5 ** (s - 1)
        dm = T.diamond(s, d)
        assert all(pr[dm[j]] == pr[j] for j in range(n))


def test_diamond_group_law():
    T = L.Tower(3, 5, 2)
    a, b = T.diamond(2, 6), T.diamond(2, 11)
    ab = T.diamond(2, (6 * 11) % 25)
    assert [a[b[j]] for j in range(len(a))] == ab


def test_mass_ex_checks():
    X = L.XB(2, 1, 1)
    assert X.mass == Fraction(1, 24) and X.massW == Fraction(1, 12)
    X = L.XB(3, 1, 1)
    assert X.mass == Fraction(1, 12)
    X = L.XB(11, 1, 1)
    assert X.gamma_multiset == [4, 6] and X.mass == Fraction(10, 24)


@pytest.mark.parametrize("D,N", [(2, 3), (2, 5), (3, 7), (5, 6), (7, 4), (11, 9), (13, 15), (3, 25)])
def test_mass_U0_formula(D, N):
    """thm:s01-mass(c),(d): sum 1/w_x = phi(D) psi(N)/12 at U_0(N) (-1 in U), and |Gamma| version."""
    X = L.XB(D, 1, N)
    assert X.index == L.psi_fn(N)
    assert X.massW == Fraction(L.phi_fn(D) * L.psi_fn(N), 12)
    assert X.mass == Fraction(L.phi_fn(D) * L.psi_fn(N), 24)


@pytest.mark.parametrize("D,N", [(2, 5), (3, 5), (3, 7), (5, 4), (7, 3), (11, 13), (2, 15)])
def test_mass_U1_formula(D, N):
    X = L.XB(D, N, 1)
    assert X.index == L.psi_fn(N) * L.phi_fn(N)
    assert X.mass == Fraction(L.phi_fn(D), 24) * X.index
    assert X.massW == X.mass  # -1 not in U_1(N), N >= 3: w = |Gamma|


MASS_CASES = [
    (2, (1, 1), (1, 3)), (2, (1, 1), (5, 1)), (2, (1, 3), (5, 3)), (3, (1, 1), (1, 7)), (3, (1, 5), (5, 1)),
    (3, (7, 1), (7, 5)), (3, (7, 1), (35, 1)), (5, (1, 7), (7, 1)), (7, (1, 1), (4, 1)), (11, (1, 1), (3, 1)),
    (11, (1, 1), (1, 2)), (3, (1, 4), (5, 4)), (2, (3, 1), (3, 5)), (11, (3, 1), (3, 2)), (3, (1, 1), (2, 1)),
]


@pytest.mark.parametrize("D,U,Up", MASS_CASES)
def test_mass_level_change_both_conventions(D, U, Up):
    r = L.mass_check(D, U, Up)
    assert r["ok_full"], r  # sum 1/|Gamma'| = [U:U'] sum 1/|Gamma|
    assert r["ok_w"], r     # with w: extra factor 2 iff -1 in U \ U'
    # explicit statement of the two cases
    f = 2 if r["factor_two"] else 1
    assert f * r["massW_Up"] == r["index"] * r["massW_U"]


def test_factor_two_case_occurs_and_is_needed():
    r = L.mass_check(3, (1, 1), (5, 1))  # -1 in U = Ohat^x, not in U_1(5)
    assert r["factor_two"]
    assert r["massW_Up"] != r["index"] * r["massW_U"]  # the naive w-formula fails
    assert 2 * r["massW_Up"] == r["index"] * r["massW_U"]
    r = L.mass_check(3, (7, 1), (7, 5))  # -1 not in U: no factor
    assert not r["factor_two"] and r["massW_Up"] == r["index"] * r["massW_U"]
