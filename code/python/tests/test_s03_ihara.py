"""S03-C4 / T6: ``thm:s03-iharaH0``, ``rem:s03-pm`` (exponent table), ``rem:s03-T6`` for ``B_3``, ``q = 2``, ``p in {5, 7}``.

Tests compute a subset in memory (one Hecke prime for the slow ``U_1(p)`` cases) and read the committed
``code/results/s03/T6.json``; they never write tracked files.
"""

import pytest

from langlandscape import results
from langlandscape.ribet import ihara as I


def _eps_ok(r):
    cc, ch = r["conventions"]["cohomological"], r["conventions"]["homological"]
    return (r["eps_well_defined"] and r["tau_transport"] and r["shapiro_equivariance"] and cc["tau0_2_ok"]
            and cc["ker_eps_eq_im_alpha"] and ch["ker_eps_eq_im_alpha"])


@pytest.fixture(scope="module")
def max_rows():
    return {(p, k): I.IharaCase(k, p, 2, "max").run() for p in I.PS for k in range(2, 2 * p + 1)}


def test_epsilon_max_level(max_rows):
    """thm:s03-iharaH0 (a): epsilon well defined, epsilon alpha = 0, onto, |coker alpha| = |V_{SL_2}| (so ker = im)."""
    for r in max_rows.values():
        assert _eps_ok(r), (r["p"], r["k"])
        assert r["H0"] == r["V_U1_coinvariants"] == r["conventions"]["homological"]["H0"]
        assert r["H0"] == r["stage02_LocalModel_H0"]  # agrees with stage 02's homological complex


def test_H0_zero_unless_p_minus_1_divides(max_rows):
    """Acceptance after NOTES M7.1: at U_p = GL_2(Z_p), H_0(Gamma_U, V_k) = 0 unless (p - 1) | (k - 2)."""
    for (p, k), r in max_rows.items():
        if (k - 2) % (p - 1):
            assert r["H0"] == [], (p, k)


def test_H0_vanishes_up_to_p_plus_1(max_rows):
    """rem:s03-T6 (a): H_0(Gamma_U, V_k) = 0 for 2 < k <= p + 1 at U_p = GL_2(Z_p); k = 2 gives Z/p^m."""
    for p in I.PS:
        assert max_rows[(p, 2)]["H0"] == [2]
        for k in range(3, p + 2):
            assert max_rows[(p, k)]["H0"] == [], (p, k)


def test_hecke_p3_to_2p_both_conventions(max_rows):
    """thm:s03-iharaH0 (b), exponent table: T_l = (1+l)[l] (cohomological), (1+l)[l]^{-1} (homological), p+3 <= k <= 2p.
    Original plan claim, kept: it holds, but by M7.1 it does not discriminate the two conventions at this level."""
    for p in I.PS:
        for k in range(p + 3, 2 * p + 1):
            r = max_rows[(p, k)]
            for l, row in r["conventions"]["cohomological"]["hecke"].items():
                assert row["T_preserves_im"] and row["acts_as_(1+l)[l]^+1"], (p, k, l)
            for l, row in r["conventions"]["homological"]["hecke"].items():
                assert row["T_preserves_im"] and row["acts_as_(1+l)[l]^-1"], (p, k, l)


def test_max_level_observed_structure(max_rows):
    """Observed (computed): in 3 <= k <= 2p the only non-zero H_0 is k = 2p, H_0 = Z/p, [l] = 1 there, so the two
    exponents agree on H_0 at maximal level (the sign is not observable there; see the U_1(p) test)."""
    for p in I.PS:
        nz = [k for k in range(3, 2 * p + 1) if max_rows[(p, k)]["H0"]]
        assert nz == [2 * p] and max_rows[(p, 2 * p)]["H0"] == [1]
        for row in max_rows[(p, 2 * p)]["conventions"]["cohomological"]["hecke"].values():
            assert row["diamond_l_scalar_on_H0"] == 1 and row["exponent_observed"] == "undetermined"


def test_hecke_matrices_vs_pari_mf(max_rows):
    """(R1) / rem:s03-pm: cohomological T_l = classical T_l on S_k(3)^new (charpoly mod p^m); homological = l^{2-k} T_l."""
    for r in max_rows.values():
        for h in r.get("hecke_vs_mf", {}).values():
            assert h["cohom_eq_mf"] and h["hom_eq_l^(2-k)mf"], (r["p"], r["k"])


def test_central_operator(max_rows):
    """M7.3 / exponent table: S_l = [l]^2 (cohomological) and [l]^{-2} (homological) on H_0; on the Brandt module S_l is the
    scalar l^{k-2} (classical, (R1)) resp. l^{2-k} (normative homological convention)."""
    for r in max_rows.values():
        for row in r["conventions"]["cohomological"]["hecke"].values():
            assert row["S_acts_as_[l]^+2"] and row["S_scalar_on_P"]
        for row in r["conventions"]["homological"]["hecke"].values():
            assert row["S_acts_as_[l]^-2"] and row["S_scalar_on_P"]


@pytest.mark.parametrize("p,k,ell", [(5, 7, 7), (5, 9, 13), (7, 9, 5), (7, 10, 11)])
def test_U1p_exponent_sign(p, k, ell):
    """U_1(p) (Shapiro): H_0 != 0 (rem:s03-T6 (b)); here [l] != [l]^{-1} on H_0 and the observed exponent is +1
    (cohomological) and -1 (homological), as in the exponent table."""
    r = I.IharaCase(k, p, 1, "U1p").run(ells=(ell,))
    assert _eps_ok(r) and r["H0"] != []
    cc = r["conventions"]["cohomological"]["hecke"][str(ell)]
    ch = r["conventions"]["homological"]["hecke"][str(ell)]
    assert cc["distinguishes"] and ch["distinguishes"]
    assert cc["exponent_observed"] == [1]
    assert ch["exponent_observed"] == [-1]
    assert cc["S_acts_as_[l]^+2"] and ch["S_acts_as_[l]^-2"]


def test_hecke_relation_and_central(max_rows):
    """S_l derived as T_{z_l} (one coset gamma = l) satisfies T_l^2 - T_{l^2} = l S_l on P, both conventions."""
    for r in max_rows.values():
        for name in ("cohomological", "homological"):
            assert r["conventions"][name]["hecke_relation_T_l^2-T_l2=lS_l"]["ok"], (r["p"], r["k"], name)


def test_U1p_hecke_vs_pari_mf():
    """U_1(p): charpoly of cohomological T_l on M(U_1(p); V_k) = classical T_l on 3-new forms of Gamma_0(3) cap Gamma_1(p)."""
    c = I.IharaCase(7, 5, 1, "U1p")
    h = c.hecke_vs_mf_U1p(7)
    assert h["cohom_eq_mf"] and h["rank_M"] == 12
    assert c.hecke_relation(7, True) and c.hecke_relation(7, False)


def test_U1p_m2_exponent():
    """The one U_1(p) case over Z/p^2 (p = 5, k = 7): exponent +1 cohomological, -1 homological for l = 7."""
    r = I.IharaCase(7, 5, 2, "U1p").run(ells=(7,))
    assert _eps_ok(r) and r["H0"]
    assert r["conventions"]["cohomological"]["hecke"]["7"]["exponent_observed"] == [1]
    assert r["conventions"]["homological"]["hecke"]["7"]["exponent_observed"] == [-1]


def test_uninformative_primes():
    """l = 11 at p = 5 ([l] = 1 mod p) and l = 13 at p = 7 (1 + l = 0 mod p) carry no sign information."""
    assert I.uninformative(11, 5) and I.uninformative(13, 7)
    assert not I.uninformative(7, 5) and not I.uninformative(13, 5) and not I.uninformative(5, 7)
    assert not I.uninformative(11, 7)


def test_shapiro_direct_small():
    """W_{SL_2} computed directly in W = V_k (x) Z[(Z/p)^2 - 0] equals V_{U_1(p)^1} (p = 5, k = 4, m = 1)."""
    W = I.Coeff(4, 5, 1, "U1p")
    gens = [((1, 1), (0, 1)), ((1, 0), (1, 1))]
    R = []
    for g in gens:
        for i in range(W.dim):
            e = [int(j == i) for j in range(W.dim)]
            R.append([(a - b) % 5 for a, b in zip(W.act(g, e), e)])
    assert I.structure(R, W.dim, 5, 1) == I.structure(W.coinv_relations(), W.d, 5, 1) == [1]


def test_committed_json():
    """The committed T6.json: all acceptance flags; exponent +1 cohomological / -1 homological where observable."""
    d = results.read("s03/T6.json")
    acc = d["data"]["acceptance"]
    for key in ("max_H0_zero_unless_(p-1)|(k-2)", "U1p_exponent_cases_distinguished", "U1p_exponent_cohom_+1_hom_-1",
                "S_l_cohom_[l]^2_hom_[l]^-2", "S_l_scalar_on_P_max", "H0_nonzero_U1p", "epsilon_checks",
                "exponent_distinguished_somewhere", "hecke_matches_mf",
                "original_H0_vanishes_3_le_k_le_p+1", "original_T_l_p+3_le_k_le_2p_holds_vacuous_or_nondiscriminating",
                "hecke_relation_ok", "hecke_matches_mf_U1p"):
        assert acc[key] is True, key
    assert acc["exponent_cohom_observed"] == [1] and acc["exponent_hom_observed"] == [-1]
    assert "M7.1" in d["data"]["acceptance_change"] and "M7.3" in d["data"]["acceptance_change"]
    assert d["provenance"]["script"] == "code/python/langlandscape/ribet/ihara.py"
