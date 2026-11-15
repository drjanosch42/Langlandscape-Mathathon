"""Tests for S01-C6 phase 1 (``langlandscape.up_mf``): the modular-forms side of the U_p comparison."""

from fractions import Fraction

import pytest

from langlandscape import up_mf
from langlandscape.pari import get_pari


@pytest.fixture(scope="module")
def mf():
    return {s: up_mf.mf_side(s) for s in (1, 2)}


# ---------------------------------------------------------------- dimensions (first) ----------------------

@pytest.mark.parametrize("s", [1, 2])
def test_dimension_check(s):
    dims = up_mf.check_dimensions(s)
    assert dims["sum_3new"] == {1: 1, 2: 49}[s]
    assert 1 + dims["sum_3new"] == {1: 2, 2: 50}[s]


def test_dimension_tables():
    d1 = up_mf.dimensions(1)["per_orbit"]
    assert {k: v["dim_3new"] for k, v in d1.items()} == {"o1": 1, "o2": 0}
    d2 = up_mf.dimensions(2)["per_orbit"]
    assert {k: v["dim_3new"] for k, v in d2.items()} == {"o1": 5, "o2": 4, "o5": 24, "o10": 16}
    assert sum(v["dim_level"] for v in d2.values()) == 73      # genus of X(Gamma_0(3) cap Gamma_1(25))
    assert sum(v["dim_5power"] for v in d2.values()) == 12     # genus of X_1(25)


@pytest.mark.parametrize("s", [1, 2])
def test_3new_formula_vs_newspaces(s):
    """dim 3-new = sum_j (s-j+1) dim S_2^new(3*5^j, chi) over j with cond(chi) | 5^j (independent of the
    3-old subtraction)."""
    pari = get_pari()
    for c in up_mf.even_characters(s):
        tot = 0
        for j in range(0, s + 1):
            if (5 ** j) % c["conductor"]:
                continue
            N = 3 * 5 ** j
            a = int(pari.lift(pari.chinese(pari.Mod(c["conrey"], 5 ** j), pari.Mod(1, 3)))) if j else 1
            tot += (s - j + 1) * int(pari.mfdim(pari.mfinit([N, 2, pari.Mod(a, N)], 0)))
        assert tot == up_mf.dimensions(s)["per_char"][[x["conrey"] for x in up_mf.even_characters(s)]
                                                     .index(c["conrey"])]["dim_3new"]


# ---------------------------------------------------------------- sanity -----------------------------------

def test_15a_a5():
    """S_2(Gamma_0(15)) is 1-dim; U_5 = +1 there; cross-check with the elliptic curve 15a1 (split mult. at 5)."""
    pari = get_pari()
    mf15 = pari.mfinit([15, 2, 1], 1)
    assert int(pari.mfdim(mf15)) == 1
    assert pari.mfheckemat(mf15, 5)[0, 0] == 1
    E = pari.ellinit([1, 1, 1, -10, -10])
    assert int(pari.ellglobalred(E)[0]) == 15
    assert int(pari.ellap(E, 5)) == 1


def test_pari_character_convention():
    """PARI's Q(chi) = Q[t]/Phi_o has t = e(1/o): T_2^2 - T_4 = 2 chi(2) on S_2(25, chi)."""
    pari = get_pari()
    for c in up_mf.even_characters(2):
        mf = pari.mfinit([25, 2, pari.Mod(c["conrey"], 25)], 1)
        if int(pari.mfdim(mf)) == 0:
            continue
        T2, T4 = pari.mfheckemat(mf, 2), pari.mfheckemat(mf, 4)
        val = ((T2 * T2 - T4) / 2)[0, 0]
        o = c["order"]
        expected = pari.Mod(pari(f"'t^{int(c['chi2'] * o)}"), pari.polcyclo(o, "t"))
        assert pari.simplify(pari.lift(val - expected)) == 0


def test_P1(mf):
    assert mf[1]["P_s_factored"] == "(x - 5)*(x - 1)"
    assert mf[1]["P_s"] == [1, -6, 5]


def test_P2_structure(mf):
    pari = get_pari()
    r = mf[2]
    P2 = pari.Pol(r["P_s"], "x")
    assert int(pari.poldegree(P2)) == 50
    assert pari.divrem(P2, pari.Pol(mf[1]["P_s"], "x"))[1] == 0      # P_1 | P_2 (pi_* compatible)
    assert r["per_orbit"]["o1"]["charpoly_3new_Q_factored"] == "(x - 1)*x^4"
    assert r["per_orbit"]["o2"]["charpoly_3new_Q_factored"] == "x^4"
    # conductor-25 characters: all 3-new forms are 5-primitive, |a_5|^2 = 5
    for e in r["per_char"]:
        if e["conductor"] == 25:
            for re, im in e["a5_3new"]:
                assert abs(re * re + im * im - 5) < 1e-8


def test_inverse_is_conjugate(mf):
    for e in mf[2]["per_char"]:
        inv = next(x for x in mf[2]["per_char"] if x["conrey"] == e["inverse"])
        assert e["charpoly_3new_inverse_common"] == inv["charpoly_3new_common"]
        mine = sorted((round(a, 6), round(-b, 6)) for a, b in e["a5_3new"])
        theirs = sorted((round(a, 6), round(b, 6)) for a, b in inv["a5_3new"])
        assert mine == theirs


# ---------------------------------------------------------------- compare / compare_matrices -----------------

def test_compare_orbits(mf):
    for s in (1, 2):
        polys = {k: v.get("with_nrd", v["charpoly_3new_Q"]) for k, v in mf[s]["per_orbit"].items()}
        polys["total"] = mf[s]["P_s"]
        res = up_mf.compare(polys, s, mf=mf[s])
        assert res["all_match"], res
        assert res["matching_normalisation"].startswith("N_Up")
    # keys by Conrey label and by chi(2)
    res = up_mf.compare({4: mf[2]["per_orbit"]["o10"]["charpoly_3new_Q"],
                         Fraction(1, 5): mf[2]["per_orbit"]["o5"]["charpoly_3new_Q"],
                         "1/2": [1, 0, 0, 0, 0]}, 2, mf=mf[2])
    assert res["all_match"]
    bad = up_mf.compare({"o1": [1, -2, -15]}, 1, mf=mf[1])
    assert not bad["all_match"]


_KRON = """(M, C) -> my(d = #M, f = #C, ev = (p) -> my(q = lift(p)); if(type(q) == "t_POL", subst(q, 't, C), q * matid(f)));
  my(B = matrix(d, d, i, j, ev(M[i, j])));
  matrix(d * f, d * f, r, c, B[(r - 1) \\ f + 1, (c - 1) \\ f + 1][(r - 1) % f + 1, (c - 1) % f + 1])"""


def _synthetic_brandt(r):
    """Integer matrices (U, <2>) on Q^{|S_s|} realising the mf side with the "same" convention."""
    pari = get_pari()
    kron = pari(_KRON)
    blocks_U, blocks_D = [pari.matrix(1, 1, [5])], [pari.matrix(1, 1, [1])]
    seen = set()
    for e in r["per_char"]:
        if e["orbit"] in seen or e["dim_3new"] == 0:
            continue
        seen.add(e["orbit"])
        o = e["order"]
        Phi = pari.polcyclo(o, "t")
        Pnew = pari.Pol([pari.Mod(pari(c), Phi) for c in e["charpoly_3new_K"]], "x")
        Cmp = pari.matcompanion(Pnew)
        Co = pari.matcompanion(Phi) if o > 1 else pari.matrix(1, 1, [1])
        chi2 = pari.Mod(pari(f"'t^{int(e['chi2'] * o)}"), Phi)
        d = e["dim_3new"]
        blocks_U.append(kron(Cmp, Co))
        blocks_D.append(kron(chi2 * pari.matid(d), Co))
    U = pari.matconcat(pari.matdiagonal(blocks_U))
    Dm = pari.matconcat(pari.matdiagonal(blocks_D))
    return U, Dm


@pytest.mark.parametrize("s", [1, 2])
def test_compare_matrices_synthetic(mf, s):
    pari = get_pari()
    U, Dm = _synthetic_brandt(mf[s])
    assert int(pari.matsize(U)[0]) == {1: 2, 2: 50}[s]
    res = up_mf.compare_matrices(U, Dm, s, mf=mf[s])
    assert res["total_charpoly_matches_P_s"]
    assert res["consistent"] == ("both" if s == 1 else "same")
    res_inv = up_mf.compare_matrices(U, Dm ** -1, s, mf=mf[s])
    assert res_inv["consistent"] == ("both" if s == 1 else "inverse")


# ---------------------------------------------------------------- phase 2: Brandt side (S01-C5) -------------

@pytest.fixture(scope="module")
def brandt(mf):
    return {s: up_mf.brandt_comparison(s, mf=mf[s]) for s in (1, 2)}


@pytest.mark.parametrize("s", [1, 2])
def test_brandt_dimension_first(s):
    from langlandscape import up
    assert len(up.context(2).levels[s]) == 1 + up_mf.check_dimensions(s)["sum_3new"]


@pytest.mark.parametrize("s", [1, 2])
def test_brandt_total_charpoly(brandt, s):
    """charpoly(N_{U_p} | Q[S_s]) = P_s (and the same for U'_p = N_{U_p}^T)."""
    assert brandt[s]["details"]["N_Up"]["total_charpoly_matches_P_s"]
    assert brandt[s]["details"]["Up_prime"]["total_charpoly_matches_P_s"]


@pytest.mark.parametrize("s", [1, 2])
def test_R1_NUp_is_classical_Up(brandt, s):
    """Plan expectation (rem:s01-Upconv, def:s01-hecke): on the psi-eigenspace of the adelic <2>, N_{U_p}
    has the a_5 of S_2(3*5^s, psi^{-1})^{3-new}, also jointly with T_2.  Failure = R1 trigger."""
    r = brandt[s]
    assert r["R1_ok"], r["table"]
    for lab, row in r["table"].items():
        assert "inverse" in row["N_Up"] and "inverse" in row["N_Up_joint_T2"] and "inverse" in row["T2"]
        if s == 2 and lab not in ("1", "24"):          # non-real characters: the convention is visible
            assert row["N_Up"] == ["inverse"] and row["N_Up_joint_T2"] == ["inverse"]


def test_Up_prime_is_adjoint(brandt):
    """U'_p (= N_{U_p}^T) matches a_5 only with chi = psi (i.e. it is the adjoint U_5^*), and jointly
    with T_2 it matches neither convention: U'_p is not the classical U_5."""
    d = brandt[2]["details"]["Up_prime"]
    assert d["consistent"] == "same"
    assert d["consistent_T2"] == "inverse"
    assert d["consistent_joint"] is None
