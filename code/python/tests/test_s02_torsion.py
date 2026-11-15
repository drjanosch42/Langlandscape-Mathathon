"""S02-C4: torsion example D=2, q=3 (rem:s02-torsion). Computes in memory; JSON via torsion_s02.main."""

from fractions import Fraction as F

import pytest

from langlandscape import torsion_s02 as t


@pytest.fixture(scope="module")
def d():
    return t.compute()


def test_vertex_groups(d):
    assert d["class_number_S01"] == 1 and d["gamma_S01"] == [24]
    assert d["gamma_v0_order"] == d["gamma_v1_order"] == 24
    assert d["gamma_v_is_SL2F3"] is True
    assert d["gamma_v_abelianisation_order"] == [3, 3]


def test_edge(d):
    assert d["gamma_e_order"] == 6 and d["gamma_e_cyclic"] and d["one_edge_orbit"]
    assert F(d["mass_edge_Ge"]) == F(d["mass_edge_formula_(q+1)/24"]) == F(1, 6)
    assert F(d["mass_edge_Ge_mod_pm1"]) == F(1, 3)


def test_H1(d):
    assert d["H1_Gamma_U_Z_description"] == "Z/3" and d["matches_tex"] is True
