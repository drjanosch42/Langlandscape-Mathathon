# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S03-C5 tests: det(Psi*Psi) nonvanishing, normalisation table, Petersson ratios."""

from langlandscape import results
from langlandscape.ribet import betti


def test_normalisation_table_equals_tex():
    n = betti.NORMALISATION
    assert n["matrix"] == [["q+1", "-q^(2-k)*lambda"], ["-lambda", "q+1"]]
    assert n["q_2_minus_k_slot"] == "(1,2)"
    assert n["off_diagonal_assignment"] == "untested by PARI"


def test_small_cases():
    c = betti.case(11, 2, 2)  # S_2(11): T_2 = -2
    assert c["charpoly_Tq"] == [1, 2]
    assert c["norm_Dint"] == 9 - 4 == 5 and not c["det_vanishes"]
    assert c["level_raising_primes"] == [5]
    c = betti.case(1, 2, 2)  # S_2(1) = 0
    assert c is None
    c = betti.case(1, 3, 12)  # tau(3)=252: 3^10*16 - 252^2
    assert c["norm_Dint"] == 3 ** 10 * 16 - 252 ** 2


def test_committed_json_grid_nonvanishing():
    d = results.read("s03/betti_det.json")
    data = d["data"]
    assert data["normalisation"] == betti.NORMALISATION
    assert len(data["cases"]) > 100
    assert data["vanishing_triples_M_k_q"] == []
    for c in data["cases"]:
        assert c["norm_Dint"] != 0 and not c["det_vanishes"]
        assert c["q"] not in c["level_raising_primes"]
        assert c["M"] % c["q"] != 0 and c["k"] % 2 == 0
    assert all(p["match"] for p in data["petersson_check"])


def test_petersson_tiny():
    p = betti.petersson_check(11, 2, 2)
    assert p["match"]
