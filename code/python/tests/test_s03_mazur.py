# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S03-C2 / T1: class sets, weights, Phi^comb of the DR graph, Eisenstein property."""

import pytest

from langlandscape.ribet import mazur

from langlandscape import results

# the full l <= 13 run (about 50 s) is stored in code/results/s03/T1.json; the fast test uses l <= 7 for q = 101, 131
FAST = {11: mazur.ELLS, 23: mazur.ELLS, 37: mazur.ELLS, 101: (2, 3, 5), 131: (2, 3, 5)}


def test_stored_json_full():
    d = results.read("s03/T1.json")["data"]
    for q in mazur.QS:
        r = d[str(q)]
        assert r["eisenstein_all"] and sorted(int(l) for l in r["eisenstein"]) == [l for l in mazur.ELLS if l != q]
        assert (r["h"], r["phi_order"]) == mazur.EXPECTED[q] and r["phi_cyclic"]


@pytest.mark.parametrize("q", mazur.QS)
def test_t1(q):
    r = mazur.t1_row(q, FAST[q])
    h, order = mazur.EXPECTED[q]
    assert r["h"] == h and r["phi_order"] == order and r["phi_order_ok"]
    assert r["phi_cyclic"] and r["mass_w_ok"] and r["mass_gamma_ok"]
    assert r["n2"] == (q % 4 == 3) and r["n3"] == (q % 3 == 2)
    assert r["eisenstein_all"] and len(r["eisenstein"]) == len([l for l in FAST[q] if l != q])


def test_eisenstein_negative():
    # a non-Eisenstein example: B = identity + shifted rows violating the structure
    assert not mazur.eisenstein_check([[1, 2], [1, 2]], [1, 1], 2)
