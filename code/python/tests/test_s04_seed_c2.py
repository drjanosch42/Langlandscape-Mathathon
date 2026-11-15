# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C4 (seed C2): rk e Z_5[X_1] = # ordinary 3-new weight-2 forms; diamonds match P^ad_k (k <= 6)."""

import pytest

from langlandscape.ordinary import seed_c2 as c2
from langlandscape.pari import get_pari


def test_rank_s1():
    A, W = c2.rank_s1(), c2.weight2_count()
    assert A["X1_size"] == 2 and A["deg_Up_eq_p"] and A["eisenstein_killed"]
    assert A["X1_size"] == W["dim_3new_total"] + 1  # Eisenstein line
    assert A["rank_e"] == W["ordinary_total"] == 1


def test_chi_value_convention():
    # PARI's t in mfinit is chi(2): conj of the T_2-charpoly equals the twist by chi(2)^-1 for t, not for -t
    pari = get_pari()
    for a in (7, 13):
        f = pari.charpoly(pari.mfheckemat(pari.mfinit([15, 3, pari.Mod(a, 15)], 0), 2))
        c0, c1 = c2.chi_value_2(a)
        n = int(pari.poldegree(f))
        res = []
        for sg in (1, -1):
            z = pari(f"Mod({c0}+{sg * c1}*t,t^2+1)")
            g = pari.subst(f, "x", pari("x") * z) / z**n
            res.append(pari.subst(pari.lift(f), "t", -pari("t")) == pari.lift(g))
        assert res == [True, False]


@pytest.mark.parametrize("s", [2, 3])
def test_diamonds_Pad(s):
    B = c2.diamond_test(s)
    assert B["all_match"] == {"Pad_k,chi^-1": True, "Pad_k,chi": False, "P_k,chi^-1": False, "P_k,chi": False}
    assert B["rank_e_Zq_Xs"] == 5 ** (s - 1)  # free of rank 1 over Z/5^s[Delta_s], one Teichmueller part
    ranks = {}
    for r in B["rows"]:
        ranks[r["k"]] = ranks.get(r["k"], 0) + r["mf_ord_rank"]
    assert ranks == {k: 1 for k in c2.KS}  # one Hida family: one ordinary form per weight
