# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C2: T3 (B_3, q = 2, p = 5, mod 5^3), s <= 2 (s = 3 is in the committed result)."""

from langlandscape.ordinary import t3


def test_t3_small():
    d = t3.run(write=False, smax=2)
    L = d["levels"]
    for s, n in ((1, 2), (2, 50)):
        x = L[f"s{s}"]
        assert x["S_s"] == n and x["E_s"] == 3 * n and x["rk_H1"] == n + 1
        assert x["stage02_rk_H1"] == n + 1 and x["stage02_X_per_type"] == n
        assert x["ekills_a"]["deg_e_zero_mod_5^3"]
        assert x["ekills_d"]["pairing_gram_invertible_mod_5"]
        r = x["ribet"]
        assert r["identity_rk_eH1_eq_rkeZE_minus_2rkeZS"] and r["rank_Delta_identity"]
        assert r["e_alpha_image_rank_mod5"] == 2 * r["rk_e_ZS"]
    assert d["checks"]["rank_Delta_e_constant"]
