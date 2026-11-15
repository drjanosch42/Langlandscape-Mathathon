# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C3: H6 on D = 3, M = 1 (fast): failure of U'_p with pi_*, adjoint identity, e vs e*; (2,7) is in the committed result."""

from langlandscape.ordinary import h6


def test_h6_d3():
    c = h6.case(3, 1, "+1")
    h = c["s1"]["hida_d_s1_to_s2"]
    assert h["failure_witnessed"] and h["pi_Up_equals_Up_pi_integer"] and not h["pi_Uprime_equals_Uprime_pi_integer"]
    assert not h["pi_eprime_equals_eprime_pi_mod_5^3"] and h["pi_e_equals_e_pi_mod_5^3"]
    for s in ("s1", "s2"):
        assert c[s]["adjoint_identity_exact_integer"] and c[s]["adjoint_identity_mod_5^3"]
        assert c[s]["pairing_e_estar_gram_invertible_mod_5"] and c[s]["e_star_eq_e_transpose"]
    assert c["s2"]["e_ne_e_star"]
