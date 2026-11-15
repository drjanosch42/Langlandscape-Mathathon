# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C3a: exactly one sign holds in U_p^* = <p>_M^{+-1} U'_p (D=2, M=7, p=5, s=1)."""

from langlandscape.ordinary import sign_pin


def test_sign_pin():
    d = sign_pin.run(write=False)
    c = d["checks"]
    assert c["U_p_star_eq_<p>_M_U'_p_mod_5^3"] != c["U_p_star_eq_<p>_M^-1_U'_p_mod_5^3"]
    assert d["sign"] == "+1"
    assert c["<p>_M_has_order"] == 6 and d["example"]["S_1_size"] == 48
