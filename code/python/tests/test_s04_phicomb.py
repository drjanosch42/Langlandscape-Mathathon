# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-C5 (H7): Phi^comb (x) Z_5 = Z/5^{v_5|S_s|}, U_p^* = 5, e = 0, for B_11, B_23 (s <= 2)."""

import pytest

from langlandscape.ordinary import phicomb


@pytest.mark.parametrize("D,sizes", [(11, (10, 250)), (23, (22, 550))])
def test_h7(D, sizes):
    r = phicomb.run_case(D, 5, 2)
    assert r["h"] > 1
    for s, n in zip((1, 2), sizes):
        L = r["levels"][str(s)]
        assert L["size"] == n and L["order"] == n and L["cyclic"]
        assert L["v_p_size_ge_2s_minus_2"] and L["Up_star_acts_as_p"] and L["e_zero_on_phi_p"] and L["colsum_p"]
    assert r["levels"]["2"]["Up_commutes_pi"]
