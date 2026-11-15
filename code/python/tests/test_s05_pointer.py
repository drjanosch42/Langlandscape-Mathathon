# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S05-C3 / T05-3: (X2) at Gamma_0-level is a pointer to stage-03 T1 (|Phi^comb| = num((q-1)/12))."""

import pytest

from langlandscape import results
from langlandscape.comparison import pointer_s03

QS = pointer_s03.QS


@pytest.mark.parametrize("q", QS)
def test_value_equals_stage03(q):
    stage3 = results.read("s03/T1.json")["data"][str(q)]
    s5 = results.read("s05/T05-3.json")["data"][str(q)]
    assert s5["phi_order_stage03"] == stage3["phi_order"]
    assert s5["phi_divisors_stage03"] == stage3["phi_divisors"]
    assert s5["phi_cyclic_stage03"] == stage3["phi_cyclic"]
    assert s5["h"] == stage3["h"]


@pytest.mark.parametrize("q", QS)
def test_value_equals_mazur_num(q):
    s5 = results.read("s05/T05-3.json")["data"][str(q)]
    assert s5["num_q_minus_1_over_12"] == pointer_s03.num_q_minus_1_over_12(q)
    assert s5["phi_order_stage03"] == pointer_s03.num_q_minus_1_over_12(q)
    assert s5["equal"] is True


def test_known_values():
    expected = {11: 5, 23: 11, 37: 3, 101: 25, 131: 65}
    assert {q: pointer_s03.num_q_minus_1_over_12(q) for q in QS} == expected
