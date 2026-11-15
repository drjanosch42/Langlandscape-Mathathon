# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
import json, pathlib, sys
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import pytest
from py_reference import eis_module

T1 = json.load(open(HERE.parents[3] / "results/s03/T1.json"))["data"]


@pytest.mark.parametrize("q", [11, 23, 37, 101, 131])
def test_fixture_vs_T1(q):
    r = json.load(open(HERE / "fixtures" / f"q{q}.json"))
    assert r["schema"] == "langlandscape_brandt/v1"
    f = r["free_block_z"]; h = f["r"]; g = r["weights"]
    assert len(g) == h and len(f["F"]) == len(f["ops"])
    for p, flat in zip(f["ops"], f["F"]):
        F = [[int(flat[i * h + j]) for j in range(h)] for i in range(h)]
        assert all(sum(row) == p + 1 for row in F)                          # F * 1 = (p+1) 1
        assert all(g[j] * F[i][j] == g[i] * F[j][i] for i in range(h) for j in range(h))
    assert eis_module(g) == T1[str(q)]["num_q_minus_1_over_12"] == T1[str(q)]["phi_order"]
