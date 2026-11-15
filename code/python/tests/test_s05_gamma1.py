# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""T05-2 (S05-C2): sanity relations on Z[X_B(U_1(N))] and the dictionary verdict (prop:s05-sign(c),(d))."""

import numpy as np
import pytest

from langlandscape import levels, results
from langlandscape.comparison import gamma1 as G


@pytest.fixture(scope="module")
def X():
    return G.Gamma1Module(11, 7)


def test_class_set_matches_stage1(X):
    assert X.n == len(levels.XB(11, 7, 1)) == 20


def test_relations(X):
    q, N = X.q, X.N
    I = np.eye(X.n, dtype=np.int64)
    Pi = X.Pi()
    assert (Pi @ Pi == X.diamond(pow(q, -1, N))).all()  # eq. (s05-Sell): Pi_q^2 = <q>^-1 (adelic, homological)
    assert not (Pi @ Pi == X.diamond(q % N)).all()
    assert (X.diamond(N - 1) == I).all()  # -1 central: only even characters
    ops = [X.T(2), X.T(3), Pi, X.diamond(3)]
    for A in ops:
        for B in ops:
            assert (A @ B == B @ A).all()
    assert (X.T(2).sum(axis=0) == 3).all() and (X.T(3).sum(axis=0) == 4).all()
    assert (X.diamond(3) @ X.diamond(5) == I).all()  # 3 * 5 = 1 mod 7


def test_informative_criterion():
    assert G.informative(11, 7)["even_chi_with_chi_q_sq_ne_1"]
    assert not G.informative(13, 5)["even_chi_with_chi_q_sq_ne_1"]
    assert G.informative(13, 5)["plan_criterion"]


def test_verdict_11_7():
    pd = G.run_pair(11, 7)
    m = pd["match"]
    assert pd["dim_Z0"] == pd["dim_classical_qnew"] == 19
    assert pd["some_occurring_chi_q_ne_pm1"]
    assert m["delta=+1,e=+1"] and not m["delta=+1,e=+1,eps=-1"]
    assert not m["delta=+1,e=-1"] and not m["delta=-1,e=+1"]  # witnessed failure of Pi_q^-1
    assert m["Rosati (T->,<l>T, <d>-><d>, U_q->Pi^-1)"]  # prop:s05-AL: invisible at one level
    assert G.verdict(pd) == "CONFIRMED"


def test_json():
    d = results.read("s05/T05-2.json")["data"]
    assert d["verdict"] == "CONFIRMED"
    assert all(not v.startswith(("CONTRADICTION", "INCONCLUSIVE")) for v in d["verdict_per_pair"].values())
    for p in d["pairs"]:
        assert p["match"]["delta=+1,e=+1"] and p["dim_Z0"] == p["dim_classical_qnew"]
