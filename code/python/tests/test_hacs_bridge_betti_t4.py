# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Tests for langlandscape.hacs_bridge.betti_t4 (HJ-A3 / S06-H1)."""

import pytest

from langlandscape.hacs_bridge import betti_t4 as b
from langlandscape.hacs_bridge import runner

L = 17
E = 6
Q = L ** E


def _mul(A, B):
    return b.mat_mul(A, B, Q)


def test_local_smith_toy_module():
    # Z_17^3 / diag(17, 17^2, 5) twisted by unimodular matrices: Z/17 + Z/17^2, length 3
    D = [[17, 0, 0], [0, 289, 0], [0, 0, 5]]
    U = [[1, 2, 3], [0, 1, 4], [0, 0, 1]]
    V = [[1, 0, 0], [7, 1, 0], [2, 5, 1]]
    M = _mul(_mul(U, D), V)
    vals = b.local_smith(M, L, E)
    mod = b.module_from_vals(vals, E)
    assert mod["elementary_divisor_valuations"] == [1, 2]
    assert mod["length"] == 3 and mod["unresolved_or_free"] == 0


def test_local_smith_free_part_and_rectangular():
    vals = b.local_smith([[17, 0], [0, 0], [0, 0]], L, E)
    assert sorted(vals) == [1, E]
    assert b.module_from_vals(vals, E)["unresolved_or_free"] == 1


def test_block_2x2_with_unit_diagonal_gives_det():
    # [[q+1, -t],[-c t, q+1]] on Z_17 (scalar T = t): coker = Z/17^{v(det)}; both conventions agree
    for t in (252, 1, 17 * 3 + 4):
        A, S = b.block_ops([[t]], pow(pow(3, 10, Q), -1, Q), 3, Q)
        va = b.module_from_vals(b.local_smith(A, L, E), E)
        vs = b.module_from_vals(b.local_smith(S, L, E), E)
        det = 16 * 3 ** 10 - t * t
        v = b.vl(det, L) if det % L == 0 else 0
        assert va["length"] == v == vs["length"]


def test_primary_idempotent_and_localisation():
    # T = diag(252, 252, 5) conjugated: e onto the 252-part has rank 2, localisation keeps only that part
    U = [[1, 1, 0], [0, 1, 1], [0, 0, 1]]
    Ui = [[1, Q - 1, 1], [0, 1, Q - 1], [0, 0, 1]]
    T = _mul(_mul(U, [[252, 0, 0], [0, 252, 0], [0, 0, 5]]), Ui)
    e, a = b.primary_idempotent(T, 252 % L, L, E)
    assert a == 2 and _mul(e, e) == e and b.rank_mod(e, L) == 2
    A, _ = b.block_ops(T, pow(pow(3, 10, Q), -1, Q), 3, Q)
    full = b.module_from_vals(b.local_smith(A, L, E), E)
    loc = b.module_from_vals(b.local_smith(b.localise(A, e, Q), L, E), E)
    assert loc["elementary_divisor_valuations"] == [1, 1]
    assert full["length"] >= loc["length"]


def test_ordinary_idempotent():
    T = [[10, 0], [0, 17]]                      # unit and non-unit eigenvalue
    e = b.ordinary_idempotent(T, L, E)
    assert e == [[1, 0], [0, 0]]


def test_hecke_side_k12():
    hk = b.hecke_side([1, -252], 12, E)
    assert hk["length"] == 1 and hk["branch_degree"] == 1


def test_hecke_side_branch_degree_gt1_is_open():
    # h = (x - 252)^2 - 17: ramified, irreducible over Q_17, reduces to (x - 252)^2 mod 17
    hk = b.hecke_side([1, -504, 252 * 252 - 17], 12, E)
    assert hk["branch_degree"] == 2 and hk["status"] == "open"


def test_module_z_off_by_default():
    assert "module_Z" not in b.hacs_module_script(10)
    assert "module_Z()" in b.hacs_module_script(10, allow_module_z=True)


def test_amalgam_level1_k28_hacs_free():
    am = b.amalgam_level1(28, E=E)
    r = b.betti_from_hecke_matrices(am["T"], 28, E)
    assert r["check_X_equals_T3"] and r["check_Y_equals_q^(2-k)X"]          # X = T_3, Y = 3^{-26} X
    assert r["check_omega_dg_1_equals_q+1"] and r["check_omega'_dg_q_equals_q+1"]
    assert r["coker_m"]["elementary_divisor_valuations"] == [1, 1]


def _have_hacs():
    try:
        runner.find_hacs()
        return True
    except runner.HacsNotFound:
        return False


@pytest.mark.skipif(not _have_hacs(), reason="no HACS binary")
def test_integration_k12():
    r = b.run_k(12)
    assert r["status"] == "computed"
    assert r["betti_hacs"]["status"] == "not_run" and r["betti_hacs"]["gating"] is False
    assert r["betti_amalgam"]["coker_m"]["elementary_divisor_valuations"] == [1, 1]
    assert r["hecke"]["length"] == 1
    assert r["agreement"]["task1c_(Z/17)^2"]
    assert all(v for kk, v in r["agreement"].items() if isinstance(v, bool))
    assert r["pending_crosscheck"] == "S06-C3"
