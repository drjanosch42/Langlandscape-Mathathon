# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S03-C3 (T2): collapse of BG(Ohat^x, q) onto the two-vertex graph, Ribet exactness, alpha alpha^dagger."""

import pytest

from langlandscape.ribet import collapse as C

CASES = {(2, 7): (2, 1), (2, 13): (3, 2), (11, 2): (3, 0)}  # (D,q) -> (|X(U')|, rk H1)


@pytest.fixture(scope="module")
def data():
    return {k: C.collapse_case(*k) for k in CASES}


def test_counts_and_ranks(data):
    for k, (E, g) in CASES.items():
        d = data[k]
        assert d["n_edges_X_Uprime"] == E and d["rk_H1"] == g and d["rk_H1"] == E - 2 * d["X_per_type"] + 1
        assert all(d["lem_bip"].values())


def test_ribet_exact(data):
    for d in data.values():
        r = d["ribet_exact"]
        assert r["alpha_injective_mod_H1"] and r["coker_alpha_iso_Z"] and r["eps_kills_im_alpha"]
        assert r["coker_alpha_rank"] == 1 and r["coker_alpha_torsion_free"]


def test_sign_convention(data):
    """Sec. 0.2 item 4: alpha = (-s0*, s1*) => off-diagonal blocks of alpha alpha^dagger are -T_q; Ribet's sign gives +T_q."""
    for (D, q), d in data.items():
        s = d["sign_check"]
        assert s["diag_blocks_are_q_plus_1"] and s["offdiag_upper_is_minus_Hprime"]
        assert s["offdiag_lower_is_minus_HT"] and s["offdiag_entries_nonpositive"]
        X = d["X_per_type"]
        Mw, Mr = d["alpha_alphadag_weighted"]["matrix"], d["alpha_alphadag_weighted_RibetSign"]["matrix"]
        assert all(Mr[i][k] == (Mw[i][k] if (i < X) == (k < X) else -Mw[i][k]) for i in range(2 * X) for k in range(2 * X))
        assert all(Mr[i][k] >= 0 for i in range(2 * X) for k in range(2 * X))
        assert d["hecke"]["Hprime_equals_HT"]


def test_hecke_eigenvalues(data):
    assert data[(2, 7)]["T_q_eigenvalues"] == [8] and data[(2, 13)]["T_q_eigenvalues"] == [14]
    assert data[(11, 2)]["T_q_eigenvalues"] == [-2, 3]  # weighted T_2: Eisenstein 3 = q+1, cusp form 11a: a_2 = -2


def test_coker_and_five(data):
    d = data[(11, 2)]
    assert d["collapse_two_vertex_weights"] == [2, 1, 1] and d["phi_collapsed_order"] == 5  # 2+2+1
    assert d["cusp_det_q1sq_minus_lam_sq"] == [5]  # (q+1)^2 - (-2)^2
    # coker(alpha alpha^dagger) on Z[X]^2 = Z (Eisenstein) + torsion; the torsion is 3 (weighted) / 1 (unweighted), NOT 5
    w, u = d["alpha_alphadag_weighted"], d["alpha_alphadag_unweighted"]
    assert (w["free_rank"], w["torsion_order"]) == (1, 3) and (u["free_rank"], u["torsion_order"]) == (1, 1)
    assert w["index_on_ker_eps"] == 30 and u["index_on_ker_eps"] == 4
    for k in [(2, 7), (2, 13)]:
        assert data[k]["alpha_alphadag_weighted"]["torsion_order"] == data[k]["T_q_eigenvalues"][0]


def test_cuspidal_readings_b11(data):
    d = data[(11, 2)]
    w, u = d["alpha_alphadag_weighted"], d["alpha_alphadag_unweighted"]
    assert w["eisenstein_vector"] == [3, 2, 3, 2] and u["eisenstein_vector"] == [1, 1, 1, 1]
    assert (w["coker_on_quotient_by_Eis_saturation"], u["coker_on_quotient_by_Eis_saturation"]) == (30, 4)
    assert (w["coker_W_to_Wdual_order"], u["coker_W_to_Wdual_order"]) == (1800, 16)
    assert d["cusp_det_q1sq_minus_lam_sq"] == [5]
    assert "Z + Z/3" in d["acceptance_note"] and "prop:s03-LRdef" in d["acceptance_note"]
