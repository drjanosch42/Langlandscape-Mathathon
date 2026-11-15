# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-8: unit tests for the JL defect driver (pure algebra) and one small HACS cell (skipped without the binary)."""

import json
import pathlib
from fractions import Fraction as Fr

import flint
import pytest

from langlandscape.hacs_bridge import jl_defect as jd
from langlandscape.hacs_bridge import runner

HAVE = pathlib.Path(jd.HACS_DEFAULT).is_file()
needs_hacs = pytest.mark.skipif(not HAVE, reason="no HACS binary of record")


def test_sturm_and_generators():
    assert jd.sturm_bound(13, 18) == 21 and jd.sturm_bound(3, 18) == 6 and jd.sturm_bound(1, 12) == 1
    names, dropped = jd.generators(13, 16, 101)
    assert 13 not in names and dropped == [101] and names == [2, 3, 5, 7, 11, 17, 19]
    names, dropped = jd.generators(3, 18, 53)
    assert names == [2, 5, 7, 53] and dropped == []


def test_batches_respect_hacs_caps():
    ps = jd.primes_upto(47)
    bs = jd.batches(ps)
    assert sorted(x for b in bs for x in b) == ps
    assert all(len(b) <= 6 and sum(b) <= 100 for b in bs)
    with pytest.raises(ValueError):
        jd.batches([101])


def test_sign_solutions():
    assert jd.sign_solutions([1, 2], 2) == [(-1, 1)]
    assert sorted(jd.sign_solutions([1, 1], 1)) == [(-1, 1), (1, -1)]
    assert jd.sign_solutions([3], 0) == [(-1,)]
    assert jd.sign_solutions([2, 2], 1) == []


def test_lattice_rep_new_and_old_toys():
    q, kk = 3, 4
    # new orbit K = Q(sqrt 5), T_2 = (1 + sqrt 5)/2 is integral but not in Z[sqrt 5]: lattice must contain it
    new = {"kind": "new", "phi": flint.fmpz_poly([-5, 0, 1]), "eps": -1,
           "evals": {2: [Fr(1, 2), Fr(1, 2)]}}
    L = jd.lattice_rep(new, [2], q, kk)
    T2, U = flint.fmpz_mat(L["T2"]), flint.fmpz_mat(L["T3"])
    assert T2 * T2 - T2 == flint.fmpz_mat([[1, 0], [0, 1]])          # x^2 - x - 1 = 0
    assert U == flint.fmpz_mat([[-3, 0], [0, -3]])                   # a_q = -q^{(kk-2)/2}
    # old orbit (rational g): U_q with U^2 - a_q(g) U + q^{kk-1} = 0, T_2 scalar
    old = {"kind": "old", "phi": flint.fmpz_poly([-7, 1]), "evals": {2: [Fr(7)], 3: [Fr(4)]}}
    L = jd.lattice_rep(old, [2], q, kk)
    T2, U = flint.fmpz_mat(L["T2"]), flint.fmpz_mat(L["T3"])
    one = flint.fmpz_mat([[1, 0], [0, 1]])
    assert T2 == one * 7 and U * U - U * 4 + one * 27 == flint.fmpz_mat(2, 2)


def test_krylov_polys_detects_non_separating_operator():
    A = flint.fmpz_mat([[1, 0], [0, 1]])                              # A scalar, T not a polynomial in A
    T = flint.fmpz_mat([[1, 0], [0, 2]])
    with pytest.raises(ArithmeticError):
        jd.krylov_polys(A, {2: T}, flint.fmpz_poly([-1, 1]), 2)
    T = flint.fmpz_mat([[3, 0], [0, 3]])
    assert jd.krylov_polys(A, {2: T}, flint.fmpz_poly([-1, 1]), 2) == {2: [Fr(3)]}


def test_compare_row_identity():
    g = {"weight": 12, "status": "computed", "t_f_q": 1, "sign_robust": True, "dims": {"new": 11},
         "components": [{"forms": [{"status": "computed", "ord": {"eta": 1, "c": 1, "eta_new": 0},
                                    "thm_E_identity": True, "gorenstein": {"S_m": {"gorenstein": True}},
                                    "a_q_sign": 1, "place": {}}],
                         "ranks": {"S_m": 2, "S_new_m": 1, "S_old_m": 1}, "ordinary": True, "U_q_residue": 3}]}
    dB = {"m": {"rank": 1, "vp_etaB": [0]}, "dim_brandt": 11}
    r = jd.compare_row(g, dB, None)
    assert r["identity_with_etaB"] and r["etaB_eq_eta_new"] and r["status"] == "computed"
    r = jd.compare_row(g, None, None)
    assert r["vp_etaB"] is None and r["etaB_status"] == "open"


@needs_hacs
def test_hacs_cell_13_12_31():
    """T5 triple (13, 12, 31) at weight 12 through HACS (about 10 s): eta = c = 1, eta_new = 0 (S06-C4/C6)."""
    g = jd.gl2_cell(13, 12, 31, hacs=jd.HACS_DEFAULT, threads=4)
    comp, f = jd._gl2_form(g)
    assert g["status"] == "computed"
    assert {k: f["ord"][k] for k in ("eta", "c", "eta_new")} == {"eta": 1, "c": 1, "eta_new": 0}
    assert comp["ranks"] == {"S_m": 2, "S_new_m": 1, "S_old_m": 1} and f["thm_E_identity"]
    assert g["hacs"]["L_q"]["saturation"] == "det_pm1" and g["t_f_q"] == 1
    assert runner.hacs_sha256(jd.HACS_DEFAULT)


def test_abstract_hecke_matches_matrix_algebra_toy():
    """The abstract order Z[gens]*1 in prod K_s equals the S06-C4 matrix closure on a toy (one old, one new orbit)."""
    from langlandscape.defect import hecke_alg as ha
    from langlandscape.defect.congruence import Character, defect, place_info
    from langlandscape.defect.t5_gl2 import _matching_ideals
    q, kk, p = 3, 4, 5
    # new f: a_2 = 2, a_3 = +3; old g: a_2 = 7, a_3(g) = 7, so y^2 - 7y + 27 has the root 3 mod 5: f, g congruent mod 5
    new = {"kind": "new", "phi": flint.fmpz_poly([-2, 1]), "eps": 1, "evals": {2: [Fr(2)]}}
    old = {"kind": "old", "phi": flint.fmpz_poly([-7, 1]), "evals": {2: [Fr(7)], 3: [Fr(7)]}}
    kept = [{"sys": old}, {"sys": new}]
    res = {2: 2}
    a = jd._defects_on(kept, [2], q, kk, p, res, ha, Character, defect, place_info, _matching_ideals, True)
    b = jd._defects_on(kept, [2], q, kk, p, res, ha, Character, defect, place_info, _matching_ideals, False)
    strip = lambda comps: [[(f["ord"]["eta"], f["ord"]["c"], f["ord"]["eta_new"]) for f in c["forms"]] for c in comps]
    assert strip(a["components"]) == strip(b["components"])          # m_alpha (with f) and m_beta (old only)
    assert sorted(strip(a["components"])) == [[], [(1, 1, 0)]]
    assert [c["ranks"] for c in a["components"] if c["forms"]] == [{"S_m": 2, "S_new_m": 1, "S_old_m": 1}]


def test_local_route_matches_matrix_algebra_toy():
    """The default local p-adic route gives the same (eta, c, eta_new) and ranks as the S06-C4 matrix closure (toy)."""
    from langlandscape.defect import hecke_alg as ha
    from langlandscape.defect.congruence import Character, defect, place_info
    from langlandscape.defect.t5_gl2 import _matching_ideals
    q, kk, p = 3, 4, 5
    new = {"kind": "new", "phi": flint.fmpz_poly([-2, 1]), "eps": 1, "evals": {2: [Fr(2)]}}
    old = {"kind": "old", "phi": flint.fmpz_poly([-7, 1]), "evals": {2: [Fr(7)], 3: [Fr(7)]}}
    kept = [{"sys": old}, {"sys": new}]
    args = (kept, [2], q, kk, p, {2: 2}, ha, Character, defect, place_info, _matching_ideals)
    a = jd._defects_on(*args, True)
    b = jd._defects_local(*args)
    key = lambda comps: sorted((json.dumps(c["ranks"], sort_keys=True),
                                [(f["ord"]["eta"], f["ord"]["c"], f["ord"]["eta_new"]) for f in c["forms"]])
                               for c in comps if c["forms"])
    assert key(a["components"]) == key(b["components"]) == [('{"S_m": 2, "S_new_m": 1, "S_old_m": 1}', [(1, 1, 0)])]


def _blk(res, rank=1, vps=(0,), old=None, deg=1):
    return {"m_id": {str(l): f"x + {(-v) % 7}" for l, v in res.items()}, "residual_eigenvalues": res, "rank": rank,
            "n_orbits": len(vps), "old_congruent": old,
            "orbits": [{"degree": deg, "resolved_Qp_orbit": True, "vp_etaB": v} for v in vps]}


def _g(forms, ranks, status="computed", t=None):
    return {"status": status, "sign_robust": True, "t_f_q": t,
            "components": [{"ranks": ranks, "U_q_residue": 1, "T_p_residue": 1,
                            "forms": [{"status": "computed", "ord": {"eta": e, "c": c, "eta_new": n},
                                       "thm_E_identity": e == c + n, "gorenstein": {"S_m": {"gorenstein": True}},
                                       "orbit_degree": 1, "a_q_sign": 1} for e, c, n in forms]}]}


def test_compare_block_old_congruent_and_genuine():
    r = jd.compare_block(_g([(1, 1, 0)], {"S_m": 2, "S_new_m": 1, "S_old_m": 1}, t=1), _blk({2: 3}, old=True))
    assert r["status"] == "computed" and r["agree"] and r["checks"]["ord_c_eq_t_f_q"] and r["ord_c_minus_t_f_q"] == 0
    # genuine congruence of two new forms: eta^B = p for both orbits, eta = eta_new = 1, c = 0
    r = jd.compare_block(_g([(1, 0, 1), (1, 0, 1)], {"S_m": 2, "S_new_m": 2, "S_old_m": 0}),
                         _blk({2: 3}, rank=2, vps=(1, 1)))
    assert r["agree"] and r["checks"]["etaB_multiset_eq_eta_new"] and "identity_with_etaB" not in r["checks"]
    # a disagreement is reported, not hidden
    r = jd.compare_block(_g([(1, 0, 1), (0, 0, 0)], {"S_m": 2, "S_new_m": 2, "S_old_m": 0}),
                         _blk({2: 3}, rank=2, vps=(1, 1)))
    assert r["status"] == "computed" and not r["agree"]
    # GL_2 side open -> block open with a reason
    r = jd.compare_block(_g([(1, 1, 0)], {"S_m": 2, "S_new_m": 1, "S_old_m": 1}, status="open"), _blk({2: 3}))
    assert r["status"] == "open" and r["reason"]


def test_census_cells_selection_and_degree_one_blocks():
    b1, b2, b3 = _blk({2: 1}, old=True), _blk({2: 2}, rank=2, vps=(1, 1)), _blk({2: 4})
    b4 = dict(_blk({2: 5}), residual_eigenvalues=None)
    native = {"census": {"cells": [{"q": 5, "k": 8, "p": 19, "blocks": [b1, b3]},
                                   {"q": 3, "k": 6, "p": 7, "blocks": [b2, b4]}],
                         "classification": {"genuine_congruence": [{"q": 3, "k": 6, "p": 7, "m_id": b2["m_id"]}],
                                            "old_congruent": [{"q": 5, "k": 8, "p": 19, "m_id": b1["m_id"]}]}}}
    cells = jd.census_cells(native)
    assert [(c["q"], c["k"], c["p"]) for c in cells] == [(3, 6, 7), (5, 8, 19)]       # genuine first
    assert [b["census_class"] for c in cells for b in c["blocks"]] == ["genuine_congruence", "old_congruent"]
    one, other = jd.degree_one_blocks({"blocks": [b2, b4]})
    assert one == [b2] and other == [b4]


def test_ramified_filter_does_not_raise_on_missing_generators():
    """Review m1: residues for generators without eigenvalue data are skipped, never a KeyError."""
    s = {"kind": "new", "phi": flint.fmpz_poly([-5, 0, 1]), "eps": 1, "evals": {2: [Fr(0), Fr(1)]}}
    # p = 5 ramifies in Q(sqrt 5); residue of T_2 = sqrt 5 is 0: resid T2 = 1 -> not in m (no refusal), T7 unknown
    assert jd.local_places([s], [2], 3, 4, 5, 20, {"T2": 1, "T7": 3}) == []
    with pytest.raises(jd.Refused):
        jd.local_places([s], [2], 3, 4, 5, 20, {"T2": 0})


def test_pari_newform_sign_oracle_19_6():
    """Team-lead source (b): the sign of a_q(f) from PARI's newforms, matched by the T_2 charpoly (no HACS, no
    definite side).  S_6^new(Gamma_0(19)): a_2 = -2 has a_19 = -361, a_2 = -6 has a_19 = +361."""
    from langlandscape.pari import get_pari
    get_pari()
    o1 = {"phi": flint.fmpz_poly([2, 1]), "evals": {2: [Fr(-2)]}}
    o2 = {"phi": flint.fmpz_poly([6, 1]), "evals": {2: [Fr(-6)]}}
    assert jd.pari_newform_signs(19, 6, [o1, o2], [2]) == [-1, 1]
    # an orbit that matches no PARI orbit: no answer (never a guess)
    o3 = {"phi": flint.fmpz_poly([5, 1]), "evals": {2: [Fr(-5)]}}
    assert jd.pari_newform_signs(19, 6, [o3], [2]) is None


@needs_hacs
def test_etale_route_h3_13_4_7():
    """Review HJ-8b m6: the residue-degree-2 block of (q, k, p) = (13, 4, 7) through HACS (about 1 s): one unramified
    new place of degree 2 meets m, so S_m = O_v and eta = c = eta_new = (1); the rank is the GL_2 side's own."""
    blk = {"m_id": {"2": "x^2 + 6*x + 3", "3": "x^2 + 2*x + 3", "5": "x^2 + 3*x + 5", "7": "x^2 + 2*x + 3",
                    "11": "x^2 + 4*x + 1"}, "rank": 2, "n_orbits": 1}
    gl = jd.gl2_block_unramified(13, 4, 7, blk, {}, jd.HACS_DEFAULT, threads=2)
    assert gl["status"] == "computed" and gl["ranks"] == {"S_m": 2, "S_new_m": 2, "S_old_m": 0}
    assert gl["places_matching_m"] == [{"kind": "new", "orbit_degree": 2, "place_degree": 2, "e": 1}]
    # a residual system no place carries: open, never (1) by default
    bad = dict(blk, m_id=dict(blk["m_id"], **{"2": "x^2 + 1"}))
    assert jd.gl2_block_unramified(13, 4, 7, bad, {}, jd.HACS_DEFAULT, threads=2)["status"] == "open"
