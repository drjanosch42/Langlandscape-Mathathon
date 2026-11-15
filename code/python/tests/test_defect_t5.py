# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06-C4 / C6 tests: T5 GL_2 side (``eta_f(q) = c_q(f) * eta_f(1, q)``, Thm E (iii)) and the T5 comparison."""

import json
import pathlib

import pytest

from langlandscape.defect import hecke_alg as ha
from langlandscape.defect import t5_gl2 as t5
from langlandscape.defect.congruence import Character, defect

RESULTS = pathlib.Path(__file__).resolve().parents[2] / "results" / "s06"


def _form(r):
    comps = [c for c in r["components"] if c["forms"]]
    assert len(comps) == 1, "exactly one maximal ideal of g carries a q-new form"
    assert len(comps[0]["forms"]) == 1
    return comps[0], comps[0]["forms"][0]


def test_triples_match_c5():
    """The seven T5 triples are those of the definite side (S06-C5, ``gram.TRIPLES``)."""
    gram = pytest.importorskip("langlandscape.defect.gram")
    assert tuple(t5.TRIPLES) == tuple(gram.TRIPLES)


def test_reduced_equals_full_13_12_31():
    """The reduction to ``W`` (exact) gives the same local invariants as the full algebra of ``S_12(Gamma_0(13))``."""
    q, k, p = 13, 12, 31
    r = t5.gl2_side(q, k, p)
    comp, f = _form(r)
    D = ha.mf_qnew_qold(q, k, q, ns=r["hecke_generators"])
    reps = {"new": D["new"], "old": D["old"]}
    reps.update({f"o{i}": o["rep"] for i, o in enumerate(D["orbits"])})
    T = ha.HeckeAlgebra(D["full"], reps)
    m = ha.find_maximal_ideal(T, p, {g: v for g, v in comp["m"]["values"].items()})
    found = []
    for i in range(len(D["orbits"])):
        chi = Character.from_rep(T, f"o{i}")
        try:
            chi.place(m)
        except ValueError:
            continue
        found.append(defect(T, chi, m))
    assert len(found) == 1
    assert found[0]["ord"] == f["ord"]
    assert found[0]["ranks"]["S_m"] == comp["ranks"]["S_m"] and found[0]["ranks"]["S_new_m"] == comp["ranks"]["S_new_m"]


@pytest.mark.parametrize("triple", t5.TRIPLES)
def test_weight_k(triple):
    """At weight ``k``: Thm E identity (proved; failure = bug), ``S_m`` Gorenstein, ``O_v`` a DVR,
    ``ord c_q(f) = t_f(q)`` (Cor. fixed), rank ``S_m = 2``, ``S'_m = 1`` (as on the definite side), ordinary."""
    r = t5.gl2_side(*triple)
    comp, f = _form(r)
    assert f["place"]["dvr"] and f["place"]["residue_degree"] == 1
    assert f["thm_E_identity"]
    assert f["gorenstein"]["S_m"]["gorenstein"]
    assert f["ord"]["eta"] == f["ord"]["c"] + f["ord"]["eta_new"]
    assert f["ord"]["c"] == r["t_f_q"] == 1
    assert comp["ranks"] == {"S_m": 2, "S_new_m": 1, "S_old_m": 1}
    assert comp["ordinary"] and comp["T_p_residue"] == r["a_p_g_mod_p"]


def test_shifted_weight_5_18_23():
    """At ``k + (p-1) = 40``: identity holds, ordinary component of the same ranks as at ``k`` (Hida control)."""
    r = t5.gl2_side(5, 18, 23, 40)
    comp, f = _form(r)
    assert f["thm_E_identity"] and comp["ordinary"]
    assert comp["ranks"] == {"S_m": 2, "S_new_m": 1, "S_old_m": 1}
    assert comp["T_p_residue"] == t5.level_one_eigenform(18, [23])[23] % 23


def test_result_file_gl2():
    """``T5_gl2.json``: provenance, every computed identity holds, weight-``k`` rows complete."""
    d = json.loads((RESULTS / "T5_gl2.json").read_text())
    assert d["provenance"]["script"].endswith("t5_gl2.py")
    assert d["data"]["all_thm_E_identities_hold"]
    assert set(d["data"]["triples"]) == {f"{q},{k},{p}" for q, k, p in t5.TRIPLES}
    for row in d["data"]["triples"].values():
        _, f = _form(row["k"])
        assert f["thm_E_identity"]
        s = row["k+p-1"]
        if "components" in s:
            for c in s["components"]:
                assert all(x.get("thm_E_identity", True) for x in c["forms"])
        else:
            assert s["status"] == "not computed" and s["reason"]


def test_result_file_comparison():
    """``T5.json`` (S06-C6): at weight ``k``, ``v_p(eta^B) = ord eta_f(1, q)`` and ``eta_f(q) = c_q(f) eta^B`` for all
    seven triples; ``k + (p-1)`` rows are "not computed" on the definite side, with a reason."""
    d = json.loads((RESULTS / "T5.json").read_text())
    assert d["data"]["all_ok_weight_k"]
    for row in d["data"]["triples"].values():
        assert row["k"]["etaB_eq_eta_new"] and row["k"]["identity_with_etaB"]
        assert row["k+p-1"]["status"] == "not computed" and row["k+p-1"]["reason"]
