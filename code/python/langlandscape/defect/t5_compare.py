# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06-C6 (T5 comparison): ``eta^B`` (definite side, S06-C5) against ``eta_f(1, q)`` (GL_2 side, S06-C4).

Tex: ``plan/staged/stage-06-integral-defect.tex``, computation H2 (T5): check ``eta_f(q) = c_q(f) * eta^B``.  Inputs are
the committed results ``code/results/s06/T5_def.json`` (``m.vp_etaB``, the Gram-determinant valuation at the rank-one
``q``-new block of ``m``) and ``code/results/s06/T5_gl2.json``.  Per triple and weight:

* ``etaB_eq_eta_new``: ``v_p(eta^B) == ord eta_f(1, q)`` (JL: ``eta^B`` is the congruence ideal of the ``q``-new
  algebra, ``if:s04-etaB``),
* ``identity_with_etaB``: ``ord eta_f(q) == ord c_q(f) + v_p(eta^B)``.

``eta^B`` exists only at weight ``k`` (C5 did not compute weight ``k + (p-1)``, where the pairing is not perfect), so
the ``k + (p-1)`` rows record ``"not computed"`` with the reason, together with the GL_2-side numbers where those exist.
Valuations are ``ord_varpi`` at a place of degree 1 and ramification 1 (checked in C4), so ``v_p = ord_varpi``.
Status: *computed* (comparison of computed numbers).
"""

from __future__ import annotations

import json

from .. import results

__all__ = ["compare", "main"]


def _gl2_form(w: dict):
    comps = [c for c in w.get("components", []) if c["forms"]]
    if len(comps) != 1 or len(comps[0]["forms"]) != 1:
        return None, None
    return comps[0], comps[0]["forms"][0]


def compare(defn: dict, gl2: dict) -> dict:
    rows = {}
    for key, g in gl2["triples"].items():
        dB = defn["triples"].get(key)
        row = {}
        comp, f = _gl2_form(g["k"])
        etaB = dB["m"]["vp_etaB"] if dB else None
        if f is None or etaB is None or len(etaB) != 1 or dB["m"]["rank"] != 1:
            row["k"] = {"status": "not computed", "reason": "no unique rank-one q-new block on one of the two sides"}
        else:
            o, place = f["ord"], f["place"]
            unr = place["residue_degree"] == 1 and str(place["ramification_index"]) == "1"
            row["k"] = {"weight": g["k"]["weight"], "vp_etaB": etaB[0], "ord_eta_new": o["eta_new"], "ord_eta": o["eta"],
                        "ord_c": o["c"], "t_f_q": g["k"].get("t_f_q"), "rank_new_definite": dB["m"]["rank"],
                        "rank_new_gl2": comp["ranks"]["S_new_m"], "dim_brandt": dB["dim_brandt"],
                        "dim_mf_new": g["k"]["dims"]["new"], "place_unramified_degree_1": unr,
                        "etaB_eq_eta_new": unr and etaB[0] == o["eta_new"],
                        "identity_with_etaB": unr and o["eta"] == o["c"] + etaB[0],
                        "ranks_agree": dB["m"]["rank"] == comp["ranks"]["S_new_m"],
                        "dims_agree": dB["dim_brandt"] == g["k"]["dims"]["new"]}
        s = g["k+p-1"]
        sc, sf = _gl2_form(s)
        srow = {"weight": s.get("weight"), "status": "not computed",
                "reason": "eta^B not computed at k+(p-1) (S06-C5 is weight k only; the Gram pairing is not perfect "
                          "there, Hida control instead)"}
        if sf is not None:
            srow["gl2_side"] = {"ord_eta": sf["ord"]["eta"], "ord_c": sf["ord"]["c"], "ord_eta_new": sf["ord"]["eta_new"],
                                "thm_E_identity": sf["thm_E_identity"], "ranks": sc["ranks"], "ordinary": sc["ordinary"]}
        else:
            srow["gl2_side"] = {"status": s.get("status", "not computed"), "reason": s.get("reason")}
        row["k+p-1"] = srow
        rows[key] = row
    ok = all(r["k"].get("etaB_eq_eta_new") and r["k"].get("identity_with_etaB") and r["k"].get("ranks_agree")
             and r["k"].get("dims_agree") for r in rows.values())
    return {"triples": rows, "all_ok_weight_k": ok}


def main() -> None:  # pragma: no cover - script entry point
    """Write ``code/results/s06/T5.json``."""
    root = results.repo_root() / "code" / "results" / "s06"
    with results.Timer() as tm:
        dB = json.loads((root / "T5_def.json").read_text())
        g = json.loads((root / "T5_gl2.json").read_text())
        data = compare(dB["data"], g["data"])
    data["inputs"] = {"T5_def.json": dB["provenance"]["commit"], "T5_gl2.json": g["provenance"]["commit"]}
    path = results.write("s06/T5.json", data, script="code/python/langlandscape/defect/t5_compare.py",
                         params={"inputs": ["code/results/s06/T5_def.json", "code/results/s06/T5_gl2.json"]},
                         runtime_s=round(tm.seconds, 3),
                         notes="S06-C6: T5 comparison eta^B (C5) vs eta_f(1,q) (C4); eta_f(q) = c_q(f) eta^B at k")
    print(path)


if __name__ == "__main__":  # pragma: no cover
    main()
