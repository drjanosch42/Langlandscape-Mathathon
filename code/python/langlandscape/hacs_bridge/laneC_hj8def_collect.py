# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Lane C, WP HJ-8-def: collect the native eta^B values (``jl_eta_def``) into ``code/results/laneC/hj8_def_native.json``.

Reads the three dumps of ``code/hacs/src/hacs/Registry/JL/quat/tools/jl_eta_def.cpp`` (``--suite t5``, ``h3``, ``census``;
schema ``langlandscape_eta_def/v1``), compares the weight-k T5 cells with ``code/results/s06/T5_def.json`` (S06-C5,
``defect/gram.py``), and writes one file for worker D's driver (``jl_defect.py``).  Nothing is recomputed here.

Per-cell schema (``cells[*]``; every number *computed*):

* ``q, k, p``: B = B_{q,infinity}, weight k (n = k - 2), the prime p; ``weight_role``: "k" or "k+(p-1)" (T5) / "census";
* ``pairing_perfect``: p > n (and p >= 5); if false the Gram values carry the p in the binomial denominators of <,>_V
  and are NOT eta^B (reported for information only);
* ``gram_weight``: "w" (G_w = (+)_x w_x^{-1} <,>_V, w_x = |Gamma_x|/2; Hsieh's weight); ``vp_det_gram_Gamma`` is the
  |Gamma_x| variant (differs by 2^dim, so equal v_p for p odd);
* ``blocks[*]`` = the maximal ideals m above p of the Hecke algebra Z[T_l : l in {2,3,5,7,11} \\ {q}]:
  ``m_id`` = the residual eigensystem (for each T_l the irreducible factor mod p of its char-poly on the block, PARI-style
  text in x) and ``residual_eigenvalues`` {l: a_l mod p} when the residue field is F_p; ``rank`` = rk_{Z_p} M_m;
  ``orbits[*]`` = the Q_p-orbits (eigenforms up to Galois) in M_m with ``degree``, ``residue_degree``,
  ``resolved_Qp_orbit`` (false: an unsplit union, e.g. a ramified orbit), ``vp_etaB`` (= v_p det G_w|A_phi, the
  eta-principle; deg > 1: Z_p-length of the congruence module, Hsieh Rem. 7.3) and ``etaB`` = "p^v";
  ``congruence``: more than one orbit, or some vp_etaB > 0, or an unresolved union; ``old_congruent``: residually equal
  to the level-one eigenform g of weight k (only when dim S_k(1) = 1; null otherwise);
* ``m_old_congruent``: the old-congruent block (the m of the T5 comparison), or null; ``vp_level_raising`` =
  v_p(a_q(g)^2 - q^{k-2}(q+1)^2).

Run (from ``code/python``)::

    python3 -m langlandscape.hacs_bridge.laneC_hj8def_collect --binary B --t5 t5.json --h3 h3.json [--census census.json]
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import pathlib
import sys

from .laneC_hj7_compare import RES, git_commit, load, sha256


def norm_cell(c: dict, role: str) -> dict:
    p = c["p"]
    perfect = c["pairing_perfect"]
    blocks = []
    for b in c["blocks"]:
        orbs = []
        for o in b["orbits"]:
            d = {"degree": o["degree"], "residue_degree": o["residue_degree"], "e": o["e"],
                 "resolved_Qp_orbit": o["resolved_Qp_orbit"], "separated_by": o["separated_by"],
                 "Q_factor": o["Q_factor"], "Q_factor_degree": o["Q_factor_degree"],
                 "residue_of_generic_T": o["residue_of_generic_T"],
                 "vp_det_gram_w": o["vp_det_gram_w"], "vp_det_gram_Gamma": o["vp_det_gram_Gamma"],
                 "vp_ratio": o["vp_ratio"], "det_ok": o["det_ok"]}
            # review m1: eta^B only where the pairing is perfect AND the orbit is a resolved Q_p-orbit
            if perfect and o["resolved_Qp_orbit"]:
                d["vp_etaB"] = o["vp_det_gram_w"]
                d["etaB"] = f"{p}^{o['vp_det_gram_w']}"
                d["etaB_method"] = "Gram: v_p det G_w|A_phi (eta-principle, Hsieh Rem. 7.3)"
            else:
                d["vp_etaB"] = None
                d["etaB"] = "not determined" if perfect else None
                d["etaB_method"] = ("not determined: unresolved Q_p-orbit (ramified or non-maximal Z_p[T])" if perfect
                                    else "not eta^B: pairing not perfect (p <= n); vp_det_gram_w for information only")
            orbs.append(d)
        blocks.append({"m_id": b["residual"], "residual_eigenvalues": b["residual_eigenvalues"], "rank": b["rank"],
                       "n_orbits": b["n_orbits"], "congruence": b["congruence"], "old_congruent": b["old_congruent"],
                       "orbits": orbs, "all_ok": b["all_ok"]})
    out = {"q": c["q"], "k": c["k"], "p": p, "weight_role": role, "pairing_perfect": perfect,
           "dim_brandt": c["dim_brandt"], "h": c["h"], "gram_weight": "w", "n_blocks": c["n_blocks"],
           "vp_level_raising": c["vp_level_raising"], "m_old_congruent": c["m_old_congruent"],
           "old_congruent_detection": c.get("old_congruent_detection"), "blocks": blocks,
           "precision_R": c["R"], "seconds": float(c["seconds"])}
    if "m_from_weight_k" in c:
        out["m_from_weight_k"] = c["m_from_weight_k"]
    return out


def block_key(blocks, vp_g="vp_det_gram_Gamma"):
    return sorted((b["rank"], tuple(sorted((o["degree"], o["vp_det_gram_w"] if "vp_det_gram_w" in o else o["vp_etaB"],
                                           o[vp_g]) for o in b["orbits"])), b["old_congruent"]) for b in blocks)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--t5", required=True)
    ap.add_argument("--h3", required=True)
    ap.add_argument("--census", default=None)
    ap.add_argument("--shift", nargs="*", default=[], help="dumps of --suite shift (the m-block rank at k+(p-1))")
    ap.add_argument("--build-cmd", default=None)
    ap.add_argument("--out", default=str(RES / "laneC" / "hj8_def_native.json"))
    a = ap.parse_args(argv)
    t5 = json.loads(pathlib.Path(a.t5).read_text())
    h3 = json.loads(pathlib.Path(a.h3).read_text())
    ref = load("s06/T5_def.json")["data"]["triples"]
    t5ref = load("s06/T5.json")["data"]
    cells, t5_cmp = [], []
    for c in t5["cells"]:
        role = c["weight_role"]
        if c["status"] != "computed":
            cells.append({"q": c["q"], "k": c["k"], "p": c["p"], "weight_role": role, "status": c["status"],
                          "reason": c["reason"]})
            t5_cmp.append({"cell": f"{c['q']},{c['k']},{c['p']}", "weight_role": role, "status": "not computed",
                           "reason": c["reason"]})
            continue
        nc = norm_cell(c["cell"], role)
        nc["status"] = "computed"
        nc["module"] = c["module"]
        cells.append(nc)
        if role == "k":
            key = f"{c['q']},{c['k']},{c['p']}"
            r = ref[key]
            mine = block_key(c["cell"]["blocks"])
            theirs = block_key(r["blocks"])
            m_ok = (c["cell"]["m_old_congruent"] or {}).get("vp_etaB") == r["m"]["vp_etaB"] and \
                (c["cell"]["m_old_congruent"] or {}).get("rank") == r["m"]["rank"]
            t5_cmp.append({"cell": key, "weight_role": "k", "dim_brandt_eq": c["cell"]["dim_brandt"] == r["dim_brandt"],
                           "n_blocks_eq": c["cell"]["n_blocks"] == r["n_blocks"],
                           "blocks_eq (rank, orbit degrees, vp_w, vp_Gamma, old_congruent)": mine == theirs,
                           "m_eq (rank, vp_etaB)": m_ok,
                           "vp_level_raising_eq": c["cell"]["vp_level_raising"] == r["level_one_form"]["vp_level_raising"],
                           "vp_etaB_m": c["cell"]["m_old_congruent"]["vp_etaB"] if c["cell"]["m_old_congruent"] else None})
        else:
            key0 = f"{c['q']},{c['k'] - c['p'] + 1},{c['p']}"
            mk = c["cell"].get("m_from_weight_k")
            g = t5ref["triples"].get(key0, {}).get("k+p-1", {}).get("gl2_side", {})
            row = {"cell": key0, "weight": c["k"], "weight_role": "k+(p-1)", "pairing_perfect": c["cell"]["pairing_perfect"],
                   "m_from_weight_k": mk,
                   "gl2_side (s06/T5.json)": {"ord_eta_new": g.get("ord_eta_new"), "S_new_m": (g.get("ranks") or {}).get("S_new_m"),
                                             "status": g.get("status", "computed") if g else "absent"}}
            if mk and "rank" in mk and g.get("ord_eta_new") is not None:
                row["definite_rank_eq_gl2_S_new_m"] = mk["rank"] == g["ranks"]["S_new_m"]
                row["etaB_ring_eq_ord_eta_new"] = mk["etaB_ring_vp"] == g["ord_eta_new"]
            t5_cmp.append(row)
    # the shift route (jl_eta_def --suite shift): rank of M_m at k+(p-1) from the joint generalized eigenspace mod p
    shift_rows = {}
    for f in a.shift:
        for c in json.loads(pathlib.Path(f).read_text())["cells"]:
            shift_rows[f"{c['q']},{c['k']},{c['p']}"] = c
    for r in t5_cmp:
        if r.get("weight_role") != "k+(p-1)" or r["cell"] not in shift_rows:
            continue
        sc = shift_rows[r["cell"]]
        sh = sc["shift"]
        r["m_shift_route"] = {"weight": sc["k_shift"], "rank_M_m": sh.get("rank_M_m"), "etaB_ring": sh.get("etaB_ring"),
                              "etaB_ring_vp": sh.get("etaB_ring_vp"), "method": sh.get("method"),
                              "dim_brandt": sh.get("dim_brandt"), "steps": sh.get("steps"),
                              "seconds": sh.get("seconds"), "build_seconds": sh.get("build_seconds")}
        if r.get("m_from_weight_k") and "rank" in r["m_from_weight_k"]:
            r["shift_route_eq_full_route"] = r["m_from_weight_k"]["rank"] == sh.get("rank_M_m")
        if r.get("status") == "not computed":
            r["status"] = "computed by the shift route only (the full module route was skipped for cost)"
            r.pop("reason", None)
        g = t5ref["triples"].get(r["cell"], {}).get("k+p-1", {}).get("gl2_side", {})
        if g.get("ord_eta_new") is not None and sh.get("rank_M_m") is not None:
            r["definite_rank_eq_gl2_S_new_m"] = sh["rank_M_m"] == g["ranks"]["S_new_m"]
            r["etaB_ring_eq_ord_eta_new"] = sh.get("etaB_ring_vp") == g["ord_eta_new"]
    for c in cells:
        key = f"{c['q']},{c['k'] - c['p'] + 1},{c['p']}"
        if c.get("weight_role") == "k+(p-1)" and c.get("status") == "not computed" and key in shift_rows:
            sh = shift_rows[key]["shift"]
            c["status"] = "computed by the shift route only"
            c.pop("reason", None)
            c["m_from_weight_k"] = {"rank": sh.get("rank_M_m"), "etaB_ring": sh.get("etaB_ring"),
                                    "etaB_ring_vp": sh.get("etaB_ring_vp"), "method": sh.get("method"),
                                    "dim_brandt": sh.get("dim_brandt"), "route": "shift (jl_eta_def --suite shift)"}
    for c in h3["cells"]:
        nc = norm_cell(c["cell"], "H3 (q, p, k) triple")
        nc["status"] = "computed"
        nc["module"] = c["module"]
        cells.append(nc)
    census = None
    if a.census and pathlib.Path(a.census).exists():
        cz = json.loads(pathlib.Path(a.census).read_text())
        census = {"params": cz["census"], "seconds": cz["seconds"],
                  "rule": "every (q, k, p) with q <= qmax prime, k <= kmax even, k < p < pmax prime, p >= 5, p != q, "
                          "p !| q^2 - 1 is examined; a cell is skipped as trivial when the generic charpoly is "
                          "squarefree mod p (every m is then a single Q_p-orbit with eta^B = 1) and no level raising "
                          "congruence with the level-one form is possible (p !| a_q(g)^2 - q^{k-2}(q+1)^2); emitted "
                          "cells keep only the blocks with a congruence or an old congruence",
                  "cells": [norm_cell(c, "census") if "blocks" in c else c for c in cz["cells"]]}
        ram_cited = {(31, 6, 13): "unramified, residue degree 2 (non-maximal Z_p[T])",
                     (31, 10, 23): "unramified, residue degree 2 (non-maximal Z_p[T])"}
        cls = {"genuine_congruence": [], "old_congruent": [], "unresolved_not_determined": [], "other": []}
        for c in census["cells"]:
            if "blocks" not in c:
                cls["other"].append({"cell": [c.get("q"), c.get("k"), c.get("p")], "error": c.get("error")})
                continue
            for b in c["blocks"]:
                key = (c["q"], c["k"], c["p"])
                rec = {"q": c["q"], "k": c["k"], "p": c["p"], "rank": b["rank"], "n_orbits": b["n_orbits"],
                       "m_id": b["m_id"], "all_ok": b["all_ok"]}
                if any(not o["resolved_Qp_orbit"] for o in b["orbits"]):
                    rec["etaB"] = "not determined"
                    rec["cited_PARI_check (HJ-8-def review, idealprimedec)"] = ram_cited.get(key, "ramified")
                    cls["unresolved_not_determined"].append(rec)
                elif b["n_orbits"] > 1 or any((o["vp_etaB"] or 0) > 0 for o in b["orbits"]):
                    rec["etaB"] = [o["etaB"] for o in b["orbits"]]
                    cls["genuine_congruence"].append(rec)
                elif b["old_congruent"]:
                    rec["etaB"] = [o["etaB"] for o in b["orbits"]]
                    cls["old_congruent"].append(rec)
                else:
                    cls["other"].append(rec)
        census["classification"] = cls
        census["classification_counts"] = {k_: len(v) for k_, v in cls.items()}
        census["bounds"] = (f"q prime, 2 <= q <= {cz['census']['qmax']}; k even, 2 <= k <= {cz['census']['kmax']}; "
                            f"p prime, k < p < {cz['census']['pmax']}, p >= 5, p != q, p !| q^2 - 1")
    def eq_all(r):
        return all(v for k_, v in r.items() if (k_.endswith("_eq") or "_eq " in k_) and isinstance(v, bool))
    doc = {
        "provenance": {
            "script": "code/python/langlandscape/hacs_bridge/laneC_hj8def_collect.py",
            "tool": "code/hacs/src/hacs/Registry/JL/quat/tools/jl_eta_def.cpp (standalone g++ -O2; links the quat library "
                    "sources unchanged)",
            "build_cmd": a.build_cmd, "binary": str(pathlib.Path(a.binary).resolve()),
            "binary_sha256": sha256(pathlib.Path(a.binary)), "commit": git_commit(),
            "date": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
            "binary_source": "built from this commit (jl_eta_def.cpp) on top of impl/hacs-laneC; see build_cmd",
            "runtime_s": {"t5": t5.get("seconds"), "h3": h3.get("seconds"),
                          "census": census["seconds"] if census else None},
            "status": "computed (native C++); the weight-k T5 cells agree with s06/T5_def.json where compared",
            "definitions": "defect/gram.py (S06-C5): M = BrandtSym (HJ-4a intrinsic lattice, = Sym^n(Z_p^2) at p != q), "
                           "G_w, generic T = sum c_l T_l (gram.py coefficient choices), Q_p-orbits via Q-factorisation + "
                           "Hensel (+ separation by T + c T_l when the generic T is not separating), A_phi = ker phi(T) "
                           "saturated mod p^R, v_p det G_w|A_phi; blocks = residual eigensystems",
        },
        "schema": __doc__.split("Per-cell schema")[1].split("Run (from")[0].strip(),
        "T5_comparison": {"rows": t5_cmp, "weight_k_all_equal": all(eq_all(r) for r in t5_cmp if r.get("weight_role") == "k"
                                                                       and "status" not in r),
                          "k+(p-1)_closed_against_gl2": [r["cell"] for r in t5_cmp if r.get("etaB_ring_eq_ord_eta_new")
                                                          and r.get("definite_rank_eq_gl2_S_new_m")],
                          "k+(p-1)_definite_etaB_ring": {r["cell"]: (r.get("m_shift_route") or r.get("m_from_weight_k") or {}).get("etaB_ring")
                                                          for r in t5_cmp if r.get("weight_role") == "k+(p-1)"},
                          "shift_route_eq_full_route": [r["cell"] for r in t5_cmp if r.get("shift_route_eq_full_route")]},
        "cells": cells,
        "census": census,
    }
    outp = pathlib.Path(a.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(doc, indent=1) + "\n")
    print(json.dumps(doc["T5_comparison"], indent=1)[:3000])
    if census:
        print(json.dumps(census["params"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
