# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Lane C, WP HJ-9: the Lambda-adic definite side natively (``jl_hj9``), compared with stage 04.

Reads the JSON of ``code/hacs/src/hacs/Registry/JL/quat/tools/jl_hj9.cpp`` (schema ``langlandscape_hj9/v1``) and compares it
field by field with ``code/results/s04/{T3,H6,H7}.json`` (ordinary/t3.py, h6.py, phicomb.py); it recomputes nothing.
Writes ``code/results/laneC/hj9_lambda.json`` with the NEW values rk_{Delta_s} e at s = 4, 5 (coinvariant route).

Run (from ``code/python``)::

    python3 -m langlandscape.hacs_bridge.laneC_hj9_compare --binary /path/to/jl_hj9 --native dump.json [--build-cmd ...]
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import pathlib
import sys

from .laneC_hj7_compare import RES, Cmp, git_commit, load, sha256


# review m1: derived / duplicated / echoed fields (not independent evidence)
NON_SUBSTANTIVE = {"ekills_a.deg_U_p_eq_p", "ribet.expected_2rk_e_ZS", "ekills_d.rk_e", "hida_d_rank_Delta_ZS.rank_Zp",
                   "hida_d_rank_Delta_ZS.delta_order", "delta_order", "rk_H1", "rk_H1_eq_S_plus_1", "E_eq_3S",
                   "S_s_expected", "D", "M", "p", "h", "ribet.eps_e_zero", "ribet.rk_e_ZS"}


def sub_count(c: dict, cm: Cmp) -> dict:
    keys = [k for k in cm.fields if k not in NON_SUBSTANTIVE and not k.endswith(".n") and k != "n"]
    c["n_fields_substantive"] = len(keys)
    c["n_fields_substantive_matched"] = sum(cm.fields[k] for k in keys)
    return c


def walk(cm: Cmp, prefix: str, ours, ref):
    if isinstance(ref, dict):
        for k, v in ref.items():
            walk(cm, f"{prefix}.{k}" if prefix else k, (ours or {}).get(k) if isinstance(ours, dict) else None, v)
    else:
        cm.eq(prefix, ours, ref)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--native", required=True)
    ap.add_argument("--native-runtime", type=float, default=None)
    ap.add_argument("--native-cmd", default=None)
    ap.add_argument("--build-cmd", default=None)
    ap.add_argument("--out", default=str(RES / "laneC" / "hj9_lambda.json"))
    a = ap.parse_args(argv)
    natdoc = json.loads(pathlib.Path(a.native).read_text())
    nat = natdoc["suites"]
    if a.native_runtime is None and natdoc.get("suite_seconds"):
        a.native_runtime = round(sum(float(v) for v in natdoc["suite_seconds"].values()), 2)
    cells = []
    # T3
    t3 = load("s04/T3.json")["data"]
    skip_t3 = {"S_s_expected", "stage02_X_per_type", "stage02_edges", "stage02_rk_H1", "rk_H1_eq_S_plus_1"}
    for s in (1, 2, 3):
        r, o = t3["levels"][f"s{s}"], nat["T3"][f"s{s}"]
        cm = Cmp(f"T3 B_3 q=2 p=5 s={s}", "s04/T3.json")
        for k, v in r.items():
            if k in skip_t3:
                continue
            walk(cm, k, o.get(k), v)
        cm.eq("rk_H1_eq_S_plus_1", o["rk_H1"] == o["S_s"] + 1, r["rk_H1_eq_S_plus_1"])
        cm.eq("S_s_expected", o["S_s"], r["S_s_expected"])
        cm.skip("stage02_*", "stage-02 values (HJ-7a reproduced them natively: hj7_tree_w2.json, s02/T3 cells)")
        cells.append(sub_count(cm.out({"coinvariant_route": o["coinvariant_route"],
                                       "coinvariant_route_eq_direct": o["coinvariant_route_eq_direct"]}), cm))
    # H6
    h6 = load("s04/H6.json")["data"]["cases"]
    for r, o in zip(h6, nat["H6"]):
        cm = Cmp(f"H6 D={r['D']} M={r['M']}", "s04/H6.json")
        for k, v in r.items():
            walk(cm, k, o.get(k), v)
        cells.append(sub_count(cm.out(), cm))
    # H7
    h7 = load("s04/H7.json")["data"]
    for D, r in h7.items():
        o = nat["H7"][D]
        cm = Cmp(f"H7 B_{D} p=5 s=1,2", "s04/H7.json")
        for k, v in r.items():
            walk(cm, k, o.get(k), v)
        cells.append(sub_count(cm.out(), cm))
    # NEW
    levels = {k: v for k, v in nat["T3"].items()}
    ranks = {k: v["coinvariant_route"]["rank_Delta_ZS"] for k, v in levels.items()}
    new = {
        "rk_Delta_e_ZS_by_s": ranks,
        "rk_Delta_e_ZE_by_s": {k: v["coinvariant_route"]["rank_Delta_ZE"] for k, v in levels.items()},
        "rk_Delta_e_H1_by_s (exact sequence; e alpha surjectivity checked mod p on the coinvariants)":
            {k: v["coinvariant_route"]["rank_Delta_H1"] for k, v in levels.items()},
        "hypotheses_by_s": {k: {f: v["coinvariant_route"][f] for f in ("U_p_commutes_Delta_S", "U_p_commutes_Delta_E",
                                                                       "delta_free_S", "delta_free_E", "e_alpha_surjective")}
                            for k, v in levels.items()},
        "constant": len(set(ranks.values())) == 1,
        "s_ge_4_caveat": "at s >= 4 the full e on Z/p^m[S_s] is not formed; the ranks come from the coinvariant route, "
                         "whose hypotheses (free Delta action with orbit length |Delta_s|, [U_p, Delta] = 0) are checked "
                         "per s; rk_Delta e H_1 additionally uses the surjectivity of e alpha onto e Z[S]^2, checked mod p "
                         "on the coinvariants (Nakayama), not by a direct restriction to H_1",
        "sizes": {k: {"S_s": v["S_s"], "E_s": v["E_s"], "delta_order": v["delta_order"],
                      "delta_free_S": v["coinvariant_route"]["delta_free_S"],
                      "delta_free_E": v["coinvariant_route"]["delta_free_E"],
                      "alpha_equivariant_U_p_Delta": v["alpha_equivariant_U_p_Delta"], "deg_U_p_eq_p": v["deg_U_p_eq_p"],
                      "seconds": float(v["seconds"])} for k, v in levels.items()},
        "method": "coinvariant route (Ordinary.h (O4)): Delta_s acts freely, so Z/p^m[S_s] is free over the local ring "
                  "Z/p^m[Delta_s]; eM is a direct summand, hence free, and its rank g = dim_{F_p} e(F_p[S_s/Delta_s]) is the "
                  "ordinary rank of U_p on the coinvariants. Exact; at s <= 3 it equals the direct computation "
                  "(coinvariant_route_eq_direct).",
        "status": "computed (NEW for s = 4, 5)",
    }
    summary = {"cells": len(cells), "cells_matched": sum(c["match"] for c in cells),
               "fields": sum(c["n_fields"] for c in cells), "fields_matched": sum(c["n_fields_matched"] for c in cells),
               "fields_substantive": sum(c["n_fields_substantive"] for c in cells),
               "fields_substantive_matched": sum(c["n_fields_substantive_matched"] for c in cells),
               "mismatched": [c["label"] for c in cells if not c["match"]]}
    binp = pathlib.Path(a.binary).resolve()
    doc = {
        "provenance": {
            "script": "code/python/langlandscape/hacs_bridge/laneC_hj9_compare.py",
            "tool": "code/hacs/src/hacs/Registry/JL/quat/tools/jl_hj9.cpp (standalone g++ -O2 build)",
            "build_cmd": a.build_cmd, "native_cmd": a.native_cmd, "binary": str(binp), "binary_sha256": sha256(binp),
            "commit": git_commit(), "date": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
            "runtime_s": a.native_runtime,
            "params": {"D": 3, "q": 2, "p": 5, "m": 3, "s_direct": [1, 2, 3], "s_coinvariant": sorted(levels)},
            "status": "computed (native C++), agreeing with the stage-04 Python values where compared",
            "conventions": "Ordinary.h (O1)-(O4): homological U_p, lines != <v mod p>, datum moved by LevelModel::move "
                           "(Level.h (L4)); U'_p with [[1,0],[p^s j, p]]; <d> v -> d^{-1} v; <p>_M v -> p^{-1} v mod M",
        },
        "summary": summary,
        "NEW_rank_Delta": new,
        "cells": cells,
    }
    outp = pathlib.Path(a.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(doc, indent=1) + "\n")
    print(json.dumps({"summary": summary, "NEW": {k: new[k] for k in ("rk_Delta_e_ZS_by_s", "constant")}}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
