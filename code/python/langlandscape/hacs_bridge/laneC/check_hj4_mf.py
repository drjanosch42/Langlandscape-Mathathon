# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""HJ-4a cross-check: native Sym^n Brandt char-polys (code/results/laneC/hj4_symn.json) against PARI's newspace.

JL at level O^x (thm:s01-JLclassical, M = 1, D squarefree with omega(D) odd):
    charpoly(T_ell | M(O^x; V_k)) = (x - ell - 1)^{[k = 2]} * charpoly(mfheckemat(mfinit([D, k], 0), ell)).
This extends symn.json (ell in {2, 3}, prime D <= 13) to every ell < 20 recorded natively, and to the composite D of
classsets.json (30, 42, 66, 70, 78). Run from code/python:  python3 -m langlandscape.hacs_bridge.laneC.check_hj4_mf
Writes code/results/laneC/hj4_symn_mfcheck.json.
"""

from __future__ import annotations

import json

from ... import results
from ...pari import get_pari


def mf_charpoly(pari, D: int, k: int, ell: int) -> list[int]:
    mf = pari.mfinit([D, k], 0)
    if int(pari.mfdim(mf)) == 0:
        cp = [1]
    else:
        cp = [int(c) for c in reversed(list(pari.Vec(pari.charpoly(pari.mfheckemat(mf, ell)))))]
    if k == 2:  # times (x - ell - 1)
        out = [0] * (len(cp) + 1)
        for i, c in enumerate(cp):
            out[i] += -(ell + 1) * c
            out[i + 1] += c
        cp = out
    return cp


def main() -> None:
    pari = get_pari()
    src = results.repo_root() / "code" / "results" / "laneC" / "hj4_symn.json"
    d = json.loads(src.read_text())["data"]
    cells = []
    with results.Timer() as t:
        for group in ("symn", "composite_D"):
            for c in d[group]:
                if c.get("rank", 0) == 0 or "charpoly_T" not in c:
                    continue
                D, k = c["D"], c["k"]
                per = {}
                for ell, txt in c["charpoly_T"].items():
                    ours = json.loads(txt)
                    per[ell] = ours == mf_charpoly(pari, D, k, int(ell))
                cells.append({"D": D, "k": k, "group": group, "ells": per, "all_equal": all(per.values())})
    n_ok = sum(c["all_equal"] for c in cells)
    n_ops = sum(len(c["ells"]) for c in cells)
    n_ops_ok = sum(sum(c["ells"].values()) for c in cells)
    data = {"source": "code/results/laneC/hj4_symn.json", "cells": cells, "cells_equal": n_ok, "cells_total": len(cells),
            "ops_equal": n_ops_ok, "ops_total": n_ops,
            "rule": "charpoly(T_ell | Brandt) = (x-ell-1)^[k=2] * charpoly(mfheckemat(mfinit([D,k],0),ell))"}
    results.write("laneC/hj4_symn_mfcheck.json", data, script="code/python/langlandscape/hacs_bridge/laneC/check_hj4_mf.py",
                  params={"source_sha_commit": json.loads(src.read_text())["provenance"]["commit"]}, runtime_s=t.seconds,
                  notes="HJ-4a: native hacs_jl Sym^n Brandt char-polys vs PARI newspace (JL); tag computed")
    print(f"cells {n_ok}/{len(cells)}, operators {n_ops_ok}/{n_ops}")
    assert n_ok == len(cells), "mismatch"


if __name__ == "__main__":
    main()
