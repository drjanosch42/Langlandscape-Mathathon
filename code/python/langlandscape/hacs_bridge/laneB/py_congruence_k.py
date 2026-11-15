# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Pure-Python/PARI (cypari2, exact integer linear algebra) re-computation of the lane-B JL congruence reads on the
v2 free_block_z records, for timing against the native HACS reads (code/results/laneB/congruence_k.json).

(i)  k = 2: Eisenstein module L/(Z e + L_cusp), e = constant function, L_cusp = {x : sum x_c/|Gamma_c| = 0}.
(ii) all cells with rank > 0: theta = first T_p (ops order) with squarefree charpoly P; for each irreducible f | P,
     g = P/f, L_f = ker_Z f(theta), L_f^c = ker_Z g(theta) (saturated), C_f = L/(L_f + L_f^c) (Smith invariants, order).
Usage: python py_congruence_k.py RECORD_DIR CONGRUENCE_K_JSON OUT_JSON
"""
import json, sys, time, pathlib, math
sys.path.insert(0, pathlib.Path(__file__).resolve().parents[3].as_posix())
from langlandscape.pari import get_pari

pari = get_pari()


def pmat(M):
    n = len(M); m = len(M[0])
    return pari.matrix(n, m, [int(M[i][j]) for i in range(n) for j in range(m)])


def smith_nontriv(M):
    return [int(x) for x in pari.matsnf(M) if int(x) > 1]


def eis_module(F_row_sums_ok, gam):
    h = len(gam)
    N = math.lcm(*gam)
    c = [N // g for g in gam]
    # L_cusp = ker of x -> sum c_i x_i ; e = ones; Smith of [e | K]
    K = pari.matkerint(pmat([c]))
    M = pari.concat(pmat([[1]] * h), K)
    return smith_nontriv(M)


def congr_cell(F):
    h = len(F[0])
    for t, T in enumerate(F):
        Tm = pmat(T)
        P = pari.charpoly(Tm, "x")
        fac = pari.factor(P)
        if all(int(e) == 1 for e in fac[1]):
            break
    else:
        return {"status": "no_squarefree_theta"}
    out = []
    I = pari.matid(h)
    for i in range(len(fac[0])):
        f = fac[0][i]; g = P / f
        A = pari.subst(f, "x", Tm); B = pari.subst(g, "x", Tm)
        Kf = pari.matkerint(A); Kg = pari.matkerint(B)
        sm = smith_nontriv(pari.concat(Kf, Kg))
        order = 1
        for s in sm: order *= s
        out.append({"f": [int(c) for c in pari.Vecrev(f)], "smith": sm, "order": order})
    return {"status": "ok", "theta_index": t, "orbits": out}


if __name__ == "__main__":
    rd = pathlib.Path(sys.argv[1]); ref = json.load(open(sys.argv[2]))["data"]["jl_cong"]
    refk = {(c["D"], c["M"], c["k"], tuple(int(x) for x in c["f"])): c for c in ref if c["status"] == "ok"}
    idx = json.load(open(rd / "index.json"))["data"]["cells"]
    t_all = time.perf_counter()
    t_load = t_eis = t_orb = 0.0
    res = []; n_ok = n_match = n_mis = n_orb = 0; n_eis = 0
    for c in idx:
        t0 = time.perf_counter()
        rec = json.load(open(rd / c["file"]))["data"]
        fb = rec["free_block_z"]; t_load += time.perf_counter() - t0
        if c["status"] != "ok":
            continue
        n_ok += 1
        F = [[[int(x) for x in row] for row in M] for M in fb["F"]]
        row = {"D": c["D"], "M": c["M"], "k": c["k"], "rank": c["rank"]}
        if c["k"] == 2 and c["M"] == 1:
            t0 = time.perf_counter()
            row["eis_smith"] = eis_module(None, fb["gammas"]); n_eis += 1
            t_eis += time.perf_counter() - t0
        t0 = time.perf_counter()
        r = congr_cell(F)
        t_orb += time.perf_counter() - t0
        row.update(r)
        for o in r.get("orbits", []):
            n_orb += 1
            rc = refk.get((c["D"], c["M"], c["k"], tuple(o["f"])))
            o["native_match"] = (rc is not None and [int(s) for s in rc["smith"]] == o["smith"])
            n_match += o["native_match"]; n_mis += (not o["native_match"])
        res.append(row)
    tot = time.perf_counter() - t_all
    summary = {"cells_total": len(idx), "cells_rank_gt0": n_ok, "k2_eis_cells": n_eis, "orbits": n_orb,
               "orbit_smith_match_native": n_match, "mismatch": n_mis,
               "wall_s": {"total": tot, "load_json": t_load, "phase_i_k2_eisenstein": t_eis, "phase_ii_orbit_congruences": t_orb}}
    json.dump({"summary": summary, "cells": res}, open(sys.argv[3], "w"), indent=1)
    print(json.dumps(summary, indent=1))
