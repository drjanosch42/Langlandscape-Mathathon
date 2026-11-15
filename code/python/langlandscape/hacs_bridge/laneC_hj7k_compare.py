# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Lane C, WP HJ-7b: weight-k tree complexes natively (``jl_tree_k``), compared with the Python two-term complex.

Reads the JSON of ``code/hacs/src/hacs/Registry/JL/quat/tools/jl_tree_k.cpp`` (schema ``langlandscape_tree_k/v1``; it
either runs the binary or reads ``--native``) and writes ``code/results/laneC/hj7_ihara_k.json``:

* **cross-check** with ``code/results/s02/H_Vk.json`` (twoterm.py; all 15 cases x k = 2..10 and the acceptance rows)
  and ``code/results/s03/T6.json`` (ribet/ihara.py; all 40 cases).  The k = 2 cells were already in HJ-7a; the weight-k
  cells (k >= 3) are counted separately.  No number is recomputed here.
* **BrandtSym cross-check**: rank M(O; V_k) and charpoly(T_q) mod 1000003 of the tree's T_q = s_{0*}^{coh} s_1^* against
  HJ-4a's integral BrandtSym T_q (both native; reported as computed by the binary).
* **NEW values** (v6 Task 2): the quaternionic Ihara cokernel coker(iota : M(O; V_k)^2 -> M(O_0(q); V_k)) for
  D in {2,3,5,7,11,13}, q in {2,3,5,7,11,13} \\ {D}, even k = 2..14: its free rank (checked here against the JL dimension
  dim S_k(Gamma_0(Dq))^new from PARI ``mfdim``, an independent reference) and its torsion at every prime 5 <= l <= L,
  l !| Dq (Task 2's range is l > k); and W_D (Task 2(c)) as an integral matrix on HJ-4a's lattice.

Run (from ``code/python``)::

    python3 -m langlandscape.hacs_bridge.laneC_hj7k_compare --binary /path/to/jl_tree_k [--native dump.json] [--build-cmd "..."]
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import pathlib
import subprocess
import sys
import time

from .laneC_hj7_compare import RES, Cmp, git_commit, load, msort, sha256

HVK_FIELDS_LIST = ("elem_div_vals_d", "H0", "H1", "Hco0", "Hco1")
HVK_FIELDS = ("rank_C0", "rank_C1", "rank_d_Qp_lower", "rank_H1_Zp_upper", "rank_H0_Zp_upper", "rank_Hco0_Zp_upper",
              "H0_p_part_exact")
# echoes / duplicates (review m1-m3 rule of HJ-7a): not counted as substantive
NON_SUBSTANTIVE = {"rank_M_U", "rank_M_Uprime", "p_le_k_minus_2", "pred_coh_d_rank_H1", "pred_free_rank_H1", "D", "q",
                   "p", "m", "X", "E", "acceptance.rank_H1", "H0(top-level)"}


def out_cell(cm: Cmp, extra=None) -> dict:
    d = cm.out(extra)
    subst = [k for k in cm.fields if k.split(".")[-1] not in NON_SUBSTANTIVE and k not in NON_SUBSTANTIVE]
    d["n_fields_substantive"] = len(subst)
    d["n_fields_substantive_matched"] = sum(cm.fields[k] for k in subst)
    return d


def cmp_hvk(nat: list[dict]) -> list[dict]:
    ref = load("s02/H_Vk.json")["data"]
    idx = {(c["D"], c["q"], c["N1"], c["N0"]): c for c in nat}
    out = []
    for r in ref["cases"]:
        o = idx[(r["D"], r["q"], r["N1"], r["N0"])]
        for k, rk in r["k"].items():
            ok = o["k"][k]
            cm = Cmp(f"D={r['D']} q={r['q']} N1={r['N1']} N0={r['N0']} p={r['p']} m={r['m']} k={k}", "s02/H_Vk.json")
            for f in ("D", "q", "p", "m", "X", "E"):
                cm.eq(f, o[f], r[f])
            for f in HVK_FIELDS:
                cm.eq(f, ok[f], rk[f])
            for f in HVK_FIELDS_LIST:
                cm.eq(f, msort(ok[f]), msort(rk[f]))
            for f in ("rank_M_U", "rank_M_Uprime", "p_le_k_minus_2", "pred_coh_d_rank_H1", "pred_free_rank_H1"):
                if f in rk:
                    cm.eq(f, ok.get(f), rk[f])
            if "rank_d_certified" in rk:
                cm.eq("rank_d (ours, bound-pinned) = reference pinned rank of d", ok["rank_d_pinned"], rk["rank_d_certified"])
            for f in ("rank_H1", "rank_H0"):
                if f in rk:
                    cm.eq(f, ok.get(f), rk[f])
            if "rank_d_Fell" in rk:
                cm.eq("rank_d mod ell (ours: local model at ell = 1000003; ref: global model mod a prime of K)",
                      ok["rank_d_mod_ell"], rk["rank_d_Fell"])
            cm.skip("pred_rank_*_JL", "PARI mfdim predictions (modular-forms side)")
            out.append(out_cell(cm, {"weight_k": int(k) > 2, "conj_ok": o["conj_ok"]}))
    for a in ref["acceptance"]:
        o = next(c for c in nat if (c["D"], c["q"]) == (a["D"], a["q"]) and lvl(c) == a["level"])
        cm = Cmp(f"acceptance D={a['D']} q={a['q']} {a['level']} k={a['k']}", "s02/H_Vk.json#acceptance")
        cm.eq("acceptance.rank_H1", o["k"][str(a["k"])].get("rank_H1"), a["rank_H1"])
        out.append(out_cell(cm, {"weight_k": a["k"] > 2}))
    return out


def lvl(c) -> str:
    s = []
    if c["N1"] > 1:
        s.append(f"U1({c['N1']})")
    if c["N0"] > 1:
        s.append(f"U0({c['N0']})")
    return "*".join(s) or "O^x"


T6_NOT = {"hecke (T_l, S_l, exponents)": "Hecke operators T_l (l != q) on H_0 and the exponent table: not built natively",
          "hecke_vs_mf": "PARI mf comparison", "eps_* / shapiro_equivariance / tau_transport": "ihara.py's epsilon map"}


def cmp_t6(nat: list[dict]) -> list[dict]:
    ref = load("s03/T6.json")["data"]["cases"]
    out = []
    for o in nat:
        r = next(c for c in ref if (c["k"], c["level"], c["p"], c["m"]) == (o["k"], o["level"], o["p"], o["m"]))
        cm = Cmp(f"B_3 q=2 {o['level']} k={o['k']} p={o['p']} m={o['m']}", "s03/T6.json")
        cm.eq("H0(top-level)", msort(o["H0_cohomological"]), msort(r["H0"]))
        cm.eq("cohomological.H0", msort(o["H0_cohomological"]), msort(r["conventions"]["cohomological"]["H0"]))
        cm.eq("homological.H0", msort(o["H0_homological"]), msort(r["conventions"]["homological"]["H0"]))
        cm.eq("rank_P", o["rank_P"], r["rank_P"])
        cm.eq("rank_edge_module", o["rank_edge_module"], r["rank_edge_module"])
        cm.eq("V_U1_coinvariants", msort(o["V_U1_coinvariants"]), msort(r["V_U1_coinvariants"]))
        for k, v in T6_NOT.items():
            cm.skip(k, v)
        out.append(out_cell(cm, {"weight_k": o["k"] > 2, "conj_ok": o["conj_ok"]}))
    return out


def summarize(cells: list[dict]) -> dict:
    def part(cs):
        return {"cells": len(cs), "cells_matched": sum(c["match"] for c in cs),
                "fields": sum(c["n_fields"] for c in cs), "fields_matched": sum(c["n_fields_matched"] for c in cs),
                "fields_substantive": sum(c["n_fields_substantive"] for c in cs),
                "fields_substantive_matched": sum(c["n_fields_substantive_matched"] for c in cs),
                "mismatched": [c["label"] for c in cs if not c["match"]]}
    return {"weight_k (k >= 3)": part([c for c in cells if c["weight_k"]]),
            "k = 2 (already in HJ-7a)": part([c for c in cells if not c["weight_k"]])}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", required=True)
    ap.add_argument("--native", default=None, help="read this dump instead of running the binary")
    ap.add_argument("--native-runtime", type=float, default=None)
    ap.add_argument("--build-cmd", default=None)
    ap.add_argument("--L", type=int, default=2000, help="scan bound passed to the binary (shipped: 2000)")
    ap.add_argument("--out", default=str(RES / "laneC" / "hj7_ihara_k.json"))
    a = ap.parse_args(argv)
    binp = pathlib.Path(a.binary).resolve()
    if a.native:
        nat = json.loads(pathlib.Path(a.native).read_text())
        runtime = a.native_runtime
    else:
        t0 = time.time()
        nat = json.loads(subprocess.run([str(binp), "--L", str(a.L)], capture_output=True, text=True, check=True).stdout)
        runtime = time.time() - t0
    S = nat["suites"]
    hvk, t6 = cmp_hvk(S["s02_HVk"]), cmp_t6(S["s03_T6"])

    # BrandtSym cross-check
    bs = S["brandtsym_xcheck"]
    bs_sum = {"cells": len(bs), "rank_equal": sum(c["rank_local"] == c["rank_brandtsym"] for c in bs),
              "rank_zero": sum(c["rank_brandtsym"] == 0 for c in bs),
              "charpoly_Tq_equal_mod_ell": sum(c.get("charpoly_Tq_tree_eq_brandtsym") is True for c in bs),
              "charpoly_Tq_different": [f"D={c['D']} q={c['q']} k={c['k']}" for c in bs
                                        if c.get("charpoly_Tq_tree_eq_brandtsym") is False]}

    # Ihara: JL free-rank check (PARI mfdim, the independent reference) and the torsion table
    from ..pari import get_pari
    pari = get_pari()
    ih = S["ihara"]
    rows = []
    for c in ih:
        N = c["D"] * c["q"]
        dnew = int(pari(f"mfdim([{N},{c['k']}],0)"))
        tors_gt = [t for t in c["torsion"] if t["l_gt_k"]]
        tors_le = [t for t in c["torsion"] if not t["l_gt_k"]]
        rows.append({
            "D": c["D"], "q": c["q"], "k": c["k"], "h": c["h"], "X": c["X"], "E": c["E"],
            "rank_M_O": c["rank_M_O"], "rank_M_O0q": c["rank_M_O0q"], "rank_iota_Q": c["rank_iota_Q"],
            "ker_iota_rank": c["ker_iota_rank"], "coker_iota_free_rank": c["coker_iota_free_rank"],
            "dim_S_k(Dq)^new (PARI mfdim)": dnew, "free_rank_eq_JL_dim": c["coker_iota_free_rank"] == dnew,
            "torsion_l_gt_k": tors_gt, "torsion_l_le_k": tors_le,
            "no_l_torsion_found_in_scan (k < l <= L, l >= 5, l !| D q)": not tors_gt,
            "scan": c["scan"],
            "primes_scanned": c["primes_scanned"], "primes_scanned_gt_k": c["primes_scanned_gt_k"],
            "conj_ok": c["conj_ok"]})
    ih_sum = {"cells": len(rows), "L": nat["L"],
              "scan": {"l_min": 5, "l_max": nat["L"], "excluded": "l | D q (and l = 2, 3)",
                       "statement": "for each scanned l the l-primary torsion is decided exactly (rank drop mod l, then "
                                    "the elementary divisors mod l^m, l^m < 10^12); unscanned primes are not covered"},
              "lattice": "the polynomial lattice Sym^n(Z_l^2) of twoterm.sym ((g.P)(X,Y) = P((X,Y)g)), which agrees with "
                         "BrandtSym's Lambda_c at l !| D; the l <= k torsion depends on this choice (divided powers or the "
                         "dual can differ)",
              "free_rank_eq_JL_dim": sum(r["free_rank_eq_JL_dim"] for r in rows),
              "cells_with_torsion_l_gt_k": [f"D={r['D']} q={r['q']} k={r['k']}" for r in rows if r["torsion_l_gt_k"]],
              "cells_with_torsion_l_le_k": len([r for r in rows if r["torsion_l_le_k"]]),
              "torsion_l_le_k_primes": sorted({(r["k"], t["l"]) for r in rows for t in r["torsion_l_le_k"]}),
              "torsion_l_le_k_exponents": sorted({e for r in rows for t in r["torsion_l_le_k"] for e in t["exponents"]}),
              "prime_scans_total": sum(r["primes_scanned"] for r in rows),
              "conj_ok_all": all(r["conj_ok"] for r in rows)}
    ih_sum["torsion_l_le_k_primes"] = [list(x) for x in ih_sum["torsion_l_le_k_primes"]]
    ih_sum["observation_l_le_k_lattice"] = "polynomial lattice Sym^n(Z_l^2) (twoterm.sym = BrandtSym Lambda_c at l !| D)"
    ih_sum["observation_l_le_k"] = ("every torsion prime l <= k found has (l + 1) | (k - 2), exponent 1"
                                    if all((c["k"] - 2) % (t["l"] + 1) == 0 for c in ih for t in c["torsion"]
                                           if not t["l_gt_k"]) else "pattern (l+1) | (k-2) does NOT hold for all")

    # exact integral Ihara cokernel (Smith form over Z), consistency with the prime scan and the JL dimension
    ex_rows = []
    scan = {(c["D"], c["q"], c["k"]): c for c in ih}
    dims = {(r["D"], r["q"], r["k"]): r["dim_S_k(Dq)^new (PARI mfdim)"] for r in rows}
    for c in S.get("ihara_exact", []):
        key = (c["D"], c["q"], c["k"])
        sc = scan[key]
        D, q, k = key
        inv = [int(x) for x in c["torsion_invariants_iota_prime"]]

        def vp(n, p):
            v = 0
            while n % p == 0:
                n //= p
                v += 1
            return v
        # the scan's range: 5 <= l <= L, l !| D q; compare the l-primary parts there
        primes_exact = {}
        for d in inv:
            n, p = d, 2
            while n > 1:
                if n % p == 0:
                    e = vp(n, p)
                    n //= p ** e
                    primes_exact.setdefault(p, []).append(e)
                p += 1
        in_range = lambda l: 5 <= l <= nat["L"] and D % l and q != l
        ex_scan = {p: sorted(es) for p, es in primes_exact.items() if in_range(p)}
        sc_scan = {t["l"]: sorted(t["exponents"]) for t in sc["torsion"]}
        parts = {"prime_to_6Dq": {p: es for p, es in primes_exact.items() if p not in (2, 3) and D % p and p != q},
                 "2_and_3": {p: es for p, es in primes_exact.items() if p in (2, 3)},
                 "at_D (lattice choice (O^0)^#)": {p: es for p, es in primes_exact.items() if D % p == 0},
                 "at_q (not meaningful: S-arithmetic at q)": {p: es for p, es in primes_exact.items() if p == q}}
        group = " + ".join([f"Z^{c['coker_free_rank']}"] + [f"Z/{d}" for d in inv]) if inv else f"Z^{c['coker_free_rank']}"
        ex_rows.append({
            "D": D, "q": q, "k": k, "rank_M_O": c["rank_M_O"], "rank_M_O0q": c["rank_M_O0q"],
            "rank_iota_Q": c["rank_iota_Q"], "coker_free_rank": c["coker_free_rank"],
            "coker_iota (computed, Z)": group, "torsion_invariants": inv,
            "torsion_order": c["torsion_order"], "torsion_primary_exponents": {str(p): e for p, e in sorted(primes_exact.items())},
            "parts": {kk: {str(p): e for p, e in v.items()} for kk, v in parts.items()},
            "q_scaling_exponent_a": c["q_scaling_exponent_a"],
            "checks": {"rank_eq_scan": c["rank_iota_Q"] == sc["rank_iota_Q"],
                       "free_rank_eq_JL_dim": c["coker_free_rank"] == dims[key],
                       "l_primary_eq_scan_on_scan_range": ex_scan == sc_scan,
                       "coords_ok": c["coords_ok"], "denominators_q_only": c["denominators_q_only"]},
            "seconds": float(c["seconds"])})
    ex_sum = {"cells": len(ex_rows), "cells_fitting_60s": sum(r["seconds"] <= 60 for r in ex_rows),
              "max_seconds": max((r["seconds"] for r in ex_rows), default=None),
              "all_checks": {k_: sum(r["checks"][k_] for r in ex_rows) for k_ in (ex_rows[0]["checks"] if ex_rows else {})},
              "q_scaling_exponent_max": max((r["q_scaling_exponent_a"] for r in ex_rows), default=None),
              "cells_with_torsion_prime_to_6Dq": len([r for r in ex_rows if r["parts"]["prime_to_6Dq"]]),
              "torsion_free_cells": len([r for r in ex_rows if not r["torsion_invariants"]]),
              "lattice_convention": "BrandtSym (HJ-4a) intrinsic Lambda_c on every vertex and edge cell: Sym^n(Z_l^2) at "
                                    "every l !| D (seed convention, l = 2, 3 included), the (O^0)^# choice at l | D; "
                                    "vertex module Lambda_c^{Gamma_c}, edge module Lambda_c^{Gamma_e} (c = class of the edge "
                                    "representative); Gross form, (s_0^* f)(e) = rho(gamma_0^{-1}) f, (s_1^* f)(e) = "
                                    "rho(beta^{-1}) f, beta^{-1} = conj(mu) x_1 / (N_c N_c'); iota = (s_0^*, -s_1^*). "
                                    "The s_1^* block needed no q-scaling (a = 0 in every cell), but the q-part is still "
                                    "not an invariant of the S-arithmetic group (V is not q-integral) and is reported apart."}

    wd = S["W_D"]
    wd_pari = []
    for c in wd:
        D, k = c["D"], c["k"]
        tr_w, C0, dnew = (int(x) for x in pari(f"my(mf=mfinit([{D},{k}],0),A=mfatkininit(mf,{D})); "
                                                  f"[trace(A[2]), A[3], mfdim(mf)]"))
        pred_tr = (1 if k == 2 else 0) - tr_w  # tr W_D (definite) = [k = 2] - tr(w_D | S_k(D)^new), C = 1
        rec = {"D": D, "k": k, "rank": c["rank"], "dim_S_k(D)^new": dnew, "pari_tr_w_D_new": tr_w, "pari_C": C0,
               "rank_eq_dim_plus_eis": c["rank"] == dnew + (1 if k == 2 else 0)}
        if c["rank"] > 0:
            rec["trace_ours"] = int(c["trace"])
            rec["trace_eq_[k=2]-tr_pari"] = (C0 == 1 and int(c["trace"]) == pred_tr)
        wd_pari.append(rec)
    wd_sum = {"cells": len(wd), "rank_positive": sum(c["rank"] > 0 for c in wd),
              "pari_mfatkininit_check": {"relation": "tr W_D = [k = 2] - tr(w_D | S_k(D)^new) (PARI mfatkininit, C = 1); "
                                                     "rank = dim S_k(D)^new + [k = 2]",
                                         "rank_ok": sum(r["rank_eq_dim_plus_eis"] for r in wd_pari),
                                         "trace_ok": sum(r.get("trace_eq_[k=2]-tr_pari") is True for r in wd_pari),
                                         "of_positive_rank": sum(r["rank"] > 0 for r in wd_pari)},
              "integral": sum(c.get("Pi_D_over_D^m_integral") is True for c in wd),
              "involution": sum(c.get("W_squared_is_identity") is True for c in wd),
              "commutes_with_T_l": sum(any(v is True for kk, v in c.items() if kk.startswith("commutes")) for c in wd),
              "selfadjoint_w": sum(c.get("selfadjoint_w") is True for c in wd)}

    doc = {
        "provenance": {
            "script": "code/python/langlandscape/hacs_bridge/laneC_hj7k_compare.py",
            "tool": "code/hacs/src/hacs/Registry/JL/quat/tools/jl_tree_k.cpp (standalone g++ -O2 build)",
            "build_cmd": a.build_cmd, "binary": str(binp), "binary_sha256": sha256(binp), "commit": git_commit(),
            "date": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
            "runtime_s": runtime, "native_suite_seconds": nat.get("suite_seconds"), "params": {"L": nat["L"]},
            "native_cmd": f"jl_tree_k --L {nat['L']} --out <file> (all suites; the default suite list)",
            "status": "computed (native C++), agreeing with the Python stage-02/03 values where compared; the Ihara "
                      "torsion and W_D are NEW (computed; W_D agrees with PARI mfatkininit traces, the Ihara free rank "
                      "with PARI mfdim)",
            "conventions": {
                "coefficients": "Sym^{k-2}, (g.P)(X,Y) = P((X,Y)g), columns = images of X^{n-t}Y^t (twoterm.sym = [C] "
                                "def:rhon); interim local model at p (TreeK.h): iota_p = right multiplication on e O/p^m, "
                                "frames a_c with I_c (x) Z_p = O_p a_c",
                "ihara_map": "iota(f0, f1) = s_0^* f0 - s_1^* f1 (amalgam.py MV sign alpha(x,y) = dg_1 x - dg_q y); "
                             "(s_j^* f)(e) = u_j^{-1} f(s_j e); u_0 = phi_c(gamma_0), u_1 = iota(a_{c'} gamma_1 g a_c^{-1}), "
                             "g = mu/(q N_{c'}) (transport as amalgam.py's kappa: the second vertex group is moved back "
                             "along the edge)",
                "weights": "W_H = W^H = e_H W (|H| a unit for l >= 5); the cohomological H_0 uses the traces [H_x:H_e] "
                           "(ihara.py), the homological e_H u_j (twoterm.py); |Gamma_x| includes -1",
                "W_D": "BrandtSym.h (C4)/(C5): Pi_D unnormalised (Pi_D^2 = D^n); reported W_D = Pi_D / D^{n/2}",
                "flag": "no convention was ambiguous for the compared cells (all match); the l <= k torsion lies outside "
                        "Task 2's range and is reported separately",
            },
        },
        "summary": {
            "s02/H_Vk.json": summarize(hvk), "s03/T6.json": summarize(t6),
            "brandtsym_xcheck": bs_sum, "ihara_NEW": ih_sum, "ihara_exact_NEW": ex_sum, "W_D_NEW": wd_sum,
        },
        "ihara_exact_NEW": ex_rows,
        "ihara_NEW": rows,
        "W_D_NEW": wd,
        "W_D_pari_check": wd_pari,
        "brandtsym_xcheck": bs,
        "cells": {"s02/H_Vk.json": hvk, "s03/T6.json": t6},
    }
    outp = pathlib.Path(a.out)
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(doc, indent=1) + "\n")
    print(json.dumps(doc["summary"], indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
