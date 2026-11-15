# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S06 cross-check (F4, batch 7): run t4_hecke.gp / h3.gp through cypari2 and write the result JSONs with provenance.

Usage: python3 code/cas/s06-xcheck/run.py {t4|h3} [--no-level3]
Definitions: code/cas/s06-xcheck/README.md.
"""
import datetime
import json
import os
import resource
import subprocess
import sys
import time

import cypari2

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OUT = os.path.join(REPO, "code", "results", "s06-xcheck")


def git_commit():
    try:
        sha = subprocess.check_output(["git", "-C", REPO, "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", REPO, "status", "--porcelain", "code/cas/s06-xcheck"], text=True).strip()
        return sha + ("+dirty(code/cas/s06-xcheck)" if dirty else "")
    except Exception:  # pragma: no cover
        return "unknown"


def s(x):
    return str(x)


def i(x):
    return int(x)


def level_q_rows(lq):
    """Convert the output of xc_level_q (h3.gp) to a dict."""
    keys = ["N", "k", "p", "dim_S_k_N", "dim_S_old", "rank_T", "rank_b", "rank_T_an", "rank_b_an",
            "B_T", "B_T_an", "T_lattice_stable", "T_an_lattice_stable"]
    d = {key: i(lq[n]) for n, key in enumerate(keys)}
    d["forms"] = [{
        "form": i(r[0]), "field_poly": s(r[1]), "degree": i(r[2]), "P_index": i(r[3]), "e": i(r[4]), "f": i(r[5]),
        "a_q": s(r[6]), "eisenstein_mod_P": bool(i(r[7])), "ord_c_q": s(r[8]), "t_an_q": s(r[9]),
        "ord_c_minus_t_an": s(r[10]),
    } for r in lq[13]]
    return d


def run_h3(P):
    out = P("h3_run()")
    triples = [[13, 7, 4], [13, 7, 6], [19, 5, 4], [29, 5, 4]]
    res = []
    for (q, p, k), lq in zip(triples, out):
        d = level_q_rows(lq)
        d.update({"q": q, "M": 1})
        d["non_eisenstein_diffs"] = [r["ord_c_minus_t_an"] for r in d["forms"] if not r["eisenstein_mod_P"]]
        res.append(d)
    sup = []
    cases = P("H3M_CASES")
    for c, lq in zip(cases, P("h3m_run()")):
        d = level_q_rows(lq)
        d.update({"q": i(c[0]), "M": i(c[3]), "route": s(c[4])})
        d["non_eisenstein_nonzero_pairs"] = [r for r in d["forms"] if not r["eisenstein_mod_P"]
                                             and (r["ord_c_q"] != "0" or r["t_an_q"] != "0")]
        sup.append(d)
    return {"parameters": {"triples_qpk": triples, "M": 1,
                           "supplement_M_gt_1_qpkM": [[i(c[0]), i(c[1]), i(c[2]), i(c[3])] for c in cases]},
            "rows": res,
            "note": "The four M = 1 triples are vacuous (S_k(1) = 0 for k = 4, 6): see README, doubt 1. "
                    "supplement_M_gt_1 holds non-vacuous q = -1 mod p cases (S^old != 0).",
            "supplement_M_gt_1": sup}


def run_t4(P, level3):
    out = P("t4_run(%d)" % (1 if level3 else 0))
    res = []
    for w in out:
        rows = [{
            "form": i(r[0]), "field_poly": s(r[1]), "degree": i(r[2]), "P_index": i(r[3]), "e": i(r[4]), "f": i(r[5]),
            "in_m": bool(i(r[6])), "in_m_away_from_17": bool(i(r[7])), "a17_unit_mod_P": bool(i(r[8])),
            "ord_P_delta": i(r[9]), "t_G_3": i(r[10]), "a_3": s(r[11]),
        } for r in w[2]]
        rB = w[7]
        d = {
            "k": i(w[0]), "dim_S_k_1": i(w[1]),
            "routeA_eigenforms": rows,
            "length_T1m_mod_delta_routeA": i(w[3]),
            "length_all_17_routeA": i(w[4]),
            "rank_T1m": i(w[5]), "rank_forms_congruent_to_Delta_away_from_17": i(w[6]),
            "routeB_smith": {"v17_index_T_over_xT": i(rB[0]), "v17_elementary_divisors": [i(v) for v in rB[1]],
                             "rank_T": i(rB[2]), "B": i(rB[3]), "lattice_stable": bool(i(rB[4])),
                             "v17_det_x_on_S": i(rB[5])},
            "t_G_k_3": [r["t_G_3"] for r in rows if r["in_m"]],
        }
        if level3:
            d["level3"] = level_q_rows(w[8])
        res.append(d)
    return {"parameters": {"p": 17, "q": 3, "weights": [12, 28, 44, 60, 124], "m": "(17, T_l - tau(l), all l incl. 17)",
                           "prediction_ord17_c3": [1, 1, 1, 1, 2]}, "rows": res}


def main():
    which = sys.argv[1]
    level3 = "--no-level3" not in sys.argv
    t0 = time.time()
    P = cypari2.Pari()
    P.allocatemem(int(os.environ.get("XC_PARI_STACK", 6 * 10**9)))  # level 3, k = 124 needs > 2 GB
    P('read("%s")' % os.path.join(HERE, "h3.gp"))
    if which == "t4":
        P('read("%s")' % os.path.join(HERE, "t4_hecke.gp"))
        data, script, fname = run_t4(P, level3), "code/cas/s06-xcheck/t4_hecke.gp (+ h3.gp routines)", "T4_hecke.json"
    elif which == "h3":
        data, script, fname = run_h3(P), "code/cas/s06-xcheck/h3.gp", "H3.json"
    else:
        raise SystemExit("usage: run.py {t4|h3} [--no-level3]")
    runtime = time.time() - t0
    rss_kb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    prov = {
        "script": script, "wrapper": "code/cas/s06-xcheck/run.py " + " ".join(sys.argv[1:]),
        "git_commit": git_commit(), "pari_version": s(P.version()), "pari_version_string": "PARI/GP 2.15.4 (cypari2 %s)"
        % getattr(cypari2, "__version__", "2.2.0"),
        "date_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "runtime_s": round(runtime, 2), "peak_rss_MB": round(rss_kb / 1024, 1),
        "definitions": "code/cas/s06-xcheck/README.md",
    }
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, fname), "w") as fh:
        json.dump({"provenance": prov, **data}, fh, indent=1, ensure_ascii=False)
        fh.write("\n")
    print(json.dumps(prov))


if __name__ == "__main__":
    main()
