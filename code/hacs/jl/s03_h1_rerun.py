#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2024-2026 Fabian Januszewski
# SPDX-License-Identifier: LGPL-3.0-only WITH LicenseRef-CUDA-exception
"""S03-H1 (JL extension of HACS, new file; upstream untouched).

Re-runs the seed's (C3) check  det(Psi*Psi) = (q+1)^2 - q^(2-k) T_q^2  on S_k(Gamma_0(M)) with the HACS integral
descent: char_Z(T_q | H^1(Gamma_0(M); Sym^{k-2} Z^2)/tors)  =  chi_cusp(x)^2 * (x - (1+q^(k-1)))^c   (c = #cusps,
minus 1 for k = 2), from which the cusp-form charpoly chi_cusp is extracted exactly.  The normalisation table, the
exact det and the integer norm Dint = prod (q^(k-2)(q+1)^2 - lambda^2) are compared with code/results/s03/betti_det.json
(C5, computed with PARI).  Also T1: Mazur's |Phi| = 5 from the Eisenstein congruence at level 11.

Usage: s03_h1_rerun.py [--hacs build/hacs] [--out code/results/s03/C3_rerun.json]
Needs sympy (outside HACS: only post-processing of exact integer polynomials).
"""
import argparse, datetime, json, math, os, pathlib, platform, re, subprocess, sys, tempfile, time
from fractions import Fraction
import sympy as sp

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[2]
X = sp.symbols("x")
GRID_M_K = [(1, 12), (11, 2), (11, 4), (11, 12), (5, 4)]
GRID_Q = [2, 3, 5]
Q_T1 = [2, 3, 5, 7, 13]


def cusps(M):
    return sum(sp.totient(math.gcd(d, M // d)) for d in sp.divisors(M))


def hacs_charpolys(hacs, M, k, primes):
    oc = ('set coefficient_ring = "Z";\n'
          f"d = descent({M}, {k-2}, {json.dumps(primes)});\n"
          'print("@@STATUS " + json(d.status));\n'
          'print("@@GROUPS " + json(d.groups));\n'
          'for c in d.charpoly { print("@@CP " + json([c.p, c.exact, c.determined])); }\n')
    with tempfile.NamedTemporaryFile("w", suffix=".oc", delete=False) as f:
        f.write(oc); fn = f.name
    t = time.perf_counter()
    r = subprocess.run([str(hacs), "--script", fn], capture_output=True, text=True,
                       env=dict(os.environ, ENGINE_THREADS="4"))
    wall = time.perf_counter() - t
    os.unlink(fn)
    if r.returncode != 0:
        raise RuntimeError(f"hacs exit {r.returncode}: {r.stderr[-800:]}")
    out = {"cp": {}, "wall_s": wall, "oc": oc}
    for line in r.stdout.splitlines():
        if line.startswith("@@"):
            tag, payload = line[2:].split(" ", 1)
            v = json.loads(payload)
            if tag == "CP":
                out["cp"][v[0]] = [int(c) for c in v[1]]  # high -> low
            else:
                out[tag.lower()] = v
    return out


def cusp_charpoly(Hcp, M, k, q):
    """chi_H1 = chi_cusp^2 * (x-(1+q^(k-1)))^c  ->  chi_cusp (exact, checked)."""
    c = int(cusps(M)) - (1 if k == 2 else 0)
    P = sp.Poly(Hcp, X)
    E = sp.Poly((X - (1 + q ** (k - 1))) ** c, X)
    Qt, rem = sp.div(P, E)
    assert rem.is_zero, "Eisenstein factor does not divide"
    f = sp.factor_list(Qt.as_expr())
    root = sp.Integer(f[0]) ** 0  # leading constant must be 1
    assert f[0] == 1
    res = sp.Poly(1, X)
    for fac, m in f[1]:
        assert m % 2 == 0, "H^1 charpoly / Eis is not a square"
        res = res * sp.Poly(fac, X) ** (m // 2)
    return [int(a) for a in res.all_coeffs()]


def dint_norm(cp, q, k):
    """prod over roots lam of cp of (q^(k-2)(q+1)^2 - lam^2) = det(A - T^2), via the companion matrix."""
    d = len(cp) - 1
    A = q ** (k - 2) * (q + 1) ** 2
    C = sp.zeros(d, d)
    for i in range(1, d):
        C[i, i - 1] = 1
    for i in range(d):
        C[i, d - 1] = -cp[d - i]
    return int((A * sp.eye(d) - C * C).det())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hacs", default=str(HERE.parent / "build" / "hacs"))
    ap.add_argument("--out", default=str(REPO / "code/results/s03/C3_rerun.json"))
    a = ap.parse_args()
    t0 = time.perf_counter()
    ref = json.load(open(REPO / "code/results/s03/betti_det.json"))
    refcases = {(c["M"], c["k"], c["q"]): c for c in ref["data"]["cases"]}
    ver = subprocess.run([a.hacs, "--version"], capture_output=True, text=True).stdout.strip()
    cases, runs, ok_all = [], [], True
    lam_cache = {}
    for M, k in GRID_M_K:
        primes = sorted(set(GRID_Q + Q_T1) if M == 11 and k == 2 else GRID_Q)
        primes = [p for p in primes if M % p]
        h = hacs_charpolys(a.hacs, M, k, primes)
        runs.append({"M": M, "k": k, "descent_script": h["oc"], "wall_s": h["wall_s"], "status": h.get("status"),
                     "groups": h.get("groups")})
        for q in primes:
            cp = cusp_charpoly(h["cp"][q], M, k, q)
            lam_cache[(M, k, q)] = cp
            if q not in GRID_Q:
                continue
            r = refcases.get((M, k, q))
            norm = dint_norm(cp, q, k)
            case = {"M": M, "k": k, "q": q, "dim": len(cp) - 1,
                    "hacs_charpoly_H1_high_to_low": h["cp"][q],
                    "charpoly_Tq": cp, "norm_Dint": norm,
                    "det_formula": "(q+1)^2 - q^(2-k) lambda^2", "overlap_with_C5": r is not None}
            if len(cp) - 1 == 1:
                lam = -cp[1]
                case["lambda"] = lam
                case["det"] = str(Fraction((q + 1) ** 2) - Fraction(lam * lam, q ** (k - 2)))
                case["det_vanishes"] = case["det"] == "0"
            if r is not None:
                case["agrees_charpoly"] = cp == r["charpoly_Tq"]
                case["agrees_norm_Dint"] = norm == r["norm_Dint"]
                case["agrees_dim"] = (len(cp) - 1) == r["dim"]
                case["agrees_s"] = (q ** (k // 2 - 1) * (q + 1)) == r["s"]
                ok_all &= case["agrees_charpoly"] and case["agrees_norm_Dint"] and case["agrees_dim"]
            cases.append(case)
    # normalisation table: the same as C5 (strings of the matrix, determinant, slots)
    norm_ref = ref["data"]["normalisation"]
    table = {"det": "(q+1)^2 - q^(2-k)*lambda^2",
             "matrix": [["q+1", "-q^(2-k)*lambda"], ["-lambda", "q+1"]],
             "entries": {"(1,1)": "q+1", "(1,2)": "-q^(2-k)*lambda", "(2,1)": "-lambda", "(2,2)": "q+1"},
             "q_2_minus_k_slot": "(1,2)",
             "source": "C5 normalisation (betti_det.json); here checked on the HACS values numerically via det of the 2x2 matrix"}
    for kk in ("det", "matrix", "entries", "q_2_minus_k_slot"):
        table["agrees_C5_" + kk] = table[kk] == norm_ref[kk]
    # numeric check of the matrix determinant against the det column on every 1-dim case
    for c in cases:
        if "lambda" in c:
            q, k, lam = c["q"], c["k"], c["lambda"]
            m = sp.Matrix([[q + 1, -sp.Rational(1, q ** (k - 2)) * lam], [-lam, q + 1]])
            c["det_matrix_check"] = str(m.det()) == c["det"]
            ok_all &= c["det_matrix_check"]
    table["all_agree"] = all(v for kk, v in table.items() if kk.startswith("agrees_"))
    ok_all &= table["all_agree"]
    # T1: Mazur at level 11 (Eisenstein congruence): gcd_q Res(chi_cusp, x-(1+q))  (k = 2, M = 11)
    t1_terms = {}
    for q in Q_T1:
        cp = lam_cache[(11, 2, q)]
        lam = -cp[1]
        t1_terms[q] = lam - (1 + q)
    g = 0
    for v in t1_terms.values():
        g = math.gcd(g, abs(v))
    t1 = {"statement": "Mazur: |Phi| = numerator((11-1)/12) = 5; Eisenstein congruence a_q = 1+q mod 5 for the weight-2 level-11 newform",
          "lambda_minus_(1+q)": t1_terms, "gcd": g, "mazur_numerator_of_(N-1)/12": 5,
          "agrees": g == 5 and all(v % 5 == 0 for v in t1_terms.values()),
          "status": "computed (HACS exact char_Z(T_q | H^1(Gamma_0(11);Z))); congruence modulus read from a_q - (1+q), not from a HACS congruence-module record"}
    ok_all &= t1["agrees"]
    commit = subprocess.run(["git", "-C", str(REPO), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(["git", "-C", str(REPO), "status", "--porcelain"], capture_output=True, text=True).stdout.strip()
    payload = {"provenance": {
        "script": "code/hacs/jl/s03_h1_rerun.py", "commit": commit + ("-dirty" if dirty else ""),
        "params": {"M_k": GRID_M_K, "q": GRID_Q, "T1_q": Q_T1, "hacs": ver, "hacs_verb": "descent (coefficient_ring=Z)"},
        "date": datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat(),
        "runtime_s": time.perf_counter() - t0, "python": platform.python_version(), "sympy": sp.__version__,
        "hacs_version": ver, "pari_version": None,
        "notes": "S03-H1: C3 det(Psi*Psi) re-run on HACS data; compared with code/results/s03/betti_det.json (C5)."},
        "data": {"normalisation_table": table, "cases": cases, "T1_mazur": t1, "hacs_runs": runs,
                 "acceptance": {"all_overlapping_cases_agree": ok_all,
                                "n_cases": len(cases), "n_overlap": sum(c["overlap_with_C5"] for c in cases)}}}
    p = pathlib.Path(a.out); p.parent.mkdir(parents=True, exist_ok=True)
    json.dump(payload, open(p, "w"), indent=1, sort_keys=True); open(p, "a").write("\n")
    print("wrote", p, "cases", len(cases), "all agree:", ok_all)
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
