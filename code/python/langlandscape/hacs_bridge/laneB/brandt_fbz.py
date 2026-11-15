# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""INTERIM / TEST-FIXTURE-ONLY writer of ``langlandscape_brandt/v1`` + ``free_block_z`` for prime q (weight 2).

To be replaced by the official exporter HJ-B0 (``code/hacs/jl/brandt_export.py``, Lane A).

Transpose decision: ``brandt.py`` has ``B[c][c'] = #{p-neighbours of class c lying in class c'}`` (row sums p+1,
``|G_c'| B[c][c'] = |G_c| B[c'][c]``), i.e. B is the row action (T_p Phi)(c) = sum_c' B[c][c'] Phi(c').  In the
indicator basis b_j = 1_j this is T_p b_j = sum_i B[i][j] b_i, i.e. the LatticeModule column matrix F is B itself
(NO transpose).  Hence F rows sum to p+1 (F * ones = (p+1) ones; e = sum b_j is the Eisenstein vector) and the
weighted symmetry reads |G_j| F_ij = |G_i| F_ji.

Run from code/python:  python -m langlandscape.hacs_bridge.laneB.brandt_fbz.py OUTDIR q1 q2 ...
"""
from __future__ import annotations
import datetime, json, math, pathlib, subprocess, sys, time

HERE = pathlib.Path(__file__).resolve()
sys.path.insert(0, str(HERE.parents[3]))
from langlandscape import brandt, quat  # noqa: E402
from langlandscape.pari import get_pari  # noqa: E402
from langlandscape.quat import prime_factors  # noqa: E402


def _find_ab(D, bound=400):
    """Fast (a,b) for prime D (also D > 400, where quat.find_ab's default bound fails)."""
    pari = get_pari()
    target = set(prime_factors(D))
    for a, b in [(-1, -D), (-2, -D)] + [(-p, -D) for p in range(3, 400, 4)]:
        if {p for p in prime_factors(2 * a * b) if int(pari.hilbert(a, b, p)) == -1} == target:
            return a, b
    return _find_ab.orig(D, bound)


if quat.find_ab is not _find_ab:
    _find_ab.orig = quat.find_ab
    quat.find_ab = _find_ab


def primes_upto(n):
    return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p ** .5) + 1))]


def ops_for(q):
    num = (q - 1) // math.gcd(q - 1, 12)
    lmax = max(prime_factors(num), default=1) if num > 1 else 1
    return [p for p in primes_upto(max(13, lmax)) if p != q]


def build(q):
    t0 = time.perf_counter()
    m = brandt.module(q)
    t_cls = time.perf_counter() - t0
    ops = ops_for(q)
    Ts = {}
    t_T = {}
    for p in ops:
        t1 = time.perf_counter()
        Ts[p] = m.T(p)
        t_T[p] = time.perf_counter() - t1
    return m, ops, Ts, t_cls, t_T, time.perf_counter() - t0


def checks(m, ops, Ts, q, w2=None):
    h = m.h
    mm = brandt.matmul
    comm = all(mm(Ts[a], Ts[b]) == mm(Ts[b], Ts[a]) for i, a in enumerate(ops) for b in ops[i + 1:])
    rows = all(sum(r) == p + 1 for p in ops for r in Ts[p])
    sym = all(m.gammas[j] * Ts[p][i][j] == m.gammas[i] * Ts[p][j][i] for p in ops for i in range(h) for j in range(h))
    out = {"commute": comm, "row_sums_p_plus_1": rows, "weighted_symmetry": sym}
    if 2 in Ts:
        cp = brandt.charpoly_coeffs(Ts[2])
        out["charpoly_T2"] = cp
        if w2 is not None and str(q) in w2:
            out["charpoly_T2_matches_brandt_w2"] = (w2[str(q)]["charpoly"] == cp)
    return out


def export(q, outdir, w2=None):
    m, ops, Ts, t_cls, t_T, t_all = build(q)
    chk = checks(m, ops, Ts, q, w2)
    assert chk["commute"] and chk["row_sums_p_plus_1"] and chk["weighted_symmetry"], (q, chk)
    from langlandscape import results
    rec = {
        "schema": "langlandscape_brandt/v1", "D": q, "M": 1, "k": 2,
        "provenance": {"script": "code/python/langlandscape/hacs_bridge/laneB/brandt_fbz.py (INTERIM, test fixtures only)",
                       "commit": results.git_commit(), "params": {"q": q, "ops": ops},
                       "date": datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat(),
                       "runtime_s": t_all},
        "conventions": {"gamma": "|Gamma_x| = |O_r(I_x)^x| including -1 (weights = this)",
                        "brandt": "B[c][c'] = #p-neighbours of class c in class c'; F = B (no transpose)",
                        "checks": chk},
        "weights": list(m.gammas),
        "free_block_z": {"ops": ops, "r": m.h,
                         "F": [[str(x) for row in Ts[p] for x in row] for p in ops],
                         "basis_rule": "classes in brandt.py enumeration order; basis = indicator functions",
                         "convention": "column: T_p b_j = sum_i F_ij b_i"},
    }
    path = pathlib.Path(outdir) / f"q{q}.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(rec, indent=None, separators=(",", ":")) + "\n")
    return rec, t_all


if __name__ == "__main__":
    w2 = json.load(open(HERE.parents[4] / "results/s01/brandt_w2.json"))["data"]["T2_table"]
    for q in map(int, sys.argv[2:]):
        r, t = export(q, sys.argv[1], w2)
        print(q, r["free_block_z"]["r"], r["conventions"]["checks"].get("charpoly_T2_matches_brandt_w2"), round(t, 1))
