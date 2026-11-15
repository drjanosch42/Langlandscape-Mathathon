# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Lane B collector (WP HJ-6b): run the HACS JL validations on Lane A's Brandt records and collect the results.

Runs ``<binary> JLBrandtCongruenceRead`` and ``<binary> JLBrandtFreeBlockRead`` with ``JL_BRANDT_IN=<records>``, parses the
``@@JL_CONG`` (schema ``jl_congruence/v1``) and ``@@JL_READ`` (``jl_lattice_read/v1``) lines, and writes
``code/results/laneB/congruence_k.json`` as ``{provenance, data}``.

Post-processing (all *computed*, never claimed):
* ``ring_cong`` = (T_i x T_i^c)/T for T = Z[T_p : p in ops] is lattice-independent; it is compared like |C_i|;
* the order |C_i| is factored completely with sympy where the binary left a cofactor (no factor < 2^20);
* GL_2-side comparison: JL preserves a_p for p prime to D, so the GL_2 newform orbit matching the definite orbit i has
  T_p-charpoly ``tp_on_Li[p]``. From ``code/results/s01/symn.json`` (PARI ``mfinit([D, k], 0)``, the GL_2 side) we take the full
  charpoly chi_p of T_p on S_k(Gamma_0(D))^new, the cofactor g_p = chi_p / f_p, and the resultant Res(f_p, g_p). The primes of
  gcd_p Res(f_p, g_p) (nonzero ones only) are the GL_2-side *candidate* congruence primes of the orbit (necessary condition:
  an eigen-congruence mod l forces l | Res_p for every p). They are compared with the primes of |C_i|.
* @@JL_READ: only the fields safe on L are kept from ``readlocal_L`` (c3 / dim_A1, mono, e; Lane A audit fact (2)); at l = 2 the
  L (+) L at-root fields (root, C_T) are dropped (fact (3): open(precision)).
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import time
from math import gcd

import sympy

HERE = pathlib.Path(__file__).resolve()
REPO = HERE.parents[4]
SAFE_L = ("D_lattice", "d", "P", "t_ell", "dim_A1", "c3", "mono", "e", "e_op", "e_status", "digest")


def git_commit() -> str:
    try:
        sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=HERE.parent, capture_output=True, text=True, check=True).stdout.strip()
        st = subprocess.run(["git", "status", "--porcelain"], cwd=HERE.parent, capture_output=True, text=True, check=True).stdout.strip()
        return sha + ("-dirty" if st else "")
    except (subprocess.SubprocessError, OSError):
        return "unknown"


def sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def run(binary: str, name: str, env_extra: dict) -> tuple[list[str], float, int]:
    env = dict(os.environ)
    env.update(env_extra)
    t0 = time.perf_counter()
    p = subprocess.run([binary, name], env=env, capture_output=True, text=True)
    return p.stdout.splitlines(), time.perf_counter() - t0, p.returncode


def tagged(lines: list[str], tag: str) -> list[dict]:
    return [json.loads(l[len(tag) + 1:]) for l in lines if l.startswith(tag + " ")]


def primes_of(n: int) -> list[int]:
    return sorted(sympy.factorint(abs(n)).keys()) if abs(n) > 1 else []


def gl2_compare(rec: dict, symn: dict) -> dict | None:
    cell = symn.get(f"{rec['D']},{rec['k']}")
    if not cell or not rec.get("tp_on_Li"):
        return None
    x = sympy.Symbol("x")
    res_by_p, g = {}, 0
    for p, coeffs in rec["tp_on_Li"].items():
        ell = cell.get("ell", {}).get(str(p))
        if not ell:
            continue
        full = sympy.Poly(list(reversed([int(c) for c in ell["rhs"]])), x)
        f = sympy.Poly(list(reversed([int(c) for c in coeffs])), x)
        q, r = sympy.div(full, f)
        if not r.is_zero:
            res_by_p[p] = "f_p does not divide chi_p(GL2)"
            continue
        R = int(sympy.resultant(f.as_expr(), q.as_expr(), x)) if q.degree() > 0 else 1
        res_by_p[p] = str(R)
        if R != 0:
            g = gcd(g, abs(R))
    if not res_by_p:
        return None
    cand = primes_of(g) if g else None
    ours = primes_of(int(rec["order"]))
    ring = rec.get("ring_cong") or {}
    ring_p = primes_of(int(ring["order"])) if ring.get("order") not in (None, "0") else None
    return {
        "source": "code/results/s01/symn.json ell[p].rhs (PARI mfinit, GL_2 side)",
        "res_by_p": res_by_p,
        "gcd_res": str(g),
        "candidate_primes": cand,
        "C_primes": ours,
        "C_primes_subset_of_candidates": (cand is not None and set(ours) <= set(cand)),
        "equal": (cand is not None and set(ours) == set(cand)),
        "ring_C_primes": ring_p,
        "ring_primes_subset_of_candidates": (cand is not None and ring_p is not None and set(ring_p) <= set(cand)),
        "status": "computed",
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--binary", default="/home/janosch/data/hacs-build/laneB/b6/hacs")
    ap.add_argument("--records", default="/home/janosch/data/hacs-run/laneB/laneA_fbz_f54b109e/code/results/s06/brandt_free_block_z/index.json")
    ap.add_argument("--symn", default=str(REPO / "code/results/s01/symn.json"))
    ap.add_argument("--out", default=str(REPO / "code/results/laneB/congruence_k.json"))
    ap.add_argument("--no-read", action="store_true", help="skip JLBrandtFreeBlockRead")
    ap.add_argument("--no-small-ells", action="store_true", help="do not set JL_BRANDT_SMALL_ELLS=1 (l = 2, 3) for JLBrandtFreeBlockRead")
    a = ap.parse_args()
    t0 = time.perf_counter()
    env = {"JL_BRANDT_IN": a.records}
    cong_lines, cong_s, cong_rc = run(a.binary, "JLBrandtCongruenceRead", env)
    cong = tagged(cong_lines, "@@JL_CONG")
    summary = [l for l in cong_lines if l.startswith("JLBrandtCongruenceRead:")]
    reads, read_s, read_rc, read_summary = [], 0.0, None, []
    if not a.no_read:
        rl, read_s, read_rc = run(a.binary, "JLBrandtFreeBlockRead", dict(env, **({} if a.no_small_ells else {"JL_BRANDT_SMALL_ELLS": "1"})))
        read_summary = [l for l in rl if l.startswith("JLBrandtFreeBlockRead:")]
        for r in tagged(rl, "@@JL_READ"):
            if "readlocal_L" in r:
                r["readlocal_L"] = {k: v for k, v in r["readlocal_L"].items() if k in SAFE_L}
            if r.get("ell") == 2 and "readlocal_LL" in r:
                for k in ("root", "C_T", "roots"):
                    r["readlocal_LL"].pop(k, None)
                r["readlocal_LL"]["dropped_at_ell2"] = ["root", "C_T", "roots"]
            reads.append(r)
    symn = json.load(open(a.symn))["data"]["grid"] if pathlib.Path(a.symn).exists() else {}
    for r in cong:
        if r.get("orbit") is None:
            continue
        of = r["order_factor"]
        if of["cofactor"] != "1":
            fz = sympy.factorint(int(r["order"]))
            r["order_factor_full"] = {"pp": [[int(p), e] for p, e in sorted(fz.items())], "by": "sympy.factorint"}
        cmpd = gl2_compare(r, symn)
        if cmpd:
            r["gl2_compare"] = cmpd
    out = pathlib.Path(a.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    doc = {
        "provenance": {
            "script": "code/python/langlandscape/hacs_bridge/laneB_collect.py",
            "commit": git_commit(),
            "binary": a.binary,
            "binary_sha256": sha256(pathlib.Path(a.binary)),
            "params": {"JL_BRANDT_IN": a.records, "JL_BRANDT_SMALL_ELLS": not a.no_small_ells, "symn": os.path.relpath(a.symn, REPO), "validations": ["JLBrandtCongruenceRead"] + ([] if a.no_read else ["JLBrandtFreeBlockRead"])},
            "date": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
            "runtime_s": round(time.perf_counter() - t0, 3),
            "runtime_binary_s": {"JLBrandtCongruenceRead": round(cong_s, 3), "JLBrandtFreeBlockRead": round(read_s, 3)},
            "rc": {"JLBrandtCongruenceRead": cong_rc, "JLBrandtFreeBlockRead": read_rc},
            "summary": summary + read_summary,
            "python": sys.version.split()[0],
            "sympy": sympy.__version__,
            "notes": "computed (HACS-native JL module); k > 2 lattices are A Hecke-stable lattice (brandt_symn_int/v1), not canonical: "
                     "C_i depends on it. Key cells on (D, M, k, orbit f), never on F_fnv or class index (class order not canonical).",
        },
        "data": {"schema": "laneB_congruence_k/v1", "jl_cong": cong, "jl_read": reads},
    }
    out.write_text(json.dumps(doc, indent=1, sort_keys=False) + "\n")
    print(f"wrote {out}: {len(cong)} @@JL_CONG, {len(reads)} @@JL_READ; {summary[0] if summary else ''}")
    return 0 if cong_rc == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
