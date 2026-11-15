#!/usr/bin/env python3
# SPDX-License-Identifier: CC-BY-4.0
"""Run the shipped HACS binary on the grid D in {3,5,7,11,13} (and d = 1), n = k-2 in {2,...,12}:
   descent(D, n, P).module_Z()  -> exact integer T_p matrices on H^1(Gamma_0(D); Sym^n Z^2)/tors, char_Z(T_p) factored
   hecke_structure(D, n, "full" | "anemic") -> the integral HeckeZ record (certified/uncertified words verbatim).
Writes data/cell_D<D>_n<n>.json and appends wall/RSS to data/runs.tsv.  Usage: run_cells.py <hacs> <outdir> [D,n ...]"""
import json, os, subprocess, sys, time, re

HACS = sys.argv[1]; OUT = sys.argv[2]
WORK = os.path.expanduser("$HACS_DATA/s27/jl/work")

def primes_for(D):
    if os.environ.get("JL_PRIMES"): return [int(x) for x in os.environ["JL_PRIMES"].split(",")]
    P = [p for p in [2, 3, 5, 7, 11, 13, 17, 19] if D % p != 0][:6]
    return P

OC = r'''set coefficient_ring = "Z";
d = descent({D}, {n}, {P});
print("@@GROUPS " + json(d.groups));
print("@@FACT " + json(d.charpoly_factored));
M = d.module_Z();
print("@@MSTATUS " + json([M.status, M.free_rank, M.free_block]));
for o in M.ops {{ print("@@F " + json([o.p, o.F, o.charpoly_Z])); }}
{HS}
'''
HS = r'''R = hecke_structure({D}, {n});
print("@@HSFULL " + json([R.status, R.signature, R.C_T, R.body]));
A = hecke_structure({D}, {n}, "anemic");
print("@@HSAN " + json([A.status, A.signature, A.C_T, A.body]));'''
HS1 = r'''R = hecke_structure(1, {n});
print("@@HSFULL " + json([R.status, R.signature, R.C_T, R.body]));'''

def run(D, n):
    P = primes_for(D)
    oc = OC.format(D=D, n=n, P=json.dumps(P), HS=(HS if D > 1 else HS1).format(D=D, n=n))
    f = os.path.join(WORK, f"cell_D{D}_n{n}.oc"); open(f, "w").write(oc)
    t = os.path.join(WORK, f"cell_D{D}_n{n}.time")
    env = dict(os.environ, ENGINE_THREADS="8", HECKEZ_LOCAL_THREADS="8")
    cmd = ["/usr/bin/time", "-v", "-o", t, "nice", "-n", "19", HACS, "--script", f]
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    out = {"D": D, "n": n, "k": n + 2, "P": P, "exit": r.returncode, "oc": oc}
    for line in r.stdout.splitlines():
        if line.startswith("@@"):
            tag, payload = line[2:].split(" ", 1)
            v = json.loads(payload)
            if tag == "F": out.setdefault("F", []).append(v)
            else: out[tag] = v
    if r.returncode != 0: out["stderr"] = r.stderr[-3000:]
    tt = open(t).read()
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", tt).group(1)
    rss = int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", tt).group(1))
    out["wall"] = wall; out["rss_kb"] = rss
    json.dump(out, open(os.path.join(OUT, f"cell_D{D}_n{n}.json"), "w"), indent=1)
    with open(os.path.join(OUT, "runs.tsv"), "a") as g:
        g.write(f"D={D}\tn={n}\texit={r.returncode}\twall={wall}\trss_kb={rss}\tcmd={' '.join(cmd)}\n")
    print(D, n, r.returncode, wall, rss, flush=True)

cells = [tuple(map(int, a.split(","))) for a in sys.argv[3:]] or \
        [(D, n) for D in [1, 3, 5, 7, 11, 13] for n in range(2, 13, 2)]
for D, n in cells: run(D, n)
