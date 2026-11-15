#!/usr/bin/env python3
# SPDX-License-Identifier: CC-BY-4.0
"""Render data/congruence_modules.json (+ the HACS records' Eisenstein C_T words) as data/grid_table.md."""
import json, os, sys
D_ = sys.argv[1]
cm = json.load(open(os.path.join(D_, "congruence_modules.json")))
def fmt(r, key):
    v = r.get(key)
    if v is None: return "-- (no such part)"
    f = r.get(key + "_order_factored", {})
    if not f: return "0 (trivial)"
    inv = " x ".join(f"Z/{x}" for x in v)
    return inv + "  [" + " * ".join(f"{q}^{e}" if e > 1 else q for q, e in sorted(f.items(), key=lambda t: int(t[0]))) + "]"
def big(r, key, k, D):
    f = r.get(key + "_order_factored") or {}
    return ", ".join(q for q in sorted(f, key=int) if int(q) > k and D % int(q)) or "none"
out = ["| D | k | rank H^1/tors | dims (eis, old cusp, new) | rank T_P | C(old cusp, new) | C(all old = Eis + old cusp, new) | C(Eis, cusp) | primes l > k, l not dividing D in C(old,new) | HACS anemic record: Eisenstein C_T (verbatim) |",
       "|---|---|---|---|---|---|---|---|---|---|"]
for r in cm:
    D, n, k = r["D"], r["n"], r["k"]
    cell = json.load(open(os.path.join(D_, f"cell_D{D}_n{n}.json")))
    an = cell["HSAN"]; ct = an[2]
    up = [l.split("=", 1)[1] for l in an[3] if l.startswith("G3.C_T.upper=")]
    ex = [l.split("=", 1)[1] for l in an[3] if l.startswith("G3.C_T.status=")]
    rec = f"{ct}; status={ex[0] if ex else '-'}; upper={up[0] if up else '-'}"
    d = r["dims"]
    out.append(f"| {D} | {k} | {r['rank_L']} | ({d['eis']}, {d['old_cusp']}, {d['new']}) | {r['rank_T_P']} | {fmt(r,'C_oldcusp_new')} | {fmt(r,'C_old_new')} | {fmt(r,'C_eis_cusp')} | {big(r,'C_old_new',k,D)} | {rec} |")
open(os.path.join(D_, "grid_table.md"), "w").write("\n".join(out) + "\n")
print("\n".join(out))
