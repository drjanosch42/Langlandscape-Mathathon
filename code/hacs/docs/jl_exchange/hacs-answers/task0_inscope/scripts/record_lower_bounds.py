#!/usr/bin/env python3
# SPDX-License-Identifier: CC-BY-4.0
"""Lower bounds for the old(Delta)/new congruence at k = 12 read from HACS's certified integral Hecke records
hecke_structure(D, 10, "anemic" | "full") (G1.theta, G2 maximal ideals; [C] sec:recordschema item 8, prop:heckeZcong).
For each ell (> 12, not dividing D) in the T_P upper bound: theta(Delta-system) mod ell (anemic: T_p -> tau(p); full: also U_D -> a root
alpha of x^2 - tau(D) x + D^11 mod ell), the maximal ideal m of T with that residue, its local rank over Z_ell, and the components
through it.  rank(T_m) >= 2 with the Eisenstein component not through m  <=>  the Delta-system shares m with a 3-new system (a certified
congruence, since the level-1 Delta-system has rank 1 in T (x) Q_ell: anemic one system, full one system per U_D root)."""
import json, sys, os
DATA = sys.argv[1]
TAU = {2: -24, 3: 252, 5: 4830, 7: -16744, 11: 534612, 13: -577738, 17: -6905934, 19: 10661420, 23: 18643272}
def body_map(b):
    m = {}
    for l in b:
        k, _, v = l.partition("="); m.setdefault(k, v)
    return b, m
def lines_with(b, pre): return [l for l in b if l.startswith(pre)]
res = []
cm = {(r["D"], r["n"]): r for r in json.load(open(os.path.join(DATA, "congruence_modules.json")))}
for D in [3, 5, 7, 11, 13]:
    d = json.load(open(os.path.join(DATA, f"cell_D{D}_n10.json")))
    ells = [int(q) for q in cm[(D, 10)]["C_oldcusp_new_order_factored"] if int(q) > 12 and D % int(q)]
    for tag in ["HSAN", "HSFULL"]:
        b = d[tag][3]
        kv = {}
        for l in b:
            key, _, v = l.partition("=")
            if key in ("G1.theta", "G1.P", "G1.theta_ops"): kv[key] = v
            # G2 lines are of the form G2.ell=17.m[0].residue_poly=[5,1]
        theta = [int(x) for x in kv["G1.theta"].split(",")] if "G1.theta" in kv and kv["G1.theta"][0] in "-0123456789" else None
        ops = kv.get("G1.theta_ops", ",".join("T_" + x for x in kv.get("G1.P", "").split(","))).split(",")
        for ell in ells:
            pre = f"G2.ell={ell}."
            g2 = [l[len(pre):] for l in b if l.startswith(pre)]
            mids = sorted({l.split(".")[0] for l in g2 if l.startswith("m[")})
            info = {}
            for mi in mids:
                f = {l[len(mi) + 1:].split("=")[0]: l.split("=", 1)[1] for l in g2 if l.startswith(mi + ".")}
                f2 = {l[len(mi) + 1:].rsplit("=", 1)[0]: l.rsplit("=", 1)[1] for l in g2 if l.startswith(mi + ".")}
                info[mi] = f2
            # theta values of the old Delta-systems mod ell
            alphas = [None]
            if any(o.startswith("U_") for o in ops):
                alphas = [a for a in range(ell) if (a * a - TAU[D] * a + pow(D, 11, ell)) % ell == 0]
            rows = []
            for a in alphas:
                val = 0
                for c, o in zip(theta or [], ops):
                    v = a if o.startswith("U_") else TAU[int(o[2:])]
                    val += c * v
                val %= ell
                hit = [mi for mi, f in info.items() if f.get("residue_degree") == "1" and
                       (int(json.loads(f["residue_poly"])[0]) + val) % ell == 0]
                rows.append({"U_D_root_mod_ell": a, "theta_value": val, "m": hit,
                             "local": {mi: {k: info[mi][k] for k in info[mi] if k.startswith("local_type") or k.startswith("components_through") or k == "residue_poly"} for mi in hit}})
            res.append({"D": D, "record": "anemic" if tag == "HSAN" else "full", "ell": ell,
                        "generation": [g for g in d[tag][1].split("gen=[")[1].split("]")[0].split(";") if g.startswith(f"{ell}:")],
                        "theta_ops": ops, "theta": theta, "maximal_ideals_listed": len(info), "delta_systems": rows})
json.dump(res, open(os.path.join(DATA, "record_lower_bounds.json"), "w"), indent=1)
for r in res:
    for row in r["delta_systems"]:
        loc = {mi: (v.get("local_type.rank"), v.get("local_type.kind"), v.get("components_through.eis", "-"),
                    [k.split(".")[1] for k, x in v.items() if k.startswith("components_through") and x == "certified"]) for mi, v in row["local"].items()}
        print(r["D"], r["record"], "ell", r["ell"], r["generation"], "theta", r["theta"], r["theta_ops"], "U_D root", row["U_D_root_mod_ell"], "->", loc)
