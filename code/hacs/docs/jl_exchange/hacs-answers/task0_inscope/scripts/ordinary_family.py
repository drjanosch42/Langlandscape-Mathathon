#!/usr/bin/env python3
# SPDX-License-Identifier: CC-BY-4.0
"""Task 0(ii) from HACS's exact char_Z(T_p | H^1(Gamma_0(N); Sym^n Z^2)/tors) (descent records, N = 1 and 3, n = 2..60 even).
 * p-ordinary rank of H^1(Gamma_0(3); Sym^{k-2})/tors (x) Z_p := number of roots of char_Z(T_p) that are p-adic units
   = deg - ord_x(char_Z(T_p) mod p), counted factor by factor; split Eisenstein / level-1 old / 3-new.
 * Delta / g p-ordinarity: tau(p) mod p, a_p(g) mod p.
 * Persistence test of the mod-17 old/new congruence along k = 12 + (p-1) j: at weight k, a level-1 eigen-system with
   a_3 = alpha in the Delta-family residue class (some factor f of char_Z(T_3 | level 1 cusp) with f(tau(3)) = 0 mod p, i.e. a root
   congruent to tau(3) mod a prime above p -- note a_3 of the family member is congruent to tau(3) mod p since 3^(k-1) = 3^11 mod p)
   and the level-raising condition at 3 mod 17: Res_x(f, x^2 - 16*3^(k-2)) = 0 mod 17 (necessary for a 17-congruence with a 3-new form).
Usage: ordinary_family.py <data/family_charpolys.txt>  -> prints tables, writes JSON next to it."""
import json, sys, os
from sympy import Poly, symbols, resultant, ZZ

x = symbols("x")
L1, L3 = {}, {}
for line in open(sys.argv[1]):
    if line.startswith("@@L1 "): n, g, f = json.loads(line[5:]); L1[n] = (g, {c["p"]: c for c in f})
    if line.startswith("@@L3 "): n, g, f = json.loads(line[5:]); L3[n] = (g, {c["p"]: c for c in f})

def factors(rec):
    return [([int(c) for c in fa["coefficients"]], fa["multiplicity"]) for fa in rec["factors"]]

def ord_count(coeffs, p):          # number of unit roots of a monic integer poly (high->low) mod p
    red = [c % p for c in coeffs]
    deg = len(coeffs) - 1
    ordx = 0
    for c in reversed(red):
        if c == 0: ordx += 1
        else: break
    return deg - ordx

tau = {2: -24, 3: 252, 5: 4830, 7: -16744, 11: 534612, 13: -577738}
out = {"ordinary": [], "persistence": [], "Delta_g": {}}
ag = {}
for fa, m in factors(L3[10][1][5]) + []:
    pass
for p in [5, 7, 11, 13]:
    rec3 = L3[10][1][p]
    a = [-c[1] for c, m in factors(rec3) if len(c) == 2 and -c[1] not in (1 + p ** 11, tau[p])]
    ag[p] = a[0]
    out["Delta_g"][p] = {"tau_p": tau[p], "tau_p_mod_p": tau[p] % p, "Delta_ordinary": tau[p] % p != 0,
                         "a_p_g": a[0], "a_p_g_mod_p": a[0] % p, "g_ordinary": a[0] % p != 0}
print("Delta, g p-ordinarity:", json.dumps(out["Delta_g"]))

for p in [5, 7, 11, 13]:
    for n in sorted(L3):
        k = n + 2
        e = 1 + p ** (k - 1)
        f3 = factors(L3[n][1][p]); f1 = factors(L1[n][1][p])
        eis3 = sum(m for c, m in f3 if c == [1, -e]); eis1 = sum(m for c, m in f1 if c == [1, -e])
        tot3 = sum(ord_count(c, p) * m for c, m in f3)
        cusp3 = sum(ord_count(c, p) * m for c, m in f3 if c != [1, -e])
        cusp1 = sum(ord_count(c, p) * m for c, m in f1 if c != [1, -e])
        rk3 = sum((len(c) - 1) * m for c, m in f3)
        out["ordinary"].append({"p": p, "k": k, "k_mod_p_minus_1": k % (p - 1), "rank_H1_level3": rk3, "eis": eis3,
                                "ord_total": tot3, "ord_cusp": cusp3, "ord_cusp_old": 2 * cusp1, "ord_cusp_new": cusp3 - 2 * cusp1})
    for k in range(12, 63, p - 1):
        n = k - 2
        if n not in L1: continue
        f1 = [c for c, m in factors(L1[n][1][3]) if c != [1, -(1 + 3 ** (k - 1))]]
        hits = []
        for c in f1:
            P = Poly(c, x, domain=ZZ)
            fam = P.eval(tau[3]) % p == 0
            cp = factors(L1[n][1][p])
            res = int(resultant(P.as_expr(), x ** 2 - 16 * 3 ** (k - 2), x)) % 17
            hits.append({"T3_factor_degree": len(c) - 1, "in_Delta_family_mod_p": fam, "level_raising_at_3_mod_17": res == 0})
        out["persistence"].append({"p": p, "k": k, "Delta_ordinary_at_p": tau[p] % p != 0, "level1_T3_factors": hits})

for r in out["ordinary"]:
    pass
json.dump(out, open(os.path.join(os.path.dirname(sys.argv[1]), "ordinary_family.json"), "w"), indent=1)
for p in [5, 7, 11, 13]:
    print(f"\np = {p}: ordinary ranks of H^1(Gamma_0(3); Sym^(k-2))/tors (x) Z_p  [total = Eis + cusp; cusp = old(from level 1) + new]")
    for c in range(0, p - 1, 2):
        row = [r for r in out["ordinary"] if r["p"] == p and r["k_mod_p_minus_1"] == c]
        print(f"  k = {c} mod {p-1}: " + "  ".join(f"k={r['k']}:{r['ord_total']}({r['ord_cusp_old']}+{r['ord_cusp_new']})" for r in row))
    print("  persistence along k = 12 + (p-1)j:", [(r["k"], [(h["T3_factor_degree"], h["in_Delta_family_mod_p"], h["level_raising_at_3_mod_17"]) for h in r["level1_T3_factors"]]) for r in out["persistence"] if r["p"] == p])
