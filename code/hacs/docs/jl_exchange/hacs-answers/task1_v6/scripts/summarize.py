# SPDX-License-Identifier: CC-BY-4.0
"""Summarise data/cells*/cell_p*_k*.json into data/summary.json + data/grid_table.md (+ data/hecke_H2.md for the core grid)."""
import json, glob, os, sys
from fractions import Fraction
import sympy
x = sympy.symbols('x')
T0 = os.path.expanduser('$JL_EXCHANGE/task0_inscope/data')

def legendre(a, p): return sympy.jacobi_symbol(a % p, p)
def dimS(k, p):
    """dim S_k(Gamma_0(p)), p prime or p = 1, k >= 4 even (standard formula)."""
    if p == 1: mu, n2, n3, c = 1, 1, 1, 1
    else:
        mu = p + 1; c = 2
        n2 = 1 + legendre(-1, p) if p != 2 else 1
        n3 = 1 + legendre(-3, p) if p != 3 else 1
    v = Fraction(k-1, 12)*mu + (Fraction(k//4) - Fraction(k-1, 4))*n2 + (Fraction(k//3) - Fraction(k-1, 3))*n3 - Fraction(c, 2)
    assert v.denominator == 1; return int(v)
def val(N, l):
    N = abs(int(N)); e = 0
    if N == 0: return float('inf')
    while N % l == 0: N //= l; e += 1
    return e

def summarize(dirs, tag):
    rows = []; md = []
    for f in sorted(sum([glob.glob(f'{d}/cell_p*_k*.json') for d in dirs], []),
                    key=lambda f: (int(f.split('_p')[1].split('_')[0]), int(f.split('_k')[1].split('.')[0]))):
        d = json.load(open(f)); p, k, n = d['p'], d['k'], d['n']
        r1 = d['rank_H1_SL2Z']; dS1 = dimS(k, 1); dSp = dimS(k, p); new = dSp - 2*dS1
        assert r1 == 2*dS1 + 1
        cp_p = sympy.Poly(sympy.sympify(d['charpoly_Tq_H1_SL2Z'][str(p)]), x)
        eis = 1 + p**(k-1)
        cusp = sympy.quo(cp_p, sympy.Poly((x - eis), x))          # char poly of T_p on the cuspidal part of H^1 = c_f(x)^2
        b = (p+1) * p**(n//2)
        cuspF = sympy.sqf_list(cusp)  # c^2
        # c(x) with c^2 = cusp
        c = sympy.Poly(1, x)
        for fac, m in cuspF[1]: c *= fac**(m//2)
        cusp_norm = int((c.eval(b) * c.eval(-b)) * (-1)**c.degree()) if c.degree() > 0 else 1   # prod_f (a_p(f)^2 - b^2)
        eis_factor = (1 - p**(k-2)) * (1 - p**k)                    # (1+p^{k-1})^2 - (p+1)^2 p^{k-2}
        ells = {}
        for l, e in sorted(d['ell'].items(), key=lambda t: int(t[0])):
            l = int(l); E = e['E']
            r = e['rank_H1_Gamma0p']
            aa = [v for v in e['alpha*alpha_elementary_divisor_valuations'] if v > 0]
            ells[l] = {
                "coker_alpha_torsion": e['coker_alpha_torsion'],
                "alpha_injective": e['alpha_injective_mod_l^E'],
                "torsion_Tq_eigenvalues_mod_l": e['T_q_on_ker_alpha_mod_l'],
                "alpha*alpha_divisors": [f"{l}^{v}" if v < E else f">= {l}^{E}" for v in aa],
                "alpha*alpha_kernel_Tq_mod_l": e['T_q_on_ker_alpha*alpha_mod_l'],
                "eisenstein_1+q^(k-1)_mod_l": e['eisenstein_value_1+q^(k-1)_mod_l'],
                "v_l(cusp: prod_f a_p(f)^2-(p+1)^2p^(k-2))": val(cusp_norm, l) if c.degree() > 0 else None,
                "v_l(eis: (1-p^(k-2))(1-p^k))": val(eis_factor, l),
                "rank_H1_Gamma0p": r, "modulus": e['modulus'],
                "equivariance_T_alpha": e['equivariance_T_alpha'],
            }
            # consistency: sum of alpha*alpha valuations = v_l(det) = 2 v(cusp) + v(eis)
            tot = sum(aa); exp = 2*(val(cusp_norm, l) if c.degree() > 0 else 0) + val(eis_factor, l)
            ells[l]["sum_vals_matches_formula"] = (tot == exp)
        r = list(ells.values())[0]['rank_H1_Gamma0p'] if ells else None
        row = {"p": p, "k": k, "rank_H1_SL2Z": r1, "dim_S_k(1)": dS1, "dim_S_k(Gamma0(p))": dSp, "dim_S_k_new": new,
               "rank_H1_Gamma0p": r, "rank_H2": (r - 2*r1) if r is not None else None, "expected_rank_H2=2dimS_new": 2*new,
               "H1_SL2Z[1/p]": "0", "candidate_ells": d['candidate_ells'], "ells": ells,
               "checks": {kk: v for kk, v in d.items() if kk.startswith('check')},
               "level1_charpoly_T_p": d['charpoly_Tq_H1_SL2Z'][str(p)],
               "det_alpha*alpha": d['det_alpha*alpha']}
        rows.append(row)
    return rows

def table(rows):
    L = ["| p | k | rk H^1(SL2Z) | rk H^1(G0(p)) | rk H^2 (= 2 dim S_k^new) | H^1(SL2(Z[1/p])) | tors H^2 = tors coker(alpha), l>k, l!=p | coker(alpha*alpha), l>k, l!=p: divisors [ideal] |",
         "|---|---|---|---|---|---|---|---|"]
    for r in rows:
        tors = []; aa = []
        for l, e in r["ells"].items():
            for t in e["coker_alpha_torsion"]:
                ev = e["torsion_Tq_eigenvalues_mod_l"]; eisv = e["eisenstein_1+q^(k-1)_mod_l"]
                tag = "Eis" if all(ev[q] == [eisv[q]] for q in ev) else "?"
                tors.append(f"{t} [{tag}]")
            if e["alpha*alpha_divisors"]:
                ker = e["alpha*alpha_kernel_Tq_mod_l"]; eisv = e["eisenstein_1+q^(k-1)_mod_l"]
                nk = len(next(iter(ker.values())))
                labs = []
                for i in range(nk):
                    labs.append("mixed (kernel vector not a T_q-eigenvector)" if any(ker[q][i] is None for q in ker) else
                                ("Eis" if all(ker[q][i] == eisv[q] for q in ker) else "cusp"))
                if nk == 0: labs = ["(ker mod l trivial?)"]
                aa.append(f"{l}: {' x '.join(e['alpha*alpha_divisors'])} [{','.join(sorted(set(labs)))}]")
        ok = (r["rank_H2"] == r["expected_rank_H2=2dimS_new"])
        L.append(f"| {r['p']} | {r['k']} | {r['rank_H1_SL2Z']} | {r['rank_H1_Gamma0p']} | {r['rank_H2']}{'' if ok else ' (MISMATCH)'} | 0 | "
                 f"{', '.join(tors) if tors else 'none'} | {'; '.join(aa) if aa else 'none'} |")
    return "\n".join(L)

def hecke_H2(rows):
    """char_Z(T_q) on H^2 free part = char_Z(T_q | H^1(G0(p)))/char_Z(T_q | H^1(SL2Z))^2, from HACS Task-0 records."""
    L = ["| p | k | q | char_Z(T_q) on H^2(SL2(Z[1/p]), V)/tors  (factored) |", "|---|---|---|---|"]
    out = []
    for r in rows:
        p, k = r['p'], r['k']; n = k - 2
        tp = json.load(open(f'{T0}/cell_D{p}_n{n}.json'))
        cell = json.load(open(glob.glob(f'data/cells/cell_p{p}_k{k}.json')[0]))
        for q_, F, cz in tp['F']:
            if str(q_) not in cell['charpoly_Tq_H1_SL2Z']: continue
            P = sympy.Poly([int(c) for c in cz], x)
            P1 = sympy.Poly(sympy.sympify(cell['charpoly_Tq_H1_SL2Z'][str(q_)]), x)
            Qq, R = sympy.div(P, P1**2)
            assert R.is_zero
            fq = str(sympy.factor(Qq.as_expr())) if Qq.degree() > 0 else "1 (H^2 has rank 0)"
            L.append(f"| {p} | {k} | {q_} | {fq} |"); out.append([p, k, q_, fq])
    return "\n".join(L), out

if __name__ == "__main__":
    core = summarize(['data/cells'], 'core')
    json.dump(core, open('data/summary.json', 'w'), indent=1, default=str)
    open('data/grid_table.md', 'w').write("# Task 1 grid (p, k): ranks over Z_(l), torsion, alpha*alpha (all l > k, l != p)\n\n" + table(core) + "\n")
    h2md, h2 = hecke_H2(core)
    open('data/hecke_H2.md', 'w').write("# T_q on H^2(SL_2(Z[1/p]), V)/torsion: char_Z = char_Z(H^1(Gamma_0(p)))/char_Z(H^1(SL_2(Z)))^2\n\n"
                                        "Level-p char_Z from the HACS Task-0 records (descent(p,n,P).module_Z()), level-1 char_Z from this computation (= HACS, see xcheck).\n\n" + h2md + "\n")
    json.dump(h2, open('data/hecke_H2.json', 'w'), indent=0)
    if os.path.isdir('data/cells_ext') and glob.glob('data/cells_ext/*.json'):
        ext = summarize(['data/cells_ext'], 'ext')
        json.dump(ext, open('data/summary_ext.json', 'w'), indent=1, default=str)
        open('data/grid_table_ext.md', 'w').write("# Extension k = 16..24 (beyond the requested range)\n\n" + table(ext) + "\n")
    bad = [(r['p'], r['k'], l) for r in core for l, e in r['ells'].items() if not e['sum_vals_matches_formula']]
    print("formula mismatches:", bad)
    print(open('data/grid_table.md').read())
