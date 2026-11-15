# SPDX-License-Identifier: CC-BY-4.0
"""(c) comparison on level-1 cusp forms: a_p(f)^2 - (p+1)^2 p^{k-2} (factored) vs the cuspidal elementary divisors of
coker(alpha* alpha) over Z_(l), l > k, l != p.  Usage: cusp_compare.py data/summary.json [data/summary_ext.json]"""
import json, sys, sympy
x = sympy.symbols('x')
out = []; md = ["| p | k | T_p cusp factor (level 1) | N(a_p^2-(p+1)^2 p^(k-2)) factored | l > k, l != p: coker(alpha*alpha)_m (cusp m) |", "|---|---|---|---|---|"]
for f in sys.argv[1:]:
    for r in json.load(open(f)):
        p, k = r['p'], r['k']; n = k - 2
        if r['dim_S_k(1)'] == 0: continue
        cp = sympy.Poly(sympy.sympify(r['level1_charpoly_T_p']), x)
        cusp = sympy.quo(cp, sympy.Poly(x - (1 + p**(k-1)), x))
        c = sympy.Poly(1, x)
        for fac, m in sympy.sqf_list(cusp)[1]: c *= fac**(m//2)
        b = (p+1)*p**(n//2)
        N = int(c.eval(b)*c.eval(-b)*(-1)**c.degree())
        fN = sympy.factorint(N)
        cus = []
        for l, e in r['ells'].items():
            ker = e["alpha*alpha_kernel_Tq_mod_l"]; eisv = e["eisenstein_1+q^(k-1)_mod_l"]
            nk = len(next(iter(ker.values()))) if ker else 0
            ncusp = sum(1 for i in range(nk) if not all(ker[q][i] == eisv[q] for q in ker))
            if ncusp: cus.append(f"{l}: {' x '.join(e['alpha*alpha_divisors'])} (cusp kernel dim {ncusp}, T_q mod l = {ker})")
        md.append(f"| {p} | {k} | {sympy.factor(c.as_expr())} | {N} = {' * '.join(f'{a}^{b}' if b > 1 else str(a) for a, b in sorted(fN.items()))} | {'; '.join(cus) if cus else 'none'} |")
        out.append({"p": p, "k": k, "cusp_charpoly_T_p": str(c.as_expr()), "norm": str(N), "norm_factored": {str(a): b for a, b in fN.items()}, "alpha*alpha_cusp": cus})
print("\n".join(md))
json.dump(out, open('data/cusp_compare.json', 'w'), indent=1, default=int)
