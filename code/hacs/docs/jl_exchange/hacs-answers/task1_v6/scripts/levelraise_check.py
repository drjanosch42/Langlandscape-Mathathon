# SPDX-License-Identifier: CC-BY-4.0
"""For each cuspidal l of coker(alpha*alpha) (level 1 form f, k = 12 in the core grid): does the p-new part H^2/tors carry a
T_q-eigenvalue = a_q(f) mod l for every q in the list?  (char_Z on H^2 from data/hecke_H2.json, a_q(f) mod l from the kernel of
alpha*alpha mod l).  Prints the multiplicity of the root a_q(f) mod l of char(T_q | H^2) for each q."""
import json, sympy
x = sympy.symbols('x')
H2 = {}
for p, k, q, s in json.load(open('data/hecke_H2.json')):
    H2[(p, k, q)] = sympy.Poly(sympy.sympify(s.split(' (')[0]) if not s.startswith('1') else 1, x)
out = []
for r in json.load(open('data/summary.json')):
    p, k = r['p'], r['k']
    for l, e in r['ells'].items():
        l = int(l); ker = e["alpha*alpha_kernel_Tq_mod_l"]; eisv = e["eisenstein_1+q^(k-1)_mod_l"]
        nk = len(next(iter(ker.values()))) if ker else 0
        for i in range(nk):
            if all(ker[q][i] == eisv[q] for q in ker): continue
            res = {}
            for q in ker:
                P = H2.get((p, k, int(q)))
                if P is None: continue
                Pm = sympy.Poly(P.as_expr(), x, modulus=l); a = ker[q][i]
                m = 0; R = Pm
                while R.degree() > 0 and R.eval(a) % l == 0: R = sympy.quo(R, sympy.Poly(x - a, x, modulus=l)); m += 1
                res[q] = (a, m)
            out.append({"p": p, "k": k, "l": l, "a_q(f) mod l, multiplicity in char(T_q|H^2)": res}); break
for o in out: print(o)
json.dump(out, open('data/levelraise_check.json', 'w'), indent=1)
