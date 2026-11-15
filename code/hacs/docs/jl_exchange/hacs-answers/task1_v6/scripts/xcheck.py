# SPDX-License-Identifier: CC-BY-4.0
"""Cross-check the independent Python computation against HACS:
 (1) fresh HACS level_n(p, n, l, qs) runs (data/hacs_level_n_xcheck.out): dim H^1(Gamma_0(p); Sym^n F_l), char poly of T_q mod l;
 (2) Task-0 HACS records (exact char_Z(T_q) of descent(N, n, P).module_Z(), N = 1 and N = p), reduced mod l / compared exactly."""
import json, glob, sys, os
import sympy
T0 = os.path.expanduser('$JL_EXCHANGE/task0_inscope/data')
x = sympy.symbols('x')
out = {"level_n": [], "task0_charZ_level1": [], "task0_charZ_levelp": []}
ln = {}
for line in list(open('data/hacs_level_n_xcheck.out')) + (list(open('data/hacs_level_n_xcheck_ext.out')) if os.path.exists('data/hacs_level_n_xcheck_ext.out') else []):
    if line.startswith('@@LN'):
        _, p, n, l, js = line.split(' ', 4); ln[(int(p), int(n), int(l))] = json.loads(js)
bad = 0
for f in sorted(glob.glob('data/cells/cell_*.json') + glob.glob('data/cells_ext/cell_*.json')):
    d = json.load(open(f)); p, k, n = d['p'], d['k'], d['n']
    # level 1 exact vs task0 D=1
    tp = None; t1 = {'F': []}
    if os.path.exists(f'{T0}/cell_D{p}_n{n}.json'):
        t1 = json.load(open(f'{T0}/cell_D1_n{n}.json'))
    for q_, F, cz in t1['F']:
        if str(q_) in d['charpoly_Tq_H1_SL2Z']:
            mine = sympy.Poly(sympy.sympify(d['charpoly_Tq_H1_SL2Z'][str(q_)]), x).all_coeffs()
            ok = [int(c) for c in mine] == [int(c) for c in cz]
            out["task0_charZ_level1"].append([p, k, q_, ok]); bad += (not ok)
    if os.path.exists(f'{T0}/cell_D{p}_n{n}.json'):
        tp = json.load(open(f'{T0}/cell_D{p}_n{n}.json')); rankZ = tp['MSTATUS'][1]
    for l, e in d['ell'].items():
        l = int(l)
        if tp is not None:
            ok_rank = (e['rank_H1_Gamma0p'] == rankZ)
            out["task0_charZ_levelp"].append([p, k, l, "rank", rankZ, e['rank_H1_Gamma0p'], ok_rank]); bad += (not ok_rank)
        for q_, F, cz in (tp['F'] if tp is not None else []):
            if str(q_) in e.get('charpoly_mod_l_Tq_H1_Gamma0p', {}):
                ok = [int(c) % l for c in cz[::-1]] == e['charpoly_mod_l_Tq_H1_Gamma0p'][str(q_)]
                out["task0_charZ_levelp"].append([p, k, l, q_, ok]); bad += (not ok)
        key = (p, n, l)
        if key in ln:
            h1, h0, dcf, ops = ln[key]
            ok = (h1 == e['rank_H1_Gamma0p'] and h0 == 0)
            row = [p, k, l, "h1", h1, e['rank_H1_Gamma0p'], ok]; bad += (not ok)
            out["level_n"].append(row)
            for o in ops:
                mine = e['charpoly_mod_l_Tq_H1_Gamma0p'].get(str(o['p']))
                ok = (mine == o['charpoly'])
                out["level_n"].append([p, k, l, o['p'], ok]); bad += (not ok)
nchk = sum(len(v) for v in out.values())
out["summary"] = f"checks={nchk} mismatches={bad}"
json.dump(out, open('data/xcheck.json', 'w'), indent=0)
print(out["summary"])
