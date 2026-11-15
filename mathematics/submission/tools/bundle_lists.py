# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
# Export the Lean "submission bundle" work lists from generated/lean-table.json. Usage: python3 -I mathematics/submission/tools/bundle_lists.py <repo root>
import json, os, re, csv, sys
root = sys.argv[1]
gen = os.path.join(root, 'mathematics/submission/generated')
d = json.load(open(os.path.join(gen, 'lean-table.json')))
DIS = {'PadicOrdDecomp', 'RamNrdSurj', 'BrandtStabFree'}
LEANROOT = os.path.join(root, 'lean/Langlandscape')

def binders(path, line):
    src = open(path).read().split('\n')
    text = '\n'.join(src[line-1:line+80])
    # signature up to the first ':=' at depth 0
    out, depth, groups, cur = [], 0, [], ''
    opens, closes = '([{⦃', ')]}⦄'
    i = 0; started = False
    while i < len(text):
        c = text[i]
        if depth == 0 and text.startswith(':=', i): break
        if c in opens:
            if depth == 0: cur = ''
            depth += 1
        if depth > 0: cur += c
        if c in closes:
            depth -= 1
            if depth == 0: groups.append(cur)
        i += 1
    return groups

def locate(file):
    for base in (LEANROOT, os.path.join(LEANROOT, 'Langlandscape')):
        p = os.path.join(base, file)
        if os.path.exists(p): return p
    return None

rows18 = []
for r in d['rows']:
    if r['kind'] == 'theorem' and r['hyp_args'] and set(r['hyp_args']) <= DIS:
        p = locate(r['file']); pos = []; others = []
        if p:
            gs = binders(p, r['line'])
            others = [g.strip() for g in gs if g.startswith('(') and g.strip() not in [b.strip() for b in r['hyp_binders']] and ':' in g]
            for j, g in enumerate(gs):
                for b in r['hyp_binders']:
                    if b.strip() == g.strip(): pos.append((j + 1, g.strip(), g[0]))
        rows18.append({'name': r['name'], 'file': f"{r['file']}:{r['line']}", 'discharged_hyps': '+'.join(r['hyp_args']),
                       'binder_positions': '; '.join(f"#{j} {'explicit' if br=='(' else 'instance/implicit'} {g}" for j, g, br in pos) or 'see hyp_binders: ' + ' '.join(r['hyp_binders']),
                       'other_explicit_binders': ' '.join(' '.join(o.split()) for o in others),
                       'discharge_lemmas': ', '.join(r.get('discharge') or []) or {'RamNrdSurj':'Langlandscape.Hyp.ramNrdSurj_holds','BrandtStabFree':'Langlandscape.Hyp.brandtStabFree_holds','PadicOrdDecomp':'see HYPOTHESES.md (discharged)'}.get(r['hyp_args'][0], '')})
rows104 = []
for r in d['cited_unaudited']:
    why = 'not listed in Audit/PrintAxioms.lean (chapter-cited; covered only by the sorry count and the forbidden-token grep)'
    if 'Tests' in r['where'] or 'Test' in r['name']: why = 'test-library declaration (LanglandscapeTests), not in the audited library set'
    hyps = r.get('hyp_args') or []
    rows104.append({'name': r['name'], 'file': r['where'], 'kind': r['kind'], 'claims': ' '.join(r['labels']),
                    'hyp_args': '+'.join(hyps), 'only_discharged_hyps': 'yes' if hyps and set(hyps) <= DIS else '', 'why_not_audited': why})
# File names carry the counts (and the JSON the gated tree), so the pre-bundle work lists (gated tree 2323a252:
# bundle-uncited-104.csv, bundle-discharged-18.csv, bundle-lists.json) are kept next to the post-bundle ones.
tree = d['summary']['gate_tree']
for fn, rows in ((f'bundle-uncited-{len(rows104)}.csv', rows104), (f'bundle-discharged-{len(rows18)}.csv', rows18)):
    with open(os.path.join(gen, fn), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
json.dump({'cited_unaudited': rows104, 'discharged_only': rows18}, open(os.path.join(gen, 'bundle-lists.json' if tree == '2323a252' else f'bundle-lists-{tree}.json'), 'w'), indent=1, ensure_ascii=False)
print(len(rows104), len(rows18), sum(1 for r in rows104 if r['only_discharged_hyps']))
for r in rows18: print(r['name'], r['discharged_hyps'], r['binder_positions'][:120])
