#!/usr/bin/env python3
"""Build algebraic_jl/latex/backtranslation from parent B chapters filtered by kept IDs."""
import re, sys, os, glob
HERE=os.path.dirname(os.path.abspath(__file__))
DST=os.path.dirname(HERE)                  # algebraic_jl/latex/backtranslation
LATEX=os.path.dirname(DST)                 # algebraic_jl/latex
FORK=os.path.dirname(LATEX)                # algebraic_jl
SRC=HERE+'/parent_src'                     # frozen copy of the parent B chapters and generated data @ 84818d0
MODE=sys.argv[1] if len(sys.argv)>1 else 'final'   # provisional|final

# (parent chapter, fork chapter dir) in order
# chapter order = order of the \input lines of A's master (latex/readable/algjl.tex)
CHAPTERS=[m for m in re.findall(r'\\input\{(vol\d/[^}]*)\}',open(LATEX+'/readable/algjl.tex').read()) if os.path.exists(f'{SRC}/{m}.tex')]

kept=set(); droppedlist=set()
IDPAT=re.compile(r'^(I|II|III|X)\.[a-z0-9]+\.[a-z]+:[A-Za-z0-9-]+$')
for f in glob.glob(FORK+'/KEPT_IDS/*.txt'):
    tgt=droppedlist if 'dropped' in f else kept
    for l in open(f):
        w=l.split()[0] if l.strip() else ''
        if IDPAT.match(w): tgt.add(w)

idre=re.compile(r'\\tfstmt\{([^}]*)\}')
startre=re.compile(r'^\\begin\{(definition|theorem|lemma|proposition|corollary|hypothesis|example|conjecture|remark)\}')
secre=re.compile(r'^\\(chapter|section|subsection|part|paragraph)\b')

def parse(lines):
    """-> list of blocks: ('pre'|'sec'|'item', id, [lines])"""
    blocks=[]; cur=None; i=0; n=len(lines)
    def push(kind,id_,l):
        nonlocal cur
        cur=[kind,id_,[l]]; blocks.append(cur)
    while i<n:
        l=lines[i]
        if secre.match(l): push('sec',None,l)
        elif startre.match(l) and any(idre.search(x) for x in lines[i+1:i+4]):
            m=[idre.search(x) for x in lines[i+1:i+4] if idre.search(x)][0]
            push('item',m.group(1),l)
        elif l.startswith('\\begin{tfoutline}'):
            # skip planned-outline block entirely
            while not lines[i].startswith('\\end{tfoutline}'): i+=1
        elif l.startswith('\\input{notation}') or l.strip()=='\\section{Notation table}':
            pass
        else:
            if cur is None: push('pre',None,l)
            else: cur[2].append(l)
        i+=1
    return blocks

allids={}
chap_blocks={}
for ch in CHAPTERS:
    lines=open(f'{SRC}/{ch}.tex').read().split('\n')
    bl=parse(lines); chap_blocks[ch]=bl
    for b in bl:
        if b[0]=='item': allids[b[1]]=ch

# Lean truth: tf_id/tf_aux tags in the fork's Lean sources
lean_tags=set()
for root,_,fs in [x for d in ('AlgJL','Vendor') for x in os.walk(FORK+'/lean/'+d)]:
    for fn in fs:
        if fn.endswith('.lean') and not root.endswith('/Meta'):
            lean_tags.update(re.findall(r'tf_(?:id|aux)\s+"([^"]+)"',open(os.path.join(root,fn)).read()))
lean_tags={t for t in lean_tags if IDPAT.match(t)}
if MODE=='final': kept_file=set(kept); kept=set(lean_tags)   # the Lean sources are the single truth; KEPT_IDS only cross-checked
# Orphans: B-only items living in a parent chapter the fork excludes (ch-0-09-hecke): appended to ch-0-04-top-groups (section 'Auxiliary pairing constructions').
DONOR='vol1/ch-0-09-hecke'; HOST='vol1/ch-0-04-top-groups'
donor_items=[b for b in parse(open(f'{SRC}/{DONOR}.tex').read().split('\n')) if b[0]=='item']
extra=[b for b in donor_items if b[1] in lean_tags and b[1] not in allids and b[1].startswith('I.topgrp.')]
if extra and HOST in chap_blocks:
    chap_blocks[HOST]+= [['sec',None,['\\section{Auxiliary pairing constructions (B-only)}\\label{sec:topgrp-aux-pairing}']]]+extra
    for b in extra: allids[b[1]]=HOST
# Fork-new items (no parent B block, no parent generated data): hand-written blocks in tools/fork_new.tex, each
# introduced by a line `%% fork-new after <anchor ID>`; inserted right after the anchor item's block of its chapter.
FN=HERE+'/fork_new.tex'
if os.path.exists(FN):
    for chunk in re.split(r'^%% fork-new after ',open(FN).read(),flags=re.M)[1:]:
        anchor_id,body=chunk.split('\n',1)
        anchor_id=anchor_id.strip(); ch=allids[anchor_id]
        nb=[b for b in parse(body.rstrip('\n').split('\n')) if b[0]=='item']
        assert len(nb)==1, f'fork_new.tex: one item block per chunk ({anchor_id})'
        bl=chap_blocks[ch]; k=[j for j,b in enumerate(bl) if b[0]=='item' and b[1]==anchor_id][0]
        bl.insert(k+1,nb[0]); allids[nb[0][1]]=ch
if MODE=='provisional':
    keepset=set(allids)  # whole chapters
else:
    keepset=kept
def ipath(i):
    v,a,rest=i.split('.',2); k,slug=rest.split(':',1)
    return f'items/{v}/{a}/{k}--{slug}.tex'
# B-only items (\\bonly in the chapter block): their snippets belong to B (D14); copied from the frozen parent snippets into backtranslation/items/
bonly={b[1] for bl in chap_blocks.values() for b in bl if b[0]=='item' and any('\\bonly' in x for x in b[2])}
def has_snippet(i):
    return os.path.exists(f'{LATEX}/{ipath(i)}') or (i in bonly and os.path.exists(f'{SRC}/{ipath(i)}'))
nosnip=sorted(i for i in keepset if not has_snippet(i))
keepset=set(i for i in keepset if has_snippet(i))   # an item without its A snippet cannot be typeset

dropped=set(); outchaps=[]
usesre=re.compile(r'\\uses\{([^}]*)\}')
def prune_uses(m):
    ids=[x.strip() for x in m.group(1).split(',') if x.strip()]
    k=[x for x in ids if x in keepset]
    return '\\uses{%s}'%','.join(k) if k else ''
for ch,bl in chap_blocks.items():
    # decide sections to drop: section blocks followed by no kept item before next sec
    out=[]; 
    # group into sections
    groups=[]; g=[]
    for b in bl:
        if b[0]=='sec' and b[2][0].startswith('\\section') or b[0]=='sec' and b[2][0].startswith('\\chapter'):
            if g: groups.append(g)
            g=[b]
        else: g.append(b)
    if g: groups.append(g)
    nkept=0
    for g in groups:
        items=[b for b in g if b[0]=='item']
        k=[b for b in items if b[1] in keepset]
        for b in items:
            if b[1] not in keepset: dropped.add(b[1])
        head=g[0]
        is_chapter=head[0]=='sec' and head[2][0].startswith('\\chapter')
        if head[0]=='pre' or is_chapter or k or not items:
            for b in g:
                if b[0]=='item' and b[1] not in keepset: continue
                out+=b[2]
            nkept+=len(k)
    txt='\n'.join(out)
    txt=usesre.sub(prune_uses,txt)
    outchaps.append((ch,txt,nkept))

# dangling \cref / \ref to dropped IDs (any ID not in keepset but known in parent)
parent_all=set()
parent_all.update(re.findall(r'\\tfsetstatus\{([^}]*)\}',open(SRC+'/generated/status.tex').read()))
for f in glob.glob(SRC+'/vol*/*.tex'):
    for m in idre.finditer(open(f).read()): parent_all.add(m.group(1))
deflabels=set()
for ch,txt,nk in outchaps: deflabels.update(re.findall(r'\\label\{([^}]*)\}',txt))
refre=re.compile(r'\\(cref|Cref|ref|autoref|cpageref)\{([^}]*)\}')
nref=0; refs_dropped=set()
def fixref(m):
    global nref
    ids=[x.strip() for x in m.group(2).split(',')]
    bad=[x for x in ids if x not in keepset and (x in parent_all or x.startswith(('ch:','sec:','subsec:')) and x not in deflabels)]
    if not bad: return m.group(0)
    good=[x for x in ids if x not in bad]
    nref+=len(bad); refs_dropped.update(bad)
    parts=[]
    if good: parts.append('\\%s{%s}'%(m.group(1),','.join(good)))
    parts+=['\\texttt{%s}'%x.replace('_','\\_') for x in bad]
    return ', '.join(parts)

def scrub(t):
    t=re.sub(r'\s*\((?:decision )?D-[A-Za-z0-9-]+(?:[;:,][^()]*)?\)','',t)       # (decision D-XXX ...)
    t=re.sub(r'\s*\(D(?:ecision)?\s?\d+[^()]*\)','',t)
    t=re.sub(r'\s*\(see \\texttt\{M\d+[a-z]*-divergences\}\)','',t)
    t=re.sub(r'\s*\(\\texttt\{M\d+[a-z]*-divergences\}\)','',t)
    t=re.sub(r'\s*\(milestone M\w+(?:, unit U\d+)?\)','',t)
    t=re.sub(r';? ?milestone [MQ]\w+(?: and [MQ]\w+)?','',t)
    t=re.sub(r'; D9 route \(\$\\beta\$\)','',t)
    t=t.replace('commutativity is in M1, the rest in M5. ','')
    t=re.sub(r'(\\emph\{Scope:\} area \\texttt\{[^}]*\}(?:, \\texttt\{[^}]*\})*)[.;]? ?(?=\\emph\{Sources)',r'\1. ',t)
    t=t.replace('\\emph{Sources:} as in document A. ','')
    t=re.sub(r'\s*\(plan \\texttt\{docs/[^}]*\}\)','',t)
    R=[(r'\(decision\s+D-GMF;\s*',r'('),
     (r'\(decision D-TARGET of the sprint\)',''),
     (r'Divergences? D-[A-Za-z0-9-]+(?: to D-[A-Za-z0-9-]+)?(?=[ .(])','Divergence from A'),
     (r'D-U7-\d \(','('),
     (r'\s*\(see the divergence note for U9\)',''),
     (r'\(M3: ','('),(r' of M3, not rederived',', not rederived'),
     (r', M[34]([;)])',r'\1'),(r'as in M3/M4','as in the topology chapters'),
     (r"\bM7a's ",''),(r"\bM4's ",'the '),(r"\bQ2's ",''),(r' of M2\b',''),
     (r' ?\(with \$q\$ and \$q\+1\$ as in the corrected form of decision L9\)',''),
     (r'Exit item of M5a \(registry entry \\texttt\{exits\.yaml\}\);','Exit item;'),(r'Exit item of Q1;','Exit item;'),
     (r' of the Iwasawa chapter \(M1\)',' of the Iwasawa chapter'),(r'decomposition of M1 \(','decomposition ('),
     (r'\\emph\{Scope:\} area \\texttt\{smooth\};.*?(?=\\emph\{Sources)',lambda m:'\\emph{Scope:} area \\texttt{smooth}. '),
     (r' Core-late item: may move to M5b\.',''),
     (r', registered in \\texttt\{registry/assumptions\.yaml\}',', registered as a project assumption'),
     (r', \\texttt\{registry/assumptions\.yaml\}',''),
     (r' and imports only the vocabulary of \\texttt\{registry/hyp\\_imports\.yaml\}',' and imports only a restricted vocabulary'),
     (r'\(rule 12, decision D4; registry entry',r'(registry entry'),
     (r'fails at the D1 pin','fails at the pinned Mathlib version'),
     (r"\s*\(L2's divergence note, item~3\)",''),
     (r', Q2 trap 3',''),
     (r'Not proved in this milestone \(scope trim, Q2-U5\)\.','Not proved.'),
     (r'\(exit item of the milestone\)','(exit item)'),
     (r'Proof pending \(W3\)\.','Proof pending.'),
     (r'Per decision Q1-C the statement','The statement'),
     (r'; SCR-Q3-1\)',')'),
     (r'\s*\(nor, since Q3-G1 m-1, the Lean docstring\)',''),
     (r'The hidden binder reported by the audit','The hidden binder'),
    ]
    for a,b in R: t=re.sub(a,b,t,flags=re.S)
    t='\n'.join(l for l in t.split('\n') if not re.match(r'%.*from G1 on',l))
    return t

import shutil
shutil.rmtree(DST+'/items',ignore_errors=True)
for i in sorted(keepset):
    if not os.path.exists(f'{LATEX}/{ipath(i)}'):
        os.makedirs(os.path.dirname(f'{DST}/{ipath(i)}'),exist_ok=True); shutil.copy(f'{SRC}/{ipath(i)}',f'{DST}/{ipath(i)}')
# path scrub of leading header comments
os.makedirs(DST,exist_ok=True)
for ch,txt,nk in outchaps:
    txt=refre.sub(fixref,txt)
    txt=scrub(txt)
    lines=txt.split('\n')
    # drop leading comment lines
    j=0
    while j<len(lines) and (lines[j].startswith('%') or not lines[j].strip()): j+=1
    lines=['%% Document B (back-translation), algebraic_jl fork. Filtered copy of parent chapter %s (parent commit 84818d0); kept items only.'%os.path.basename(ch)]+lines[j:]
    txt='\n'.join(lines)
    txt='\n'.join(l for l in txt.split('\n') if not (l.startswith('%') and re.search(r'docs/|tools/|tex/',l)))
    txt=re.sub(r'\\texttt\{docs/[^}]*\}',"the parent repository's notes",txt)
    txt=txt.replace('\\texttt{tex/shared/hypotheses.tex}','\\texttt{hypotheses.tex}').replace('tex/shared/hypotheses.tex','hypotheses.tex')
    txt=txt.replace('lean/GL2TF/','lean/AlgJL/').replace('GL2TFTests','AlgJLTests')  # path mentions only (Lean decl names GL2TF.* unchanged)
    d=os.path.dirname(f'{DST}/{ch}.tex'); os.makedirs(d,exist_ok=True)
    open(f'{DST}/{ch}.tex','w').write(txt)
    print(f'{ch}: {nk} items kept')

print('ids in chapters:',len(allids),' kept (in chapters):',len(set(allids)&keepset),' dropped:',len(dropped),' refs rewritten:',nref)
inB=set(allids)&keepset
rep2='lean-tags: %d  B-items: %d\nLean tag with no B item: %s\nB item without Lean tag: %s\n'%(len(lean_tags),len(inB),sorted(lean_tags-inB),sorted(inB-lean_tags))
if MODE=='final': rep2+='KEPT_IDS vs Lean tags: in KEPT_IDS only: %s\nin Lean only: %s\n'%(sorted(kept_file-lean_tags),sorted(lean_tags-kept_file))
open(DST+'/.mkB_report.txt','w').write(rep2+'mode %s\nkept-not-in-B: %s\nB-not-in-kept: %s\nkept-but-no-A-snippet (dropped from B): %s\nrefs->texttt: %s\n'%(MODE,
   sorted(kept-set(allids)), sorted(set(allids)-kept), nosnip, sorted(refs_dropped)))

# generated filtered copy
G=DST+'/generated'; os.makedirs(G,exist_ok=True)
CHG={'I.quot.lem:automorphic-right-action-continuous-instance'}   # proof changed in the fork: hash differs from the parent
hdr='%% NOTE: for I.quot.lem:automorphic-right-action-continuous-instance the proof was changed in the fork; its hashes differ from the parent copy recorded here.\n%% FROZEN from parent repo commit 84818d0 (tfaudit stamp 2026-11-13T22:36:14Z, lean tree e209793e...), not regenerated. Filtered to kept IDs.\n'
fre=re.compile(r'^\\tfset\w+\{([^}]*)\}')
for name in ['status','signatures','binders','axioms']:
    out=[hdr]
    for l in open(f'{SRC}/generated/{name}.tex'):
        m=fre.match(l)
        if l.startswith('%'):
            if 'GENERATED' in l: out.append('% (origin) generated by the parent repository status tool; do not edit.\n')
            continue
        if m:
            if m.group(1) in keepset:
                if name=='status': l=re.sub(r'audited \d{4}-\d\d-\d\d','audit inherited from parent @84818d0',l)
                if name=='status' and m.group(1) in CHG: l=re.sub(r'\}\s*$','; proof changed in the fork, hash differs from the parent}',l.rstrip('\n'))+'\n'
                out.append(l)
        else: out.append(l)
    open(f'{G}/{name}.tex','w').write(''.join(out))
