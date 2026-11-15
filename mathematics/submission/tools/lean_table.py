# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Generate the Lean declaration table of the submission report.

Inputs (all read-only):
  * lean/Langlandscape/Audit/PrintAxioms.lean      -- the audited declarations (one ``#print axioms`` each)
  * the gate axiom log (``c-axioms.log``)          -- read with ``git show <gate-ref>:<path>`` or from a file
  * lean/Langlandscape/Langlandscape/**/*.lean     -- file:line, signature (explicit Hyp.* arguments), docstring
  * lean/Langlandscape/HYPOTHESES.md               -- the registry (names; discharge lemmas)
  * mathematics/chapters/**.tex                    -- the chapter labels whose text cites a declaration

Outputs:
  * mathematics/submission/generated/lean-table.tex   -- three longtables (main, uncited/cited-unaudited, appendix)
  * mathematics/submission/generated/lean-table.json  -- the same data, machine-readable

Usage (from anywhere):  python3 -I mathematics/submission/tools/lean_table.py [--axlog FILE] [--gate-ref REF] [--gate-tree T]

Mapping rules (documented in the generated file as well):
  * A declaration is *cited* by a chapter label if its full name appears in ``\\lean{...}`` (or, for full names or
    unambiguous dotted/underscored suffixes of an audited name, in ``\\texttt{...}``) inside the environment with
    that label, inside the ``proof`` following it, or in the running text after it and before the next
    theorem-like environment or sectioning command (where the chapters put their "Lean:" notes).
  * The main table contains the audited declarations cited from theorem / proposition / lemma / corollary labels.
  * Explicit hypothesis arguments are read off the signature: binders (and arrow antecedents of the type) whose type
    mentions one of the 29 registered hypotheses.
  * The "difference" column combines (i) a per-label qualifier transcribed from the chapter's Lean note (``LABEL_NOTES``
    below; each entry was checked against the chapter text at the final tree), (ii) per-declaration qualifiers
    (``DECL_NOTES``), and (iii) qualifier phrases found in the declaration's docstring. Where none applies the
    entry is "see chapter label": no match is claimed that was not checked.
"""
from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
from collections import OrderedDict, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve()
ROOT = HERE.parents[3]
LEAN = ROOT / "lean" / "Langlandscape"
LIB = LEAN / "Langlandscape"
AUDIT = LEAN / "Audit" / "PrintAxioms.lean"
REGISTRY = LEAN / "HYPOTHESES.md"
CHAPTERS = ROOT / "mathematics" / "chapters"
MAIN_TEX = ROOT / "mathematics" / "main.tex"
OUT_DIR = ROOT / "mathematics" / "submission" / "generated"
GATE_REF = "origin/titan/bsf-gate-1"   # final gate (build machine A, from scratch, unseeded worktree); previous: origin/titan/subl-gate-1, origin/titan/ramnrd-final-2
GATE_TREE = "c70ef3a9"                  # gated Lean tree (final gate bsf-gate-1, logs fa755069); previous: 28d2b091 (bundle gate dc61af50), 2323a252
AXLOG_PATH = "lean/Langlandscape/.titan/out/c-axioms.log"
STD = ["propext", "Classical.choice", "Quot.sound"]

# --------------------------------------------------------------------------------------------------------------
# The 29 registered hypotheses (HYPOTHESES.md); short display name -> regex fragment of the Lean name after `Hyp.`
HYPS = [
    "EichlerMass", "JLClassical", "LambdaJL", "SA", "HS", "BTtree", "SerreCoh", "SerreFree", "RamNrdSurj",
    "IharaH0", "EllipticCount", "BrandtStabFree", "PadicOrdDecomp", "MordLambdaFree", "HidaControl", "HsiehCR",
    "InvLimExact", "X.char", "X.gal", "X.iso", "HsiehGor", "OldDecomp", "HsiehGorFull", "FreeRankTwo",
    "ResidualBurnside", "TamSpec", "HidaControlGL2", "KimOta", "KimOtaRT",
]
# Rows whose axiom lines come from an acceptance build, not from the final gate (stated in Table L3's preface).
ACCEPTANCE = {
    "Langlandscape.Hyp.brandtStabFree_holds", "Langlandscape.StabFree.Orbit.brandtStabFree_of_core",
    "Langlandscape.StabFree.Principal.principality", "Langlandscape.StabFree.LocalPi.local_pi",
    "Langlandscape.StabFree.Core.stabFree_core",
}
ACC_NOTE = ""   # the five BrandtStabFree rows are covered by the final gate bsf-gate-1
DISCHARGE = {
    "PadicOrdDecomp": ("discharged", r"\texttt{Ordinary.\allowbreak{}padicOrdDecomp\_\allowbreak{}holds}"),
    "RamNrdSurj": ("discharged", r"\texttt{Hyp.\allowbreak{}ramNrdSurj\_\allowbreak{}holds}"),
    "BrandtStabFree": ("discharged", r"\texttt{Hyp.\allowbreak{}brandtStabFree\_\allowbreak{}holds}"),
    "ResidualBurnside": ("conditionally discharged",
                         r"\texttt{Hyp.\allowbreak{}residualBurnside\_\allowbreak{}of\_\allowbreak{}absIrred} "
                         "(modulo absolute irreducibility)"),
}
_HYP_ALT = "|".join(sorted((re.escape(h) for h in HYPS), key=len, reverse=True))
HYP_QUAL_RE = re.compile(r"(?<![\w.'])(?:Langlandscape\.Hyp\.|GL2TF\.Hyp\.|Hyp\.)(" + _HYP_ALT + r")(?![\w'.])")
HYP_BARE_RE = re.compile(r"(?<![\w.'])(" + _HYP_ALT + r")(?![\w'.])")

BLOCK_TITLES = {
    "Stage 01": "stage 01",
    "S02 block": "stage 02",
    "Stage 03": "stages 03 and 04, and the first commutative-algebra lane of stage 06",
    "stage 05": "stage 05",
    "S06 integration round 1": "stage 06, commutative algebra",
    "stage 06": "stage 06, the defect layer and its hypotheses",
    "submission bundle": "submission bundle: chapter-cited declarations added to the audit, and Uncond.lean",
}
THEOREMLIKE = {"theorem", "proposition", "lemma", "corollary"}
LABELLED_ENVS = THEOREMLIKE | {"definition", "remark", "hypothesis", "interface", "example", "conjecture",
                               "testcase"}

# --------------------------------------------------------------------------------------------------------------
# Per-label qualifiers, transcribed from the chapters' Lean notes at the final tree (read by hand; LaTeX-safe text).
LABEL_NOTES: dict[str, str] = {
    # ---- stage 01
    "prop:s01-finite": r"Formalized here: finiteness of $X_B(U)$ and $|\Gamma_x|$ divides 24; for the remaining parts the chapter cites results of the frozen import, which are not among the audited declarations",
    "lem:s01-stab": r"(a), (c) and (b) formalized; (b$'$) only for the tower levels (\texttt{diamondAct\_free})",
    "lem:s01-nrd": r"Split-prime parts and assembly take the $\ell\mid D$ part as the explicit argument \texttt{Hyp.RamNrdSurj}, discharged in Lean by \texttt{Hyp.ramNrdSurj\_holds}; the Lean proof of the ramified part proves a stronger local statement (every $\ell$-adic unit is a reduced norm, all $\ell$); the representative statement uses \texttt{Hyp.HS} (cited Hasse--Schilling)",
    "thm:s01-mass": r"(a) Eichler's mass formula is the registered hypothesis \texttt{Hyp.EichlerMass} (cited); the $w$-weighted level change is formalized; the class number at the tower levels is formalized only under \texttt{Hyp.EichlerMass}",
    "prop:s01-adjoint": r"Formalized for general $g$ (\texttt{brandtPairing\_heckeTHom}) and the named ``in particular'' clauses; the $U_p$ clause is Lemma lem:s01-Up(d), which has no Lean counterpart",
    "lem:s01-Up": r"(a), (b), the coset half of (c), and (e) formalized; the trace half of (c) and (d) have no Lean counterpart",
    "prop:s01-relations": r"Only (b) second half, (c) first half, and (c) second half in the $R_g$ form (not the $\rho_g$ form on $X_B(U)$); for the other parts the chapter cites results of the frozen import (at maximal level, resp.\ for $(n,DM)=1$), which are not among the audited declarations",
    "lem:s01-dictionary": r"Only $k=2$ at level $\hat{\mathcal O}^\times$; all $k$ and level $\hat{\mathcal O}(M)^\times$ not formalized",
    "thm:s01-JLclassical": r"Schematic interface only: $k=2$, trivial coefficients, abstract Hecke module in place of $S_k(\Gamma_0(DM))^{D\text{-new}}$; a registered hypothesis (cited), never discharged",
    "thm:s01-lambdaJL": r"Schematic interface: the $\mathrm{GL}_2$ side (algebra, generators, ideal) is abstract data; a registered hypothesis (cited), never discharged",
    # ---- stage 02
    "lem:s02-tree": r"(a) (the tree is a $(q+1)$-regular tree) is the registered hypothesis \texttt{Hyp.BTtree} (cited); (b)--(d) formalized in the coset model of the tree; the lattice model and its identification with the coset model are not formalized",
    "lem:s02-normone": r"(a) formalized assuming $U'\le\hat{\mathcal O}^\times$ (stronger than the text, holds at all levels used); (b) formalized modulo \texttt{Hyp.HS} (Hasse--Schilling, cited)",
    "thm:s02-SA": r"Not a theorem in Lean: strong approximation $(\mathrm{SA}_U)$ is the registered hypothesis \texttt{Hyp.SA} (cited); its derivation from density is not formalized",
    "prop:s02-BG": r"All tree-free parts formalized in the coset model; (i)$\Rightarrow$(iii) modulo \texttt{Hyp.BTtree}; the ``in particular'' modulo \texttt{Hyp.SA}, \texttt{Hyp.HS}, \texttt{Hyp.BTtree}; the last clause of (b) is not formalized",
    "prop:s02-quot": r"(a) given connectivity (iii) (\texttt{Tree.BGConnected} as an argument) or modulo \texttt{Hyp.SA}, \texttt{Hyp.HS}; (b) the three stabiliser identities, without (iii); (c) only for trivial coefficients $V=R$ and the pull/push maps (not the traces, not general $V$, not $\Pi_\ell$)",
    "prop:s02-coh": r"(b) for trivial coefficients is the registered hypothesis \texttt{Hyp.SerreCoh} (cited); only the combinatorial part $\ker(\mathrm{tr}_0,\mathrm{tr}_1)=\nu'(\ker\partial)$ for $V=R$ is formalized, assuming all $w_x$ units in $R$",
    "prop:s02-harm": r"Only the $q$-new module for $V=R$ and $\nu_{U'}:\ker\partial\cong\ker(\mathrm{tr}_0,\mathrm{tr}_1)$, assuming all $w_x$ units in $R$; the isomorphism with $H_1$ is \texttt{Hyp.SerreCoh}; the identification with harmonic cochains on the tree is not formalized",
    "prop:s02-free": r"(a) is the registered hypothesis \texttt{Hyp.SerreFree} (cited); the count in (b) is formalized under weaker hypotheses than stated ($\Gamma_x=1$ only); the homology statement of (b) is not formalized",
    "prop:s02-Mhomprops": r"Only (d), for trivial coefficients $V=R$ (\texttt{normMap\_comp\_s0Push}, \texttt{normMap\_comp\_s1Push}; the other declarations are the maps of Def.~def:s02-Mhom); (a)--(c), (e), (f) and general $V$ are not formalized",
    "prop:s02-duality": r"Only the pushforward identity $\langle s_{j*}a,f\rangle_{\rm ev}=\langle a,s_j^*f\rangle_{\rm ev}$ of (a) ($j=1$: \texttt{evalPairing\_s1Push}; $j=0$ as the level-change case \texttt{evalPairing\_pushforward}); the transfer identity of (a), $\delta=\partial^{\mathsf T}$ and (b) are not formalized",
    "prop:s02-indefprops": r"Only (c), given connectivity (\texttt{BGConnected}), as a $\mathbb Z$-\texttt{finrank}; (a), (b), (d) not formalized",
    # ---- stage 03
    "prop:s03-phi": r"Only for $E\neq\emptyset$ with all edges oriented $v_0\to v_1$; orientation independence and the example $w=(2,2,2)$ not formalized",
    "lem:s03-cyclic": r"Only for two-vertex graphs with $E\neq\emptyset$, edges $v_0\to v_1$",
    "lem:s03-elliptic": r"Not a theorem in Lean: the statement is the registered hypothesis \texttt{Hyp.EllipticCount} (cited), which also contains $|X_B(\hat{\mathcal O}^\times)|=1$ for $q\in\{2,3\}$",
    "prop:s03-mazur": r"Abstract arithmetic core formalized ($q\ge5$); the identification with the DR graph (\texttt{mazur\_check}, all primes $q$) modulo \texttt{Hyp.EllipticCount} and \texttt{Hyp.EichlerMass}; the chapter's elementary derivation of the case $q=2,3$ is replaced by the $q\le3$ clause of \texttt{Hyp.EllipticCount}",
    "lem:s03-stabfree": r"Formalized: the registered hypothesis \texttt{Hyp.BrandtStabFree} is discharged by \texttt{Hyp.brandtStabFree\_holds}; the Lean statement is weaker than the lemma (only at $\hat{\mathcal O}^\times$, $M=1$)",
    "prop:s03-phieis": r"Abstract core formalized (steps (2)--(4)); the instantiation at $U=\hat{\mathcal O}^\times$ modulo \texttt{Hyp.BrandtStabFree} (step (1))",
    "prop:s03-LRdef": r"Abstract core under the fibre-sum and symmetry hypotheses; the symmetry is discharged at the quaternionic instances ($\hat{\mathcal O}^\times$, $U_0$); the definition of $s_j^\dagger$ as weighted adjoint and the index formula (steps (0)--(2)) are not formalized",
    "lem:s03-bip": r"Abstract graph statement (no quaternions), any commutative ring $R$ (rank over $\mathbb Z$)",
    "thm:s03-ribet": r"(a) and the rank in (c) formalized under connectivity (\texttt{Tree.BGConnected} as an argument) or, in the \texttt{\_of\_SA\_HS} versions, modulo \texttt{Hyp.SA}, \texttt{Hyp.HS}, \texttt{Hyp.BTtree}; (b) with coefficients $V$: definitions and compatibilities only, the exactness itself is not formalized",
    "cor:s03-ihara": r"(i), (ii) formalized (any $A$) given connectivity, or modulo \texttt{Hyp.SA}, \texttt{Hyp.HS}, \texttt{Hyp.BTtree}; (ii$'$) not formalized",
    "thm:s03-iharaH0": r"Definitions only ($\tau$, diamonds, $\varepsilon$, well-definedness predicate); clause (a) is the registered hypothesis \texttt{Hyp.IharaH0} (an assumption, not a theorem); clause (b) is neither stated nor proved in Lean",
    # ---- stage 04
    "lem:s04-ekills": r"For $\mathbb Z_p$, $U=U_1(M)$, $p\ge5$; \texttt{hdec} discharged. (a) degree part and (d) formalized; (b), (c) only in abstract form (graph inputs and $\Phi^{\mathrm{comb}}\cong\mathbb Z/|X_s|$ as hypotheses; the valuation bound modulo \texttt{Hyp.EichlerMass}); the $H_0$ clause and the flatness identification are not formalized",
    "prop:s04-freeA": r"For $\mathcal O=\mathbb Z_p$, $U=U_1(M)$, $p\ge5$ (also over $(\mathbb Z/p^m)[\Delta_s]$); general $\mathcal O_E$ and other levels not formalized; \texttt{hdec} discharged, so free of registered hypotheses",
    "lem:s04-hida": r"For $\mathbb Z_p$, $U=U_1(M)$, $p\ge5$; the first claim of (c), the tensor-product isomorphism as a stated equivalence, and the rank independence of $s$ in (d) are not formalized",
    "thm:s04-control": r"(a) finite-level part only, for $\mathbb Z_p$, $U=U_1(M)$, $p\ge5$; constancy of the rank in $s$ not formalized; the $\Lambda$-adic half is only stated, as the open hypothesis \texttt{Hyp.MordLambdaFree}; (b) is the schematic registered hypothesis \texttt{Hyp.HidaControl} (abstract modules, $U_1(M)$-type levels, $p\nmid\varphi(M)$)",
    "thm:s04-lambdaribet": r"Finite-level sequence of (a) and (c) at every $s\ge1$ formalized (the \texttt{\_uncond} versions: free of \texttt{Hyp.PadicOrdDecomp}, with the connectivity of $\mathrm{BG}(UU_s,q)$ as an explicit argument) for $E=\mathbb Q_p$, $U=U_1(M)$, $p\ge5$, $q\ne p$; the limit statement takes the surjectivity of the $A$-transitions as a literal argument \texttt{hA} (the conclusion of \texttt{Hyp.InvLimExact}), which is not formalized; (b) not formalized",
    "prop:s04-ekillsVk": r"Not formalized (the chapter marks the transfer step as still to be written); the citation is of \texttt{Hyp.SA} only",
    "prop:s04-etaprinciple": r"Statement as in the chapter: (a), (b) in full generality, no registered hypotheses (checked in the final-report audit)",
    "thm:s04-Gor": r"Not a theorem in Lean: registered hypothesis \texttt{Hyp.HsiehGor} (cited, Hsieh Thm 4.5); \texttt{Setting.gor\_new} instantiates it over $\Lambda$, \texttt{gor\_new\_of\_I} over $I_F$",
    # ---- stage 05
    "lem:s05-consistency": r"Only (b)--(d), with scope reductions: (b) per local factor of the diamond; (c) only ``the weights agree'' form of the projection formula, under a hypothesis on the weights; (d) only for $s'=s+1$ on $\mathbb Z[S_s]^0$; (a) not formalized",
    "prop:s05-subquot": r"Statement as in the chapter, except that the splitting hypothesis is taken in the form $(\mathfrak a+\mathfrak b)T_K=T_K$; its CRT equivalence with the product decomposition is not formalized",
    "prop:s05-Xiso": r"Only the algebraic half ($H$ free of rank one over a local Gorenstein $T$, $T/\mathfrak a$ Gorenstein); the verification of (i)--(iii) for the Hecke algebras of the modular curve and the $\Lambda$-adic compatibility are not formalized",
    "prop:s05-Xlambda": r"Part (a) at finite level only, for an abstract \texttt{CharGroupData} (not the character group of $J_s$ itself); an existence (\texttt{Nonempty}) statement, not that the equivalence is induced by $\varphi_s$; inverse limit, (b)--(d), Galois and monodromy statements not formalized",
    # ---- stage 06
    "lem:s06-cyclic": r"none recorded in the chapter's Lean note",
    "lem:s06-S": r"none recorded (the chapter states: full statement)",
    "lem:s06-G": r"Statement as in the chapter (checked)",
    "lem:s06-D": r"(a)--(c) for the structure \texttt{NewOldData}; the splitting hypothesis in the field-free form \texttt{split}; the $S$-isomorphisms as $A$-linear isomorphisms plus equivariance lemmas; the final sentence on base change not formalized",
    "lem:s06-split": r"Only the second equivalence; the first (Chinese remainder theorem, product decomposition) is not formalized",
    "thm:s06-E": r"Abstract statement: (i), (ii), (iii) (both halves) and (iv) for $S'$ $A$-free, under the hypotheses of Lemma lem:s06-D as \texttt{NewOldData}; not formalized: the localisation clause of (iii) for $A$ normal, the isomorphism $\mathrm{im}(\mathfrak b\to S')\cong\mathfrak b\cong S'^\vee$ standalone, and the specialisation $S=R$, $A=I_F$",
    "lem:s06-decomp": r"Not a theorem in Lean: registered hypothesis \texttt{Hyp.OldDecomp} for (c) (proved in the text modulo cited results)",
    "lem:s06-tam": r"Not a theorem in Lean: registered hypothesis \texttt{Hyp.TamSpec}",
    "lem:s06-control": r"Not a theorem in Lean: registered hypothesis \texttt{Hyp.HidaControlGL2} (cited)",
    "thm:s06-KO": r"Not a theorem in Lean: registered hypothesis \texttt{Hyp.KimOta} (cited, Kim--Ota)",
    "prop:s06-levM": r"Not a theorem in Lean: registered hypothesis \texttt{Hyp.KimOtaRT} (cited), the inclusion only",
    "prop:s06-galois": r"Given \texttt{Hyp.ResidualBurnside}, \texttt{Hyp.FreeRankTwo} is equivalent to $\mathfrak t_q\subseteq\mathfrak c_q$ (both directions proved), so the Galois half is not formalized independently: its arithmetic content is the cited hypothesis; \texttt{Hyp.ResidualBurnside} is discharged only given absolute irreducibility (H2)",
    "lem:s06-traceform": r"Same statement, $G$ any monoid (chapter)",
    "lem:s06-burnside": r"Stated for $A$ local with a local homomorphism $A\to K$, $K$ algebraically closed, and $\bar\rho\otimes K$ irreducible (absolute irreducibility); the case $A=k$ is the first claim",
    "lem:s06-twobytwo": r"Formalized for the case $H=T$ only; the general $T$-module $H$ is not formalized",
    "thm:s06-defect": r"Abstract \texttt{Defect.Setting} (rings $\Lambda, I, T, \mathcal O$, a group $G$, $\rho:G\to\mathrm{GL}_2(I)$); Hida's Hecke algebra and the Galois representation are not constructed in Lean; (H1), (H2), (P), (Lev) and the newform condition on $f=F_P$ are not Lean arguments but the conditions under which the cited \texttt{Hyp.*} are asserted; step (4) enters as the disjunction ((H0$^-$) and \texttt{Hyp.KimOta}) or \texttt{Hyp.KimOtaRT}",
    "cor:s06-fixed": r"Abstract \texttt{Defect.Setting}; the DVR property of $\mathcal O$ is an explicit argument",
    "cor:s06-allweights": r"Abstract \texttt{Defect.Setting}; identities of ideals only: the chapter's $\mathrm{ord}$-formula additionally needs $\mathfrak c\ne0$ at both points (newform condition), not assumed in Lean; the conditions on $P'$ are the meaning of the arguments \texttt{htam'}, \texttt{hctl'}",
}
DECL_NOTES: dict[str, str] = {
    "Langlandscape.Ordinary.lim_exact_ribet": r"Takes the surjectivity of the $A$-transitions as the literal argument \texttt{hA} (not formalized)",
    "Langlandscape.Ribet.ribet_exact": r"Takes connectivity \texttt{hc : Tree.BGConnected} as an argument",
    "Langlandscape.Ribet.ribet_rank": r"Takes connectivity \texttt{hc : Tree.BGConnected} as an argument",
    "Langlandscape.Comparison.xlambda_finite": r"\texttt{Nonempty} of an equivalence only",
}
UNCERTAIN: list[str] = []
# The `_uncond` twins: theorems that plug a discharge lemma (Ordinary.padicOrdDecomp_holds in Ordinary/TowerUncond.lean,
# Hyp.ramNrdSurj_holds in Uncond.lean) into a theorem that takes the discharged hypothesis as an explicit argument.
UNCOND_FILES = ("Langlandscape/Ordinary/TowerUncond.lean", "Langlandscape/Uncond.lean")


def explicit_h_binders(sig: str) -> list[str]:
    """Names of the explicit (round-bracket) binders of a signature that are hypotheses (name h..., or the bundled
    data H)."""
    names, depth, cur, br = [], 0, "", ""
    for c in sig.split(":=")[0]:
        if c in "([{⦃":
            depth += 1
            if depth == 1:
                cur, br = "", c
        if depth >= 1:
            cur += c
        if c in ")]}⦄":
            depth -= 1
            if depth == 0 and br == "(" and ":" in cur and ":=" not in cur:
                names += [x for x in cur[1:].split(":")[0].split() if re.match(r"h|H$", x)]
    return names
# Citations whose position puts them after the wrong environment (checked by hand): (name, found label) -> label
CITE_OVERRIDES: dict[tuple[str, str], str | None] = {
    # s06-m4.tex: "The statement is the docstring of ... Defect.galois" follows the proof of lem:s06-traceform but
    # refers to prop:s06-galois.
    ("Langlandscape.Defect.galois", "lem:s06-traceform"): "prop:s06-galois",
}

DOC_FLAGS = [
    "special case", "only", "not formalized", "not formalised", "abstract", "schematic", "for H = T", "toy",
    "weaker", "helper", "statement only", "modulo", "under", "restricted",
]


# ============================================================================================================== I/O
def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *args], check=True, capture_output=True, text=True).stdout


def read_audit() -> list[tuple[str, str]]:
    """(name, block comment) in file order."""
    out, block = [], "Stage 01 (S01 headline theorems)"
    for line in AUDIT.read_text(encoding="utf-8").splitlines():
        if line.startswith("-- "):
            block = line[3:].strip()
        m = re.match(r"#print axioms\s+(\S+)", line)
        if m:
            out.append((m.group(1), block))
    return out


def read_axlog(text: str) -> dict[str, list[str] | None]:
    ax: dict[str, list[str] | None] = {}
    for m in re.finditer(r"^'([^\n]+?)' depends on axioms: \[([^\]]*)\]", text, re.S | re.M):
        ax[m.group(1)] = [a.strip() for a in m.group(2).replace("\n", " ").split(",") if a.strip()]
    for m in re.finditer(r"^'([^\n]+?)' does not depend on any axioms", text, re.M):
        ax[m.group(1)] = []
    return ax


# ============================================================================================================ Lean
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec|public|partial|unsafe|scoped|local)\s+)*)"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque)\s+([^\s:({\[⦃]+)")


def strip_line_comment(s: str) -> str:
    i = s.find("--")
    return s if i < 0 else s[:i]


def split_top(s: str, seps: tuple[str, ...]) -> list[str]:
    """Split s at top-level (bracket depth 0) occurrences of any separator."""
    parts, depth, cur, i = [], 0, [], 0
    opens, closes = "([{⦃⟨", ")]}⦄⟩"
    while i < len(s):
        c = s[i]
        if c in opens:
            depth += 1
        elif c in closes:
            depth -= 1
        if depth == 0:
            hit = next((sp for sp in seps if s.startswith(sp, i)), None)
            if hit:
                parts.append("".join(cur))
                cur = []
                i += len(hit)
                continue
        cur.append(c)
        i += 1
    parts.append("".join(cur))
    return parts


def parse_signature(sig: str, in_hyp_ns: bool, bare_x: bool) -> list[tuple[str, str]]:
    """Return [(binder text, hyp name)] for explicit-argument hypotheses in a declaration signature."""
    # binders before the top-level ':' then the type
    depth, i, n = 0, 0, len(sig)
    binders, cur_start = [], None
    opens, closes = "([{⦃", ")]}⦄"
    colon = None
    while i < n:
        c = sig[i]
        if c in opens:
            if depth == 0:
                cur_start = i
            depth += 1
        elif c in closes:
            depth -= 1
            if depth == 0 and cur_start is not None:
                binders.append(sig[cur_start:i + 1])
                cur_start = None
        elif c == ":" and depth == 0 and not sig.startswith(":=", i):
            colon = i
            break
        i += 1
    typ = sig[colon + 1:] if colon is not None else ""
    antecedents = split_top(typ, ("→",))[:-1]
    found = []

    def hyps_in(t: str) -> list[str]:
        hs = [m.group(1) for m in HYP_QUAL_RE.finditer(t)]
        if in_hyp_ns:
            hs += [m.group(1) for m in HYP_BARE_RE.finditer(t)]
        if bare_x:
            hs += ["X." + m.group(1) for m in re.finditer(r"(?<![\w.'])(char|gal|iso)(?![\w'.])", t)]
        return list(OrderedDict.fromkeys(hs))

    for b in binders:
        inner = b[1:-1]
        if ":" not in inner:
            continue
        btype = inner.split(":", 1)[1]
        for h in hyps_in(btype):
            found.append((" ".join(b.split()), h))
    for a in antecedents:
        for h in hyps_in(a):
            found.append((" ".join(a.split()), h))
    # de-duplicate per hypothesis
    seen, res = set(), []
    for b, h in found:
        if (b, h) not in seen:
            seen.add((b, h))
            res.append((b, h))
    return res


def index_lean() -> dict[str, dict]:
    idx: dict[str, dict] = {}
    for path in sorted(LIB.rglob("*.lean")):
        rel = path.relative_to(LEAN).as_posix()
        lines = path.read_text(encoding="utf-8").splitlines()
        stack: list[tuple[str, str]] = []  # (kind, name)
        opens_x = False
        comment_depth = 0
        doc_buf: list[str] = []
        in_doc = False
        last_doc = ""
        last_doc_end = -10
        i = 0
        while i < len(lines):
            raw = lines[i]
            line = raw
            # block comments / docstrings
            if comment_depth > 0:
                if in_doc:
                    doc_buf.append(raw)
                comment_depth += raw.count("/-") - raw.count("-/")
                if comment_depth <= 0:
                    comment_depth = 0
                    if in_doc:
                        last_doc = "\n".join(doc_buf)
                        last_doc_end = i
                        in_doc = False
                i += 1
                continue
            st = raw.lstrip()
            if st.startswith("/-"):
                in_doc = st.startswith("/--")
                doc_buf = [raw]
                comment_depth = raw.count("/-") - raw.count("-/")
                if comment_depth <= 0:
                    comment_depth = 0
                    if in_doc:
                        last_doc = raw
                        last_doc_end = i
                        in_doc = False
                i += 1
                continue
            code = strip_line_comment(line).rstrip()
            s = code.strip()
            if re.match(r"open\b.*\bLanglandscape\.Hyp\.X\b", s):
                opens_x = True
            m = re.match(r"namespace\s+(\S+)", s)
            if m:
                stack.append(("ns", m.group(1)))
            elif re.match(r"(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?section\b", s):
                nm = re.match(r"(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?section\s*(\S*)", s).group(1)
                stack.append(("sec", nm))
            elif re.match(r"end\b", s) and not re.match(r"end\s*:=", s):
                nm = s[3:].strip()
                for j in range(len(stack) - 1, -1, -1):
                    if (nm and stack[j][1] == nm) or (not nm and stack[j][0] == "sec" and stack[j][1] == ""):
                        del stack[j:]
                        break
                else:
                    if not nm and stack:
                        stack.pop()
            md = DECL_RE.match(code)
            if md:
                mods, kind, name = md.group(1), md.group(2), md.group(3)
                ns = ".".join(n for k, n in stack if k == "ns")
                full = name[len("_root_."):] if name.startswith("_root_.") else (ns + "." + name if ns else name)
                # signature: accumulate until ':=' / 'where' / '|' at line start
                sig_lines, j = [], i
                while j < len(lines) and j < i + 60:
                    c = strip_line_comment(lines[j])
                    if j > i and re.match(r"\s*(\||where\b|deriving\b)", c):
                        break
                    k = c.find(":=")
                    if k >= 0:
                        sig_lines.append(c[:k])
                        break
                    if re.search(r"\swhere\s*$", c):
                        sig_lines.append(re.sub(r"\swhere\s*$", "", c))
                        break
                    sig_lines.append(c)
                    j += 1
                sig = " ".join(x.strip() for x in sig_lines)
                sig = sig[sig.find(name) + len(name):]
                in_hyp = ns.startswith("Langlandscape.Hyp")
                doc = last_doc if last_doc_end >= i - 3 else ""
                entry = {
                    "file": rel, "line": i + 1, "kind": kind, "private": "private" in mods,
                    "hyps": parse_signature(sig, in_hyp, opens_x), "doc": doc, "sig": sig,
                }
                if full not in idx:
                    idx[full] = entry
                # structure fields / constructors
                if kind in ("structure", "class"):
                    k2 = i + 1
                    while k2 < len(lines) and (lines[k2].startswith(" ") or not lines[k2].strip()):
                        fm = re.match(r"\s{2}(\w[\w']*)\s*:", strip_line_comment(lines[k2]))
                        if fm:
                            idx.setdefault(full + "." + fm.group(1), dict(entry, line=k2 + 1, kind="field",
                                                                           hyps=parse_signature(
                                                                               ": " + lines[k2].split(":", 1)[1],
                                                                               in_hyp, opens_x),
                                                                           doc=""))
                        k2 += 1
                    idx.setdefault(full + ".mk", dict(entry, kind="constructor"))
            i += 1
    return idx


# ========================================================================================================= chapters
def chapter_files() -> list[Path]:
    order: list[Path] = []

    def walk(p: Path):
        order.append(p)
        for m in re.finditer(r"\\(?:input|InputIfFileExists|include)\{([^}]+)\}", p.read_text(encoding="utf-8")):
            tgt = ROOT / "mathematics" / (m.group(1) + ("" if m.group(1).endswith(".tex") else ".tex"))
            if tgt.exists() and "chapters" in tgt.as_posix() and tgt not in order:
                walk(tgt)

    for m in re.finditer(r"\\input\{(chapters/[^}]+)\}", MAIN_TEX.read_text(encoding="utf-8")):
        walk(ROOT / "mathematics" / (m.group(1) + ".tex"))
    return order


def unescape(name: str) -> str:
    return name.replace("\\_", "_").replace("\\allowbreak", "").replace("{}", "").strip()


def scan_chapters(audited: set[str], idx: dict) -> tuple[list[dict], dict[str, dict]]:
    """Return citations [{name, label, envtype, ctx, file, line, via}] and labels {label: {type, file, line}}."""
    cites, labels = [], {}
    suffix: dict[str, list[str]] = defaultdict(list)
    for n in audited:
        parts = n.split(".")
        for k in range(1, len(parts)):
            suffix[".".join(parts[k:])].append(n)
    env_re = re.compile(r"\\(begin|end)\{(\w+)\*?\}")
    explicit: list[dict] = []
    for path in chapter_files():
        rel = path.relative_to(ROOT).as_posix()
        stack: list[dict] = []
        last: dict | None = None
        pending_section = False
        text = re.sub(r"(?<!\\)%.*", "", path.read_text(encoding="utf-8"))
        for m in re.finditer(r"\\ref\{([^}]+)\}(?:\([^)]*\))?\s*\$\\leftrightarrow\$\s*"
                             r"\\(?:texttt|pathtt|lean)\{([A-Za-z0-9_.'\\]+)\}", text):
            raw = unescape(m.group(2))
            cand = [raw] if raw in audited else suffix.get(raw, [])
            if len(cand) == 1:
                explicit.append({"name": cand[0], "label": m.group(1), "envtype": None, "ctx": "explicit",
                                 "file": rel, "line": text[:m.start()].count("\n") + 1, "via": "leftrightarrow"})
        for ln, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            code = re.sub(r"(?<!\\)%.*", "", line)
            if re.search(r"\\(section|subsection|subsubsection|paragraph|chapter)\*?\{", code):
                last = None
                pending_section = True
            # process tokens in order of position
            events = []
            for m in env_re.finditer(code):
                events.append((m.start(), "env", m))
            for m in re.finditer(r"\\label\{([^}]+)\}", code):
                events.append((m.start(), "label", m))
            for m in re.finditer(r"\\lean\{([^}]*)\}", code):
                events.append((m.start(), "lean", m))
            for m in re.finditer(r"\\(?:texttt|pathtt)\{([A-Za-z0-9_.'\\]+)\}", code):
                events.append((m.start(), "tt", m))
            for _, kind, m in sorted(events, key=lambda e: e[0]):
                if kind == "env":
                    be, env = m.group(1), m.group(2)
                    if env in LABELLED_ENVS:
                        if be == "begin":
                            stack.append({"type": env, "label": None, "file": rel, "line": ln})
                        elif stack:
                            last = stack.pop()
                    elif env == "proof" and be == "begin" and not stack:
                        pass
                elif kind == "label":
                    if not stack and pending_section:
                        last = {"type": "section", "label": m.group(1), "file": rel, "line": ln}
                        labels[m.group(1)] = {"type": "section", "file": rel, "line": ln}
                        pending_section = False
                    elif stack and stack[-1]["label"] is None:
                        stack[-1]["label"] = m.group(1)
                        labels[m.group(1)] = {"type": stack[-1]["type"], "file": rel, "line": stack[-1]["line"]}
                else:
                    raw = unescape(m.group(1))
                    name, via = None, kind
                    if raw in idx or raw in audited:
                        name = raw
                    elif ("Langlandscape." + raw) in idx:
                        name = "Langlandscape." + raw
                    elif kind == "lean" and len(suffix.get(raw, [])) == 1 and "." in raw:
                        name = suffix[raw][0]
                    elif kind == "tt":
                        cand = suffix.get(raw, [])
                        if len(cand) == 1 and ("." in raw or "_" in raw):
                            name = cand[0]
                        elif ("Langlandscape." + raw) in audited:
                            name = "Langlandscape." + raw
                    elif kind == "lean":
                        name = raw  # keep unresolved \lean names too (reported)
                    if name is None:
                        continue
                    if stack:
                        env, ctx = stack[-1], "statement"
                    elif last is not None:
                        env, ctx = last, "after"
                    else:
                        env, ctx = None, "text"
                    cites.append({"name": name, "label": env["label"] if env else None,
                                  "envtype": env["type"] if env else None, "ctx": ctx,
                                  "file": rel, "line": ln, "via": via})
    for c in explicit:
        c["envtype"] = labels.get(c["label"], {}).get("type")
    for c in cites:
        key = (c["name"], c["label"])
        if key in CITE_OVERRIDES:
            c["label"] = CITE_OVERRIDES[key]
            c["envtype"] = labels.get(c["label"], {}).get("type") if c["label"] else None
            c["ctx"] = "override"
    return cites + explicit, labels


# ============================================================================================================ LaTeX
UNI = {
    "ℤ": r"$\mathbb{Z}$", "ℚ": r"$\mathbb{Q}$", "ℕ": r"$\mathbb{N}$", "ℂ": r"$\mathbb{C}$", "ℓ": r"$\ell$",
    "→": r"$\to$", "≤": r"$\le$", "≥": r"$\ge$", "≠": r"$\ne$", "∣": r"$\mid$", "∀": r"$\forall$",
    "∃": r"$\exists$", "∧": r"$\wedge$", "∨": r"$\vee$", "¬": r"$\neg$", "⊗": r"$\otimes$", "≃": r"$\simeq$",
    "≅": r"$\cong$", "×": r"$\times$", "Λ": r"$\Lambda$", "λ": r"$\lambda$", "η": r"$\eta$", "ρ": r"$\rho$",
    "φ": r"$\varphi$", "ε": r"$\varepsilon$", "α": r"$\alpha$", "β": r"$\beta$", "θ": r"$\theta$",
    "τ": r"$\tau$", "π": r"$\pi$", "Γ": r"$\Gamma$", "Δ": r"$\Delta$", "Φ": r"$\Phi$", "ϖ": r"$\varpi$",
    "𝔞": r"$\mathfrak{a}$", "𝔟": r"$\mathfrak{b}$", "𝔪": r"$\mathfrak{m}$", "𝔠": r"$\mathfrak{c}$",
    "𝔱": r"$\mathfrak{t}$", "𝔭": r"$\mathfrak{p}$", "𝒪": r"$\mathcal{O}$", "𝕀": r"$\mathbb{I}$", "⊥": r"$\bot$",
    "⊤": r"$\top$", "∈": r"$\in$", "⁻¹": r"$^{-1}$", "²": r"$^2$", "₀": r"$_0$", "₁": r"$_1$", "₂": r"$_2$",
    "ˣ": r"$^\times$", "′": "'", "—": "---", "–": "--", "…": r"\dots{}", "·": r"$\cdot$", "⟨": r"$\langle$",
    "⟩": r"$\rangle$", "∑": r"$\sum$", "Ô": r"$\hat{O}$", "ō": "o", "é": r"\'e", "è": r"\`e", "ü": r"\"u",
    "ö": r"\"o", "ä": r"\"a", "⧸": "/", "↠": r"$\twoheadrightarrow$", "ρ̄": r"$\bar\rho$", "̄": "",
}


def tex(s: str) -> str:
    """Escape plain text for LaTeX (standard article; pdfLaTeX-safe: unknown non-ASCII is dropped)."""
    out = []
    for ch in s:
        if ch in "\\":
            out.append(r"\textbackslash{}")
        elif ch in "_&%#$":
            out.append("\\" + ch)
        elif ch in "{}":
            out.append("\\" + ch)
        elif ch == "^":
            out.append(r"\^{}")
        elif ch == "~":
            out.append(r"\~{}")
        elif ch == "`":
            out.append("")
        elif ord(ch) < 128:
            out.append(ch)
        else:
            out.append(UNI.get(ch, ""))
    return "".join(out)


def ttname(n: str) -> str:
    """A declaration name as breakable \\texttt."""
    short = n[len("Langlandscape."):] if n.startswith("Langlandscape.") else n
    return r"\texttt{" + tex(short).replace(".", r".\allowbreak{}").replace(r"\_", r"\_\allowbreak{}") + "}"


def tthyp(h: str) -> str:
    """Hyp.<name> as breakable \\texttt (breaks after the dot and before capitals of long names)."""
    t = tex(short_hyp(h)).replace(".", r".\allowbreak{}")
    t = re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", t)
    return r"\texttt{" + t + "}"


def doc_flags(doc: str) -> list[str]:
    body = re.sub(r"^\s*/--|-/\s*$", "", doc, flags=re.S)
    body = " ".join(body.split())
    hits = []
    for sent in re.split(r"(?<=[.;])\s+", body):
        low = sent.lower()
        if any(re.search(r"\b" + re.escape(f.lower()) + r"\b", low) for f in
               ("special case", "not formalized", "not formalised", "schematic", "only", "abstract", "weaker",
                "for h = t", "toy", "statement only")):
            hits.append(sent.strip())
    return hits


def short_hyp(h: str) -> str:
    return "Hyp." + h


def status_of(entry: dict | None) -> tuple[str, list[str], list[str]]:
    """(status text, hyp names, discharge notes)."""
    if entry is None:
        return "Lean-verified", [], []
    hs = list(OrderedDict.fromkeys(h for _, h in entry["hyps"]))
    if not hs:
        return "Lean-verified", [], []
    notes = []
    for h in hs:
        if h in DISCHARGE:
            kind, lem = DISCHARGE[h]
            notes.append(f"{tthyp(h)} {kind} by {lem}")
    return "conditional", hs, notes


# ============================================================================================================== main
def main() -> int:
    global GATE_TREE
    ap = argparse.ArgumentParser()
    ap.add_argument("--axlog", help="path to c-axioms.log (default: git show <gate-ref>:" + AXLOG_PATH + ")")
    ap.add_argument("--gate-ref", default=GATE_REF)
    ap.add_argument("--gate-tree", default=GATE_TREE, help="gated Lean tree (recorded in the output)")
    ap.add_argument("--out", default=str(OUT_DIR))
    a = ap.parse_args()
    GATE_TREE = a.gate_tree

    axtext = Path(a.axlog).read_text(encoding="utf-8") if a.axlog else git("show", f"{a.gate_ref}:{AXLOG_PATH}")
    ax = read_axlog(axtext)
    audit = read_audit()
    names = [n for n, _ in audit]
    audited = set(names)
    assert len(names) == len(audited), "duplicate #print axioms lines"
    idx = index_lean()
    cites, labels = scan_chapters(audited, idx)

    problems = []
    missing_ax = [n for n in names if n not in ax]
    extra_ax = [n for n in ax if n not in audited]
    missing_src = [n for n in names if n not in idx]
    nonstd = {n: ax[n] for n in names if n in ax and ax[n] is not None and not set(ax[n]) <= set(STD)}
    sorry = [n for n in names if n in ax and ax[n] and "sorryAx" in ax[n]]
    if missing_ax:
        problems.append(f"{len(missing_ax)} audited names without axiom line: {missing_ax[:5]}")
    if extra_ax:
        problems.append(f"{len(extra_ax)} axiom lines not in PrintAxioms.lean: {extra_ax[:5]}")
    if missing_src:
        problems.append(f"{len(missing_src)} audited names not located in the sources: {missing_src}")
    if nonstd or sorry:
        problems.append(f"NONSTANDARD axioms: {nonstd}")

    # citations per declaration
    by_decl: dict[str, list[dict]] = defaultdict(list)
    for c in cites:
        by_decl[c["name"]].append(c)

    def main_labels(n: str) -> list[str]:
        return list(OrderedDict.fromkeys(c["label"] for c in by_decl.get(n, [])
                                         if c["envtype"] in THEOREMLIKE and c["label"]))

    def any_labels(n: str) -> list[str]:
        return list(OrderedDict.fromkeys(c["label"] for c in by_decl.get(n, []) if c["label"]))

    rows = []
    for n, block in audit:
        e = idx.get(n)
        st, hs, dnotes = status_of(e)
        axl = ax.get(n)
        rows.append({
            "name": n, "block": block, "file": e["file"] if e else None, "line": e["line"] if e else None,
            "kind": e["kind"] if e else None, "axioms": axl,
            "axioms_class": ("standard" if axl == STD or (axl and sorted(axl) == sorted(STD)) else
                             "none" if axl == [] else "subset" if axl and set(axl) <= set(STD) else "OTHER"),
            "is_hyp_def": any(n == "Langlandscape.Hyp." + h or n == "GL2TF.Hyp." + h for h in HYPS),
            "hyp_args": hs, "hyp_binders": [b for b, _ in (e["hyps"] if e else [])], "discharge": dnotes,
            "status": ("Lean-verified" if not hs else
                       "Lean-verified conditional on " + ", ".join(short_hyp(h) for h in hs)
                       + " (explicit argument" + ("s" if len(hs) > 1 else "") + ")"),
            "labels_main": main_labels(n), "labels_all": any_labels(n),
            "cites": [{k: c[k] for k in ("label", "envtype", "ctx", "file", "line", "via")} for c in by_decl.get(n, [])],
            "doc_flags": doc_flags(e["doc"]) if e else [],
            "uncond": (explicit_h_binders(e["sig"]) if e and e["file"] in UNCOND_FILES and n.endswith("_uncond")
                       and e["kind"] == "theorem" and not hs else None),
        })
    cited_unaudited = OrderedDict()
    for c in cites:
        if c["via"] == "lean" and c["name"] not in audited:
            cited_unaudited.setdefault(c["name"], []).append(c)

    # differences
    def difference(r: dict, labs: list[str]) -> tuple[str, bool]:
        parts = []
        if r["name"] in DECL_NOTES:
            parts.append(DECL_NOTES[r["name"]])
        for lab in labs:
            if lab in LABEL_NOTES and LABEL_NOTES[lab]:
                parts.append(LABEL_NOTES[lab] if len(labs) == 1 else f"{tex(lab)}: {LABEL_NOTES[lab]}")
        if r["discharge"]:
            parts.append("; ".join(r["discharge"]))
        flagged = any(not re.match(r"(none recorded|Statement as in the chapter)", x) for x in parts)
        if not parts:
            parts.append("see chapter label")
        return " ".join(p if p.endswith(".") else p + "." for p in parts), flagged

    main_rows = [r for r in rows if r["labels_main"]]
    for r in rows:
        r["difference"], r["has_difference"] = difference(r, r["labels_main"] or r["labels_all"])

    # ---------------------------------------------------------------------------------------------- write tex
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    T = []
    w = T.append
    w("% SPDX-License-Identifier: CC-BY-4.0")
    w("% Copyright (C) 2026 the Langlandscape team")
    w("% GENERATED by mathematics/submission/tools/lean_table.py -- do not edit by hand.")
    w(f"% Sources: lean/ at the gated tree {GATE_TREE}; the final gate's axiom log.")
    w("% Needs: longtable, booktabs.")
    w("")
    n_cond = sum(1 for r in rows if r["hyp_args"])
    n_main_cond = sum(1 for r in main_rows if r["hyp_args"])
    n_sub = sum(1 for r in rows if r["axioms_class"] == "subset")
    n_none = sum(1 for r in rows if r["axioms_class"] == "none")

    def loc(r):
        if not r["file"]:
            return "?"
        t = tex(f"{r['file'].removeprefix('Langlandscape/')}:{r['line']}").replace("/", r"/\allowbreak{}")
        return re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", t)

    def labs_tex(ls):
        return ", ".join(r"\texttt{" + tex(x).replace(":", r":\allowbreak{}").replace("-", r"-\allowbreak{}") + "}"
                         for x in ls)

    def status_tex(r):
        if r["is_hyp_def"]:
            hn = r["name"].split("Hyp.", 1)[1]
            extra = {"PadicOrdDecomp": "; discharged in Lean", "RamNrdSurj": "; discharged in Lean",
                     "BrandtStabFree": "; discharged in Lean",
                     "ResidualBurnside": "; discharged in Lean modulo absolute irreducibility"}.get(hn, "")
            return "Registered hypothesis (Prop-valued definition; asserted, not proved" + extra + ")"
        if r["kind"] in ("def", "abbrev", "structure", "class", "instance", "inductive", "field", "constructor"):
            pre = "Lean definition"
            if not r["hyp_args"]:
                return pre + " (no theorem content)"
            return pre + " taking " + ", ".join(tthyp(h) for h in r["hyp_args"])
        if not r["hyp_args"] and r.get("uncond") is not None:
            ex = ", ".join(r"\texttt{" + tex(x) + "}" for x in r["uncond"]) or "none"
            return ("Lean-verified; free of registered hypotheses, under the stated explicit hypotheses (" + ex + ")")
        if not r["hyp_args"]:
            return "Lean-verified"
        return ("Lean-verified conditional on " + ", ".join(tthyp(h) for h in r["hyp_args"]) + " (explicit argument"
                + ("s" if len(r["hyp_args"]) > 1 else "") + ")")

    stage_of_label = lambda lab: (re.match(r"\w+:(s0\d)", lab).group(1) if re.match(r"\w+:(s0\d)", lab) else "other")
    order = {f.relative_to(ROOT).as_posix(): i for i, f in enumerate(chapter_files())}

    def labkey(lab):
        L = labels.get(lab, {})
        return (order.get(L.get("file"), 999), L.get("line", 0), lab)

    envname = {"theorem": "Theorem", "proposition": "Proposition", "lemma": "Lemma", "corollary": "Corollary"}
    w(r"\subsection*{Table L1: declarations the report relies on}")
    w(r"\label{tab:lean-main}")
    w(f"The {len(main_rows)} declarations below are those of the {len(names)} audited ones (Table~L3) whose names the "
      "chapters cite in the statement, the proof or the Lean note of a theorem, proposition, lemma or corollary. "
      "They are grouped by that claim (the chapter label; a declaration cited by several claims appears under each). "
      "The line of a claim records how the Lean declarations differ from it; "
      "``see chapter label'' means that no difference is recorded there and that no exact match is claimed. "
      "\\emph{Lean-verified}: the declaration compiles in the gated tree, without \\texttt{sorry}, and its "
      "axioms are among \\texttt{propext}, \\texttt{Classical.choice}, \\texttt{Quot.sound}. "
      "\\emph{Conditional}: in addition, the type of the declaration takes the named registered "
      "hypotheses as explicit arguments, so the statement holds for every proof of them that is supplied. "
      "\\emph{Registered hypothesis}: the declaration is the hypothesis itself, a \\texttt{Prop}-valued definition; "
      "the claim is asserted, not proved, in Lean. \\emph{Lean definition}: a definition the statements use; it has no "
      "theorem content of its own.")
    w("")
    w(r"{\small\setlength{\tabcolsep}{3pt}")
    w(r"\begin{longtable}{@{}p{0.38\textwidth}p{0.30\textwidth}p{0.30\textwidth}@{}}")
    w(r"\toprule Declaration & File:line (in \texttt{Langlandscape/}) & Status \\ \midrule \endhead")
    w(r"\bottomrule \endfoot")
    by_label = OrderedDict()
    for lab in sorted({l for r in main_rows for l in r["labels_main"]}, key=labkey):
        by_label[lab] = [r for r in main_rows if lab in r["labels_main"]]
    cur_stage = None
    for lab, rs in by_label.items():
        st = stage_of_label(lab)
        if st != cur_stage:
            cur_stage = st
            w(r"\multicolumn{3}{@{}l}{\textbf{Stage " + st[-1] + r"}} \\ \midrule")
        L = labels.get(lab, {})
        note = LABEL_NOTES.get(lab) or "see chapter label"
        w(r"\multicolumn{3}{@{}p{0.98\textwidth}@{}}{\textbf{" + envname.get(L.get("type"), "Claim") + r"} "
          + labs_tex([lab]) + r" \emph{Difference:} " + (note if note.endswith(".") else note + ".") + r"} \\*")
        for r in sorted(rs, key=lambda r: (r["file"] or "", r["line"] or 0)):
            extra = ""
            if r["name"] in DECL_NOTES:
                extra += r" \emph{Note:} " + DECL_NOTES[r["name"]] + "."
            if r["discharge"] and not r["is_hyp_def"]:
                extra += " (" + "; ".join(r["discharge"]) + ".)"
            w(f"\\quad{ttname(r['name'])} & {{\\footnotesize {loc(r)}}} & {status_tex(r)}{extra} \\\\")
        w(r"\midrule")
    w(r"\end{longtable}}")
    w("")

    # ---- table L2: cited but not audited
    w(r"\subsection*{Table L2: declarations cited by the chapters but not among the audited ones}")
    w(r"\label{tab:lean-unaudited}")
    w(f"The chapters cite {len(cited_unaudited)} further names in \\verb|\\lean{{}}| that are not among the "
      f"{len(names)} audited declarations. @@L2WHERE@@")
    w("")
    w(r"{\small\setlength{\tabcolsep}{3pt}")
    w(r"\begin{longtable}{@{}p{0.42\textwidth}p{0.27\textwidth}p{0.27\textwidth}@{}}")
    w(r"\toprule Declaration & Location & Cited at (label) \\ \midrule \endhead")
    w(r"\bottomrule \endfoot")
    unaudited_rows = []
    for n, cs in cited_unaudited.items():
        e = idx.get(n)
        if e is None:
            tests = (LEAN / "LanglandscapeTests")
            where = "not in the library"
            # look in the test library / import by grep of the last component
            short = n.split(".")[-1]
            try:
                g = subprocess.run(["grep", "-rlE", r"(theorem|lemma|def|abbrev|structure|instance)\s+(\S*\.)?"
                                    + re.escape(short) + r"\b", str(tests), str(LIB)],
                                   capture_output=True, text=True).stdout.split()
                if g:
                    where = "test library: " + ", ".join(Path(x).relative_to(LEAN).as_posix() for x in g[:2])
            except Exception:
                pass
        else:
            where = f"{e['file'].removeprefix('Langlandscape/')}:{e['line']}"
        labs = list(OrderedDict.fromkeys(c["label"] or f"{c['file'].split('/')[-1]}:{c['line']}" for c in cs))
        unaudited_rows.append({"name": n, "where": where, "kind": e["kind"] if e else None,
                               "labels": labs, "hyp_args": [h for _, h in e["hyps"]] if e else []})
        wtex = tex(where).replace("/", "/\\allowbreak{}")
        w(f"{ttname(n)} & {{\\footnotesize {wtex}}} & {labs_tex(labs)} \\\\")
    w(r"\end{longtable}}")
    w("")
    n_test = sum(1 for u in unaudited_rows if u["where"].startswith("test"))
    n_nf = sum(1 for u in unaudited_rows if u["where"].startswith("not"))
    n_lib = len(unaudited_rows) - n_test - n_nf
    where_txt = f"{n_lib} in the library, {n_test} in the test library" + (f", {n_nf} not found" if n_nf else "")
    l2 = (f"Each of them exists in the code of the gated tree ({where_txt}) and compiles in the from-scratch build, "
          "but it is not in the axiom audit and is not claimed as Lean-verified; the gate's \\texttt{sorry} count and "
          "forbidden-token grep cover these files, \\texttt{\\#print axioms} does not. "
          + ("Both are toy instances of registered hypotheses in the test library \\texttt{LanglandscapeTests}, which "
             "the audit file does not import; no claim of the report rests on them. "
             "The other chapter-cited declarations (102 of the 104 at the previous final gate) were added to the audit "
             "by the submission bundle and are now in Tables~L1 and~L3."
             if n_lib == 0 and n_nf == 0 else ""))
    T[:] = [t.replace("@@L2WHERE@@", l2) for t in T]

    # ---- table L3: appendix, all audited
    w(r"\subsection*{Table L3: all audited declarations}")
    w(r"\label{tab:lean-all}")
    w(f"All {len(names)} declarations of \\texttt{{Audit/PrintAxioms.lean}}, in the order of that file, grouped by "
      "its blocks. Axioms: \\texttt{std} = \\texttt{[propext, Classical.choice, Quot.sound]}; "
      "\\texttt{P,Q} = \\texttt{[propext, Quot.sound]}; \\texttt{P} = \\texttt{[propext]}; "
      "\\texttt{--} = no axioms. Every entry is the standard triple or a subset of it; no entry contains "
      "\\texttt{sorryAx}. Hypotheses: the registered \\texttt{Hyp.*} taken as explicit arguments "
      "(${}^{\\ast}$: discharged in Lean; ${}^{\\dagger}$: discharged modulo absolute irreducibility). "
      "For the \\texttt{\\_uncond} twins (\\texttt{Ordinary/TowerUncond.lean}, \\texttt{Uncond.lean}): "
      "``none; explicit: \\dots'' = free of registered hypotheses, under the stated explicit hypotheses named. "
      "Cited: \\texttt{M} = in Table~L1; \\texttt{c} = cited only from a definition, remark, hypothesis or interface; "
      "blank = not cited by the chapters." + ACC_NOTE)
    w("")
    w(r"{\footnotesize\setlength{\tabcolsep}{3pt}")
    w(r"\begin{longtable}{@{}>{\raggedright}p{0.35\textwidth}>{\raggedright}p{0.24\textwidth}>{\raggedright}p{0.07\textwidth}>{\raggedright}p{0.19\textwidth}>{\raggedright\arraybackslash}p{0.05\textwidth}@{}}")
    w(r"\toprule Declaration & File:line & Axioms & Hypotheses & Cited \\ \midrule \endhead")
    w(r"\bottomrule \endfoot")
    axshort = {"standard": r"\texttt{std}", "none": r"\texttt{--}"}
    cur = None
    blocknames = {}
    for r in rows:
        if r["block"] != cur:
            cur = r["block"]
            short = BLOCK_TITLES.get(re.split(r"\s*[(,:]", cur, 1)[0].strip(), cur)
            w(r"\multicolumn{5}{@{}p{0.92\textwidth}@{}}{\raggedright\textit{Audit block: " + tex(short) + r"}} \\ \midrule")
        if r["axioms_class"] == "subset":
            a_ = r"\texttt{" + ",".join("P" if x == "propext" else "Q" if x == "Quot.sound" else "C"
                                        for x in r["axioms"]) + "}"
        else:
            a_ = axshort.get(r["axioms_class"], r"\textbf{" + tex(str(r["axioms"])) + "}")
        hy = ", ".join(re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", tex(h)) + (r"${}^{\ast}$" if h in ("PadicOrdDecomp", "RamNrdSurj", "BrandtStabFree") else
                                 r"${}^{\dagger}$" if h == "ResidualBurnside" else "") for h in r["hyp_args"])
        if r.get("uncond") is not None:
            hy = "none; explicit: " + (", ".join(tex(x) for x in r["uncond"]) or "none")
        cflag = "M" if r["labels_main"] else ("c" if r["labels_all"] else "")
        w(f"{ttname(r['name'])} & {loc(r)} & {a_} & {hy} & {cflag} \\\\")
    w(r"\end{longtable}}")
    (out / "lean-table.tex").write_text("\n".join(T) + "\n", encoding="utf-8")

    for r in rows:
        r["status"] = re.sub(r"\\allowbreak\{\}|\\texttt\{|\}", "", status_tex(r)).replace("\\_", "_")
        r["has_difference"] = bool(r["labels_main"]) and any(
            not re.match(r"(none recorded|Statement as in the chapter)", LABEL_NOTES.get(l, "none recorded"))
            for l in r["labels_main"]) or r["name"] in DECL_NOTES
    for r in main_rows:
        for lab in r["labels_main"]:
            cs = [c for c in r["cites"] if c["label"] == lab]
            if any(c["via"] == "lean" or c["ctx"] in ("explicit", "override") for c in cs):
                continue  # named in full by \lean{} (statement or Lean note) or by an explicit correspondence
            c = cs[0]
            UNCERTAIN.append(f"{r['name']} -> {lab} (only a short \\texttt name, {c['file']}:{c['line']}, ctx {c['ctx']})")
    for r in rows:
        r["uncertain"] = any(u.startswith(r["name"] + " -> ") for u in UNCERTAIN)
    # ---------------------------------------------------------------------------------------------- json/csv
    n_uncited = sum(1 for r in rows if not r["labels_all"])
    summary = {
        "gate_tree": GATE_TREE, "audited": len(names), "axiom_lines": len(ax),
        "standard_triple": sum(1 for r in rows if r["axioms_class"] == "standard"), "subset": n_sub,
        "no_axioms": n_none, "sorryAx": len(sorry), "nonstandard": len(nonstd),
        "main_rows": len(main_rows), "main_conditional": n_main_cond, "appendix_rows": len(rows),
        "conditional_all": n_cond, "main_with_difference": sum(1 for r in main_rows if r["has_difference"]),
        "audited_uncited": n_uncited, "audited_cited_nonmain": sum(1 for r in rows if r["labels_all"] and not r["labels_main"]),
        "cited_unaudited": len(cited_unaudited),
        "uncond_twins": sum(1 for r in rows if r.get("uncond") is not None),
        "uncond_twins_ramnrd": sum(1 for r in rows if r.get("uncond") is not None
                                   and r["file"] == "Langlandscape/Uncond.lean"),
        "conditional_theorems": sum(1 for r in rows if r["hyp_args"] and r["kind"] == "theorem"),
        "conditional_nontheorems": sum(1 for r in rows if r["hyp_args"] and r["kind"] != "theorem"),
        "conditional_theorems_only_discharged": sum(1 for r in rows if r["hyp_args"] and r["kind"] == "theorem"
                                                    and set(r["hyp_args"]) <= {"PadicOrdDecomp", "RamNrdSurj", "BrandtStabFree"}),
        "hyp_defs": sum(1 for r in rows if r["is_hyp_def"]),
        "cited_unaudited_not_in_library": sum(1 for u in unaudited_rows if u["where"].startswith(("not", "test"))),
        "problems": problems, "uncertain": UNCERTAIN,
    }
    js = {"summary": summary, "rows": [{k: v for k, v in r.items() if k != "doc"} for r in rows],
          "cited_unaudited": unaudited_rows}
    (out / "lean-table.json").write_text(json.dumps(js, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    with open(out / "lean-table.csv", "w", newline="", encoding="utf-8") as f:
        cw = csv.writer(f)
        cw.writerow(["name", "file", "line", "kind", "axioms", "hyp_args", "status", "labels_main", "labels_all",
                     "difference"])
        for r in rows:
            cw.writerow([r["name"], r["file"], r["line"], r["kind"], " ".join(r["axioms"] or []),
                         " ".join(r["hyp_args"]), r["status"], " ".join(r["labels_main"]),
                         " ".join(r["labels_all"]), r["difference"]])
    print(json.dumps(summary, indent=1, ensure_ascii=False))
    return 1 if problems else 0


if __name__ == "__main__":
    sys.path.insert(0, str(HERE.parent))
    sys.exit(main())
