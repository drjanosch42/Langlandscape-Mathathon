# Audit of stage.tex (stage 05) against SPLIT.md, stage.bib and seed plan

## Findings

### F1
- **id:** F1
- **location:** Prop. \ref{prop:s05-sign}(a) (§3.2, lines 119-121) + Proof strategy §5 item 1 (lines 424-426)
- **severity:** major
- **category:** correctness / gap
- **claim:** Under Thm. \ref{thm:s05-G}(ii) with Deuring bijection, $U_q=T_q$ acts as $[x]\mapsto[x\Pi_q]$ so $\varepsilon=+1$, citing Ribet Remark 3.5(b) for "Frobenius = right multiplication by $\Pi_q$".
- **why problem:** At $\Gamma_0$-level $\Pi_q^2$ is central and acts trivially on $\Z[\XBq{\Uzero{M'}}]^0$; $x\mapsto x\Pi_q$ and $x\mapsto x\Pi_q^{-1}$ coincide on the $\Gamma_0$ class set. The cited Ribet Remark 3.5(b) does not distinguish $\Pi_q$ from $\Pi_q^{-1}$ at this level. The draft itself notes in proof strategy "irrelevant at $\Gamma_0$-level since $\Pi_q^2$ is central and acts trivially" (line 426), which contradicts the claim that (a) fixes the sign. The sign cannot be fixed without $\Gamma_1$-level with non-trivial $\langle q\rangle$ or a weight $>2$ check.
- **suggested fix:** Downgrade (a) to \stpmc{} that $U_q=\pm\Pi_q$ at $\Gamma_0$-level and note $\Pi_q=\Pi_q^{-1}$ there; make $\varepsilon=+1$ rely on Prop. \ref{prop:s05-sign}(c)+(d) plus test T05-2 and Prop. \ref{prop:s05-sign}(b)/(e) (or add a $\Gamma_1$ lemma). Do not present (a) as fixing $\varepsilon$.

### F2
- **id:** F2
- **location:** Prop. \ref{prop:s05-sign}(e) (§3.2, lines 135-139) and Definitions §3.2 line 39 ($U_{s,q}=\cO_q^\times$)
- **severity:** major
- **category:** correctness
- **claim:** For even $k\ge2$ trivial character, Brandt module $\Brandt{\Uzero{M'}}{V_k}$ with $\Pi_q$ acting by pure right translation (no $V$-action, $q\ne p$; $\Pi_q^2=q^{k-2}$), JL transfer matches $a_q(f)$ with eigenvalue of $+\Pi_q$.
- **why problem:** With $U_{s,q}=\cO_q^\times$ maximal, $q\ne p$, the double coset at $q$ in $\Bhat^\times$ is trivial; pure right translation by a uniformiser does not preserve level $U_0$ structure. $\Pi_q^2=q^{k-2}$ omits the reduced-norm central character and the necessary $V$-twist when $k>2$: for Brandt with $V_k=\Sym^{k-2}$, stage 01 defines $S_q=\langle q\rangle^{-1}$ times $q^{k-2}$ via $V$-action; stating "no $V$-action" contradicts $w_x$ conventions and gives wrong $q$-power for non-scalar $V$. No citation is given (\stexp{} pointing to `missing/stage-05.md`).
- **suggested fix:** State (e) only for $q\nmid D$ case or move to stage 01 conventions: include central $V$-action and factor $\chi\circ\Nrd$, cite explicit local JL (e.g. Jacquet-Langlands Shimizu or Chevalley) for $\mathrm{St}\otimes\chi\mapsto\chi\circ\Nrd$, and correct $\Pi_q^2 = q^{k-2}S_q$; mark \sttoprove{} pending that citation.

### F3
- **id:** F3
- **location:** Thm. \ref{thm:s05-G}(iii) (lines 84-87) and Hyp. \ref{hyp:s05-X}(X4) (lines 182-183)
- **severity:** major
- **category:** correctness / reference
- **claim:** On torus $w_q=-T_q$, Frobenius of special fibre acts as $qT_q=-qw_q$, and on bottom graded piece $\Frob_q$ acts as $qU_q$.
- **why problem:** Mazur Appendix Thm.(A.1)(a) p173 (cited in same theorem) states $F=-pw$ on torus. Ribet Prop.3.7 p445 cited for $w_q=-T_q$ concerns Atkin-Lehner on character group, not Frobenius. Conflating geometric Frobenius vs arithmetic Frobenius and the sign $-1$ from $w_q=-T_q$ yields $F=-q w_q = qT_q$ only with a chosen Frobenius convention; stage never specifies geometric vs arithmetic $\Frob_q$. In (X4) "Frob_q acts on bottom piece as $qU_q$" then inherits the same sign ambiguity, which propagates to Prop.\ref{prop:s05-Xlambda}(d) Hecke-equivariance.
- **suggested fix:** Fix Frobenius convention (geometric vs arithmetic) explicitly in Setting §3.1; quote Mazur "F = -p w" verbatim and state $w_q=-U_q$ on torus vs $T_q$ on $\Xq$; make (X4) read $\Frob_q^{\rm geom}=qU_q = -qw_q$ or $\Frob_q^{\rm arith}= -qU_q$ consistently, and note dependence on Remark \ref{rem:s05-illusie} sign.

### F4
- **id:** F4
- **location:** Lemma \ref{lem:s05-consistency}(a) lines 200-202 and Lemma \ref{lem:s05-consistency}(b) lines 203-205
- **severity:** major
- **category:** correctness
- **claim:** $\theta_s$ respects $U_q^2=\langle q\rangle$ and $T_\ell^2-T_{\ell^2}=\ell\langle\ell\rangle$; Brandt adjoint $T_\ell^*=S_\ell^{-1}T_\ell=\langle\ell\rangle T_\ell$, $\Pi_q^*=\Pi_q^{-1}$.
- **why problem:** The relation $T_\ell^2-T_{\ell^2}=\ell\langle\ell\rangle$ is not the standard Hecke relation in weight 2 ($\ell$-adic or classical): standard is $T_{\ell^2}=T_\ell^2-\ell\langle\ell\rangle$ on forms of level prime to $\ell$, but on the $q$-new quotient or on $\Xq(J_s)\otimes\Q$ the operator $T_{\ell^2}$ is not a generator of $\cH_s$ and the identity holds only after projecting to anemic algebra. More seriously, (b) states $T_\ell^*=\langle\ell\rangle T_\ell$ whereas stage 01 Prop. relations gives $T_\ell^* = \langle\ell\rangle^{-1}T_\ell$ (since $S_\ell=\langle\ell\rangle$ and adjoint is $S_\ell^{-1}T_\ell$). The draft writes $S_\ell^{-1}T_\ell=\langle\ell\rangle T_\ell$, inverting $\langle\ell\rangle$. If $S_\ell=\langle\ell\rangle$, the equality is $\langle\ell\rangle^{-1}T_\ell$.
- **suggested fix:** Correct (a) to $T_\ell^2 - T_{\ell^2} = \ell S_\ell$ and note it holds in $\End(\Xq(J_s))\otimes\Q$ via Eichler-Shimura, or restrict to anemic algebra; correct (b) to $T_\ell^*=\langle\ell\rangle^{-1}T_\ell$, $\langle d\rangle^*=\langle d\rangle^{-1}$, and check Rosati dual $h^\Ros$ matches ($T_\ell^\Ros=\langle\ell\rangle^{-1}T_\ell$) consistently with (X4).

### F5
- **id:** F5
- **location:** Hypothesis \ref{hyp:s05-X}(X3) lines 176-178 + Lemma \ref{lem:s05-consistency}(c) lines 206-207 + Remark \ref{rem:s05-factor2} lines 56-66
- **severity:** major
- **category:** interface / gap
- **claim:** $\varphi_s\circ\beta_{s's}=\pi_*\circ\varphi_{s'}$ where $\beta_{s's}$ is induced by Picard pullback $J_s\to J_{s'}$, and (X2)+(X3) imply projection formula $\langle\pi_*a,b\rangle_s=\langle a,\pi^!b\rangle_{s'}$ with $\pi^!=\pi^*$ for $s\ge1$ and factor 2 at $s=0$ when $M\le2$.
- **why problem:** SPLIT requires $\HypX$ naturality to be fixed precisely (stage 05 owns it). The draft declares $J_s=\Jac X_s$ with Picard functoriality, hence $X_s$ map $X_{s'}\to X_s$ (degeneracy) gives Albanese pushforward $J_{s'}\to J_s$ and Picard pullback $J_s\to J_{s'}$, but Néron character functor $\Xq$ is covariant in $J$ for semistable reduction via torus of Néron model, not contravariant as stated without citation; direction of $\beta_{s's}$ is not justified. Moreover the factor-2 hypothesis (F2) is introduced as "Hypothesis used throughout" (line 62) and made part of (X3) at $s=0,M\le2$ (D5), but no literature citation proves $\nu\circ\pi_*= {\rm tr}\circ\nu'/2$ translates to pairings with $w_e=|\Gamma_e/(\Gamma_e\cap\{\pm1\})|$; $s'=s\ge1$ claim "$w_x=1$ because $U_s$ omits $-1$" uses \texttt{if:s01-classset} freeness at $U_1(p^s)$ but stage does not verify $U_s=\Uone{Mp^s}$ satisfies $p\nmid|\Gamma_x|$ for Brandt level $M$ divisible by 2.
- **suggested fix:** Cite Raynaud Thm.5/Cor.6 for functoriality of $\Xq$ under Picard vs Albanese; clarify $\beta_{s's}$ is Picard pullback followed by Néron functoriality and give reference for contravariance claim or swap to Albanese description. Make (F2) an explicit part of exported \texttt{if:s05-hypX}: "for $s=0,M\le2$ pairings agree up to documented factor 2" and reference stage 01 Lemma stab + Prop. adjoint(c) revised for precise factor.

### F6
- **id:** F6
- **location:** Prop. \ref{prop:s05-Xlambda}(a) lines 227-233 + Proof strategy §5 line 429
- **severity:** major
- **category:** gap
- **claim:** $\varprojlim_s e(\Xq(J_s)\otimes\Zp)\cong\Mord(M)$ \stproved{} given \texttt{if:s04-ekills}(a) ($e\Zp[S_s]^0=e\Zp[S_s]$) and exactness of $e$ and of $\varprojlim$ on compact modules.
- **why problem:** Exactness of $\varprojlim$ on compact modules fails in general without Mittag-Leffler; the system $e(\Xq(J_s)\otimes\Zp)$ with maps $\beta_{s's}$ is not known to be Mittag-Leffler at torsion. Stage 04 \texttt{if:s04-Mord} gives $\Lambda$-freeness of $\Mord$ only on definite side; left side $\Lambda$-freeness is claimed as consequence (item (b) \stpmc), but control theorem for $J_s$ at $q$ (needed to identify transition maps with $\pi_*$) is not cited - Remark \ref{rem:s05-Xstatus} explicitly says Hida $\Lambda$-adic ordinary theory of $J_s$ at $q$ is not cited. So (a) cannot be \stproved{} from stated inputs.
- **suggested fix:** Weaken to \stpmc{} or \stsketch{}, add ML verification (finite-level $\Xq(J_s)\otimes\Zp$ are finite free $\Zp$-modules, maps are surjective after $e$? – prove or hypothesize), and cite Hida control for $J_1(Mp^s)$ at $q$ or state as additional hypothesis \texttt{if:s04-Mord} extension.

### F7
- **id:** F7
- **location:** Prop. \ref{prop:s05-Xiso} (§3.5, lines 275-282) and Prop. \ref{prop:s05-subquot} (§3.5, lines 287-298) + §6 Lean track L2 (lines 527-528)
- **severity:** major
- **category:** gap / feasibility
- **claim:** Under Def. \ref{def:s05-Xiso} plus $eH^1_{\rm par}(\Gamma_s,\Zp)^\pm_\m$ free rank 1 over $\T_\m$ and $\T_\m$ Gorenstein, both sides free rank 1 over $\T'_\m$ hence isomorphic via [Hs Thm.4.5] + [Hel Cor.8.11] + Prop. \ref{prop:s05-subquot}; Lean-friendly.
- **why problem:** Prop. \ref{prop:s05-subquot} application requires stage 06 Lemma D ($\Ann\fa=\fb$) which assumes $\T$ finite free $A$-Gorenstein, $\T/\fa,\T/\fb$ torsion-free, $\fa\cap\fb=0$, $\T_K=(\T/\fa)_K\times(\T/\fb)_K$, and $\T''=\T/\fb$ $A$-free. The GL2 Hecke algebra $\T_\m$ (Hida ordinary) is not known to be finite free over $\Lambda$ at Eisenstein or without control; Gorenstein hypothesis alone does not give $\Ann\fa=\fb$. Stage 06 Lemma D proof is not imported, so circular inter-stage dependency is hidden as "citation not interface" (line 482-483) but Lean L2 explicitly needs Lemma D from stage 06. Compatibility in $s$ "by choosing $\Lambda$-adic generators" is not proved (requires $\Lambda$-freeness of both sides, only definite side cited).
- **suggested fix:** State Prop. \ref{prop:s05-Xiso} as \stpmc{} with explicit extra hypotheses ($\T_\m$ finite free over $\Lambda$, $\T''$ $\Lambda$-free, etc.) matching Prop. \ref{prop:s05-subquot}; note Lean L2 depends on stage 06 Lemma D copy (decouple tracks per SPLIT §Conventions 3) or prove Lemma D locally.

### F8
- **id:** F8
- **location:** Imported interfaces §6 (lines 439-481)
- **severity:** minor
- **category:** interface
- **claim:** Imported restated as in SPLIT; all required interfaces present.
- **why problem:** SPLIT lists for stage 05 \texttt{if:s01-classset}, \texttt{if:s01-brandt}, \texttt{if:s01-hecke}, \texttt{if:s01-targets}, \texttt{if:s02-indef}, \texttt{if:s03-graph}, \texttt{if:s03-ribet}, \texttt{if:s03-amalgam}, \texttt{if:s04-ekills},\texttt{if:s04-Mord},\texttt{if:s04-lambdaribet},\texttt{if:s04-etaB}. Draft correctly imports these but: (i) merges \texttt{if:s04-*} into one interface environment (line 476) instead of separate \texttt{if:} labels; (ii) omits rank formula $(q-1)|X_B(U)|+1$ from \texttt{if:s02-indef} in label but includes it in body (line 461) – body actually includes rank, so label merge is cosmetic but violates "restate verbatim" convention; (iii) does not list \texttt{if:s01-mass} but SPLIT does not require it for 05, so no issue. More importantly, local macros \providecommand{\BG}{\mathrm{BG}} etc. (lines 4-9) violate SPLIT Conventions 2: macros are defined in preamble.tex; do not redefine locally. $\BG$ collides with SPLIT \G (Bruhat-Tits tree) and \GDR definitions.
- **suggested fix:** Split combined interface into four separate \texttt{interface} envs with correct \texttt{\label{if:s04-ekills}} etc.; keep rank formula explicitly labelled; move local macros to `missing/stage-05.md` request per drafter convention 1, or guard with \providecommand only if absent from preamble.

### F9
- **id:** F9
- **location:** Thm. \ref{thm:s05-G}(G1) line 75 + stage.bib entry DR line DR note + Risks R7 line 569
- **severity:** minor
- **category:** reference
- **claim:** (G1) semistable model of $X_0(N)$ with two copies of $X_0(M')$ meeting at $\Sigma(M')$ \stcited{} \lit{deligne-rapoport_1973_les-schemas-de-modules-de-courbes-elliptiques}{Ch.V §1 cited by Ribet} + \lit{ribet-stein_2001_lectures-on-serres-conjectures_preprint}{§3.9 Fig.3 (3.1) p45 for $X_1(M')\cap\Gamma_0(q)$}.
- **why problem:** DR Ch.V §1 is not verified line by line: stage.bib note admits "did not re-verify Ch.V §1 line by line (OCR quality)" and proof strategy relies on Ribet secondary citation. SPLIT requires verify every \stcited{} against PDF in `literature/` with theorem/section/page via \lit{}{}. Using [RS (3.1)] for $X_1(M')\cap\Gamma_0(q)$ to support $X_0(N)$ description mixes levels; Risks R7 already flags [RS (3.1)] and [PW Prop.6.5] do not state (G2) in form used, but same applies to (G1). Preprint pagination (RS p45) is unstable.
- **suggested fix:** Keep \stcited{} but add "(reference not re-verified beyond Ribet's citation; see missing/stage-05.md)" per convention 6, or verify DR Ch.V Thm.1.16 / Ch.V §1 directly and cite page number after OCR cleanup.

### F10
- **id:** F10
- **location:** Hypothesis \ref{hyp:s05-X}(X4) lines 180-185 + Prop. \ref{prop:s05-Xlambda}(d) lines 237-240 + Risks R4 line 564
- **severity:** major
- **category:** correctness / gap
- **claim:** Graded pieces are $\Hom(\Z[S_s]^0,\Zp(1))$ (transpose), $T_pJ_1(Mp^s)^{\oplus2}$, $\Z[S_s]^0\otimes\Zp$ with action $h\mapsto\theta_s(h^\Ros)$ where $h^\Ros$ is Rosati dual ($T_\ell:\langle\ell\rangle^{-1}T_\ell$), and this Rosati twist is what pins $e=+1$.
- **why problem:** Rosati dual on $J_s=J_1(Mp^s)\cap\Gamma_0(q)$ is not $ \langle\ell\rangle^{-1}T_\ell$ for all $\ell\mid M$ (Atkin-Lehner at $q$ changes dual). Stage 01 adjoint formulas are for definite Brandt pairing, not proved to coincide with Rosati on $J_1$; Lemma \ref{lem:s05-consistency}(b) asserts compatibility but is marked \sttoprove{} formal from stage 01. Without that, (X4) top piece Hecke structure is underdetermined, and Prop.\ref{prop:s05-AL} shows $\theta_s$ vs $\theta_s^\Ros$ are indistinguishable at fixed $s$ but fixed by (X3) naturality – which itself is hypothetical. Risks R4 acknowledges this is "easy to get wrong" but stage exports it as part of \texttt{if:s05-hypX} hypothesis, so downstream stages (06) will assume it.
- **suggested fix:** Keep \sthyp{} label but add explicit proviso: "Rosati-twisted action is part of hypothesis; verification requires comparison of Rosati on $J_1(Mp^s)$ with definite adjoint - see missing/stage-05.md M1". Cite Grothendieck SGA7 IX 9.1-10.4 for monodromy $N$ sign and specify top piece is dual of $\Xq(J_s^\vee)$ to justify $\theta_s(h^\Ros)$.

### F11
- **id:** F11
- **location:** Lean track L1 lines 521-526 + L4 line 529 + Risks R6 line 567
- **severity:** minor
- **category:** feasibility
- **claim:** Lean def \texttt{Hyp.X.char} as \texttt{CharGroupData} + \texttt{TateModuleData} with Hecke relations of Lemma \ref{lem:s05-consistency}(a), never an axiom; Prop.\ref{prop:s05-Xlambda}(a) as theorem taking \texttt{Hyp.X.char} as argument once stage 04's $e$ and $\varprojlim$ exist.
- **why problem:** \texttt{CharGroupData} includes a symmetric positive-definite pairing and transition maps $\beta_{s's}$ satisfying Hecke relations, which is satisfiable by fiat taking $G.X s:=\Z[S_s]^0$ (Risk R6 Lean vacuity). This makes Lean theorems "for every $G$ with these properties" vacuously true, not tying $G$ to actual $\Xq(J_s)$. Stage correctly documents this as outside Lean, but feasibility claim "Prop.\ref{prop:s05-Xlambda}(a) as theorem taking \texttt{Hyp.X.char} as argument" assumes stage 04's $e$ and $\varprojlim$ for $e\Zp[S_s]$ are already formalised; SPLIT says stage 04 has no Lean reuse for Hida theory, so L4 is blocked. No issue mathematically, but Lean roadmap overstates independence.
- **suggested fix:** Keep \texttt{CharGroupData} abstraction but note vacuity in docstring; make L4 conditional: "after stage 04 formalises $e$ on finite $\Zp$-modules and $\varprojlim$ Mittag-Leffler lemma".

### F12
- **id:** F12
- **location:** Remark \ref{rem:s05-hsieh} lines 143-155
- **severity:** minor
- **category:** reference / other
- **claim:** Hsieh defines quaternionic $U_q$ as $f\mapsto f(x\varpi^D_q)$ i.e. our $\Pi_q$, states $\mathrm{JL}(U_q)=(-1)U_q$ \lit{hsieh_2017_hida-families-and-p-adic-triple-product-l-functions_arxiv}{§4.2 p30; §4.5 p34}; either misprint or different normalisation; consequence for stages 04 and 06 to re-sign $U_q\mapsto-U_q$ relative to Hsieh.
- **why problem:** No verification that Hsieh's $U_q$ at $q\mid N^-$ is defined on forms with $f(xz)=z_p^{-\kappa}\chi^{-1}(z)f(x)$ twisted central character (stage cites this as example). If Hsieh's $U_q$ includes central twist, then $U_q\mapsto-U_q$ automorphism preserves kernels but does NOT preserve congruence ideals $ \cc_{\T'} $ when $\fa+\fb$ involves $U_q$ eigenvalue; claim "congruence ideals are unaffected" is asserted without proof and contradicts Prop.\ref{prop:s05-subquot} dependence on $\fa+\fb$.
- **suggested fix:** Weaken to "congruence ideals are unaffected up to the automorphism $U_q\mapsto-U_q$; explicit ideal equality in stage 06 must be checked after re-signing" and make test T05-1 the arbiter before exporting re-signing instruction to stages 04/06.

## Summary
Stage 05 correctly isolates $\HypX$ as hypothesis, fixes $\varepsilon=+1$ intent, and honestly marks $\Gamma_1$-level inputs as \stexp{}; its main weaknesses are $\Gamma_0$-level sign irrelevance and missing Hida/$\varprojlim$ justification for $\Lambda$-adic passage, plus Rosati-twist and factor-2 bookkeeping that propagate to exported \texttt{if:s05-hypX}.
Mathematically the stage has no critical contradictions, but Prop.\ref{prop:s05-sign}(a),(e), Lemma \ref{lem:s05-consistency}(a)-(b), and Prop.\ref{prop:s05-Xlambda}(a) need corrections/verification before Lean/HACS can depend on them.
Overall the geometric route is presented with verifiable $\Gamma_0$ citations and clearly scoped hypothetical $\Gamma_1$ extensions, suitable for a hypothesis stage once noted fixes are applied.
