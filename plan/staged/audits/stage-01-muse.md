# Audit of stage.tex (stage 01) against SPLIT.md

## Findings

### F1
- **Location:** `prop:s01-finite` (Proposition finiteness), lines ~40-48; also `lem:s01-stab`(c)
- **Severity:** minor
- **Category:** reference / correctness
- **Claim:** "`|O_x^×| ∈ {2,4,6,8,12,24}` consequently `|Γ_x|` divides 24 for every `U ⊆ \hat O^×`."
- **Why problem:** The set includes `8`. `8 | 24` is true (`8*3=24`) so divisibility claim holds, but the occurrence of `8` at maximal level (`U=\hat O^×`, `O_x` maximal) is not realized over Q. Voight Thm 11.5.14 p.176 for definite quaternion orders over Q gives `|O^×| ∈ {2,4,6}` for generic `D`, and `12` (`D=3`) and `24` (`D=2`) only for the two small discriminants. `8` occurs for Eichler orders of non-squarefree level or for `U_0(N)` structure, not for maximal `O_x`. The import `P2/ClassSet.lean: stabilizer_units (c)` is cited as source of `{2,4,6,8,12,24}` – that declaration is for `classSet_finite_of_open` with general open `U`, not specifically for `U=\hat O^×`. Statement should qualify `8` as not occurring at maximal level.
- **Suggested fix:** Amend to: at maximal level `|O_x^×| ∈ {2,4,6,12,24}` (hence `|Γ_x|∈{2,4,6,12,24}`); the value `8` occurs only after passing to `U_0(N)`/`U_1(N)` or non-maximal Eichler orders. Add precise `lit` pointer to Voight table and correct Lean declaration name/line.

### F2
- **Location:** `lem:s01-stab` proof (b), lines ~60-71
- **Severity:** minor
- **Category:** gap
- **Claim:** "At `p`, `x_p^{-1}γ x_p ∈ U_1(p)_p`, so its reduction mod `p` has eigenvalue `1`, whence `p | 2-t`."
- **Why problem:** Step implicitly uses `det=1`. A general element of `U_1(p)_p = { [[a,b],[c,d]]: c≡0, d≡1 mod p }` has reduction `[[ \bar a, \bar b],[0,1]]` with trace `\bar a+1`, not `2`. The conclusion `tr ≡2 mod p` needs `Nrd γ=1` ⇒ `det ι_p(γ)=1` ⇒ `a·1 ≡1 mod p` ⇒ `\bar a=1`. Seed and Buzzard p.11 argument include this determinant condition. Proof as written omits it, leaving gap for reader why eigenvalue `1` forces `t≡2`.
- **Suggested fix:** Insert one line: "Since `Nrd γ=1` by (a), `det ι_p(x_p^{-1}γ x_p)=1`, so with `d≡1` we get `a≡1 mod p` and reduction is unipotent `[[1,*],[0,1]]`, hence `t=tr γ ≡2 mod p`."

### F3
- **Location:** `thm:s01-mass` (b) level change and `prop:s01-adjoint` (c), `def:s01-pairing`
- **Severity:** major
- **Category:** gap / interface
- **Claim:** "`∑_{X_B(U')}1/|Γ_{x'}(U')| = [U:U']∑_{X_B(U)}1/|Γ_x(U)|`. With `w` in place same holds iff `-1∈U'` or `-1∉U`; if `-1∈U\U'` extra factor `2`" and "`ν∘π_* = tr∘ν'`" / "`ν∘T_g = T_{g^{-1}}∘ν`" without hypothesis.
- **Why problem:** The `w`-variant and the `ν` identities depend on the `-1` factor. `w_x = |Γ_x|/2` when `-1∈U` else `|Γ_x|`. The text states the condition once in Thm (b) but omits it in Prop `s01-adjoint`(c) header and in `if:s01-brandt` export. SPLIT `if:s01-brandt` intentionally abstracts "when `p∤|Γ_x|`" (SPLIT p.7) and expects the factor-2 subtlety to be documented. Without explicit hypothesis, a downstream stage using `Z_p[X]≅Z_p^X` at mixed levels (`\hat O^×` → `U_1(N)`, `N≥3`) will get the index wrong by `2`.
- **Suggested fix:** Add hypothesis to Prop `s01-adjoint`(c) and `if:s01-brandt`: "Assume either `-1∈U'` or `-1∉U` (in particular for `p≥5` at `U_1(p^s)`-level where all `Γ_x=1` the condition holds); otherwise `ν∘π_* =2·tr∘ν'` / `π^*∘ν ≠ ν'∘π^!`." Propagate same qualifier to `if:s01-mass` level-change bullet.

### F4
- **Location:** `def:s01-NUp` / `lem:s01-Up` (a)-(c) and Interface deviation (iii)
- **Severity:** major
- **Category:** interface / correctness
- **Claim:** "`N_{U_p}=[U ι_p^{-1}diag(p,1) U]` commutes with `π_*` along `S_{s+1}→S_s`; the seed's literal `[U diag(1,p) U]` is the other operator commuting with trace."
- **Why problem:** SPLIT Shared conventions and `if:s01-hecke` require "Fix the one that commutes with pushforward `S_{s+1}→S_s` (seed §2.5). Stage 01 owns this choice." Stage correctly identifies the inconsistency in seed §2.5 (seed states requirement and gives opposite matrix) and fixes `N_{U_p}`. This is mathematically correct, but downstream consistency requires every citation of `U_p` from literature (Buzzard, Hida, LV, Hsieh, Chenevier) to be translated; the stage does this in `rem:s01-Upconv` and `thm:s01-lambdaJL` Caveat. No error, but the audit must record that the deviation from seed's literal formula is intentional and must be carried through stages 04/05. The proof of Lemma (c) claim "both of size `p^3`" for `K_s g' K_s /K_{s+1}` is unverified – index `[K_s:K_{s+1}]=p^3`? Actually `[U_1(p^s):U_1(p^{s+1})]=p^3` (`a∈1+p^sZ_p`, `b,c` free). The multiset sizes are plausible but the text does not justify `K_s=(K_s∩g'^{-1}K_s g')K_{s+1}` needed for the trace claim.
- **Suggested fix:** Keep `N_{U_p}` as defined. In Lemma proof (c) add explicit index computation: `|K_s/K_{s+1}|=p^3`, `|K_s/(K_s∩g'K_s g'^{-1})|=p`, and the decomposition `K_sq'K_s = ∐_{c∈p^sZ_p/p^{s+1}} [[1,0],[c,1]] g' K_s`. State that the "size `p^3`" refers to cosets modulo `K_{s+1}`, not to double-coset size. No change to interface content.

### F5
- **Location:** `def:s01-brandt` / `rem:s01-dictionary`
- **Severity:** major
- **Category:** gap / feasibility
- **Claim:** Dictionary `F↦f`, `f(x)=x_p·F(x)` is isomorphism `Brandt(U,V_k)⊗Q_p ≅ quatForms` and carries seed's `T_g` to import's `f↦∑ f(xg_i)`. "It is not integral (`x_p∉GL_2(Z_p)`); integral statements must be made on seed side."
- **Why problem:** Correctly flagged, but the Lean track L4 proposes "dictionary as linear equivalence over `Q_p`, so that `hecke_self_adjoint` etc. transfer." Transfer of `hecke_self_adjoint`/`brandt_weighted_symmetry` which are proved in import for `quatForms` at level `\hat O(M)^×` and trivial-prime-to-level Hecke only, to the seed side with non-integral twist, requires checking the twist commutes with `μ_A(g)` factor (Gross Prop 6.9). The stage states this is "one line: `x_p u_p F(xu)=x_p F(x)`" but integrality failure means `L3` (double-coset Hecke with monoid action) cannot reuse import's `heckeOperator O n` for `n` not prime to level – the stage itself notes "import's `heckeOperator O n` sums over all of `\hat O_n`; for `n` not prime to level it is not `U_ℓ`". This gap between formal (`Q_p`) and integral (`Z_p`) levels is correctly noted in Risks (R5) but not reflected in interface: `if:s01-brandt` exports "norm-map identification `Z_p[X]≅Z_p^X` when `p∤|Γ_x|`" without caveat that it is perfect only via adjoint.
- **Suggested fix:** In `if:s01-brandt` and Lean L4, explicitly state: transfer holds over `Q_p` for Hecke away from `pD`; integral `Z_p` statements (pairing perfectness, `U_p` integrality) stay on seed side and require `p>k-2` or dual coefficients (`def:s01-pairingV` note). No interface content change, but add sentence to Dependencies: "Import results used only after tensor `⊗Q_p` via dictionary."

### F6
- **Location:** `thm:s01-mass` (d) second half, `ex:s01-masschecks` (D=3 case)
- **Severity:** minor
- **Category:** correctness
- **Claim:** "`|S_s| = φ(D)/24·ψ(Mp^s)·φ(Mp^s)` for `p≥5`, `s≥1`, `(M,pD)=1`" and example `D=3`: "`|S_s|=2·25^{s-1}` for `p=5`, `M=1` – this is count used in seed test T3."
- **Why problem:** Formula is correct given (a)-(c) plus Lemma stab (b) (`Γ_x=1`). However SPLIT `if:s01-mass` exports only "mass formula `∑1/|Γ_x|=1/24∏(ℓ-1)` at maximal level (full-unit convention) and its level change" – the closed `|S_s|` formula is intended for stages 02-04/HACS but is not part of the `if:` label per SPLIT p.7 `if:s01-mass`. Stage's interface `if:s01-mass` adds "`including |S_s|=...`" – this is an allowed strengthening (SPLIT says "including" in Goals, but Interfaces paragraph lists only mass + level change). No inconsistency, but Lean L2 claims "|S_s| (from `mass_orbit_count`)" – `mass_orbit_count` is orbit-counting lemma, not the index `ψφ`; the index part is `sttoprove` per Thm (c) second half. Status labeling should separate them.
- **Suggested fix:** Split Thm (d) status: first half `stpmc` (under `Hyp.EichlerMass`), second half `stpmc` modulo `Hyp.EichlerMass` + Lemma stab, with explicit sub-status: level-change is `stformal`, index `ψφ` is `sttoprove`. Update Lean L2 to list two separate lemmas.

### F7
- **Location:** `thm:s01-JLclassical`, `thm:s01-lambdaJL` (Targets), stage.bib entries `JL`, `HPS80`, `Shz65`
- **Severity:** minor
- **Category:** reference
- **Claim:** Classical JL cited to `jacquet-langlands_1970` Thm 16.1 p.494; basis problem to `hijikata-pizer-shemanske_1980` §0 p.280; Shimizu scan "not text-verified"; Λ-adic JL to `LV` Prop 6.1 p.27 and `Hs` §4.5 p.34 with sign `±`.
- **Why problem:** Citations are as careful as possible; `stage.bib` correctly marks `Shz65` scan as "statements NOT verified" and `Piz80` scan not verified, and `JL` Thm 16.1 is noted as "proof sketched" – matching SPLIT Doubtful points about missing literature (`Shimizu`, `Pizer` scans). The Λ-adic citation notes convention mismatch (`U_q ↦ ±Π_q`, Hsieh `(-1)U_q`) and records sign issue for stage 05 (`ex:s01-Pi11`). This matches SPLIT Gaps/O1. No wrong theorem numbers detected in spot-check of `Vo` pages (11.5.14 p176, 13.3.11 p206, 25.1.1 p415, 41.3.1 p770) – all exist in Voight 2021.
- **Suggested fix:** No fix needed; retain "scan, not text-verified" tags. Optionally add explicit note in `thm:s01-JLclassical` that `JL` Thm 16.1 is representation-theoretic and seed's Brandt-form statement is via HPS/Shimizu, as already done.

### F8
- **Location:** Lean/HACS/Talk tracks (sections "Lean, HACS, talk" and "Risks")
- **Severity:** minor
- **Category:** feasibility
- **Claim:** Lean L0-L4 and HACS H1-H5 as listed; Risks R1-R7.
- **Why problem:** Feasibility assessment is realistic: L0 is reuse (thin facade), L1-L3 are "easy/medium" matrix algebra, L4 is `Q_p` linear equivalence, Hypotheses `Hyp.EichlerMass`, classical JL, `Thm s01-lambdaJL` as `Prop`s only if needed – aligns with SPLIT "Lean. Mostly reuse and adapt. Levels `U_1(Mp^s)` and Iwahori ... are new." and "HACS. Definite module: class sets plus Brandt matrices... checked against mass formula and seed C4(ii)." No overclaim: stage does not promise proof of mass formula or JL, keeps them `stcited`/`sthyp`. HACS H4 (verify `π_*U_p=U_pπ_*` vs failure for `U'_p`) is concrete test of `N_{U_p}` normalisation; SPLIT Doubtful points O1 explicitly leaves `U_p` normalisation to stage 01.
- **Suggested fix:** Add to Lean L3 explicit bound `s≥1` for `N_{U_p}` representatives (index `p` vs `p+1` at `s=0`), mirroring Lemma `s01-Up`(a) to prevent `s=0` misuse in later stages.

## Summary

Stage 01 correctly fixes `B_D`, levels, `X_B(U)`, `Γ_x`, `w_x`, mass formula (full-unit) and `|S_s|` counts, Brandt modules/pairing with adjoint-aware norm map, and `N_{U_p}` normalisation commuting with pushforward, matching SPLIT interfaces `if:s01-*`. All cited theorem numbers/pages checked against `stage.bib` verified notes exist; scans are honestly flagged. Main gaps are expositional: determinant step in Lemma stab (b), factor-2 hypothesis for `w`/`ν` level change, and `Q_p` vs `Z_p` scope of the import dictionary – all fixable with one-line qualifiers and no change to exported interfaces.
