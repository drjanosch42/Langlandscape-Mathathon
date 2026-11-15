<!-- SPDX-FileCopyrightText: 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# HACS Lean project vs. our hypotheses: a forward-looking survey

Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)

- Date: 2026-11-15. **Read-only survey**: no build, no `lake`/`lean`, nothing under `code/hacs/` modified.
- Sources: `origin/main` = `5348973647df993db7f5a8c570c8e60467eceea7` (HACS snapshot `code/hacs/lean`, tree
  `793db08b`, last touched by `5162c43d`, 2026-11-14); `origin/wip-implementation` =
  `59af5e78a3e947b66f38b225047fecbbee668f78` (`lean/Langlandscape/HYPOTHESES.md`, `Hyp/*.lean`,
  `mathematics/report/hypotheses.tex` §"Projected hypotheses", `plan/implementation/stage-06.md`).
- Question: which HACS 0.2.1 Lean statements could, **after a port to Lean v4.35.0 (post-Mathathon)**, discharge or
  substantially shorten the discharge of hypotheses our Lean formalization assumes? This is a map, not a plan.
- Vocabulary in the table: **exact** (same statement up to renaming), **stronger/weaker**, **related** (same
  mathematics or source, different statement; does not discharge), **related-infrastructure** (reusable
  definitions/lemmas/techniques, not the statement), **no match**. "Discharges" is claimed only for exact/stronger
  *proved* results; there is **none** (see §3).
- Every file:line below was re-checked with `grep -n`/`sed -n` on the snapshot. Paths relative to `code/hacs/lean/`.

## 1. Inventory of `code/hacs/lean`

**Versions.** `lean-toolchain` = `leanprover/lean4:v4.33.0`; `lakefile.toml` requires only Mathlib at
`rev = db584cd6d46c92f209a44c0f1c829460d327499d` ("chore: bump toolchain to v4.33.0 (#42604)"). Our frozen Mathlib
(`56a00585`, 2026-10-13, v4.35.0) has `db584cd6` as an ancestor; 1682 commits lie between. Libraries: `GL2` (default),
`AnthropicFLT` (srcDir `Vendor/AnthropicFLT`, default, needs `backward.isDefEq.respectTransparency.types=false`),
`L23Bench`, `L23Cells` (generated, not default).

**Modules (GL2/: 271 files, 66,361 lines; plus 25 vendored FLT files, generated `cells/` ~25k lines).**

| area | content (mathematics) |
|---|---|
| `MP/` (33 files) | SL₂(ℤ) Bass–Serre tree `Γ·[ρ,i]` (stabilisers ⟨U⟩, ⟨S⟩, ⟨−I⟩), its permutation-module SES, Mayer–Vietoris LES, periodic resolutions of cyclic stabilisers, Moerdijk–Pronk/Bredon comparison |
| `Model/`, `Cone/`, `Cosets/` | 7-vertex orbifold model of SL₂(ℤ)\ℍ, mapping cones, coset reps of Γ diag(1,N) Γ |
| `M4/`, `M5/`, `M6/` | Hecke operators `T_{ΓgΓ} = cor∘c_g∘res` on `H^n(SL₂(ℤ);V)` (all degrees, resolution-independent), Γ₀(N) via Shapiro, nebentypus correspondences, double-coset classification |
| `Conventions/` | Sym^n action, contragredient, `T(p^ν)` full vs primitive, **nebentypus/diamond dictionary**, Bernoulli `B₁` |
| `HeckeZ/`, `Saturation/`, `Algorithms/` | Hecke algebras over ℤ / ℤ_p at specific (N,k), congruence modules, Eisenstein splits, saturation `T^sat`, certificates |
| `L23/` | dim H^q(SL₂(ℤ); Sym^n F_ℓ²), ℓ = 2,3; 2-torsion exponent |
| `Literature/` (17 files, 1353 lines) | cited theorems as `structure … : Prop` (Hida ENS/Invent, Emerton, Wiles, Mazur, Diamond–Im, Serre, Sturm, Bellaïche–Khare, Washington) |
| `Vendor/AnthropicFLT/` | byte-identical copy of anthropics/fermats-last-theorem @ `6e837e75`: corestriction, Hecke on H¹, abstract `HeckeAlgebra` (Gelfand pair), `AbstractHeckeOperator` |

**Status.** Re-checked: 0 `axiom` declarations, 0 `sorry`/`admit` in code (all hits are prose:
`Conventions/SymPowDet.lean:228`, `Saturation/Basic.lean:18`, `Model/WellDefTau.lean:579`, …), 0 `native_decide`
uses (kernel evaluation is `decide +kernel`). `census.tsv` (3972 rows): 3714 `proved`, 208 `proved_mod_lit`,
49 `lit_hyp`. Vocabulary: `proved`, `proved_mod_lit` (proved from named literature structures only), `lit_hyp`
(the structures), plus `stated/planned/lit_mathlib/lit_flt_*`. Literature convention (`Literature/Basic.lean`):
every external fact is a `Prop`-structure with a quoted, locator-checked source; arithmetic objects are
**interface data** (type parameters, never identified with real Hecke algebras) — exactly our F6 "schematic" pattern.

**Licence.** Own files Apache-2.0 (© 2024–2026 Fabian Januszewski; SPDX lines on most files, rest via
`REUSE.toml`); vendor Apache-2.0 (© Anthropic, PBC; `AbstractHeckeOperator` adapted from Imperial FLT, © Kevin
Buzzard, Apache-2.0). Our Lean is Apache-2.0 (`agents/rules/licensing.md` l. 7), so code can be moved across with
attribution/NOTICE kept and a change notice per Apache-2.0 §4(b) (as our import already does for its FLT copies).
No compatibility issue on the Lean side.

**Overlap with Mathlib v4.35 (conservative).** HACS already uses Mathlib's `groupCohomology.coindIso` (Shapiro),
`Rep.res`, `CongruenceSubgroup.Gamma0`, `ModularForms.LevelOne`. HACS's own cyclic periodic resolution
(`MP/TreeCyclic.lean:50 CycDat`, `MP/PeriodicCone.lean`) parallels Mathlib's
`RepresentationTheory/Homological/GroupCohomology/FiniteCyclic.lean`, which was already present at `db584cd6`;
HACS uses its own for cochain-level control. v4.35 adds group *homology* (`GroupHomology/{Basic,Shapiro,LowDegree,
LongExactSequence,FiniteCyclic}` exist in our Mathlib) — relevant because our `SerreCoh` is stated in homology,
HACS only in cohomology. Mathlib v4.35 still has no Hecke operators on modular forms, no quaternion orders, no
Iwasawa algebra ℤ_p[[ℤ_p]] ≅ ℤ_p[[T]] (grep; conservative). I cannot tell beyond that without building.

**Overlap with our project.** No mutual imports. Mathematically complementary: HACS has nothing on quaternion
algebras, Brandt modules, Eichler orders/mass, strong approximation, Bruhat–Tits trees, Ihara, Ribet, Jacobians,
Tate modules, Γ₁(N) cohomology, parabolic cohomology, ordinary projectors, Gorenstein (grep over `GL2/`, `Vendor/`).
**Module-name clash:** HACS's `AnthropicFLT` and our import's `AlgJLVendor`
(`lean/trace-formula-project-import/lean/lakefile.toml:28`) both use srcDir `Vendor/AnthropicFLT` with top-level
modules `Definitions.Def_LocalLanglands_{HeckePair,GelfandInvolution}`; the contents differ (ours: bare
`import Mathlib` replaced by 9 specific imports, unused import removed, per its GL2TF change notice). HACS has 4 more
`Definitions.Def_*` files plus `Theorems.*`, `P2M.*`. Building both in one workspace requires one copy (ours,
import-minimised, extended by the 4 missing files) or a renamed module prefix.

## 2. Mapping table

HACS status column: per-file sorry/axiom counts are **0/0 for every file cited** (global grep, §1), so only the
declaration status is given. Effort S = mechanical port of ≤ a few small files; M = port + non-trivial glue to our
definitions; L = substantial new mathematics beyond what HACS provides.

### 2a. Registered hypotheses (21 rows of `HYPOTHESES.md`)

| our Lean name | HACS file:line + decl | match | gap | HACS status | effort |
|---|---|---|---|---|---|
| `GL2TF.Hyp.EichlerMass` | none found; nearest `Literature/EisensteinIdeal.lean:19 mazurN` (= num((N−1)/12)) | no match | for D prime, 24·Mass = D−1 and Mazur's n = num((D−1)/12) is only a numerical echo; HACS has no class sets/orders | def | — |
| `Hyp.EichlerMass` (alias) | as above | no match | — | — | — |
| `Hyp.JLClassical` | `M6/ThetaExt.lean:129 heckeClassical_holds`; `M4/LevelN.lean:30 levelN_shapiro`, `:607 nebCorr`, `:737 nebRelations`; `M4/Relations.lean:174 heckeAlg_comm` | related-infrastructure | gives genuine Hecke modules `H^n(Γ₀(N);V)` with `T_ℓ` (`Γ₀Q N`, general N, `LevelN.lean:571`), a candidate to instantiate `GL2CuspData` on the cohomology side; missing: Eichler–Shimura over ℂ at k=2 (only cited), the cuspidal/parabolic part, the D-new subspace, `FiniteDimensional ℂ`; commutativity is proved only modulo `HeckeCommute` (Shimura 3.8); JL itself stays cited | proved; `nebRelations`, `heckeAlg_comm` proved_mod_lit | L |
| `Hyp.JLClassical` | `Literature/DiamondIm.lean:56 DiamondImEichlerShimura`, `:86 DiamondImEigenspaces` | related (lit) | would let the "S is the true space" caveat be stated as an ES literature structure instead of prose; stated weaker than source (∃ Hecke-equivariant β) | lit_hyp | M |
| `Hyp.LambdaJL` | `Conventions/NebentypusDictionary.lean:221 transported_eq`; `Conventions/Nebentypus.lean:159 diamond_eigen` | related-infrastructure (normalisation) | HACS's cohomological `T_p` on `V(χ)` equals `χ(p)·T_p^{cl}` on `S_k(N, χ̄)`, i.e. DS's `T_p^* = ⟨p⟩⁻¹T_p`; `⟨d⟩ = χ(d)` on the character model. This is the GL₂-side analogue of our X1 diamond erratum and is what an honest `genGL (.dia d)` must be checked against; it does not touch the Λ-adic/ordinary statement | proved (file final theorems proved_mod_lit: Petersson as hypothesis) | S (read) / M (port) |
| `Hyp.LambdaJL` | `Literature/Hida.lean:35 HidaEns31`, `HidaControl.lean:56 EmertonEis`; `Vendor/AnthropicFLT/Definitions/Def_LocalLanglands_HeckePair.lean:63 HeckeAlgebra` | related | HidaEns31 gives Λ-freeness of `TGL`-type algebras (GL₂, p∣N) as lit; `HeckeAlgebra` is the abstract local Gelfand-pair algebra, not an ordinary Λ-adic Hecke algebra; nothing about the D-new ideal or the surjection to `TB` | lit_hyp / proved | — |
| `Hyp.SA` | none found | no match | no adeles, no quaternion units | — | — |
| `Hyp.HS` | none found | no match | — | — | — |
| `Hyp.BTtree` | none found; nearest `MP/TreeRetract.lean:514 treeses_exact`, `MP/TreeSES.lean:184 treeSES_shortExact` | no match | HACS's tree is the (4,6)-biregular Bass–Serre tree of SL₂(ℤ) as a chain complex, proved acyclic by retraction from the 7-vertex model; no `SimpleGraph`, no `IsTree`, no lattice/coset model of the (q+1)-regular BT tree of PGL₂(ℚ_q); the proof route does not transfer | proved | — |
| `Hyp.SerreCoh` | `MP/TreeComparison.lean:35 PermRes`, `:209 PermRes.cohIso`; `MP/TreeCochains.lean:70 permHom`; `MP/TreeCyclic.lean:306 resP`, `:325 barIso`; `MP/TreeSES.lean:184`, `MP/TreeMV.lean:283 mvLES_exact_coh` | related-infrastructure | the *general* pieces are: resolutions by free permutation modules on bases (`PermRes.free` demands free actions), `Hom_G(k[X],A) ≃` equivariant functions, restriction of such resolutions; the tree SES and MV LES are **only for the specific 2-vertex amalgam of SL₂(ℤ)** — there is no general "group acting on a tree / graph of groups" lemma. Ours needs: Γ_U acting on the BT tree with finite (not necessarily cyclic) stabilisers, `|Γ_x|` invertible in R, **homology** H₀, H₁ (HACS: cohomology only), identification with `ker/coker ∂` of our `partialHom` | proved | L |
| `Hyp.SerreFree` | none found | no match | no free groups / `FreeGroupBasis`; HACS does not even state the amalgam isomorphism SL₂(ℤ) ≅ ℤ/4 *_{ℤ/2} ℤ/6 | — | — |
| `Hyp.RamNrdSurj` | none found | no match | no local division algebras | — | — |
| `Hyp.IharaH0` | none found | no match | no Ihara/level raising (only the word "Ribet" in blueprint prose) | — | — |
| `Hyp.EllipticCount` | none found; nearest `MP/TreeGamma.lean:244 model7_stab_I`, `:254 model7_stab_Rho` | no match | those are stabiliser orders 4, 6 of i, ρ in SL₂(ℤ), not unit groups of Eichler orders / Eichler's class number formula | proved | — |
| `Hyp.BrandtStabFree` | none found; nearest `M5/Smith.lean:88 dc_classify` | no match | double cosets / elementary divisors in M₂(ℤ) of det p^ν (split side); our lemma needs the neighbour description inside B and ℤ[i], ℤ[ω] ⊂ B | proved | — |
| `Hyp.PadicOrdDecomp` (discharged) | none needed; HACS has no ordinary projector (the `e` in `Saturation/LevelOne.lean` ~1016–1200 is a generic idempotent) | no match | already discharged by `Ordinary.padicOrdDecomp_holds` | — | — |
| `Hyp.MordLambdaFree` | `Literature/Hida.lean:73 HidaInvent31` (V⁰, W⁰ Λ-free, ranks), `:35 HidaEns31` | related (GL₂ analogue) | GL₂ ordinary cohomology/Hecke algebra vs definite `M_ord(U) = lim e ℤ_p[X_s(U)]`; HACS Λ = `PowerSeries ℤ_[p]` (`Hida.lean:16 Iw`) vs our `Lam ℤ_[p] G π = lim ℤ_p[Δ_s]` (no Lean iso between them on either side); our control-kernel clause has no HACS counterpart (Invent Thm 3.1(i) is not encoded) | lit_hyp | — |
| `Hyp.HidaControl` (definite, mod p^s) | `Literature/Hida.lean:54 HidaEns32` (`h/(P_k h) ≃+* hk k`), `:110 HidaInvent66` (ordinary H¹_P ⊗ ℤ/p^m) | related (GL₂ analogue) | GL₂ Hecke algebras vs definite Brandt modules; ring iso vs iso of ordinary parts of modules mod p^s; `Pk p k = (1+T) − (1+p)^k` (`Hida.lean:19`, weight character γ ↦ (1+p)^k) vs our `P^ad_k = ker([u] ↦ u^{2−k})`; level p ∣ N, p ≥ 5 vs `U₁(M)`-type with p ∤ φ(M) | lit_hyp | — |
| `Hyp.HsiehCR` | `Literature/Hida.lean:146 Wiles214` | related only | Wiles' ordinary local shape (ε₁, ε₂) is a property of λ-adic reps, ours is a condition (p-distinguished, ramification) on abstract residual data; nothing to discharge | lit_hyp | — |
| `Hyp.InvLimExact` | `Literature/Hida.lean:92 HidaInvent47` | related only | GL₂: `e₀H¹(Γ₁(N)) ≃ eH¹(Φ_r)` as bare ℤ_p-isos (no transition maps, no Hecke equivariance); ours: surjectivity of the A-transitions of the definite Ribet system under connectivity | lit_hyp | — |
| `Hyp.X.char` | none found; consistency only: `Literature/EisensteinIdeal.lean:35 Mazur97` | no match | no Jacobians, character groups, Néron models, component groups; `Mazur97` (T/𝔍 ≅ ℤ/n, n = num((N−1)/12)) can be cross-checked against our `Ribet.mazur_check` (Φ^comb ≅ ℤ/num((q−1)/12)) but discharges nothing | lit_hyp | — |
| `Hyp.X.gal` | none found | no match | no Tate modules of Jacobians; `Wiles214` concerns Galois reps of forms | — | — |
| `Hyp.X.iso` | none found; nearest `Saturation/LevelOne.lean:1201 cohforms_iso`, `HeckeZ/Bock/Fibre.lean:32,40` | related only | ours: `e H¹_par(Γ_s, ℤ_p)^±_𝔪[𝔞] ≃ L` at p-power level, localised at a non-Eisenstein 𝔪; HACS: Hecke algebra of H¹(SL₂(ℤ)) ≅ that of M_k at **level 1**, no parabolic cohomology, no Γ₁, no localisation | proved_mod_lit (ES, FormsSameSystems) | — |

### 2b. Planned stage-6 hypotheses (`hypotheses.tex` §sec:hyp-planned; not in Lean)

| our planned name | HACS file:line + decl | match | gap | HACS status | effort |
|---|---|---|---|---|---|
| `Hyp.HsiehGor` | none found | no match | Gorenstein is never stated in HACS Lean (`MazurEis.lean:42`: Mazur (16.3) "not used and not stated") | — | — |
| `Hyp.OldDecomp` | `Literature/Hida.lean:35 HidaEns31`, `:54 HidaEns32` | related (same source) | our source Hi86b Thm 3.1, Cor 3.2 (p. 250) is **the same paper and page** HACS quotes (VERIFIED); but HACS encodes freeness + control, ours is the corrected new/old decomposition (`NewOldData`, `Module.Free I (R/𝔟)`) + Hensel | lit_hyp | S (as cited antecedent) |
| `Hyp.HsiehGorFull` | `Literature/MazurEis.lean:69 MazurEisLocal` | related only | monogenic `T = ℤ_ℓ[η_q]` would imply Gorenstein, but HACS does not state it, and it is the Eisenstein ideal at prime level, weight 2; ours is the full ordinary Hecke algebra at a non-Eisenstein 𝔪 | lit_hyp | — |
| `Hyp.FreeRankTwo` | `Saturation/LevelOne.lean:734 heckerankone`; `Literature/EichlerShimuraLevelOne.lean:52` (cusp systems of multiplicity 2) | related only | level-1 rank count `rank e T^L = ⌈rank e L'/2⌉`; not freeness of rank two over a local Λ-adic Hecke algebra, no Chebotarev | proved_mod_lit | — |
| `Hyp.ResidualBurnside` | none found | no match | no Galois-representation algebra in HACS | — | — |
| `Hyp.TamSpec` | none found | no match | — | — | — |
| `Hyp.HidaControlGL2` | `Literature/Hida.lean:54 HidaEns32` (+ `HidaControl.lean:41 HidaControl` at N = p); consumers/sanity `Saturation/LevelOne.lean:1318 ideal_p_Pk` (proved), `:1342 hidaalgconst`, `HidaControl.lean:62 hidaControl_rankOne` | **near-verbatim source match** (Hi86b Cor 3.2 (3.3b)); statement **weaker/different** | ours (stage-06 l. 138) adds p-stabilisation, (P2), localisation at 𝔪 and the identification `𝒪 ⊗[I] D.R ≅ T_k(N)_𝔪`; HACS: whole cuspidal ordinary algebra, ring iso, guards p ≥ 5, p ∣ N, extra guard k ≡ a (mod p−1) (documented restriction), Λ = ℤ_p[[T]] with `P_k` normalisation (§4) | lit_hyp (+ proved sanity instance) | S |
| `Hyp.KimOta` | none found | no match | — | — | — |
| `Hyp.KimOtaRT` | none found | no match | — | — | — |

## 3. Prioritised targets after a port

No HACS result discharges any of our hypotheses: HACS has nothing on the definite quaternion side, and its
Hida/Emerton material consists of literature structures, which only re-encode hypotheses. The targets below shorten
work or make statements more faithful.

1. **`Hyp.HidaControlGL2` ← `GL2.Literature.HidaEns32` (+ `HidaEns31`, `ideal_p_Pk`).** Same source
   (Hi86b, p. 250), already quoted and locator-verified in HACS, with guards from the source and a non-vacuity
   instance. Porting `Literature/Hida.lean` (153 lines, needs only `PowerSeries ℤ_[p]`) and stating our
   `HidaControlGL2` as "HidaEns32 + bridge" would pin the citation and save the faithfulness audit. Gain:
   consistency and less audit time; no proof. Effort S. The normalisation has to be checked (§4).
2. **A non-schematic GL₂ side for `Hyp.JLClassical` / `Hyp.LambdaJL` (long term).** HACS's proved Hecke
   operators on `H^n(Γ₀(N); V)` (`heckeClassical_holds`, `levelN_shapiro`, `nebCorr`, `levelCorr_eq_res_cor`) are
   the only Lean source we know of for genuine GL₂ Hecke modules at level Γ₀(N). With `DiamondImEichlerShimura` as
   the cited bridge, `GL2CuspData` could be instantiated on parabolic H¹ instead of left as arbitrary data. The F6
   caveat would then shrink from "any S" to "ES + D-new + JL cited". Still missing: parabolic cohomology, the
   D-new part, finite dimension, commutativity without `HeckeCommute`. Effort L; the payoff is in faithfulness, not
   in fewer hypotheses.
3. **Diamond/U_p normalisation for `Hyp.LambdaJL` ← `Conventions/NebentypusDictionary.lean` (`transported_eq`)
   and `Nebentypus.lean` (`diamond_eigen`).** These are proved statements, explicit on the GL₂ side, of the same kind
   of inverse that caused our X1 erratum (cohomological `T_p` = DS's `⟨p⟩⁻¹T_p`; `V(χ)` ↔ `S_k(N, χ̄)`). Reading
   them now costs nothing. Porting them is the natural test for any future `genGL (.dia d)` instance. Effort S/M.
4. **Infrastructure for `Hyp.SerreCoh` (partial).** `PermRes`/`cohIso`, `permHom` and `resP`/`barIso` are
   general-group lemmas, and the tree-SES pattern `k[E] → k[V] → k` in `Rep k Γ` is a template. But HACS has no
   general tree or graph-of-groups lemma, it works in cohomology rather than homology, and `PermRes` needs free
   actions. The real work (finite non-free stabilisers with invertible orders, a tree acting with them, homology)
   remains. Effort L; the gain is moderate.

## 4. Caveats

- **Version drift 4.33 → 4.35.** Between `db584cd6` and v4.35 Mathlib (`git diff --stat`):
  `RepresentationTheory/` 43 files, +590/−380 (incl. `Rep/Basic.lean` 75 lines, `GroupCohomology/{LowDegree,
  LongExactSequence,Shapiro}`); `NumberTheory/ModularForms/` ~38 files changed (`Delta.lean` deleted,
  `RamanujanFormula.lean` added); `RingTheory/PowerSeries`, `Padics`, `Algebra/Homology` also touched (256 files
  over these five areas). HACS uses `Rep` (~1084 identifier hits), `groupCohomology` (~550), `ℤ_[` (~1068), so the
  `MP/`, `M4–M6/` stack is the most drift-exposed. The `Literature/` files are small and probably cheap to port
  (estimate, not tested). The vendored FLT needs `backward.isDefEq.respectTransparency.types=false`; whether 4.35
  still needs it is untested.
- **Imports.** 56 HACS files use `import Mathlib` wholesale; our rule (`agents/rules/lean.md`, minimised imports,
  public/private split, module layout) requires minimising every ported file (as our import did for the FLT copies).
  This counts toward every effort estimate above.
- **Normalisations.** (i) Diamonds: our LambdaJL convention is `φ⟨d⟩_GL · ⟨d⟩_B = 1` (classical `⟨d⟩` ↦ seed
  `⟨d⟩⁻¹`). HACS's GL₂-internal dictionary has its own inverse (cohomology with `V(χ)` ↔ forms with `χ̄`; transported
  `T_p = χ(p)·T_p^{cl}`). Any bridge has to compose these explicitly, never assume they agree. (ii) Λ: HACS
  `Iw p = ℤ_p[[T]]`, γ = 1+p ↦ 1+T, `P_k = (1+T) − (1+p)^k` (weight character u ↦ u^k on 1+pℤ_p). Ours:
  `Lam ℤ_[p] G π = lim ℤ_p[Δ_s]` and `P^ad_k = ker([u] ↦ u^{2−k})`. Matching needs (a) a Lean iso
  `lim ℤ_p[Δ_s] ≅ ℤ_p[[T]]`, which neither project has, and (b) the automorphism `[u] ↦ u^{2}[u]^{-1}`. That is
  the inverse of our X1 convention combined with the k vs k−2 shift, and is consistent with Hsieh's ι-normalisation
  issue recorded in `mathematics/bib/s04.bib` l. 6. I have **not** verified which twist Hida ENS uses internally
  beyond the shape quoted in HACS. (iii) U_p: HACS has no ordinary projector. At p ∣ N its "U_p" is the dump
  operator `[Γ₀(N) diag(1,N) Γ₀(N)]`, the adjoint `W_N U_N W_N^{-1}` of the classical one
  (`Literature/SturmCuspPrime.lean:26`, `FullRank.lean`). Ours (`UpV`, `Brandt/UpCoeff.lean`) is a definite-side
  operator. Neither is identified with the other. (iv) Level/weight: HACS's proved Hecke theory is for SL₂(ℤ) and
  Γ₀(N) (needs 6 ∈ R^× in the model route; the tree route works for every R). There is nothing at Γ₁(N) or Γ₁(Np^r),
  which is where all our ordinary towers live.
- **Literature structures re-encode, they do not discharge.** HidaEns31/32, HidaInvent31/47/66, EmertonThm,
  DiamondIm*, Mazur97, MazurEisLocal are `Prop`-structures over interface data, and HACS's own docstring says none
  of HidaControl/EmertonEis is used by a theorem yet. Adopting one swaps our hypothesis for theirs: it gains a
  checked citation and guard discipline, and leaves the logical status unchanged.
- **Uncertainty.** "None found" means none found by grep for the relevant terms plus reading the T1–T6 scan and the
  `Literature/` files. A lemma hidden in a generically named file (`Cone/`, `Model/`) could have been missed. Effort
  ratings are estimates without any build. The Mathlib-overlap claims are limited to file existence and diff size.
- **Scanner corrections.** Minor only: `Literature/Hida.lean` `Iw` is at l. 16 (scan said "~14"). The two scanners
  disagree on textual `native_decide` hits (~125 vs 14); both agree there are zero real uses, which I confirmed. The
  scan's "Γ₀(N) only through Shapiro" is right, but `Γ0Q N` (`M4/LevelN.lean:571`) is for general N via Mathlib's
  `Gamma0`; the explicit coset combinatorics in `Cosets/` are for `N = p^ν`. Every other file:line I spot-checked
  matched.
