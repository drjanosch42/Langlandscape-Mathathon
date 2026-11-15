<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# S06-L8a notes: Defect.Setting, the 9 stage-06 hypotheses, signatures for L8b/L8c/L9a/L9b/L10b

Branch `impl/s06-l8a`. Nothing was built locally (brief rule 3). Every Mathlib name used was grepped in the frozen tree
(`/home/janosch/data/mathlib4_v4350/Mathlib`). Binding inputs: `stage-06.md` §0, `stage-06-launch.md` A2–A5, §3, §4, and the
coordinator's amendments (chapter audit R1: `𝒪 = 𝒪̃_P` is the normalisation of `I_F/P`, so `P` is local but **not surjective**;
R2: (H0) and the newform condition must appear explicitly).

## 0. Design decisions (deviations from §0 rev. 2, all recorded)
1. `[Algebra I 𝒪]` is a parameter; `Setting.P := algebraMap I 𝒪` (abbrev); launch A4.1.
2. **`P_surj` was dropped.** It is replaced by the structural *field* `P_local : IsLocalHom (algebraMap I 𝒪)`. It is a field,
   not an instance parameter of `Setting`, because then (a) `withPoint` carries the locality of `P′` as data, and (b) no
   theorem needs an extra `[IsLocalHom (algebraMap I 𝒪)]` binder. `Setting.isLocalHom_P : IsLocalHom D.P := D.P_local`. Use
   `haveI := D.isLocalHom_P` before `CommAlg.squeeze`.
3. `lamΛ' : (T ⧸ 𝔞Λ) →ₐ[Λ] I` (A4.2). `lam' : D.R ⧸ D.𝔞 →ₐ[I] I := (AlgHom.liftEquiv Λ I (T ⧸ 𝔞Λ) I lamΛ').comp
   quotient_baseChange.toAlgHom`, `lam := lam'.comp (Ideal.Quotient.mkₐ I D.𝔞)`, so
   `ThmE.lam (D.newOld h) D.lam' = D.lam` should hold by `rfl`.
4. Fixed-weight data at `P` (in `Setting.lean`): `Rk := 𝒪 ⊗[I] D.R` (abbrev), `𝔞k`, `𝔟k` (`map includeRight`),
   `lam'k : D.Rk ⧸ D.𝔞k →ₐ[𝒪] 𝒪` (through `tensorQuotientEquiv (R := I) 𝒪 D.R 𝒪 D.𝔞`), `lamk := lam'k.comp mkₐ`,
   `cqk := D.𝔟k.map D.lamk`. As in point 3, `ThmE.lam (D.newOldAt h0 h) D.lam'k = D.lamk` should hold by `rfl`.
5. `withPoint 𝒪' hP' t'` copies `𝔞Λ, 𝔟Λ, lamΛ', Iq, ρ`; `withPoint_cq`, `withPoint_tq` are `rfl`.
6. Guards (R2): `Defect.H0 p q M` (decidable arithmetic, `hyp:s06-H` (H0)) and `Setting.H0minus D p q := ¬ p ∣ q+1 ∨ D.tq = ⊤`
   ("`ρ̄` ramified at `q`" ⟺ `𝔱_q = I_F` under unipotence). `HidaControlGL2`, `KimOta` and `KimOtaRT` take `(p q M : ℕ)` and are
   *guarded implications* `H0 p q M → …` (and `KimOta` also `H0minus p q → …`). The consumer has to supply the guards
   explicitly. "f = F_P is a q-new newform of level N, weight k" is not representable on abstract data. It is reflected in
   (i) `lamΛ'` living on the `q`-new quotient and (ii) the clause `η(R_k ⧸ 𝔞_k, λ′_f) ≠ 0` of `KimOta`, and is stated in the
   docstrings.
7. `(ϖ^t)` is written uniformiser-free as `IsLocalRing.maximalIdeal 𝒪 ^ D.t` (equal in a DVR). `TamSpec` includes
   `𝔪^t ≠ ⊥`, which gives `P h ≠ 0` for the squeeze without a DVR assumption.
8. `OldDecomp` and `HidaControlGL2` are plain conjunctions (A4.3, A4.4). `Setting.newOld` is in `Hyp/OldDecomp.lean`;
   `Setting.newOldAt` (needs `h0`) is in `Hyp/HidaControlGL2.lean`. Both are in namespace `Langlandscape.Defect.Setting`,
   with `rfl` simp lemmas for `𝔞`/`𝔟`. They cannot live in `Setting.lean`, because that would be an import cycle.
9. `FreeRankTwo` is the *output* of inputs (1)–(3) and proof steps 1–3 of `prop:s06-galois`: there is
   `ρM : G →* GL (Fin 2) (I ⧸ D.cq)`, trivial on `Iq`, with `tr ρM g = mk (tr ρ g)`. Steps 4–5 are left to L8b.
10. `HsiehGorFull D := IsGorenstein I D.R` (the §0 table; the chapter derives it from (Gor_𝐓) over Λ by base change).
    `HsiehGor` is byte-identical to §0 (A3).
11. Diamond normalisation: the launch-note §3 sentence is in the `HidaControlGL2` docstring verbatim. I added a *reading
    note*: Hi86b (3.1), p. 248, says `z` acts on weight `k` by `z^k · f|σ_z`, `σ_z ≡ diag(z⁻¹, z)`, which is `= z² T(z,z)`
    (p. 249). So Hida's `[z]` acts by `z^k` on trivial-character weight-`k` forms, while ours acts by `u^{k-2}`. The two
    Λ-structures differ by the twist `[u] ↦ u²[u]` (no inversion), and **Hida's `P_k` matches our `P_k` (same `k`)**, not
    `P_{k+2}`. This needs a second reader. HACS's raw `Pk p k` would need this twist to be used as ours.

All 10 files are `module`s (`@[expose] public section`). Imports are `Mathlib.*`, `Langlandscape.CommAlg.Gorenstein` and
`Langlandscape.Defect.Setting` only, so none of them depends on MODH (`LambdaJL` is not imported by L8a files).

## 1. Root aggregator lines (stage master)
```
import Langlandscape.Defect.Setting
import Langlandscape.Hyp.FreeRankTwo
import Langlandscape.Hyp.HidaControlGL2
import Langlandscape.Hyp.HsiehGor
import Langlandscape.Hyp.HsiehGorFull
import Langlandscape.Hyp.KimOta
import Langlandscape.Hyp.KimOtaRT
import Langlandscape.Hyp.OldDecomp
import Langlandscape.Hyp.ResidualBurnside
import Langlandscape.Hyp.TamSpec
```

## 2. HYPOTHESES.md rows (final text; replaces X1's placeholders)
Common binders: `{Λ I T 𝒪 G}` with the `Setting` instances, `D : Defect.Setting Λ I T 𝒪 G`.

| Lean name | file | statement label | source | used by (decls) | instances | discharge plan | status |
|---|---|---|---|---|---|---|---|
| `Langlandscape.Hyp.HsiehGor A TB M` | `Langlandscape/Hyp/HsiehGor.lean` | `thm:s04-Gor` (`if:s04-Mord`): `IsGorenstein A TB ∧ Nonempty (M ≃ₗ[TB] TB)`; (Gor_{R′}) of `thm:s06-defect` step (1) | cited: Hsieh 2017 Thm 4.5 + proof, p. 34; Rem. 7.8, p. 71; under (CR,{q}) (`rem:s06-CR`) | `Defect.Setting.gor_new` → `Defect.defect_formula` | L10b: `TB = A`, `M = A` (`isGorenstein_self`): satisfiable, not vacuous | cited, post-hackathon | open |
| `Langlandscape.Hyp.OldDecomp D` | `Langlandscape/Hyp/OldDecomp.lean` | `lem:s06-decomp`(a)–(c): `NewOldData` fields for `D.𝔞`, `D.𝔟` + `Module.Free I (D.R ⧸ D.𝔟)` | Hi86b Thm 3.1, Cor. 3.2, p. 250; Hensel; Carayol Th. (A) / DDT Thm 3.1 (chapter M2); shares Hi86b with HACS `HidaEns31/32` (row note) | `Defect.Setting.newOld`, `Defect.Setting.free_quot_b`, `Defect.defect_formula` | L10b toy Setting from L10a (`Λ = I = ℤ_[p]`, `T = toy`), transported by `TensorProduct.lid`; else reason | maths (proved modulo cited, M2), not formalized | open |
| `Langlandscape.Hyp.HsiehGorFull D` | `Langlandscape/Hyp/HsiehGorFull.lean` | (Gor_R) of `thm:s06-defect` step (1): `IsGorenstein I D.R` | cited: Hsieh §3.3 p. 17–18, §7.2 p. 68; Wiles 1995 Cor. 2 p. 482; MW86 §9 Prop. 2; Helm Cor. 8.11 p. 31 (shared with `Hyp.X.iso`) | `Defect.defect_formula`, `Defect.cor_fixed`, `Defect.cor_allweights` (via `IsGorenstein.baseChange`) | L10b toy (L10a `isGorenstein` + `IsGorenstein.baseChange`) | cited, post-hackathon | open |
| `Langlandscape.Hyp.FreeRankTwo D` | `Langlandscape/Hyp/FreeRankTwo.lean` | `prop:s06-galois` inputs (1)–(3), steps 1–3: `∃ ρM : G →* GL₂(I ⧸ cq), ρM|_{Iq} = 1 ∧ tr ρM = tr ρ mod cq` | cited: Hsieh §7.2 Lemma 7.4 p. 68; Wiles 1995 Cor. 1, 2 p. 482; DDT Thm 3.1(a) p. 85, Thm 2.3 p. 52 | `Defect.galois` | reason: needs a Galois representation with Chebotarev data; a trivial-`G` toy makes it vacuous (forbidden by launch §4) | cited, post-hackathon | open |
| `Langlandscape.Hyp.ResidualBurnside D` | `Langlandscape/Hyp/ResidualBurnside.lean` | `lem:s06-burnside` / `prop:s06-galois` step 5: `Function.Surjective (MonoidAlgebra.lift I (Matrix (Fin 2) (Fin 2) I) G ((Units.coeHom _).comp D.ρ))` | tex proof of `prop:s06-galois` ((H2) + Burnside + Nakayama) | `Defect.galois` | discharged by L6c `Hyp.residualBurnside_of_absIrred` (from `CommAlg.surjective_groupAlgebra_of_absIrred`) | L6c | proved modulo `IsIrreducible` of the residual rep once L6c is green; open until then |
| `Langlandscape.Hyp.TamSpec D` | `Langlandscape/Hyp/TamSpec.lean` | `lem:s06-tam`(a)–(c): unipotent on `Iq`; `tq` generated by entries of `ρ τ - 1`; `tq.map P = 𝔪^t`; `𝔪^t ≠ ⊥` | KO Def. 2.12 p. 6 = PW Def. 3.3 p. 9; Carayol / DDT; lattice uniqueness under (H2) | `Defect.defect_formula` (step 5), `Defect.cor_allweights` (at `P′`) | L10b toy: `G = Multiplicative ℤ`, `ρ n = !![1, n·p^t; 0, 1]`, `Iq = ⊤`, `𝒪 = I = ℤ_[p]`, `t > 0` (not the vacuous `t = 0`, `tq = ⊤` shape, which contradicts nothing but is uninformative) | maths (proved modulo cited, M2) | open |
| `Langlandscape.Hyp.HidaControlGL2 D p q M` | `Langlandscape/Hyp/HidaControlGL2.lean` | `lem:s06-control` + `lem:s06-pstab` + (P2) + `lem:s06-decomp` at weight `k`: `H0 p q M →` `NewOldData` fields for `D.𝔞k`, `D.𝔟k` in `𝒪 ⊗[I] D.R` + `Module.Free 𝒪 (D.Rk ⧸ D.𝔟k)` | cited: Hi86b Thm 3.1, Cor. 3.2 (3.3 b), p. 250 (same source and page as HACS `HidaEns32`: cross-reference, not a port; normalisation in the docstring) | `Defect.Setting.newOldAt`, `Defect.cor_fixed`, `Defect.cor_allweights` | optional toy with `𝒪 = I`, `P = id`, `p = 5, q = 2, M = 1` (guard true); else reason | cited, post-hackathon | open |
| `Langlandscape.Hyp.KimOta D p q M` | `Langlandscape/Hyp/KimOta.lean` | `thm:s06-KO` at `P` (`N⁻ = q`, `N⁺ = M`): `H0 → H0minus → η(lamk) = 𝔪^t · η(lam'k) ∧ η(lam'k) ≠ ⊥` | cited: KO Thm 1.1 p. 1, Def. 2.11 p. 6; PW Thm 6.8 p. 21 (`k = 2`) | `Defect.cor_fixed` → `Defect.defect_formula` (H0⁻ branch) | reason: KO Thm 1.1 needs GL₂ Galois-deformation data | cited, post-hackathon | open |
| `Langlandscape.Hyp.KimOtaRT D p q M` | `Langlandscape/Hyp/KimOtaRT.lean` | `prop:s06-levM` output: `H0 → D.cqk ≤ 𝔪^t` (**inclusion only**) | cited: KO Thm 3.14 p. 12; second reader M6: CONFIRMED for `M = 1`, `M > 1` per D1 (R1–R5) | `Defect.defect_formula` (Lev_M branch) | reason as `KimOta` | cited, post-hackathon | open |

Row update: `Langlandscape.Hyp.LambdaJL` "used by" → `Defect.Setting.gor_new`, `Defect.defect_formula`.
Row note: `HidaControlGL2` ≠ stage-04 `Hyp.HidaControl` (definite side, mod `p^s`). No name collisions (grep of `Hyp/`).

## 3. Signatures for the stacked WPs (against this draft)
Binders V := `{Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I] [IsLocalRing I] [Algebra Λ I]
[CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [Algebra I 𝒪] [Group G] (D : Defect.Setting Λ I T 𝒪 G)`.
Namespace `Langlandscape.Defect`. Names `Dq Mq p` per launch A2 (`D` is the Setting; `q = Dq`, `M = Mq`).

### L8c — `Defect/Gorenstein.lean`
```lean
theorem Setting.gor_new {TB M : Type*} [CommRing TB] [Algebra Λ TB] [AddCommGroup M] [Module TB M]
    (Dq Mq p : ℕ) (genGL : Hyp.LambdaJLGen → T) (genB : Hyp.LambdaJLGen → TB)
    (hJL : Hyp.LambdaJL Dq Mq p Λ T TB genGL genB D.𝔞Λ) (hGor' : Hyp.HsiehGor Λ TB M) :
    CommAlg.IsGorenstein I (D.R ⧸ D.𝔞)
```
Route: `hJL` gives a surjection `φ` with `RingHom.ker φ.toRingHom = D.𝔞Λ`, so `T ⧸ 𝔞Λ ≃ₐ[Λ] TB`
(`Ideal.quotientKerAlgEquivOfSurjective` + `Ideal.quotEquivOfEq`). Then `IsGorenstein.of_algEquiv` gives
`IsGorenstein Λ (T ⧸ 𝔞Λ)`, `IsGorenstein.baseChange I` gives `IsGorenstein I (I ⊗[Λ] (T ⧸ 𝔞Λ))`, and `of_algEquiv` with
`D.quotient_baseChange.symm` finishes. Imports `Hyp.LambdaJL` (module after MODH) and `CommAlg.BaseChange`.

### L8b — `Defect/Galois.lean`
```lean
theorem galois (hfr : Hyp.FreeRankTwo D) (hbur : Hyp.ResidualBurnside D) : D.tq ≤ D.cq
```
Route: if `D.cq = ⊤`, trivial. Otherwise `A := I ⧸ D.cq` is local (quotient of a local ring, `cq ≠ ⊤`).
`ρA := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk D.cq)).comp D.ρ`. Surjectivity over `A` follows from `hbur`
composed with the entrywise surjection, `tr ρA (g σ) = tr ρA g` follows from `hfr`, and `CommAlg.eq_one_of_trace_mul_eq`
gives `ρA σ = 1`, i.e. every entry of `ρ σ - 1` is in `cq`; then `Ideal.span_le`. (Check the name of the GL map by grep
before use.)

### L9b part 1 — `Defect/Fixed.lean` (new file, imported by Main: `cor_fixed` is used by `defect_formula`, so it cannot live
in `Corollaries.lean` without an import cycle)
```lean
theorem Setting.lamk_eq_liftEquiv :
    D.lamk = AlgHom.liftEquiv I 𝒪 D.R 𝒪 ((Algebra.ofId I 𝒪).comp D.lam)
theorem Setting.map_cq : D.cq.map D.P = D.cqk
theorem cor_fixed [IsDiscreteValuationRing 𝒪] {p q M : ℕ} (h0 : H0 p q M) (h0m : D.H0minus p q)
    (hGor : Hyp.HsiehGorFull D) (hctl : Hyp.HidaControlGL2 D p q M) (hKO : Hyp.KimOta D p q M) :
    D.cqk = IsLocalRing.maximalIdeal 𝒪 ^ D.t
```
Route for `cor_fixed`: `hS : IsGorenstein 𝒪 D.Rk := IsGorenstein.baseChange 𝒪 hGor`, then
`ThmE.eta_eq_c_mul_of_dvr (D.newOldAt h0 hctl) hS D.lam'k`. Its LHS is `congruenceIdeal D.lamk` by `rfl`, and its first
factor is `D.cqk` by `rfl`. Compare with `hKO h0 h0m` and cancel `η(lam'k) ≠ ⊥` (ideals of a DVR, a Dedekind domain).
`[IsDiscreteValuationRing 𝒪]` is an explicit assumption (audit R1). `map_cq` is formal (`Ideal.map_map`,
`lamk (1 ⊗ₜ x) = P (lam x)`).

### L9a — `Defect/Main.lean`
```lean
theorem defect_formula_of_le (hdec : Hyp.OldDecomp D) (hGor : Hyp.HsiehGorFull D)
    (hGor' : CommAlg.IsGorenstein I (D.R ⧸ D.𝔞))
    (hfr : Hyp.FreeRankTwo D) (hbur : Hyp.ResidualBurnside D) (htam : Hyp.TamSpec D)
    (hle : D.cqk ≤ IsLocalRing.maximalIdeal 𝒪 ^ D.t) :
    ∃ h : I, CommAlg.congruenceIdeal D.lam = Ideal.span {h} * CommAlg.congruenceIdeal D.lam' ∧
      Ideal.span {h} = D.cq ∧ D.cq = D.tq
theorem defect_formula {TB M : Type*} [CommRing TB] [Algebra Λ TB] [AddCommGroup M] [Module TB M]
    [IsDiscreteValuationRing 𝒪]
    (Dq Mq p : ℕ) (genGL : Hyp.LambdaJLGen → T) (genB : Hyp.LambdaJLGen → TB)
    (hJL : Hyp.LambdaJL Dq Mq p Λ T TB genGL genB D.𝔞Λ) (hGor' : Hyp.HsiehGor Λ TB M)
    (hdec : Hyp.OldDecomp D) (hGor : Hyp.HsiehGorFull D)
    (hfr : Hyp.FreeRankTwo D) (hbur : Hyp.ResidualBurnside D) (htam : Hyp.TamSpec D)
    (h0 : H0 p Dq Mq) (hctl : Hyp.HidaControlGL2 D p Dq Mq)
    (h4 : (D.H0minus p Dq ∧ Hyp.KimOta D p Dq Mq) ∨ Hyp.KimOtaRT D p Dq Mq) :
    ∃ h : I, CommAlg.congruenceIdeal D.lam = Ideal.span {h} * CommAlg.congruenceIdeal D.lam' ∧
      Ideal.span {h} = D.cq ∧ D.cq = D.tq
```
(Gor_R) (`hGor`) and (Gor_{R′}) (`hGor'` with `hJL`) are separate arguments (L12 item 3). `KimOtaRT` is the inclusion
only (item 4). The `KimOta` branch gives `hle` through `cor_fixed` (`le_of_eq`); the `KimOtaRT` branch gives it as
`h4 h0`. In the core lemma, step (1) is `ThmE.eta_eq_c_mul_of_isGorenstein (D.newOld hdec) hℓ D.lam' hGor'` (with
`ThmE.lam _ D.lam' = D.lam` by `rfl`), plus principality of `cq` (ThmE (iv) / Lemma S). Step (2) is `galois`. Steps
(3)–(5): `Setting.map_cq` and `hle` give `map P cq ≤ 𝔪^t = map P tq` (TamSpec), and `CommAlg.squeeze` with
`haveI := D.isLocalHom_P`; `P h ≠ 0` comes from `𝔪^t ≠ ⊥`. Optional split: the `KimOtaRT` branch alone needs neither
`[IsDiscreteValuationRing 𝒪]` nor `hctl`; `defect_formula_of_le` exposes that.

### L9b part 2 — `Defect/Corollaries.lean` (imports Main)
```lean
theorem cor_allweights {TB M : Type*} [CommRing TB] [Algebra Λ TB] [AddCommGroup M] [Module TB M]
    [IsDiscreteValuationRing 𝒪] (Dq Mq p : ℕ) (genGL : Hyp.LambdaJLGen → T) (genB : Hyp.LambdaJLGen → TB)
    (hJL : Hyp.LambdaJL Dq Mq p Λ T TB genGL genB D.𝔞Λ) (hGor' : Hyp.HsiehGor Λ TB M)
    (hdec : Hyp.OldDecomp D) (hGor : Hyp.HsiehGorFull D)
    (hfr : Hyp.FreeRankTwo D) (hbur : Hyp.ResidualBurnside D) (htam : Hyp.TamSpec D)
    (h0 : H0 p Dq Mq) (hctl : Hyp.HidaControlGL2 D p Dq Mq)
    (h4 : (D.H0minus p Dq ∧ Hyp.KimOta D p Dq Mq) ∨ Hyp.KimOtaRT D p Dq Mq)
    {𝒪' : Type*} [CommRing 𝒪'] [IsDomain 𝒪'] [IsLocalRing 𝒪'] [Algebra I 𝒪'] [IsDiscreteValuationRing 𝒪']
    (hP' : IsLocalHom (algebraMap I 𝒪')) (t' : ℕ)
    (htam' : Hyp.TamSpec (D.withPoint 𝒪' hP' t')) (hctl' : Hyp.HidaControlGL2 (D.withPoint 𝒪' hP' t') p Dq Mq) :
    (D.withPoint 𝒪' hP' t').cqk = IsLocalRing.maximalIdeal 𝒪' ^ t' ∧
      CommAlg.congruenceIdeal (D.withPoint 𝒪' hP' t').lamk =
        IsLocalRing.maximalIdeal 𝒪' ^ t' * CommAlg.congruenceIdeal (D.withPoint 𝒪' hP' t').lam'k
```
Route: `defect_formula` gives `cq = tq`. Then `map_cq` at `D′ := D.withPoint …` with `withPoint_cq`/`withPoint_tq` and
`htam'` gives `cqk′ = 𝔪′^{t′}`. The second clause is `ThmE.eta_eq_c_mul_of_dvr (D′.newOldAt h0 hctl')`, with (Gor) by
`IsGorenstein.baseChange 𝒪' hGor` (`HsiehGorFull D′ = HsiehGorFull D` by `rfl`). `ord_ϖ` of both sides is the tex
formula; no `R = 𝐓` theorem is used at `P′`.

### L10b — `LanglandscapeTests/S06/Hyp.lean`
- `HsiehGor`: `example : Hyp.HsiehGor ℤ_[p] ℤ_[p] ℤ_[p] := ⟨isGorenstein_self, ⟨LinearEquiv.refl _ _⟩⟩`.
- Toy `Setting` (`Λ = I = 𝒪 = ℤ_[p]`, `Algebra.id`, `P_local` from the `RingHom.id` instance, `T = toy ϖ` of L10a with
  `𝔞Λ = ker snd`-type coordinate kernels, `lamΛ'` induced by the coordinate that kills `𝔞Λ`, `G = Multiplicative ℤ`,
  `Iq = ⊤`, `ρ n = !![1, n • ϖ^t; 0, 1]`): instances of `HsiehGorFull` (via `TensorProduct.lid` + `of_algEquiv`),
  `OldDecomp` (transport), `TamSpec` (`tq = span {ϖ^t}`, `PadicInt` maximal ideal `= span {p}`).
- `ResidualBurnside`: **not** for the unipotent toy (the span of `ρ(G)` is upper triangular). Use a separate Setting with
  `G = GL (Fin 2) ℤ_[p]`, `ρ = MonoidHom.id`, or write the reason.
- `FreeRankTwo`, `KimOta`, `KimOtaRT`, `HidaControlGL2`: reason sentences (launch §4). A guard-false instance (`p < 5`)
  would be vacuous and must not be offered as non-vacuity.

## 4. Open risks
- Instance glue in `tensorQuotientEquiv` (its own body needs `backward.isDefEq.respectTransparency false`): the
  `quotient_baseChange` / `lam'k` type ascriptions rely on defeq of `D.R ⧸ D.𝔞` with `(I ⊗[Λ] T) ⧸ 𝔞Λ.map includeRight`
  (delta of `Setting.𝔞`). If elaboration fails, make `𝔞`, `𝔞k` `abbrev`s, or add `set_option … in`.
- (fixed after s06-int2b-1) every `Setting.*` decl now takes `(D : Setting …)` explicitly (`P`, `R` as `(_D : …)`);
  `include D in` gave no usable field-notation parameter (27 errors, all cascading from `D.R`).
- The `rfl` claims (`ThmE.lam (D.newOld h) D.lam' = D.lam`, `withPoint_cq`) are unbuilt.
- `KimOta` is stated as the ideal identity `η = 𝔪^t η′` in place of KO's `ord` identity. The two are equivalent over the
  DVR `𝒪̃_P`, with `η′ ≠ 0` from the newform condition.
