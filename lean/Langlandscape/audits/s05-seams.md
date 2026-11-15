<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# S05 seam check (S05-X1), 2026-11-15

Checked on `wip-implementation` after the X1 merges. Signatures are quoted verbatim from the tree
(`lean/Langlandscape/Langlandscape/<file>:<line>`); docstrings elided. Variable blocks are given where they matter.

## `if:s06-lemD`: state 1 (merged, no stub, no SORRIES row, L6F not needed)

Namespace `Langlandscape.CommAlg`; `variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]` (Gorenstein.lean:41, NewOld.lean:39).
Inside `namespace NewOldData` of NewOld.lean (127): `variable [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (D : NewOldData A S)` (129).

`CommAlg/Gorenstein.lean:65` (docstring above, `variable (A S) in` at 60):
```lean
structure NewOldData where
  /-- the new kernel `𝔞` (`S/𝔞` is the new quotient) -/
  𝔞 : Ideal S
  /-- the old kernel `𝔟` -/
  𝔟 : Ideal S
  /-- `S` is free over `A` -/
  free : Module.Free A S
  /-- `S` is finite over `A` -/
  finite : Module.Finite A S
  /-- `S/𝔞` is `A`-torsion-free -/
  tf_a : Module.IsTorsionFree A (S ⧸ 𝔞)
  /-- `S/𝔟` is `A`-torsion-free -/
  tf_b : Module.IsTorsionFree A (S ⧸ 𝔟)
  /-- `𝔞 ∩ 𝔟 = 0` -/
  inf_eq_bot : 𝔞 ⊓ 𝔟 = ⊥
  /-- field-free form of `S_K = (S/𝔞)_K × (S/𝔟)_K` -/
  split : ∃ c : A, c ≠ 0 ∧ algebraMap A S c ∈ 𝔞 ⊔ 𝔟
```

`CommAlg/Gorenstein.lean:126`:
```lean
theorem NewOldData.split_iff [IsDomain A] (𝔞 𝔟 : Ideal S) :
    (∃ c : A, c ≠ 0 ∧ algebraMap A S c ∈ 𝔞 ⊔ 𝔟) ↔
      (𝔞 ⊔ 𝔟).map (Algebra.TensorProduct.includeRight : S →ₐ[A] FractionRing A ⊗[A] S) = ⊤ := by
```

`CommAlg/NewOld.lean:132, 137` (a, b):
```lean
theorem ann_a : ann D.𝔞 = D.𝔟 := by
```
```lean
theorem ann_b : ann D.𝔟 = D.𝔞 := by
```

`CommAlg/NewOld.lean:145-156` (bEquivDualQuot, _apply, _smul):
```lean
noncomputable def bEquivDualQuot {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) :
    D.𝔟 ≃ₗ[A] Module.Dual A (S ⧸ D.𝔞) :=
  LinearEquiv.ofBijective (dualQuot ℓ D.𝔞 D.𝔟 D.ann_a.ge) (dualQuot_bijective hℓ D.ann_a)

/-- `lem:s06-D` (`s06-D`)(b): `bEquivDualQuot hℓ β (s mod 𝔞) = ℓ (β s)`. -/
theorem bEquivDualQuot_apply {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (b : D.𝔟) (s : S) :
    D.bEquivDualQuot hℓ b (Ideal.Quotient.mk D.𝔞 s) = ℓ ((b : S) * s) := rfl

/-- `lem:s06-D` (`s06-D`)(b): `S`-equivariance of `bEquivDualQuot`: `s • β ↦ ℓ(β ·) ∘ (s ·)`. -/
theorem bEquivDualQuot_smul {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (s : S) (b : D.𝔟) :
    D.bEquivDualQuot hℓ (s • b) =
      D.bEquivDualQuot hℓ b ∘ₗ LinearMap.mulLeft A (Ideal.Quotient.mk D.𝔞 s) := by
```

`CommAlg/NewOld.lean:164-175` (aEquivDualQuot, _apply, _smul):
```lean
noncomputable def aEquivDualQuot {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) :
    D.𝔞 ≃ₗ[A] Module.Dual A (S ⧸ D.𝔟) :=
  LinearEquiv.ofBijective (dualQuot ℓ D.𝔟 D.𝔞 D.ann_b.ge) (dualQuot_bijective hℓ D.ann_b)

/-- `lem:s06-D` (`s06-D`)(b): `aEquivDualQuot hℓ α (s mod 𝔟) = ℓ (α s)`. -/
theorem aEquivDualQuot_apply {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (a : D.𝔞) (s : S) :
    D.aEquivDualQuot hℓ a (Ideal.Quotient.mk D.𝔟 s) = ℓ ((a : S) * s) := rfl

/-- `lem:s06-D` (`s06-D`)(b): `S`-equivariance of `aEquivDualQuot`. -/
theorem aEquivDualQuot_smul {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ) (s : S) (a : D.𝔞) :
    D.aEquivDualQuot hℓ (s • a) =
      D.aEquivDualQuot hℓ a ∘ₗ LinearMap.mulLeft A (Ideal.Quotient.mk D.𝔟 s) := by
```

Part (c) names (`isComplemented_b`, `free_b`, `quotAEquivDualB`, `free_quot_a`):
- CommAlg/NewOld.lean:189:theorem isComplemented_b (hb : Module.Free A (S ⧸ D.𝔟)) :
- CommAlg/NewOld.lean:228:theorem free_b (hb : Module.Free A (S ⧸ D.𝔟)) : Module.Free A D.𝔟 := by
- CommAlg/NewOld.lean:252:noncomputable def quotAEquivDualB {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ)
- CommAlg/NewOld.lean:273:theorem quotAEquivDualB_mk {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ)
- CommAlg/NewOld.lean:278:theorem free_quot_a {ℓ : Module.Dual A S} (hℓ : IsGorensteinWith A S ℓ)

Consumers already in the tree: `CommAlg/SubQuot.lean` (S05-L6, uses `split_iff`, `ann_a`), `Comparison/XIso.lean` (S05-L8a, uses `bEquivDualQuot`, `_smul`).

## `if:s04-ekills`: merged

Namespace `Langlandscape.Ordinary`.

`Ordinary/EKills.lean:139-143` (`Ordinary.deg`, reused; no `Comparison.deg`):
```lean
variable (X R : Type*) [CommRing R]

/-- The degree `deg : R[X] → R`, the sum of the coefficients (`lem:s04-ekills`(a), `s04-ekills`).
Stage 05 bridges the Brandt degree to this definition. -/
def deg : (X →₀ R) →ₗ[R] R := Finsupp.lsum R (fun _ : X => (LinearMap.id : R →ₗ[R] R))
```

`Ordinary/EKills.lean:206-208` (`ordPart_ker_deg`):
```lean
theorem ordPart_ker_deg (hUp : (deg X R).comp Up = p • deg X R)
    (hdecUp : HasOrdDecomp p Up) (hdecR : HasOrdDecomp p (LinearMap.lsmul R R p)) :
    Submodule.map (LinearMap.ker (deg X R)).subtype
      (ordPart (R := R) (M := ↥(LinearMap.ker (deg X R))) (UpKer Up p hUp)) = ordPart Up :=
```

`Ordinary/Tower.lean:136` (variable block of `ekillsA_tower`) and `:151`:
```lean
variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}
```
```lean
theorem ekillsA_tower (hdec : Hyp.PadicOrdDecomp p) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Submodule.map (LinearMap.ker (deg (Xs d M p s hN) ℤ_[p])).subtype
        (ordPart (R := ℤ_[p]) (M := ↥(LinearMap.ker (deg (Xs d M p s hN) ℤ_[p])))
          (UpKer (UpHom d M p s hN hp hM hpM hs ℤ_[p]) (p : ℤ_[p]) (deg_comp_UpHom ℤ_[p] hM hpM hs))) =
      ordPart (UpHom d M p s hN hp hM hpM hs ℤ_[p]) :=
  ordPart_ker_deg _ _ (deg_comp_UpHom ℤ_[p] hM hpM hs)
```

`Ordinary/Tower.lean:162` (`ekillsA_tower_zmod`):
```lean
theorem ekillsA_tower_zmod (m : ℕ) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Submodule.map (LinearMap.ker (deg (Xs d M p s hN) (ZMod (p ^ m)))).subtype
        (ordPart (R := ZMod (p ^ m)) (M := ↥(LinearMap.ker (deg (Xs d M p s hN) (ZMod (p ^ m)))))
          (UpKer (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))) ((p : ℕ) : ZMod (p ^ m))
            (deg_comp_UpHom (ZMod (p ^ m)) hM hpM hs))) =
      ordPart (UpHom d M p s hN hp hM hpM hs (ZMod (p ^ m))) := by
```

`Ordinary/TowerUncond.lean:161` (variable block) and `:165` (`ekillsA_tower_uncond`, the form L7 uses):
```lean
variable {d : DefiniteData} {M p s : ℕ} [Fact p.Prime] {hN : (M * p ^ s).Coprime d.D} {hp : ¬ p ∣ d.D}
```
```lean
theorem ekillsA_tower_uncond (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) :
    Submodule.map (LinearMap.ker (deg (Xs d M p s hN) ℤ_[p])).subtype
        (ordPart (R := ℤ_[p]) (M := ↥(LinearMap.ker (deg (Xs d M p s hN) ℤ_[p])))
          (UpKer (UpHom d M p s hN hp hM hpM hs ℤ_[p]) (p : ℤ_[p]) (deg_comp_UpHom ℤ_[p] hM hpM hs))) =
      ordPart (UpHom d M p s hN hp hM hpM hs ℤ_[p]) :=
```

## `if:s03-graph`: merged

Namespace `Langlandscape.Graph`.

`Graph/Weighted.lean:27` (`Graph.WGraph`; fields V E src tgt w hw):
```lean
structure WGraph where
  /-- vertices -/
  V : Type
  /-- edges -/
  E : Type
  /-- source of an edge -/
  src : E → V
  /-- target of an edge -/
  tgt : E → V
  /-- weight of an edge -/
  w : E → ℕ
  /-- weights are positive -/
  hw : ∀ e, 0 < w e
```

`Graph/Weighted.lean:43` (variable) and `:59` (`Graph.WGraph.X`; `boundary` at `:46`):
```lean
variable (G : WGraph) (R : Type*) [CommRing R]
```
```lean
noncomputable def boundary : (G.E →₀ R) →ₗ[R] (G.V →₀ R) :=
  Finsupp.linearCombination R fun e => Finsupp.single (G.tgt e) (1 : R) - Finsupp.single (G.src e) 1
```
```lean
noncomputable def X : Submodule ℤ (G.E →₀ ℤ) := LinearMap.ker (boundary G ℤ)
```

## `check_wp` docstring regex

`lean/Langlandscape/tools/check_wp.sh:87`: `ok = re.search(r's[0-9][0-9]-', doc) is not None` (generalised `sNN-` regex present).

## Not found / stubs needed

None. L6 (`CommAlg/SubQuot.lean`) and L8a (`Comparison/XIso.lean`) are merged (module form, X1 integration commit); their acceptance is the int1 round.
