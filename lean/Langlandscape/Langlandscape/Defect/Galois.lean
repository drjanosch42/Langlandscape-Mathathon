/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Defect.Setting
public import Langlandscape.Hyp.FreeRankTwo
public import Langlandscape.Hyp.ResidualBurnside
public import Langlandscape.CommAlg.TraceForm
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The Galois comparison `𝔱_q(F) ⊆ 𝔠_q(F)` (S06-L8b)

`mathematics/chapters/s06/s06-m4.tex`, `prop:s06-galois`, steps 4–5. With `A = I_F / 𝔠_q(F)`:

* from `Hyp.FreeRankTwo` we get `ρM : G → GL₂(A)`, trivial on `I_q`, with `tr ρM = tr ρ_F mod 𝔠_q(F)`;
* `ρ_A := ρ_F mod 𝔠_q(F)` has `A[G] → M₂(A)` surjective (`Hyp.ResidualBurnside` reduced mod `𝔠_q(F)`);
* for `σ ∈ I_q`: `tr ρ_A(gσ) = tr ρ_A(g)` for all `g`, so `ρ_A(σ) = 1` by `CommAlg.eq_one_of_trace_mul_eq`
  (perfectness of the trace form), i.e. all entries of `ρ_F(σ) - 1` lie in `𝔠_q(F)`.

Hence `Defect.galois : 𝔱_q(F) ≤ 𝔠_q(F)`. Status: *formalized* modulo `Hyp.FreeRankTwo`, `Hyp.ResidualBurnside` (Lean proves steps 4–5). Given `Hyp.ResidualBurnside`, `Hyp.FreeRankTwo` is equivalent to the inclusion `𝔱_q ≤ 𝔠_q`; both directions are proved in Lean (`Defect.galois`, `Defect.freeRankTwo_of_le`, packaged as `Defect.freeRankTwo_iff_le`). The Galois half is therefore not formalized independently: its arithmetic content (that the old-form representation `ρ_M` exists at level `M`, steps 1–3 of `prop:s06-galois`) is the cited hypothesis.
-/

@[expose] public section

set_option autoImplicit false

namespace Langlandscape.Defect

open Matrix

/-- `prop:s06-galois` (`s06-galois`), generic step: surjectivity of `A[G] → M₂(A)` descends along a surjective ring
map `f : A → B` (lift a matrix, write it as an image of a group-algebra element, push the element forward). -/
private theorem surjective_lift_map_s06_galois {A B G : Type*} [CommRing A] [CommRing B] [Monoid G]
    (f : A →+* B) (hf : Function.Surjective f) (ρ : G →* GL (Fin 2) A)
    (hs : Function.Surjective (MonoidAlgebra.lift A (Matrix (Fin 2) (Fin 2) A) G
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) A)).comp ρ))) :
    Function.Surjective (MonoidAlgebra.lift B (Matrix (Fin 2) (Fin 2) B) G
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) B)).comp ((Matrix.GeneralLinearGroup.map f).comp ρ))) := by
  have key : ∀ x : MonoidAlgebra A G, ∃ z : MonoidAlgebra B G,
      MonoidAlgebra.lift B (Matrix (Fin 2) (Fin 2) B) G
        ((Units.coeHom (Matrix (Fin 2) (Fin 2) B)).comp ((Matrix.GeneralLinearGroup.map f).comp ρ)) z =
      (MonoidAlgebra.lift A (Matrix (Fin 2) (Fin 2) A) G
        ((Units.coeHom (Matrix (Fin 2) (Fin 2) A)).comp ρ) x).map f := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      refine ⟨MonoidAlgebra.of B G g, ?_⟩
      rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]
      rfl
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [map_add, map_add, ha, hb]
      ext i j
      simp
    | smul r x hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨f r • a, ?_⟩
      rw [map_smul, map_smul, ha]
      ext i j
      simp
  intro Y
  choose Y' hY' using fun i j => hf (Y i j)
  obtain ⟨x, hx⟩ := hs (Matrix.of Y')
  obtain ⟨z, hz⟩ := key x
  refine ⟨z, ?_⟩
  rw [hz, hx]
  ext i j
  simp [hY']

/-- `prop:s06-galois` (`s06-galois`), steps 4–5 (**Galois comparison**): under `Hyp.FreeRankTwo D`
(`ρM` over `I_F/𝔠_q(F)`, unramified at `q`, same traces as `ρ_F`) and `Hyp.ResidualBurnside D`
(`I_F[G] ↠ M₂(I_F)`), the Tamagawa ideal is contained in the congruence ideal: `𝔱_q(F) ≤ 𝔠_q(F)`.
Proof: if `𝔠_q = ⊤` trivial; else `A = I_F/𝔠_q` is local, `ρ_A(σ) = 1` for `σ ∈ I_q` by
`CommAlg.eq_one_of_trace_mul_eq`. Disclosure: Given `Hyp.ResidualBurnside`, `Hyp.FreeRankTwo` is equivalent to the inclusion `𝔱_q ≤ 𝔠_q`; both directions are proved in Lean (`Defect.galois`, `Defect.freeRankTwo_of_le`, packaged as `Defect.freeRankTwo_iff_le`). The Galois half is therefore not formalized independently: its arithmetic content (that the old-form representation `ρ_M` exists at level `M`, steps 1–3 of `prop:s06-galois`) is the cited hypothesis. -/
theorem galois {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I]
    [IsLocalRing I] [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [Algebra I 𝒪] [Group G] (D : Defect.Setting Λ I T 𝒪 G)
    (hfr : Hyp.FreeRankTwo D) (hbur : Hyp.ResidualBurnside D) : D.tq ≤ D.cq := by
  by_cases hc : D.cq = ⊤
  · rw [hc]; exact le_top
  have : Nontrivial (I ⧸ D.cq) := Ideal.Quotient.nontrivial_iff.mpr hc
  have : IsLocalRing (I ⧸ D.cq) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk D.cq) Ideal.Quotient.mk_surjective
  obtain ⟨ρM, hρM1, hρMtr⟩ := hfr
  set ρA : G →* GL (Fin 2) (I ⧸ D.cq) :=
    (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk D.cq)).comp D.ρ with hρA
  have hsurj := surjective_lift_map_s06_galois (Ideal.Quotient.mk D.cq)
    Ideal.Quotient.mk_surjective D.ρ hbur
  have h1 : ∀ g : G, trace ((ρA g : GL (Fin 2) (I ⧸ D.cq)) : Matrix (Fin 2) (Fin 2) (I ⧸ D.cq)) =
      Ideal.Quotient.mk D.cq (trace ((D.ρ g : GL (Fin 2) I) : Matrix (Fin 2) (Fin 2) I)) :=
    fun g => (AddMonoidHom.map_trace (Ideal.Quotient.mk D.cq) _).symm
  refine Ideal.span_le.mpr ?_
  rintro x ⟨σ, hσ, i, j, rfl⟩
  have htr : ∀ g : G, trace ((ρA (g * σ) : GL (Fin 2) (I ⧸ D.cq)) :
      Matrix (Fin 2) (Fin 2) (I ⧸ D.cq)) =
      trace ((ρA g : GL (Fin 2) (I ⧸ D.cq)) : Matrix (Fin 2) (Fin 2) (I ⧸ D.cq)) := by
    intro g
    rw [h1, ← hρMtr (g * σ), map_mul, hρM1 σ hσ, mul_one, hρMtr g, h1]
  have hσ1 : ρA σ = 1 := CommAlg.eq_one_of_trace_mul_eq ρA hsurj σ htr
  have h2 : Ideal.Quotient.mk D.cq ((D.ρ σ : Matrix (Fin 2) (Fin 2) I) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (I ⧸ D.cq)) i j := by
    have := congrArg (fun u : GL (Fin 2) (I ⧸ D.cq) =>
      (u : Matrix (Fin 2) (Fin 2) (I ⧸ D.cq)) i j) hσ1
    exact this
  refine (Ideal.Quotient.eq_zero_iff_mem).mp ?_
  rw [Matrix.sub_apply, map_sub, h2]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

/-- `prop:s06-galois` (`s06-galois`), converse of `galois` (disclosure, nothing deep): if `𝔱_q ≤ 𝔠_q`, then
`Hyp.FreeRankTwo D` holds, with `ρM := ρ_F mod 𝔠_q(F)` (trivial on `I_q` because all entries of `ρ_F(σ) - 1` lie in
`𝔱_q ≤ 𝔠_q`). So on the abstract data `Hyp.FreeRankTwo D` is equivalent to `𝔱_q ≤ 𝔠_q`. -/
theorem freeRankTwo_of_le {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I]
    [IsLocalRing I] [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [Algebra I 𝒪] [Group G] (D : Defect.Setting Λ I T 𝒪 G) (h : D.tq ≤ D.cq) : Hyp.FreeRankTwo D := by
  refine ⟨(Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk D.cq)).comp D.ρ, ?_, ?_⟩
  · intro σ hσ
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hmem : ((D.ρ σ : Matrix (Fin 2) (Fin 2) I) - 1) i j ∈ D.cq :=
      h (Ideal.subset_span ⟨σ, hσ, i, j, rfl⟩)
    have h0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
    refine h0.trans ?_
    rcases eq_or_ne i j with rfl | hne
    · simp
    · simp [hne]
  · intro g
    exact (AddMonoidHom.map_trace (Ideal.Quotient.mk D.cq) _).symm

/-- `prop:s06-galois` (`s06-galois`), packaging: given `Hyp.ResidualBurnside D`, `Hyp.FreeRankTwo D` is
equivalent to the inclusion `𝔱_q(F) ≤ 𝔠_q(F)` (`Defect.galois` and `Defect.freeRankTwo_of_le`). -/
theorem freeRankTwo_iff_le {Λ I T 𝒪 G : Type*} [CommRing Λ] [CommRing I] [IsDomain I] [IsNoetherianRing I]
    [IsLocalRing I] [Algebra Λ I] [CommRing T] [Algebra Λ T] [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [Algebra I 𝒪] [Group G] (D : Defect.Setting Λ I T 𝒪 G) (hbur : Hyp.ResidualBurnside D) :
    Hyp.FreeRankTwo D ↔ D.tq ≤ D.cq :=
  ⟨fun h => galois D h hbur, freeRankTwo_of_le D⟩

end Langlandscape.Defect
