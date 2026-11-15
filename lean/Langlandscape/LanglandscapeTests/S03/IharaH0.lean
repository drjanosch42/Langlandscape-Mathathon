/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Hyp.IharaH0

/-! Shape tests for `Langlandscape.Hyp.IharaH0` and `Langlandscape.Ribet.epsilon` (S03-L11): the hypothesis at level
`Ô^×` with `V = ℤ_[p]`, trivial coefficient data, and the L14 coefficient differential `Ribet.alphaV` (the
V-coefficient option A1, not the trivial-coefficient fallback). For trivial `ρ` the coefficient premises are
discharged (`CoeffData.triv_ρ`), as are factorisation at `p` and admissibility (from `Hyp.RamNrdSurj`); for
`CoeffData.ofLocal` the "`U_p`-action" premise is discharged (`CoeffData.ofLocal_ρ_apply`). -/

set_option autoImplicit false

namespace LanglandscapeTests.S03.IharaH0

open Langlandscape.Quat Langlandscape.Brandt Langlandscape.Tree Langlandscape.Ribet

variable (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)

/-- `thm:s03-iharaH0`(a) (`s03-iharaH0`), shape test: `ε` for `V = ℤ_[p]`, trivial `ρ`, at level `Ô^×` is a
`ℤ_[p]`-linear map `Brandt(Ô^×, ℤ_p)² → V_{U^1_p}`. -/
theorem test_epsilon_shape :
    Nonempty (brandtModule d.Ohat ℤ_[p] ℤ_[p] (CoeffData.triv d q hq d.Ohat ℤ_[p]).ρ ×
        brandtModule d.Ohat ℤ_[p] ℤ_[p] (CoeffData.triv d q hq d.Ohat ℤ_[p]).ρ →ₗ[ℤ_[p]]
      Coinv (CoeffData.triv d q hq d.Ohat ℤ_[p]) p hp) :=
  ⟨epsilon (CoeffData.triv d q hq d.Ohat ℤ_[p]) p hp⟩

/-- (C6) (`s03-conv`), shape test: `[t]` is an endomorphism of `V_{U^1_p}`. -/
theorem test_diamond_shape (t : ℚ_[p]) :
    Nonempty (Coinv (CoeffData.triv d q hq d.Ohat ℤ_[p]) p hp →ₗ[ℤ_[p]]
      Coinv (CoeffData.triv d q hq d.Ohat ℤ_[p]) p hp) :=
  ⟨diamond (CoeffData.triv d q hq d.Ohat ℤ_[p]) p hp t⟩

/-- `thm:s03-iharaH0` (`s03-iharaH0`), test: the trivial coefficient action is trivial on `Ô^×`. -/
theorem triv_rho_apply (u : d.Ohat) : (CoeffData.triv d q hq d.Ohat ℤ_[p]).ρ u = 1 := by
  rw [CoeffData.triv_ρ d q hq d.Ohat ℤ_[p], MonoidHom.one_apply]

/-- `thm:s03-iharaH0` (`s03-iharaH0`), test: the continuity premise holds for trivial `ρ` (take `W = ⊤`). -/
theorem triv_continuous (n : ℕ) : ∃ W : Subgroup (BHat d.a d.b)ˣ, IsOpen (W : Set (BHat d.a d.b)ˣ) ∧
    ∀ u : d.Ohat, (u : (BHat d.a d.b)ˣ) ∈ W → ∀ v : ℤ_[p], ∃ w : ℤ_[p],
      (CoeffData.triv d q hq d.Ohat ℤ_[p]).ρ u v - v = ((p : ℤ_[p]) ^ n) • w := by
  refine ⟨⊤, ?_, fun u _ v => ⟨0, ?_⟩⟩
  · rw [Subgroup.coe_top]
    exact isOpen_univ
  · rw [triv_rho_apply d q hq p u, smul_zero]
    exact sub_self v

/-- `thm:s03-iharaH0`(a), `if:s03-ihara` (`s03-iharaH0`), shape test: `Hyp.IharaH0` at `U = Ô^×`, `V = ℤ_[p]`, trivial
`ρ` gives `ker ε = im α` for the L14 map `alphaV`. All coefficient premises, factorisation at `p` and admissibility
are discharged; only `p ≥ 5`, `p ≠ q`, `Hyp.RamNrdSurj d` and `BG(Ô^×, q)` connected remain. -/
theorem test_IharaH0_ker_eq_range (hram : Langlandscape.Hyp.RamNrdSurj d)
    (h : Langlandscape.Hyp.IharaH0 d q hq d.Ohat (isQLevel_Ohat (hq := hq)) p hp ℤ_[p]
      (CoeffData.triv d q hq d.Ohat ℤ_[p]))
    (h5 : 5 ≤ p) (hpq : p ≠ q) (hconn : BGConnected d q hq d.Ohat (isQLevel_Ohat (hq := hq))) :
    LinearMap.ker (epsilon (CoeffData.triv d q hq d.Ohat ℤ_[p]) p hp) =
      LinearMap.range (alphaV (CoeffData.triv d q hq d.Ohat ℤ_[p]) (isQLevel_Ohat (hq := hq))) :=
  (h h5 hpq (isQAdmissible_Ohat hram)
    ⟨Langlandscape.Local.GL2Zl p, hasFactorAt_GL2Zl_of_invariant isInvariantAt_Ohat le_rfl⟩ hconn
    inferInstance (fun u _ => triv_rho_apply d q hq p u) (triv_continuous d q hq p)
    (fun u _ => triv_rho_apply d q hq p u)).2.2

/-- `thm:s03-iharaH0`(a) (`s03-iharaH0`), shape test: under the same hypotheses `ε` is surjective. -/
theorem test_IharaH0_surj (hram : Langlandscape.Hyp.RamNrdSurj d)
    (h : Langlandscape.Hyp.IharaH0 d q hq d.Ohat (isQLevel_Ohat (hq := hq)) p hp ℤ_[p]
      (CoeffData.triv d q hq d.Ohat ℤ_[p]))
    (h5 : 5 ≤ p) (hpq : p ≠ q) (hconn : BGConnected d q hq d.Ohat (isQLevel_Ohat (hq := hq))) :
    Function.Surjective (epsilon (CoeffData.triv d q hq d.Ohat ℤ_[p]) p hp) :=
  (h h5 hpq (isQAdmissible_Ohat hram)
    ⟨Langlandscape.Local.GL2Zl p, hasFactorAt_GL2Zl_of_invariant isInvariantAt_Ohat le_rfl⟩ hconn
    inferInstance (fun u _ => triv_rho_apply d q hq p u) (triv_continuous d q hq p)
    (fun u _ => triv_rho_apply d q hq p u)).2.1

/-- `thm:s03-iharaH0`(a) (`s03-iharaH0`), shape test with a genuine `p`-adic action `ρ_p : GL₂(ℚ_p) → Aut(V)`
(`CoeffData.ofLocal`): the "`U_p`-action" premise is discharged; `ker ε = im α`. -/
theorem test_IharaH0_ofLocal (hram : Langlandscape.Hyp.RamNrdSurj d) (hpq : p ≠ q)
    (V : Type) [AddCommGroup V] [Module ℤ_[p] V] (ρp : GL (Fin 2) ℚ_[p] →* (V ≃ₗ[ℤ_[p]] V))
    (h : Langlandscape.Hyp.IharaH0 d q hq d.Ohat (isQLevel_Ohat (hq := hq)) p hp V
      (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp))
    (h5 : 5 ≤ p) (hconn : BGConnected d q hq d.Ohat (isQLevel_Ohat (hq := hq))) (hfin : Module.Finite ℤ_[p] V)
    (hcont : ∀ n : ℕ, ∃ W : Subgroup (BHat d.a d.b)ˣ, IsOpen (W : Set (BHat d.a d.b)ˣ) ∧
      ∀ u : d.Ohat, (u : (BHat d.a d.b)ˣ) ∈ W → ∀ v : V, ∃ w : V,
        (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp).ρ u v - v = ((p : ℤ_[p]) ^ n) • w)
    (hneg : ∀ u : d.Ohat, (u : (BHat d.a d.b)ˣ) = -1 → (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp).ρ u = 1) :
    LinearMap.ker (epsilon (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp) p hp) =
      LinearMap.range (alphaV (CoeffData.ofLocal d q hq d.Ohat p hp hpq ρp) (isQLevel_Ohat (hq := hq))) :=
  (h h5 hpq (isQAdmissible_Ohat hram)
    ⟨Langlandscape.Local.GL2Zl p, hasFactorAt_GL2Zl_of_invariant isInvariantAt_Ohat le_rfl⟩ hconn hfin
    (fun u hu => by rw [CoeffData.ofLocal_ρ_apply p hp hpq ρp u, hu, map_one]) hcont hneg).2.2

end LanglandscapeTests.S03.IharaH0
