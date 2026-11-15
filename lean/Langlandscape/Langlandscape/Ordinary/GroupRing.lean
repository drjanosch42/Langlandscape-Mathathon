/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.ZMod.LocalRing

/-!
# Group rings of finite `p`-groups over local rings (S04-L7)

`mathematics/chapters/s04/control.tex`, `prop:s04-freeA` (abstract part); plan row S04-L7 of `plan/implementation/stage-04.md`.

* `isLocalRing_monoidAlgebra_of_isPGroup`: if `R` is a commutative local ring with `p ∈ 𝔪_R` and
  `G` is a finite commutative `p`-group, then `R[G]` is local. Its maximal ideal is the kernel of
  `R[G] → R → R ⧸ 𝔪_R` (augmentation, then reduction).
* `isLocalRing_monoidAlgebra_padicInt`, `isLocalRing_monoidAlgebra_zmod`: the cases `R = ℤ_p` and
  `R = ℤ ⧸ p ^ m` (`0 < m`) for `G` commutative of order `p ^ n`; in particular `G` cyclic of
  order `p ^ n`. The case `n = 0` (trivial `G`) is included. The case `m = 0` is excluded:
  `ZMod (p ^ 0) = ZMod 1` is the zero ring, which is not local.
* `free_of_finite_of_projective`, `free_of_isCompl_of_finite`, `free_of_isCompl`: over a local ring,
  finitely generated projective modules are free, and finitely generated direct summands of free
  modules are free; with the specialisations `free_of_projective_padicInt`,
  `free_of_projective_zmod`, `free_of_isCompl_padicInt`, `free_of_isCompl_zmod`.

Proof of locality: every maximal ideal `𝔐` of `R[G]` lies over `𝔪_R` (`R[G]` is finite over `R`),
so `R[G] ⧸ 𝔐` is a field of characteristic `p`; there `(g - 1) ^ (p ^ k) = g ^ (p ^ k) - 1 = 0`,
hence `g ≡ 1 mod 𝔐` for every `g ∈ G`, and `𝔐` contains the kernel of `R[G] → R ⧸ 𝔪_R`,
which is itself maximal. So that kernel is the unique maximal ideal.

Over a local ring, the theorem that every projective module is free (Kaplansky) is not available in
Mathlib v4.35, so the summand results assume the summand finitely generated (automatic when the
ambient free module is finite).
-/

@[expose] public section

noncomputable section

namespace Langlandscape.Ordinary

open IsLocalRing

/-- `s04-freeA` (`prop:s04-freeA`, step "`R[G]` is local"), auxiliary: in `R[G] ⧸ 𝔐` for a maximal
ideal `𝔐` containing `p`, every group element `g` of `p`-power order maps to `1`. -/
private theorem single_sub_one_mem {R : Type*} [CommRing R] {G : Type*} [CommGroup G]
    {p : ℕ} [hp : Fact p.Prime] (hG : IsPGroup p G) (I : Ideal (MonoidAlgebra R G))
    [hI : I.IsMaximal] (hpI : (p : MonoidAlgebra R G) ∈ I) (g : G) :
    MonoidAlgebra.single g (1 : R) - 1 ∈ I := by
  let : Field (MonoidAlgebra R G ⧸ I) := Ideal.Quotient.field I
  have hp0 : ((p : ℕ) : MonoidAlgebra R G ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  have : CharP (MonoidAlgebra R G ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hp0
  obtain ⟨k, hk⟩ := hG g
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : (Ideal.Quotient.mk I (MonoidAlgebra.single g (1 : R) - 1)) ^ p ^ k = 0 := by
    rw [map_sub, map_one, sub_pow_char_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
      one_pow, ← MonoidAlgebra.one_def, map_one, sub_self]
  exact pow_eq_zero_iff (pow_ne_zero k hp.out.ne_zero) |>.mp h1

/-- `prop:s04-freeA` (s04-freeA, local step, general form): if `R` is a commutative local ring with
`(p : R) ∈ 𝔪_R` (residue characteristic `p`) and `G` is a finite commutative `p`-group, then the
group ring `R[G] = MonoidAlgebra R G` is a local ring. The maximal ideal is the kernel of
`R[G] → R → R ⧸ 𝔪_R`. -/
theorem isLocalRing_monoidAlgebra_of_isPGroup {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [CommGroup G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (hp : (p : R) ∈ maximalIdeal R) : IsLocalRing (MonoidAlgebra R G) := by
  classical
  -- augmentation `R[G] → R` and its reduction `ε : R[G] → R ⧸ 𝔪`
  set aug : MonoidAlgebra R G →+* R := (MonoidAlgebra.lift R R G (1 : G →* R)).toRingHom
    with haug_def
  have haug : ∀ (g : G) (r : R), aug (MonoidAlgebra.single g r) = r := by
    intro g r
    simp [haug_def, MonoidAlgebra.lift_single]
  set ε : MonoidAlgebra R G →+* ResidueField R := (residue R).comp aug with hε_def
  have hεs : Function.Surjective ε := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨MonoidAlgebra.single 1 r, by simp [hε_def, haug]⟩
  have hJ : (RingHom.ker ε).IsMaximal := RingHom.ker_isMaximal_of_surjective ε hεs
  refine IsLocalRing.of_unique_max_ideal ⟨RingHom.ker ε, hJ, fun I hI => ?_⟩
  -- every maximal ideal `I` contains `ker ε`
  have hunder : I.comap (algebraMap R (MonoidAlgebra R G)) = maximalIdeal R := by
    have : (I.comap (algebraMap R (MonoidAlgebra R G))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) I
    exact IsLocalRing.eq_maximalIdeal this
  have hmI : ∀ r ∈ maximalIdeal R, algebraMap R (MonoidAlgebra R G) r ∈ I := by
    intro r hr
    rw [← hunder] at hr
    exact hr
  have hpI : (p : MonoidAlgebra R G) ∈ I := by
    have := hmI _ hp
    rwa [map_natCast] at this
  have hfac : (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk I).comp ((algebraMap R (MonoidAlgebra R G)).comp aug) := by
    refine MonoidAlgebra.ringHom_ext (fun r => ?_) (fun g => ?_)
    · simp [haug, MonoidAlgebra.coe_algebraMap]
    · have h := single_sub_one_mem hG I hpI g
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at h
      simp only [RingHom.coe_comp, Function.comp_apply, haug, map_one]
      rw [h, map_one]
  have hle : RingHom.ker ε ≤ I := by
    intro x hx
    have hx' : aug x ∈ maximalIdeal R := by
      rw [RingHom.mem_ker, hε_def, RingHom.comp_apply, residue_eq_zero_iff] at hx
      exact hx
    rw [← Ideal.Quotient.eq_zero_iff_mem, hfac, RingHom.comp_apply, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmI _ hx'
  exact (hJ.eq_of_le hI.ne_top hle).symm

/-- `prop:s04-freeA` (s04-freeA) over `ℤ_p`: for `G` commutative of order `p ^ n` (in particular `G`
cyclic of order `p ^ n`; `n = 0`, the trivial group, included), `ℤ_p[G]` is a local ring. -/
theorem isLocalRing_monoidAlgebra_padicInt (p : ℕ) [Fact p.Prime] {G : Type*} [CommGroup G]
    {n : ℕ} (hG : Nat.card G = p ^ n) : IsLocalRing (MonoidAlgebra ℤ_[p] G) := by
  have : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  refine isLocalRing_monoidAlgebra_of_isPGroup (IsPGroup.of_card hG) ?_
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.mem_span_singleton_self _

/-- `prop:s04-freeA` (s04-freeA) over `ℤ ⧸ p ^ m` with `0 < m`: for `G` commutative of order `p ^ n`
(in particular cyclic; `n = 0` included), `(ℤ ⧸ p ^ m)[G]` is a local ring. The hypothesis `0 < m`
is necessary: `ZMod (p ^ 0)` is the zero ring. -/
theorem isLocalRing_monoidAlgebra_zmod (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : 0 < m)
    {G : Type*} [CommGroup G] {n : ℕ} (hG : Nat.card G = p ^ n) :
    IsLocalRing (MonoidAlgebra (ZMod (p ^ m)) G) := by
  have : NeZero m := ⟨hm.ne'⟩
  have : Finite G :=
    Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  refine isLocalRing_monoidAlgebra_of_isPGroup (IsPGroup.of_card hG) ?_
  rw [mem_maximalIdeal, mem_nonunits_iff, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hm,
    Nat.coprime_self]
  exact (Fact.out : p.Prime).ne_one

/-- `prop:s04-freeA` (s04-freeA, freeness step): over a local ring, a finitely generated projective
module is free (via `Module.free_of_flat_of_isLocalRing`). -/
theorem free_of_finite_of_projective {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] :
    Module.Free A P :=
  Module.free_of_flat_of_isLocalRing

/-- `prop:s04-freeA` (s04-freeA): over a local ring, a finitely generated direct summand `P`
(`IsCompl P Q`) of a free module `F` of any rank is free. The finiteness of `P` is assumed because
Kaplansky's theorem (projective modules over a local ring are free, any rank) is not in
Mathlib v4.35. -/
theorem free_of_isCompl_of_finite {A : Type*} [CommRing A] [IsLocalRing A]
    {F : Type*} [AddCommGroup F] [Module A F] [Module.Free A F]
    {P Q : Submodule A F} (h : IsCompl P Q) [Module.Finite A P] : Module.Free A P := by
  have : Module.Projective A P :=
    Module.Projective.of_split P.subtype (Submodule.projectionOnto P Q h)
      (Submodule.projectionOnto_comp_subtype h)
  exact free_of_finite_of_projective

/-- `prop:s04-freeA` (s04-freeA): over a local ring, a direct summand `P` (`IsCompl P Q`) of a
finite free module `F` is free. -/
theorem free_of_isCompl {A : Type*} [CommRing A] [IsLocalRing A]
    {F : Type*} [AddCommGroup F] [Module A F] [Module.Free A F] [Module.Finite A F]
    {P Q : Submodule A F} (h : IsCompl P Q) : Module.Free A P := by
  have : Module.Finite A P :=
    Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective h)
  exact free_of_isCompl_of_finite h

/-- `prop:s04-freeA` (s04-freeA) over `ℤ_p[G]`, `G` commutative of order `p ^ n`: finitely generated
projective modules are free. -/
theorem free_of_projective_padicInt (p : ℕ) [Fact p.Prime] {G : Type*} [CommGroup G]
    {n : ℕ} (hG : Nat.card G = p ^ n)
    {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra ℤ_[p] G) P]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) P] [Module.Projective (MonoidAlgebra ℤ_[p] G) P] :
    Module.Free (MonoidAlgebra ℤ_[p] G) P := by
  have := isLocalRing_monoidAlgebra_padicInt p hG
  exact free_of_finite_of_projective

/-- `prop:s04-freeA` (s04-freeA) over `(ℤ ⧸ p ^ m)[G]`, `0 < m`, `G` commutative of order `p ^ n`:
finitely generated projective modules are free. -/
theorem free_of_projective_zmod (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : 0 < m)
    {G : Type*} [CommGroup G] {n : ℕ} (hG : Nat.card G = p ^ n)
    {P : Type*} [AddCommGroup P] [Module (MonoidAlgebra (ZMod (p ^ m)) G) P]
    [Module.Finite (MonoidAlgebra (ZMod (p ^ m)) G) P]
    [Module.Projective (MonoidAlgebra (ZMod (p ^ m)) G) P] :
    Module.Free (MonoidAlgebra (ZMod (p ^ m)) G) P := by
  have := isLocalRing_monoidAlgebra_zmod p hm hG
  exact free_of_finite_of_projective

/-- `prop:s04-freeA` (s04-freeA) over `ℤ_p[G]`, `G` commutative of order `p ^ n`: a direct summand
of a finite free module is free. -/
theorem free_of_isCompl_padicInt (p : ℕ) [Fact p.Prime] {G : Type*} [CommGroup G]
    {n : ℕ} (hG : Nat.card G = p ^ n)
    {F : Type*} [AddCommGroup F] [Module (MonoidAlgebra ℤ_[p] G) F]
    [Module.Free (MonoidAlgebra ℤ_[p] G) F] [Module.Finite (MonoidAlgebra ℤ_[p] G) F]
    {P Q : Submodule (MonoidAlgebra ℤ_[p] G) F} (h : IsCompl P Q) :
    Module.Free (MonoidAlgebra ℤ_[p] G) P := by
  have := isLocalRing_monoidAlgebra_padicInt p hG
  exact free_of_isCompl h

/-- `prop:s04-freeA` (s04-freeA) over `(ℤ ⧸ p ^ m)[G]`, `0 < m`, `G` commutative of order `p ^ n`:
a direct summand of a finite free module is free. -/
theorem free_of_isCompl_zmod (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : 0 < m)
    {G : Type*} [CommGroup G] {n : ℕ} (hG : Nat.card G = p ^ n)
    {F : Type*} [AddCommGroup F] [Module (MonoidAlgebra (ZMod (p ^ m)) G) F]
    [Module.Free (MonoidAlgebra (ZMod (p ^ m)) G) F]
    [Module.Finite (MonoidAlgebra (ZMod (p ^ m)) G) F]
    {P Q : Submodule (MonoidAlgebra (ZMod (p ^ m)) G) F} (h : IsCompl P Q) :
    Module.Free (MonoidAlgebra (ZMod (p ^ m)) G) P := by
  have := isLocalRing_monoidAlgebra_zmod p hm hG
  exact free_of_isCompl h

end Langlandscape.Ordinary
