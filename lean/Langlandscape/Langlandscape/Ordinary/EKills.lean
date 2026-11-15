/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Langlandscape.Ordinary.Projector
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Lemma ekills, abstract parts (a) and (d)  (S04-L4)

Tex: `lem:s04-ekills`(a), (d) in `mathematics/chapters/s04/ordinary.tex`.  Status: *formalized*
(abstract versions; the Brandt-level instances are S04-L10).

* `Ordinary.deg X R : (X →₀ R) →ₗ[R] R`, the sum of the coefficients.
* (a) If `deg ∘ Up = p • deg`, then `ordPart Up ≤ ker deg` and `e (ker deg) = e ⊤`
  (`ordPart_deg_eq_bot`, `ordPart_le_ker_deg`, `ordPart_ker_deg`).
* (d) For the pairing `⟨[x],[y]⟩ = δ` on `X →₀ R` (`deltaPairing`), if `Upt` is adjoint to `Up` and
  both have an ordinary decomposition, then the pairing restricts to a perfect pairing
  `ordPart Up × ordPart Upt → R` (`perfect_ordPart_pairing`).  This is stated for any commutative
  ring `R` that is `p`-adically separated (`hsep`; true for `ℤ_[p]`, `ZMod (p ^ m)`, and fields
  with `p = 0`); separatedness is exactly what makes `ordPart ⟂ nilPart` for the adjoint pair.
-/

@[expose] public section

open Module Submodule
open scoped Pointwise

set_option autoImplicit false

namespace Langlandscape.Ordinary

noncomputable section

/-! ### Generic facts on `ordPart` / `nilPart` used below -/

section Generic

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Equivariant maps commute with iterated endomorphisms (`s04-ekills`, helper). -/
private lemma ek_comp_pow_apply (f : M →ₗ[R] N) (T : Module.End R M) (S : Module.End R N)
    (h : ∀ x, f (T x) = S (f x)) (n : ℕ) (x : M) : f ((T ^ n) x) = (S ^ n) (f x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

/-- Membership in `ordPart` unfolded (`s04-ekills`, helper). -/
private lemma ek_mem_ordPart (T : Module.End R M) (m : M) :
    m ∈ ordPart T ↔ ∀ n : ℕ, m ∈ LinearMap.range (T ^ n) := by
  rw [mem_ordPart]
  simp only [LinearMap.mem_range]

/-- An equivariant map sends `ordPart T` into `ordPart S`, without any decomposition hypothesis
(`lem:s04-ekills`(a), `s04-ekills`). -/
theorem ordPart_map_le_of_comm (f : M →ₗ[R] N) (T : Module.End R M) (S : Module.End R N)
    (h : ∀ x, f (T x) = S (f x)) : (ordPart T).map f ≤ ordPart S := by
  rintro - ⟨m, hm, rfl⟩
  refine (ek_mem_ordPart S _).2 fun n => ?_
  obtain ⟨x, hx⟩ := (ek_mem_ordPart T m).1 hm n
  exact ⟨f x, by rw [← ek_comp_pow_apply f T S h n x, hx]⟩

/-- Powers of `T` commute (`s04-ekills`, helper). -/
private lemma ek_pow_comm (T : Module.End R M) (n k : ℕ) (y : M) :
    (T ^ k) ((T ^ n) y) = (T ^ n) ((T ^ k) y) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.pow_pow_self T k n).eq]

/-- `ordPart T` is stable under all powers of `T` (`s04-ekills`, helper). -/
private lemma ek_pow_mem_ordPart (T : Module.End R M) {x : M} (hx : x ∈ ordPart T) (n : ℕ) :
    (T ^ n) x ∈ ordPart T := by
  rw [ek_mem_ordPart] at hx
  rw [ek_mem_ordPart]
  intro k
  obtain ⟨y, rfl⟩ := hx k
  exact ⟨(T ^ n) y, ek_pow_comm T n k y⟩


/-- `nilPart p T` is stable under powers of `T` (`s04-ekills`, helper). -/
theorem nilPart_pow_mem (p : R) (T : Module.End R M) {x : M} (hx : x ∈ nilPart p T) (n : ℕ) :
    (T ^ n) x ∈ nilPart p T := by
  refine mem_nilPart.2 fun k => ?_
  obtain ⟨N, hN⟩ := mem_nilPart.1 hx k
  obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hN
  refine ⟨N, ?_⟩
  rw [ek_pow_comm T n N x, ← hb, map_smul]
  exact Submodule.smul_mem_pointwise_smul _ _ _ trivial

/-- `e` of a `T`-stable submodule `K ⊇ ordPart T`, one inclusion: the image of `ordPart (T|_K)` in `M`
lies in `ordPart T` (`lem:s04-ekills`(a), `s04-ekills`, helper). -/
theorem map_subtype_ordPart_restrict_le (K : Submodule R M) (T : Module.End R M)
    (hK : ∀ x ∈ K, T x ∈ K) :
    Submodule.map K.subtype (ordPart (R := R) (M := ↥K) (T.restrict hK)) ≤ ordPart T := by
  have hcomm : ∀ x : ↥K, K.subtype (T.restrict hK x) = T (K.subtype x) := fun _ => rfl
  intro m hm
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hm
  refine (ek_mem_ordPart T _).2 fun n => ?_
  obtain ⟨z, hz⟩ := LinearMap.mem_range.1 ((ek_mem_ordPart (M := ↥K) (T.restrict hK) y).1 hy n)
  refine LinearMap.mem_range.2 ⟨K.subtype z, ?_⟩
  rw [← hz]
  exact (ek_comp_pow_apply (M := ↥K) K.subtype (T.restrict hK) T hcomm n z).symm

/-- `e` of a `T`-stable submodule `K ⊇ ordPart T`, other inclusion (uses the ordinary decomposition
of `T`) (`lem:s04-ekills`(a), `s04-ekills`, helper). -/
theorem ordPart_le_map_subtype_ordPart_restrict (p : R) (K : Submodule R M) (T : Module.End R M)
    (hK : ∀ x ∈ K, T x ∈ K) (hle : ordPart T ≤ K) (hdec : HasOrdDecomp p T) :
    ordPart T ≤ Submodule.map K.subtype (ordPart (R := R) (M := ↥K) (T.restrict hK)) := by
  have hcomm : ∀ x : ↥K, K.subtype (T.restrict hK x) = T (K.subtype x) := fun _ => rfl
  have hc : IsCompl (ordPart T) (nilPart p T) := hdec
  intro m hm
  refine Submodule.mem_map.2 ⟨⟨m, hle hm⟩,
    (ek_mem_ordPart (M := ↥K) (T.restrict hK) _).2 fun n => ?_, rfl⟩
  obtain ⟨z, hz⟩ := (ek_mem_ordPart T m).1 hm n
  have hz' : z ∈ ordPart T ⊔ nilPart p T := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz'
  have hbo : (T ^ n) b ∈ ordPart T := by
    have h1 : (T ^ n) b = m - (T ^ n) a := by
      rw [← hz, map_add]; abel
    rw [h1]
    exact Submodule.sub_mem _ hm (ek_pow_mem_ordPart T ha n)
  have hbn : (T ^ n) b ∈ nilPart p T := nilPart_pow_mem p T hb n
  have hb0 : (T ^ n) b = 0 := by
    have hinf : (T ^ n) b ∈ ordPart T ⊓ nilPart p T := Submodule.mem_inf.2 ⟨hbo, hbn⟩
    rwa [hc.inf_eq_bot, Submodule.mem_bot] at hinf
  rw [map_add, hb0, add_zero] at hz
  refine LinearMap.mem_range.2 ⟨⟨a, hle ha⟩, ?_⟩
  apply Subtype.ext
  exact (ek_comp_pow_apply (M := ↥K) K.subtype (T.restrict hK) T hcomm n ⟨a, hle ha⟩).trans hz

end Generic

/-! ### The degree map -/

section Deg

variable (X R : Type*) [CommRing R]

/-- The degree `deg : R[X] → R`, the sum of the coefficients (`lem:s04-ekills`(a), `s04-ekills`).
Stage 05 bridges the Brandt degree to this definition. -/
def deg : (X →₀ R) →ₗ[R] R := Finsupp.lsum R (fun _ : X => (LinearMap.id : R →ₗ[R] R))

variable {X R}

/-- `deg [x] r = r` (`lem:s04-ekills`(a), `s04-ekills`). -/
@[simp] theorem deg_single (x : X) (r : R) : deg X R (Finsupp.single x r) = r := by
  simp [deg]

variable (Up : (X →₀ R) →ₗ[R] (X →₀ R)) (p : R)

/-- Pointwise form of `deg ∘ Up = p • deg` (`lem:s04-ekills`(a), `s04-ekills`). -/
theorem deg_Up_apply (hUp : (deg X R).comp Up = p • deg X R) (x : X →₀ R) :
    deg X R (Up x) = p * deg X R x := by
  have h := LinearMap.congr_fun hUp x
  simpa using h

/-- `Up` preserves `ker deg` when `deg ∘ Up = p • deg` (`lem:s04-ekills`(a), `s04-ekills`). -/
theorem Up_mem_ker_deg (hUp : (deg X R).comp Up = p • deg X R) {x : X →₀ R}
    (hx : x ∈ LinearMap.ker (deg X R)) : Up x ∈ LinearMap.ker (deg X R) := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [deg_Up_apply Up p hUp, hx, mul_zero]

/-- The restriction of `Up` to `ker deg` (`lem:s04-ekills`(a), `s04-ekills`). -/
abbrev UpKer (hUp : (deg X R).comp Up = p • deg X R) :
    Module.End R (LinearMap.ker (deg X R)) :=
  Up.restrict (fun _ hx => Up_mem_ker_deg Up p hUp hx)

/-- `ordPart ((p) : R → R) = ⊥` for `p` on the module `R` (`U = p`), given an ordinary
decomposition (`lem:s04-ekills`(a), `s04-ekills`): `nilPart` is everything. -/
theorem ordPart_deg_eq_bot (hdec : HasOrdDecomp p (LinearMap.lsmul R R p)) :
    ordPart (LinearMap.lsmul R R p) = ⊥ := by
  have hc : IsCompl (ordPart (LinearMap.lsmul R R p)) (nilPart p (LinearMap.lsmul R R p)) := hdec
  have hpow : ∀ (k : ℕ) (m : R), ((LinearMap.lsmul R R p) ^ k) m = p ^ k • m := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ, Module.End.mul_apply, ih, LinearMap.lsmul_apply, smul_smul, pow_succ]
  have htop : nilPart p (LinearMap.lsmul R R p) = ⊤ := by
    rw [eq_top_iff]
    intro m _
    refine mem_nilPart.2 fun k => ⟨k, ?_⟩
    rw [hpow]
    exact Submodule.smul_mem_pointwise_smul m (p ^ k) ⊤ trivial
  have := hc.inf_eq_bot
  rwa [htop, inf_top_eq] at this

/-- `e` kills the degree: `ordPart Up ≤ ker deg` if `deg ∘ Up = p • deg` and `p` has an
ordinary decomposition on `R` (`lem:s04-ekills`(a), `s04-ekills`). -/
theorem ordPart_le_ker_deg (hUp : (deg X R).comp Up = p • deg X R)
    (hdecR : HasOrdDecomp p (LinearMap.lsmul R R p)) :
    ordPart Up ≤ LinearMap.ker (deg X R) := by
  intro x hx
  have hle := ordPart_map_le_of_comm (deg X R) Up (LinearMap.lsmul R R p)
    (fun y => by rw [deg_Up_apply Up p hUp, LinearMap.lsmul_apply, smul_eq_mul])
  have hmem : deg X R x ∈ ordPart (LinearMap.lsmul R R p) := hle ⟨x, hx, rfl⟩
  rw [ordPart_deg_eq_bot p hdecR, Submodule.mem_bot] at hmem
  exact hmem

/-- `lem:s04-ekills`(a), `e (ker deg) = e ⊤`: the ordinary part of `Up` restricted to `ker deg`
is the ordinary part of `Up`, i.e. `0 → e R[X]⁰ → e R[X] → 0` (given the ordinary decomposition of
`Up` and of `p` on `R`) (`s04-ekills`). -/
theorem ordPart_ker_deg (hUp : (deg X R).comp Up = p • deg X R)
    (hdecUp : HasOrdDecomp p Up) (hdecR : HasOrdDecomp p (LinearMap.lsmul R R p)) :
    Submodule.map (LinearMap.ker (deg X R)).subtype
      (ordPart (R := R) (M := ↥(LinearMap.ker (deg X R))) (UpKer Up p hUp)) = ordPart Up :=
  le_antisymm
    (map_subtype_ordPart_restrict_le (LinearMap.ker (deg X R)) Up
      (fun _ hx => Up_mem_ker_deg Up p hUp hx))
    (ordPart_le_map_subtype_ordPart_restrict p (LinearMap.ker (deg X R)) Up
      (fun _ hx => Up_mem_ker_deg Up p hUp hx) (ordPart_le_ker_deg Up p hUp hdecR) hdecUp)

end Deg

/-! ### The pairing `⟨[x],[y]⟩ = δ` -/

section Pairing

variable {X : Type*} {R : Type*} [CommRing R]


/-- Orthogonality of `ordPart` and `nilPart` for an adjoint pair `A`, `A'` w.r.t. a bilinear form
`C`, when `R` is `p`-adically separated (`lem:s04-ekills`(d), `s04-ekills`). -/
theorem ordPart_nilPart_orthogonal {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : R)
    (hsep : ∀ r : R, (∀ k : ℕ, ∃ s : R, r = p ^ k * s) → r = 0)
    (C : M →ₗ[R] N →ₗ[R] R) (A : Module.End R M) (A' : Module.End R N)
    (hadj : ∀ x y, C (A x) y = C x (A' y)) {x : M} (hx : x ∈ ordPart A) {y : N}
    (hy : y ∈ nilPart p A') : C x y = 0 := by
  have hpow : ∀ (n : ℕ) (x : M) (y : N), C ((A ^ n) x) y = C x ((A' ^ n) y) := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      rw [pow_succ, Module.End.mul_apply, ih, hadj, pow_succ', Module.End.mul_apply]
  apply hsep
  intro k
  obtain ⟨n, hn⟩ := mem_nilPart.1 hy k
  obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hn
  obtain ⟨x', rfl⟩ := (ek_mem_ordPart A x).1 hx n
  refine ⟨C x' z, ?_⟩
  rw [hpow, ← hz, map_smul, smul_eq_mul]

/-- Abstract perfectness of the restriction of a perfect pairing `C : M × N → R` to
`O × O'`, where `M = O ⊕ N₁`, `N = O' ⊕ N'` and `C(O, N') = 0 = C(N₁, O')`
(`lem:s04-ekills`(d), `s04-ekills`; left bijectivity). -/
theorem bijective_domRestrict₁₂_of_orthogonal {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (C : M →ₗ[R] N →ₗ[R] R) (hC : Function.Bijective C)
    {O N₁ : Submodule R M} {O' N' : Submodule R N} (hO : IsCompl O N₁) (hO' : IsCompl O' N')
    (h1 : ∀ x ∈ O, ∀ y ∈ N', C x y = 0) (h2 : ∀ x ∈ N₁, ∀ y ∈ O', C x y = 0) :
    Function.Bijective (C.domRestrict₁₂ O O') := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hxM : C (x : M) = 0 := by
      apply LinearMap.ext
      intro y
      have hy : y ∈ O' ⊔ N' := by rw [hO'.sup_eq_top]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearMap.zero_apply, h1 x x.2 b hb, add_zero]
      have h0 : C.domRestrict₁₂ O O' x ⟨a, ha⟩ = 0 := by
        rw [hx, LinearMap.zero_apply]
      rw [LinearMap.domRestrict₁₂_apply] at h0
      exact h0
    have h0 : (x : M) = 0 := hC.1 (by rw [hxM, map_zero])
    exact Subtype.ext h0
  · intro φ
    let ψ : N →ₗ[R] R := LinearMap.ofIsCompl hO' φ 0
    obtain ⟨z, hz⟩ := hC.2 ψ
    have hz' : z ∈ O ⊔ N₁ := by rw [hO.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz'
    refine ⟨⟨a, ha⟩, ?_⟩
    apply LinearMap.ext
    intro y'
    have h3 : C (a + b) (y' : N) = ψ (y' : N) := LinearMap.congr_fun hz _
    have h4 : ψ (y' : N) = φ y' := LinearMap.ofIsCompl_apply_left hO' y'
    rw [map_add, LinearMap.add_apply, h2 b hb y' y'.2, add_zero] at h3
    show C a (y' : N) = φ y'
    rw [h3, h4]

/-- Perfectness of the restriction of an abstract perfect pairing to the ordinary parts
(`lem:s04-ekills`(d), `s04-ekills`).  Hypotheses: `Upt` is adjoint to `Up`, both have an ordinary
decomposition, and `R` is `p`-adically separated (`hsep`). -/
theorem perfect_ordPart_pairing_of_perfPair {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : R)
    (hsep : ∀ r : R, (∀ k : ℕ, ∃ s : R, r = p ^ k * s) → r = 0)
    (C : M →ₗ[R] N →ₗ[R] R) (hC : C.IsPerfPair) (Up : Module.End R M) (Upt : Module.End R N)
    (hadj : ∀ x y, C (Up x) y = C x (Upt y))
    (hdec : HasOrdDecomp p Up) (hdect : HasOrdDecomp p Upt) :
    (C.domRestrict₁₂ (ordPart Up) (ordPart Upt)).IsPerfPair := by
  have hc : IsCompl (ordPart Up) (nilPart p Up) := hdec
  have hct : IsCompl (ordPart Upt) (nilPart p Upt) := hdect
  have hadj' : ∀ (y : N) (x : M), C.flip (Upt y) x = C.flip y (Up x) := by
    intro y x
    simp only [LinearMap.flip_apply]
    exact (hadj x y).symm
  have hL : Function.Bijective (C.domRestrict₁₂ (ordPart Up) (ordPart Upt)) :=
    bijective_domRestrict₁₂_of_orthogonal C (LinearMap.IsPerfPair.bijective_left C) hc hct
      (fun x hx y hy => ordPart_nilPart_orthogonal p hsep C Up Upt hadj hx hy)
      (fun x hx y hy => ordPart_nilPart_orthogonal p hsep C.flip Upt Up hadj' hy hx)
  have hR : Function.Bijective (C.flip.domRestrict₁₂ (ordPart Upt) (ordPart Up)) :=
    bijective_domRestrict₁₂_of_orthogonal C.flip (LinearMap.IsPerfPair.bijective_right C) hct hc
      (fun y hy x hx => ordPart_nilPart_orthogonal p hsep C.flip Upt Up hadj' hy hx)
      (fun y hy x hx => ordPart_nilPart_orthogonal p hsep C Up Upt hadj hx hy)
  have hfl : (C.domRestrict₁₂ (ordPart Up) (ordPart Upt)).flip
      = C.flip.domRestrict₁₂ (ordPart Upt) (ordPart Up) :=
    LinearMap.ext fun _ => LinearMap.ext fun _ => rfl
  refine ⟨hL, ?_⟩
  rw [hfl]
  exact hR

variable [DecidableEq X]

variable (X R) in
/-- The pairing `⟨[x],[y]⟩ = δ_{xy}` on `X →₀ R` (the Brandt pairing in the free case
`w_x = 1`) (`lem:s04-ekills`(d), `s04-ekills`). -/
def deltaPairing : (X →₀ R) →ₗ[R] (X →₀ R) →ₗ[R] R :=
  (Finsupp.basisSingleOne : Module.Basis X R (X →₀ R)).toDual

/-- `⟨[x] r, y⟩ = r y(x)` (`lem:s04-ekills`(d), `s04-ekills`). -/
theorem deltaPairing_single_left (x : X) (r : R) (y : X →₀ R) :
    deltaPairing X R (Finsupp.single x r) y = r * y x := by
  have h := (Finsupp.basisSingleOne : Module.Basis X R (X →₀ R)).toDual_apply_right x y
  have h1 : (Finsupp.single x r : X →₀ R) = r • (Finsupp.basisSingleOne : Module.Basis X R (X →₀ R)) x := by
    simp
  rw [h1, map_smul, LinearMap.smul_apply]
  unfold deltaPairing
  rw [h]
  simp

/-- The pairing `δ` is symmetric (`lem:s04-ekills`(d), `s04-ekills`). -/
theorem deltaPairing_comm (x y : X →₀ R) : deltaPairing X R x y = deltaPairing X R y x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single i r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | single j s =>
      rw [deltaPairing_single_left, deltaPairing_single_left]
      by_cases h : i = j
      · subst h; simp [mul_comm]
      · simp [h, Ne.symm h]

variable (X R) in
/-- The pairing `δ` is perfect for finite `X` (`lem:s04-ekills`(d), `s04-ekills`). -/
theorem deltaPairing_bijective [Finite X] : Function.Bijective (deltaPairing X R) :=
  ⟨Module.Basis.toDual_injective _, LinearMap.range_eq_top.mp (Module.Basis.toDual_range _)⟩

variable (X R) in
/-- `δ` is a perfect pairing for finite `X` (`lem:s04-ekills`(d), `s04-ekills`). -/
theorem deltaPairing_isPerfPair [Finite X] : (deltaPairing X R).IsPerfPair where
  bijective_left := deltaPairing_bijective X R
  bijective_right := by
    have h : (deltaPairing X R).flip = deltaPairing X R :=
      LinearMap.ext fun x => LinearMap.ext fun y => deltaPairing_comm y x
    rw [h]
    exact deltaPairing_bijective X R

/-- `lem:s04-ekills`(d), abstract: for finite `X`, an adjoint pair `Up`, `Upt` w.r.t.
`⟨[x],[y]⟩ = δ_{xy}` (`hadj`) with ordinary decompositions, over a `p`-adically separated
commutative ring `R` (`hsep`; e.g. `ℤ_[p]`, `ZMod (p ^ m)`), the pairing restricts to a perfect
pairing `ordPart Up × ordPart Upt → R` (`s04-ekills`). -/
theorem perfect_ordPart_pairing [Finite X] (p : R)
    (hsep : ∀ r : R, (∀ k : ℕ, ∃ s : R, r = p ^ k * s) → r = 0)
    (Up Upt : (X →₀ R) →ₗ[R] (X →₀ R))
    (hadj : ∀ x y, deltaPairing X R (Up x) y = deltaPairing X R x (Upt y))
    (hdec : HasOrdDecomp p Up) (hdect : HasOrdDecomp p Upt) :
    ((deltaPairing X R).domRestrict₁₂ (ordPart Up) (ordPart Upt)).IsPerfPair :=
  perfect_ordPart_pairing_of_perfPair p hsep (deltaPairing X R) (deltaPairing_isPerfPair X R) Up Upt
    hadj hdec hdect

end Pairing

end

end Langlandscape.Ordinary
