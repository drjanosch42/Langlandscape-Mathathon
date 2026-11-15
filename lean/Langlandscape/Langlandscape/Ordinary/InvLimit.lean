/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Inverse limits of `ℕ`-indexed systems as compatible families (S04-L13a)

`mathematics/chapters/s04/control.tex`, `def:s04-Mord`, and `mathematics/chapters/s04/lambdaribet.tex`,
`thm:s04-lambdaribet`(a) (abstract part); plan row S04-L13a and decisions D-lim, D-Λ of `plan/implementation/stage-04.md`. No category-theoretic limits are used: the limit of a
system `(M s, f s : M (s + 1) → M s)` is the submodule `Compat f` of compatible families in
`Π s, M s`.

* `Compat f`, `Compat.proj`: compatible families and the projection to level `s`.
* `Compat.exists_of_step`: dependent choice along the tower (no surjectivity).
* `Compat.exists_lift`, `Compat.lift`, `compat_proj_surjective`: lifting along transitions that are
  surjective **from level `s` on** (the transitions below `s` need not be surjective).
* `Compat.map` and `Compat.map_injective`, `Compat.map_exact` (no surjectivity),
  `Compat.map_surjective` (levelwise surjective `q`, surjective transitions of the **kernel system**
  only), `lim_exact`: `0 → lim A → lim B → lim C → 0` exact.
* `Lam R G π`: the subring of compatible families in `Π s, R[G s]` for group homs
  `π s : G (s + 1) → G s` (tex `Λ = lim 𝒪[Δ_s]`; for `G s = Δ_s` and `R = ℤ_p` this is the Iwasawa
  algebra `ℤ_p[[1 + pℤ_p]]`, which Mathlib v4.35 does not define). `Lam.proj_surjective` needs `π t`
  surjective for `t ≥ s` only; the subring itself needs no hypothesis on `π`.
* `Compat.IsEquivariant`, `Compat.instModuleLam`: for systems of `R[G s]`-modules with equivariant
  transitions, `Compat f` is a `Lam R G π`-module, `(l • x) s = l s • x s`.
-/

@[expose] public section

noncomputable section

namespace Langlandscape.Ordinary

section Compat

variable {R : Type*} [Ring R] {M : ℕ → Type*} [∀ s, AddCommGroup (M s)] [∀ s, Module R (M s)]

/-- `def:s04-Mord` (s04-Mord, abstract inverse limit, D-lim): for an `ℕ`-indexed system of
`R`-modules `M s` with transitions `f s : M (s + 1) → M s`, the submodule of `Π s, M s` of
compatible families `x` (`f s (x (s + 1)) = x s` for all `s`). This is `lim M`. -/
def Compat (f : ∀ s, M (s + 1) →ₗ[R] M s) : Submodule R (∀ s, M s) where
  carrier := {x | ∀ s, f s (x (s + 1)) = x s}
  add_mem' {x y} hx hy s := by
    simp only [Pi.add_apply, map_add, hx s, hy s]
  zero_mem' s := by simp
  smul_mem' c x hx s := by
    simp only [Pi.smul_apply, map_smul, hx s]

variable (f : ∀ s, M (s + 1) →ₗ[R] M s)

/-- `def:s04-Mord` (s04-Mord): membership in `Compat f`. -/
theorem mem_Compat_iff {x : ∀ s, M s} : x ∈ Compat f ↔ ∀ s, f s (x (s + 1)) = x s :=
  Iff.rfl

/-- `def:s04-Mord` (s04-Mord): the projection `lim M → M s` to level `s`. -/
def Compat.proj (s : ℕ) : Compat f →ₗ[R] M s :=
  (LinearMap.proj s).comp (Compat f).subtype

/-- `def:s04-Mord` (s04-Mord): the projection evaluates the family at `s`. -/
@[simp]
theorem Compat.proj_apply (s : ℕ) (x : Compat f) : Compat.proj f s x = (x : ∀ s, M s) s :=
  rfl

/-- `thm:s04-lambdaribet` (s04-lambdaribet, D-lim): dependent choice along the tower. If some
`x₀ : M 0` satisfies `P 0`, and every `x : M s` with `P s x` has a preimage `y : M (s + 1)` with
`P (s + 1) y`, then there is a compatible family `x` with `P s (x s)` for all `s`. No
surjectivity hypothesis. -/
theorem Compat.exists_of_step (P : ∀ s, M s → Prop) (h0 : ∃ x, P 0 x)
    (hstep : ∀ s x, P s x → ∃ y, P (s + 1) y ∧ f s y = x) :
    ∃ x ∈ Compat f, ∀ s, P s (x s) := by
  let seq : ∀ s, {y : M s // P s y} := fun s =>
    Nat.rec (motive := fun s => {y : M s // P s y}) ⟨h0.choose, h0.choose_spec⟩
      (fun s y => ⟨(hstep s y.1 y.2).choose, (hstep s y.1 y.2).choose_spec.1⟩) s
  exact ⟨fun s => (seq s).1, fun s => (hstep s (seq s).1 (seq s).2).choose_spec.2,
    fun s => (seq s).2⟩

/-- `thm:s04-lambdaribet` (s04-lambdaribet, D-lim), auxiliary: lifting from level `s` along
transitions that are surjective from level `s` on, by induction on `s` (shifting the system). -/
private theorem exists_lift_aux {R : Type*} [Ring R] (s : ℕ) :
    ∀ {M : ℕ → Type*} [∀ t, AddCommGroup (M t)] [∀ t, Module R (M t)]
      (f : ∀ t, M (t + 1) →ₗ[R] M t), (∀ t, s ≤ t → Function.Surjective (f t)) →
      ∀ x : M s, ∃ y ∈ Compat f, y s = x := by
  induction s with
  | zero =>
    intro M _ _ f hf x
    let P : ∀ t, M t → Prop := fun t => match t with
      | 0 => fun y => y = x
      | _ + 1 => fun _ => True
    obtain ⟨y, hy, hy0⟩ := Compat.exists_of_step f P ⟨x, rfl⟩ (fun t z _ => by
      obtain ⟨w, hw⟩ := hf t (Nat.zero_le t) z
      exact ⟨w, trivial, hw⟩)
    exact ⟨y, hy, hy0 0⟩
  | succ s ih =>
    intro M _ _ f hf x
    obtain ⟨y', hy', hy's⟩ := ih (M := fun t => M (t + 1)) (fun t => f (t + 1))
      (fun t ht => hf (t + 1) (Nat.succ_le_succ ht)) x
    let y : ∀ t, M t := fun t => match t with
      | 0 => f 0 (y' 0)
      | t + 1 => y' t
    refine ⟨y, fun t => ?_, hy's⟩
    cases t with
    | zero => rfl
    | succ t => exact hy' t

/-- `thm:s04-lambdaribet` (s04-lambdaribet, D-lim): if the transitions `f t` are surjective for all
`t ≥ s` (nothing is assumed below `s`), every `x : M s` is the `s`-component of a compatible
family. -/
theorem Compat.exists_lift {s : ℕ} (hf : ∀ t, s ≤ t → Function.Surjective (f t)) (x : M s) :
    ∃ y ∈ Compat f, y s = x :=
  exists_lift_aux s f hf x

/-- `thm:s04-lambdaribet` (s04-lambdaribet, D-lim): a chosen compatible family lifting `x : M s`,
for transitions surjective from level `s` on. -/
def Compat.lift {s : ℕ} (hf : ∀ t, s ≤ t → Function.Surjective (f t)) (x : M s) : Compat f :=
  ⟨(Compat.exists_lift f hf x).choose, (Compat.exists_lift f hf x).choose_spec.1⟩

/-- `thm:s04-lambdaribet` (s04-lambdaribet): `Compat.lift` lifts `x`. -/
theorem Compat.lift_apply {s : ℕ} (hf : ∀ t, s ≤ t → Function.Surjective (f t)) (x : M s) :
    Compat.proj f s (Compat.lift f hf x) = x :=
  (Compat.exists_lift f hf x).choose_spec.2

/-- `thm:s04-lambdaribet` (s04-lambdaribet, D-lim): the projection `lim M → M s` is surjective when
the transitions `f t` are surjective for `t ≥ s`. -/
theorem compat_proj_surjective {s : ℕ} (hf : ∀ t, s ≤ t → Function.Surjective (f t)) :
    Function.Surjective (Compat.proj f s) :=
  fun x => ⟨Compat.lift f hf x, Compat.lift_apply f hf x⟩

variable {f} {N : ℕ → Type*} [∀ s, AddCommGroup (N s)] [∀ s, Module R (N s)]
  {g : ∀ s, N (s + 1) →ₗ[R] N s}

/-- `thm:s04-lambdaribet` (s04-lambdaribet): a morphism of systems `φ s : M s → N s`
(`φ s ∘ f s = g s ∘ φ (s + 1)`) induces `lim M → lim N`, levelwise. -/
def Compat.map (φ : ∀ s, M s →ₗ[R] N s) (hφ : ∀ s, (φ s).comp (f s) = (g s).comp (φ (s + 1))) :
    Compat f →ₗ[R] Compat g :=
  LinearMap.codRestrict (Compat g) (LinearMap.pi fun s => (φ s).comp (Compat.proj f s))
    (fun x s => by
      have h := LinearMap.congr_fun (hφ s) ((x : ∀ s, M s) (s + 1))
      simp only [LinearMap.coe_comp, Function.comp_apply] at h
      simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Compat.proj_apply]
      rw [← h, x.2 s])

/-- `thm:s04-lambdaribet` (s04-lambdaribet): `Compat.map` acts levelwise. -/
@[simp]
theorem Compat.map_apply (φ : ∀ s, M s →ₗ[R] N s)
    (hφ : ∀ s, (φ s).comp (f s) = (g s).comp (φ (s + 1))) (x : Compat f) (s : ℕ) :
    ((Compat.map φ hφ x : Compat g) : ∀ s, N s) s = φ s ((x : ∀ s, M s) s) :=
  rfl

variable {P : ℕ → Type*} [∀ s, AddCommGroup (P s)] [∀ s, Module R (P s)]
  {h : ∀ s, P (s + 1) →ₗ[R] P s}

/-- `thm:s04-lambdaribet`(a) (s04-lambdaribet): `lim` preserves injectivity (levelwise injective
`i s`; no surjectivity). -/
theorem Compat.map_injective {i : ∀ s, M s →ₗ[R] N s}
    {hi : ∀ s, (i s).comp (f s) = (g s).comp (i (s + 1))}
    (hinj : ∀ s, Function.Injective (i s)) : Function.Injective (Compat.map i hi) := by
  intro x y hxy
  apply Subtype.ext
  funext s
  apply hinj s
  have := congrArg (fun z : Compat g => (z : ∀ s, N s) s) hxy
  simpa only [Compat.map_apply] using this

/-- `thm:s04-lambdaribet`(a) (s04-lambdaribet): `lim` is exact in the middle for levelwise exact
`A → B → C` with `A → B` levelwise injective (no surjectivity of any transition). -/
theorem Compat.map_exact {i : ∀ s, M s →ₗ[R] N s} {q : ∀ s, N s →ₗ[R] P s}
    {hi : ∀ s, (i s).comp (f s) = (g s).comp (i (s + 1))}
    {hq : ∀ s, (q s).comp (g s) = (h s).comp (q (s + 1))}
    (hinj : ∀ s, Function.Injective (i s)) (hex : ∀ s, Function.Exact (i s) (q s)) :
    Function.Exact (Compat.map i hi) (Compat.map q hq) := by
  intro y
  constructor
  · intro hy
    have hys : ∀ s, q s ((y : ∀ s, N s) s) = 0 := fun s => by
      have := congrArg (fun z : Compat h => (z : ∀ s, P s) s) hy
      simpa only [Compat.map_apply, ZeroMemClass.coe_zero, Pi.zero_apply] using this
    have hpre : ∀ s, ∃ a, i s a = (y : ∀ s, N s) s := fun s => (hex s _).mp (hys s)
    choose a ha using hpre
    have hac : a ∈ Compat f := fun s => by
      apply hinj s
      have h1 := LinearMap.congr_fun (hi s) (a (s + 1))
      simp only [LinearMap.coe_comp, Function.comp_apply] at h1
      rw [h1, ha, ha]
      exact y.2 s
    refine ⟨⟨a, hac⟩, Subtype.ext (funext fun s => ?_)⟩
    simp only [Compat.map_apply]
    exact ha s
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    funext s
    simp only [Compat.map_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact (hex s).apply_apply_eq_zero _

/-- `thm:s04-lambdaribet`(a) (s04-lambdaribet, D-lim): `lim` preserves surjectivity of `q` when
`A → B → C` is levelwise exact, `q s` is surjective for every `s`, and the transitions `f` of the
**kernel system `A`** are surjective. No surjectivity of the transitions of `B` or `C` is needed. -/
theorem Compat.map_surjective {i : ∀ s, M s →ₗ[R] N s} {q : ∀ s, N s →ₗ[R] P s}
    (hi : ∀ s, (i s).comp (f s) = (g s).comp (i (s + 1)))
    {hq : ∀ s, (q s).comp (g s) = (h s).comp (q (s + 1))}
    (hex : ∀ s, Function.Exact (i s) (q s))
    (hsurj : ∀ s, Function.Surjective (q s)) (hf : ∀ s, Function.Surjective (f s)) :
    Function.Surjective (Compat.map q hq) := by
  intro c
  obtain ⟨b, hb, hbc⟩ := Compat.exists_of_step g (fun s y => q s y = (c : ∀ s, P s) s)
    (hsurj 0 _) (fun s y hy => by
      obtain ⟨b', hb'⟩ := hsurj (s + 1) ((c : ∀ s, P s) (s + 1))
      have hq' := LinearMap.congr_fun (hq s) b'
      simp only [LinearMap.coe_comp, Function.comp_apply] at hq'
      have hk : q s (g s b' - y) = 0 := by
        rw [map_sub, hq', hb', hy, c.2 s, sub_self]
      obtain ⟨a, ha⟩ := (hex s _).mp hk
      obtain ⟨a', ha'⟩ := hf s a
      have hi' := LinearMap.congr_fun (hi s) a'
      simp only [LinearMap.coe_comp, Function.comp_apply] at hi'
      refine ⟨b' - i (s + 1) a', ?_, ?_⟩
      · rw [map_sub, hb', (hex (s + 1)).apply_apply_eq_zero, sub_zero]
      · rw [map_sub, ← hi', ha', ha, sub_sub_cancel])
  exact ⟨⟨b, hb⟩, Subtype.ext (funext fun s => hbc s)⟩

/-- `thm:s04-lambdaribet`(a), abstract part (s04-lambdaribet, D-lim): for a levelwise short exact
sequence of `ℕ`-indexed systems `0 → A s → B s → C s → 0` (maps `i`, `q` commuting with the
transitions `f`, `g`, `h`) whose **kernel system `A` has surjective transitions** `f`, the sequence
`0 → lim A → lim B → lim C → 0` of compatible families is exact. The surjectivity of `f` is used
only for the surjectivity of `lim B → lim C`; no hypothesis on `g` or `h`. -/
theorem lim_exact (i : ∀ s, M s →ₗ[R] N s) (q : ∀ s, N s →ₗ[R] P s)
    (hi : ∀ s, (i s).comp (f s) = (g s).comp (i (s + 1)))
    (hq : ∀ s, (q s).comp (g s) = (h s).comp (q (s + 1)))
    (hinj : ∀ s, Function.Injective (i s)) (hex : ∀ s, Function.Exact (i s) (q s))
    (hsurj : ∀ s, Function.Surjective (q s)) (hf : ∀ s, Function.Surjective (f s)) :
    Function.Injective (Compat.map i hi) ∧ Function.Exact (Compat.map i hi) (Compat.map q hq) ∧
      Function.Surjective (Compat.map q hq) :=
  ⟨Compat.map_injective hinj, Compat.map_exact hinj hex, Compat.map_surjective hi hex hsurj hf⟩

end Compat

section Lam

variable (R : Type*) [CommRing R] (G : ℕ → Type*) [∀ s, CommGroup (G s)]
  (π : ∀ s, G (s + 1) →* G s)

/-- `D-Λ` (s04-Mord, s04-lambdaribet; tex `Λ = lim 𝒪[Δ_s]`): the subring of `Π s, R[G s]` of
families compatible under the ring maps `R[G (s + 1)] → R[G s]` induced by `π s`. For `R = ℤ_p`,
`G s = Δ_s = (1 + pℤ_p) ⧸ (1 + p ^ (s + 1) ℤ_p)` and the canonical surjections `π s`, this is the
Iwasawa algebra `ℤ_p[[1 + pℤ_p]] = lim ℤ_p[Δ_s]` (cited, by definition of the completed group
ring; tex `D-Λ`; not defined in Mathlib v4.35, and not formalized here).
No hypothesis on `π` is needed for the subring; it is a `CommRing` since every `G s` is
commutative. -/
def Lam : Subring (∀ s, MonoidAlgebra R (G s)) where
  carrier := {l | ∀ s, MonoidAlgebra.mapDomainRingHom R (π s) (l (s + 1)) = l s}
  mul_mem' {a b} ha hb s := by
    simp only [Pi.mul_apply, map_mul, ha s, hb s]
  one_mem' s := by simp
  add_mem' {a b} ha hb s := by
    simp only [Pi.add_apply, map_add, ha s, hb s]
  zero_mem' s := by simp
  neg_mem' {a} ha s := by
    simp only [Pi.neg_apply, map_neg, ha s]

/-- `D-Λ` (s04-Mord): membership in `Lam R G π`. -/
theorem mem_Lam_iff {l : ∀ s, MonoidAlgebra R (G s)} :
    l ∈ Lam R G π ↔ ∀ s, MonoidAlgebra.mapDomainRingHom R (π s) (l (s + 1)) = l s :=
  Iff.rfl

/-- `D-Λ` (s04-Mord): the projection `Λ → R[G s]`, a ring homomorphism. -/
def Lam.proj (s : ℕ) : Lam R G π →+* MonoidAlgebra R (G s) :=
  (Pi.evalRingHom (fun s => MonoidAlgebra R (G s)) s).comp (Lam R G π).subtype

/-- `D-Λ` (s04-Mord): `Lam.proj` evaluates the family at `s`. -/
@[simp]
theorem Lam.proj_apply (s : ℕ) (l : Lam R G π) :
    Lam.proj R G π s l = (l : ∀ s, MonoidAlgebra R (G s)) s :=
  rfl

variable {R G π} in
/-- `D-Λ` (s04-Mord), auxiliary: a surjective group hom induces a surjective map of group rings. -/
private theorem mapDomainRingHom_surjective {H K : Type*} [CommGroup H] [CommGroup K]
    (φ : H →* K) (hφ : Function.Surjective φ) :
    Function.Surjective (MonoidAlgebra.mapDomainRingHom R φ) := by
  intro x
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩
  | single k r =>
    obtain ⟨g, rfl⟩ := hφ k
    exact ⟨MonoidAlgebra.single g r, by simp [MonoidAlgebra.mapDomain_single]⟩

/-- `D-Λ` (s04-Mord, s04-lambdaribet): `Λ → R[G s]` is surjective when `π t` is surjective for all
`t ≥ s` (nothing is assumed below `s`). -/
theorem Lam.proj_surjective {s : ℕ} (hπ : ∀ t, s ≤ t → Function.Surjective (π t)) :
    Function.Surjective (Lam.proj R G π s) := by
  intro x
  obtain ⟨y, hy, hys⟩ := Compat.exists_lift (M := fun t => MonoidAlgebra R (G t))
    (fun t => (MonoidAlgebra.mapDomainAlgHom R R (π t)).toLinearMap)
    (fun t ht => mapDomainRingHom_surjective (π t) (hπ t ht)) x
  exact ⟨⟨y, hy⟩, hys⟩

variable {R G π}
variable {M : ℕ → Type*} [∀ s, AddCommGroup (M s)] [∀ s, Module R (M s)]
  [∀ s, Module (MonoidAlgebra R (G s)) (M s)]

/-- `def:s04-Mord` (s04-Mord, D-Λ): the transitions `f s : M (s + 1) → M s` of a system of
`R[G s]`-modules are equivariant along `π s`: `f s (l • m) = π_*(l) • f s m`. -/
class Compat.IsEquivariant (π : ∀ s, G (s + 1) →* G s) (f : ∀ s, M (s + 1) →ₗ[R] M s) :
    Prop where
  /-- `def:s04-Mord` (s04-Mord): equivariance of the transitions. -/
  map_smul' : ∀ s (l : MonoidAlgebra R (G (s + 1))) (m : M (s + 1)),
    f s (l • m) = MonoidAlgebra.mapDomainRingHom R (π s) l • f s m

variable (f : ∀ s, M (s + 1) →ₗ[R] M s) [hfe : Compat.IsEquivariant π f]

/-- `def:s04-Mord` (s04-Mord, D-Λ): `Λ` acts on compatible families of an equivariant system
levelwise, `(l • x) s = l s • x s`. -/
instance Compat.instSMulLam : SMul (Lam R G π) (Compat f) where
  smul l x := ⟨fun s => (l : ∀ s, MonoidAlgebra R (G s)) s • (x : ∀ s, M s) s, fun s => by
    simp only
    rw [hfe.map_smul', l.2 s, x.2 s]⟩

/-- `def:s04-Mord` (s04-Mord, D-Λ): the `Λ`-action on `Compat f` is levelwise. -/
theorem Compat.lam_smul_apply (l : Lam R G π) (x : Compat f) (s : ℕ) :
    ((l • x : Compat f) : ∀ s, M s) s = (l : ∀ s, MonoidAlgebra R (G s)) s • (x : ∀ s, M s) s :=
  rfl

/-- `def:s04-Mord` (s04-Mord, D-Λ; tex: `M_ord` is a `Λ`-module): for an equivariant system,
`Compat f = lim M` is a `Lam R G π`-module, `(l • x) s = l s • x s`. -/
instance Compat.instModuleLam : Module (Lam R G π) (Compat f) where
  one_smul x := Subtype.ext (funext fun s => by
    simp only [Compat.lam_smul_apply]
    exact one_smul _ _)
  mul_smul a b x := Subtype.ext (funext fun s => by
    simp only [Compat.lam_smul_apply]
    exact mul_smul _ _ _)
  smul_zero a := Subtype.ext (funext fun s => by
    simp only [Compat.lam_smul_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact smul_zero _)
  smul_add a x y := Subtype.ext (funext fun s => by
    simp only [Compat.lam_smul_apply, Submodule.coe_add, Pi.add_apply]
    exact smul_add _ _ _)
  add_smul a b x := Subtype.ext (funext fun s => by
    simp only [Compat.lam_smul_apply]
    exact add_smul _ _ _)
  zero_smul x := Subtype.ext (funext fun s => by
    simp only [Compat.lam_smul_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    exact zero_smul _ _)

variable {N : ℕ → Type*} [∀ s, AddCommGroup (N s)] [∀ s, Module R (N s)]
  [∀ s, Module (MonoidAlgebra R (G s)) (N s)] {g : ∀ s, N (s + 1) →ₗ[R] N s}
  [hge : Compat.IsEquivariant π g]

/-- `def:s04-Mord` (s04-Mord, s04-lambdaribet, D-Λ): for equivariant systems and a levelwise
`R[G s]`-equivariant morphism `φ`, the induced map `lim M → lim N` is `Λ`-linear. -/
theorem Compat.map_lam_smul (φ : ∀ s, M s →ₗ[R] N s)
    (hφ : ∀ s, (φ s).comp (f s) = (g s).comp (φ (s + 1)))
    (hφl : ∀ s (l : MonoidAlgebra R (G s)) (m : M s), φ s (l • m) = l • φ s m)
    (l : Lam R G π) (x : Compat f) :
    Compat.map φ hφ (l • x) = l • Compat.map φ hφ x :=
  Subtype.ext (funext fun s => by
    simp only [Compat.map_apply, Compat.lam_smul_apply]
    exact hφl s _ _)

/-- `def:s04-Mord`, `thm:s04-lambdaribet`(a) (s04-Mord, s04-lambdaribet, D-Λ): for equivariant
systems and a levelwise `R[G s]`-equivariant morphism `φ`, the induced map `lim M → lim N` as a
`Λ`-linear map. Its underlying function is `Compat.map φ hφ` (`Compat.coe_mapLam`), so the
exactness statements of `lim_exact` apply to it unchanged. -/
def Compat.mapLam (φ : ∀ s, M s →ₗ[R] N s)
    (hφ : ∀ s, (φ s).comp (f s) = (g s).comp (φ (s + 1)))
    (hφs : ∀ s (a : MonoidAlgebra R (G s)) (m : M s), φ s (a • m) = a • φ s m) :
    Compat f →ₗ[Lam R G π] Compat g where
  toFun := Compat.map φ hφ
  map_add' := map_add (Compat.map φ hφ)
  map_smul' l x := Compat.map_lam_smul f φ hφ hφs l x

/-- `def:s04-Mord` (s04-Mord, s04-lambdaribet): `Compat.mapLam` has the same underlying function as
`Compat.map`. -/
theorem Compat.coe_mapLam (φ : ∀ s, M s →ₗ[R] N s)
    (hφ : ∀ s, (φ s).comp (f s) = (g s).comp (φ (s + 1)))
    (hφs : ∀ s (a : MonoidAlgebra R (G s)) (m : M s), φ s (a • m) = a • φ s m) :
    ⇑(Compat.mapLam (π := π) f φ hφ hφs) = ⇑(Compat.map φ hφ) :=
  rfl

/-- `def:s04-Mord` (s04-Mord, D-Λ): the product of an equivariant system with itself (levelwise
`M s × M s`, transitions `f s × f s`) is equivariant (tex: `C_s = e ℤ_p[X_s]²`). Stated as
a theorem, not an instance: instance search does not match the lambda-shaped system
`fun s => M s × M s`, so use it via `have := Compat.IsEquivariant.prod (π := π) f`. -/
theorem Compat.IsEquivariant.prod :
    Compat.IsEquivariant (M := fun s => M s × M s) π (fun s => (f s).prodMap (f s)) where
  map_smul' s l m := by
    simp only [LinearMap.prodMap_apply, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk,
      hfe.map_smul']

variable (R G π) in
/-- `D-Λ` (s04-Mord): `Lam R G π` is an `R`-algebra via the constant families `s ↦ single 1 r`
(the structure map `R → Λ`; for `R = ℤ_p` this makes `Λ` a `ℤ_p`-algebra). The scalar action is
multiplication by `algebraMap R Λ r`. -/
instance Lam.instAlgebra : Algebra R (Lam R G π) :=
  RingHom.toAlgebra
    { toFun := fun r => ⟨fun s => MonoidAlgebra.single 1 r, fun s => by
        simp [MonoidAlgebra.mapDomain_single]⟩
      map_one' := Subtype.ext (funext fun s => rfl)
      map_mul' := fun a b => Subtype.ext (funext fun s => by
        simp [MonoidAlgebra.single_mul_single])
      map_zero' := Subtype.ext (funext fun s => by simp)
      map_add' := fun a b => Subtype.ext (funext fun s => by simp [MonoidAlgebra.single_add]) }

variable (R G π) in
/-- `D-Λ` (s04-Mord): the structure map `R → Λ` is the family of constants `single 1 r`. -/
theorem Lam.algebraMap_apply (r : R) (s : ℕ) :
    ((algebraMap R (Lam R G π) r : Lam R G π) : ∀ s, MonoidAlgebra R (G s)) s =
      MonoidAlgebra.single 1 r :=
  rfl

end Lam

end Langlandscape.Ordinary
