/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Langlandscape.Ordinary.InvLimit
import Langlandscape.Ordinary.Tower
import Langlandscape.Ordinary.RibetFinite

/-!
# Inverse limits on the ordinary Brandt and Ribet towers (S04-L13b)

`plan/implementation/stage-04.md`, row S04-L13b, decisions D-lim and D-Λ;
`mathematics/chapters/s04/control.tex`, `def:s04-Mord`; `mathematics/chapters/s04/lambdaribet.tex`,
`thm:s04-lambdaribet`(a), `lem:s04-limexact`. Specialisation `𝒪_E = ℤ_p`, `E = ℚ_p`.

The tower `U_s = U_1(M p^s)` (`s ≥ 1`) is indexed by `n : ℕ` with `s = n + 1`.

* Abstract part (Mathlib + S04-L13a only):
  `surjective_of_snake` (the snake-lemma step of D-lim: `ker b → ker c` onto and `b` onto give `a` onto),
  `lim_exact_of_snake` (`lim_exact` with the kernel-system surjectivity replaced by the snake hypotheses),
  `Compat.lamModuleOfRep` (a `Lam`-module structure on `lim M` from levelwise representations
  `ρ s : G s →* End (M s)` compatible with the transitions).
* `TowerHyp d M p`: the standing hypotheses on the tower (`p ∤ D`, `M ≠ 0`, `p ∤ M`, `(M p^s, D) = 1`);
  `RibetHyp d q M p` adds `q ∤ D`, `q ∤ M p^s`.
* `Mord T`: `lim_s e ℤ_p[X_s]` along `π_*` (`def:s04-Mord`, as compatible families, D-lim);
  `mordTrans_surjective` (S04-L10 control, `hdec`), `Mord.proj_surjective`;
  `Mord.lamModule`: the `Lam`-module structure from levelwise diamond representations (supplied as an argument).
* The three ordinary Ribet systems `A_s = e H₁`, `B_s = e ℤ_p[X(U_0(q)U_s)]⁰`, `C_s = e (ℤ_p[X_s]⁰)²`
  (S04-L12 `UpH1`, `UpDeg0E`, `UpDeg0Prod`) with transitions induced by `π_*` (`transA`, `transB`, `transC`);
  `Xord H = lim A`; the limit maps `xordToLimB`, `alphaLim`.
* `lim_exact_ribet` (`thm:s04-lambdaribet`(a), in a weaker form): `0 → Xord → lim B → lim C → 0` is exact as a
  sequence of `ℤ_p`-modules, given connectivity and the surjectivity of the `A`-transitions (**fallback of D-lim**,
  explicit hypothesis `hA`, cf. `Hyp.InvLimExact`). Exactly this is stated: `lim B`, `lim C` are the limits of the
  **degree-zero** ordinary parts `e ℤ_p[X(U_0(q)U_s)]⁰`, `e (ℤ_p[X_s]⁰)²`, not identified with `M_ord(U_0(q)U)`,
  `M_ord(U)^{⊕2}` (the levelwise identifications `ordDeg0EEquiv`, `ordDeg0ProdEquiv` of S04-L17b exist, their
  `π_*`-compatibility does not; `Mord` is defined only for `TowerHyp`, not at the levels `U_0(q)U_s`); there is no
  `Λ`-structure on the three limits and no Hecke equivariance.
  The A-surjectivity via the snake lemma on the concrete Ribet systems is **not formalized**: only the abstract
  snake step `surjective_of_snake` / `lim_exact_of_snake` is. Of its inputs, the surjectivity of the `B`- and
  `C`-transitions is available (`ord_control_finite_U0q`, `ord_control_finite` with `map_ordPart_UpDeg0E`,
  `map_ordPart_UpDeg0Prod`); missing are the kernel identification `ker = I · B` (the tensor form of control, not
  formalized, see `Ordinary/Tower.lean`) and the `Δ_s`-action on `B_s` with `Δ_s`-linearity of `ordAlpha`.
  `Hyp.InvLimExact` stays undischarged (proved in the tex by the D-lim route, under connectivity,
  `thm:s04-lambdaribet`(a)).

Status: *formalized modulo `Hyp.PadicOrdDecomp`* (argument `hdec`; discharged in `Ordinary/TowerUncond.lean`,
`<name>_uncond`), the connectivity argument `hconn`, and, for `lim_exact_ribet`, the explicit surjectivity `hA` of the
`A`-transitions (registered as `Hyp.InvLimExact`, S04-L14b).
-/

set_option autoImplicit false

noncomputable section

namespace Langlandscape.Ordinary

/-! ### The snake-lemma step (abstract) -/

section Snake

variable {R : Type*} [Ring R]
  {A₁ B₁ C₁ A₀ B₀ C₀ : Type*} [AddCommGroup A₁] [AddCommGroup B₁] [AddCommGroup C₁]
  [AddCommGroup A₀] [AddCommGroup B₀] [AddCommGroup C₀] [Module R A₁] [Module R B₁] [Module R C₁]
  [Module R A₀] [Module R B₀] [Module R C₀]

/-- `thm:s04-lambdaribet`(a), D-lim snake step (`s04-lambdaribet`): for a morphism `(a, b, c)` from a sequence
`A₁ → B₁ → C₁` (exact at `B₁`) to a sequence `A₀ → B₀ → C₀` (`i₀` injective, `q₀ ∘ i₀ = 0`), if `b` is surjective
and `q₁` maps `ker b` onto `ker c`, then `a` is surjective (the part `ker b → ker c → coker a → coker b = 0` of the
snake lemma). -/
theorem surjective_of_snake (i₁ : A₁ →ₗ[R] B₁) (q₁ : B₁ →ₗ[R] C₁) (i₀ : A₀ →ₗ[R] B₀) (q₀ : B₀ →ₗ[R] C₀)
    (a : A₁ →ₗ[R] A₀) (b : B₁ →ₗ[R] B₀) (c : C₁ →ₗ[R] C₀)
    (hi : i₀ ∘ₗ a = b ∘ₗ i₁) (hq : q₀ ∘ₗ b = c ∘ₗ q₁)
    (hex₁ : Function.Exact i₁ q₁) (hex₀ : Function.Exact i₀ q₀) (hinj₀ : Function.Injective i₀)
    (hb : Function.Surjective b) (hker : ∀ z : C₁, c z = 0 → ∃ y : B₁, b y = 0 ∧ q₁ y = z) :
    Function.Surjective a := by
  intro x
  obtain ⟨y, hy⟩ := hb (i₀ x)
  have hz : c (q₁ y) = 0 := by
    have h := LinearMap.congr_fun hq y
    simp only [LinearMap.comp_apply] at h
    rw [← h, hy]
    exact hex₀.apply_apply_eq_zero x
  obtain ⟨k, hk0, hkq⟩ := hker _ hz
  have hyk : q₁ (y - k) = 0 := by
    rw [map_sub, hkq, sub_self]
  obtain ⟨a', ha'⟩ := (hex₁ (y - k)).mp hyk
  refine ⟨a', hinj₀ ?_⟩
  have h1 := LinearMap.congr_fun hi a'
  simp only [LinearMap.comp_apply] at h1
  rw [h1, ha', map_sub, hy, hk0, sub_zero]

variable {M : ℕ → Type*} [∀ s, AddCommGroup (M s)] [∀ s, Module R (M s)]
  {N : ℕ → Type*} [∀ s, AddCommGroup (N s)] [∀ s, Module R (N s)]
  {P : ℕ → Type*} [∀ s, AddCommGroup (P s)] [∀ s, Module R (P s)]
  {f : ∀ s, M (s + 1) →ₗ[R] M s} {g : ∀ s, N (s + 1) →ₗ[R] N s} {h : ∀ s, P (s + 1) →ₗ[R] P s}

/-- `thm:s04-lambdaribet`(a), `lem:s04-limexact`, D-lim route (`s04-lambdaribet`, `s04-limexact`): for a levelwise
short exact sequence of `ℕ`-systems `0 → A → B → C → 0` whose middle system has surjective transitions `g` and such
that `q (s + 1)` maps `ker (g s)` onto `ker (h s)` for every `s`, the transitions of `A` are surjective
(`surjective_of_snake`), hence `0 → lim A → lim B → lim C → 0` is exact (`lim_exact`). -/
theorem lim_exact_of_snake (i : ∀ s, M s →ₗ[R] N s) (q : ∀ s, N s →ₗ[R] P s)
    (hi : ∀ s, (i s).comp (f s) = (g s).comp (i (s + 1)))
    (hq : ∀ s, (q s).comp (g s) = (h s).comp (q (s + 1)))
    (hinj : ∀ s, Function.Injective (i s)) (hex : ∀ s, Function.Exact (i s) (q s))
    (hsurj : ∀ s, Function.Surjective (q s)) (hg : ∀ s, Function.Surjective (g s))
    (hker : ∀ s (z : P (s + 1)), h s z = 0 → ∃ y : N (s + 1), g s y = 0 ∧ q (s + 1) y = z) :
    Function.Injective (Compat.map i hi) ∧ Function.Exact (Compat.map i hi) (Compat.map q hq) ∧
      Function.Surjective (Compat.map q hq) :=
  lim_exact i q hi hq hinj hex hsurj fun s =>
    surjective_of_snake (i (s + 1)) (q (s + 1)) (i s) (q s) (f s) (g s) (h s) (hi s) (hq s)
      (hex (s + 1)) (hex s) (hinj s) (hg s) (hker s)

end Snake

/-! ### `Lam`-modules from levelwise representations (abstract) -/

section LamRep

variable {R : Type*} [CommRing R] {G : ℕ → Type*} [∀ s, CommGroup (G s)] {π : ∀ s, G (s + 1) →* G s}
  {M : ℕ → Type*} [∀ s, AddCommGroup (M s)] [∀ s, Module R (M s)]

/-- `def:s04-Mord`, D-Λ (`s04-Mord`), auxiliary: if the transitions intertwine the representations
`ρ s : G s →* End (M s)` along `π s`, they intertwine the induced `R[G s]`-actions (`MonoidAlgebra.lift`) along
`R[π s]`. -/
theorem Compat.lift_comp_eq (f : ∀ s, M (s + 1) →ₗ[R] M s) (ρ : ∀ s, G s →* Module.End R (M s))
    (hρ : ∀ s (x : G (s + 1)), (f s).comp (ρ (s + 1) x) = (ρ s (π s x)).comp (f s)) (s : ℕ)
    (l : MonoidAlgebra R (G (s + 1))) :
    (f s).comp (MonoidAlgebra.lift R (Module.End R (M (s + 1))) (G (s + 1)) (ρ (s + 1)) l) =
      (MonoidAlgebra.lift R (Module.End R (M s)) (G s) (ρ s)
        (MonoidAlgebra.mapDomainRingHom R (π s) l)).comp (f s) := by
  induction l using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, LinearMap.comp_zero, LinearMap.zero_comp]
  | add a b ha hb => simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, ha, hb]
  | single x r =>
    have e : MonoidAlgebra.mapDomainRingHom R (π s) (MonoidAlgebra.single x r) =
        MonoidAlgebra.single (π s x) r := by
      simp [MonoidAlgebra.mapDomain_single]
    rw [e, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single]
    refine LinearMap.ext fun m => ?_
    have hm := LinearMap.congr_fun (hρ s x) m
    simp only [LinearMap.comp_apply] at hm
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, hm]

/-- `def:s04-Mord`, D-Λ (`s04-Mord`; tex: "`Λ` acts through the adelic diamonds"): for levelwise representations
`ρ s : G s →* End_R (M s)` intertwined by the transitions (`f s ∘ ρ (s+1) x = ρ s (π s x) ∘ f s`), `lim M = Compat f`
is a `Lam R G π`-module, `(l • m) s = ρ_s(l s) (m s)` (`ρ_s` extended `R`-linearly to `R[G s]`). This is S04-L13a's
`Compat.instModuleLam` for the module structures `R[G s] → End (M s)` induced by `ρ s`. -/
def Compat.lamModuleOfRep (f : ∀ s, M (s + 1) →ₗ[R] M s) (ρ : ∀ s, G s →* Module.End R (M s))
    (hρ : ∀ s (x : G (s + 1)), (f s).comp (ρ (s + 1) x) = (ρ s (π s x)).comp (f s)) :
    Module (Lam R G π) (Compat f) :=
  letI : ∀ s, Module (MonoidAlgebra R (G s)) (M s) := fun s =>
    Module.compHom (M s) (MonoidAlgebra.lift R (Module.End R (M s)) (G s) (ρ s)).toRingHom
  haveI : Compat.IsEquivariant π f :=
    ⟨fun s l m => LinearMap.congr_fun (Compat.lift_comp_eq f ρ hρ s l) m⟩
  Compat.instModuleLam f

end LamRep

/-! ### Restrictions of commuting maps (abstract) -/

section Restrict

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`), auxiliary: if `f ∘ T = T' ∘ f`, the restrictions to stable
submodules commute as well. Generic (no concrete chain modules are unfolded). -/
theorem restrict_comp_restrict_of_comm {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] {S : Submodule R X} {S' : Submodule R Y} (f : X →ₗ[R] Y)
    (T : Module.End R X) (T' : Module.End R Y) (h : f ∘ₗ T = T' ∘ₗ f) (hf : ∀ x ∈ S, f x ∈ S')
    (hT : ∀ x ∈ S, T x ∈ S) (hT' : ∀ y ∈ S', T' y ∈ S') :
    f.restrict hf ∘ₗ T.restrict hT = T'.restrict hT' ∘ₗ f.restrict hf :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h x.1)

end Restrict

/-! ### The tower hypotheses -/

open Langlandscape.Quat Langlandscape.Local Langlandscape.Brandt

/-- `def:s04-Mord` (`s04-Mord`), standing hypotheses on the tower `U_s = U_1(M p^s)`: `p ∤ D`, `M ≠ 0`, `p ∤ M`
and `(M p^s, D) = 1` for all `s` (the coprimality proofs that the levels `d.Utower M p s` take). -/
structure TowerHyp (d : DefiniteData) (M p : ℕ) : Prop where
  /-- `p ∤ D`. -/
  hp : ¬ p ∣ d.D
  /-- `M ≠ 0`. -/
  hM : M ≠ 0
  /-- `p ∤ M`. -/
  hpM : ¬ p ∣ M
  /-- `(M p^s, D) = 1` for all `s`. -/
  hN : ∀ s, (M * p ^ s).Coprime d.D

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`), standing hypotheses of the Ribet tower: those of `TowerHyp`, plus
`q ∤ D` and `q ∤ M p^s` for all `s` (so `U_s` is a `q`-level, `Tree.isQLevel_Utower`). -/
structure RibetHyp (d : DefiniteData) (q M p : ℕ) : Prop extends TowerHyp d M p where
  /-- `q ∤ D`. -/
  hq : ¬ q ∣ d.D
  /-- `q ∤ M p^s` for all `s`. -/
  hqN : ∀ s, ¬ q ∣ M * p ^ s

namespace TowerHyp

variable {d : DefiniteData} {M p : ℕ} [Fact p.Prime] (T : TowerHyp d M p)

/-- `def:s04-Mord` (`s04-Mord`), notation: the level `U_{n+1} = U_1(M p^{n+1})` (index shift `s = n + 1 ≥ 1`). -/
abbrev lvl (n : ℕ) : Subgroup (GL2TF.Quat.BHat d.a d.b)ˣ :=
  d.Utower M p (n + 1) (T.hN (n + 1))

/-- `def:s04-Mord` (`s04-Mord`): `U_{n+2} ≤ U_{n+1}`. -/
theorem lvl_le (n : ℕ) : T.lvl (n + 1) ≤ T.lvl n :=
  Utower_succ_le (T.hN (n + 1)) (T.hN (n + 1 + 1)) T.hM

/-- `def:s04-Mord`, `lem:s04-hida`(a) (`s04-Mord`): `U_{n+1}` carries `U_p` (`p`-component `K1 p (n+1)`). -/
theorem isUp (n : ℕ) : IsUpLevel d p T.hp (T.lvl n) (K1 p (n + 1)) :=
  isUpLevel_Utower T.hM T.hpM (Nat.le_add_left 1 n)

/-- `def:s04-Mord` (`s04-Mord`): the level-`(n+1)` term `e ℤ_p[X_{n+1}]` of the ordinary Brandt system
(`e` for `U_p = UpAt`, S04-L9). -/
abbrev MordLevel (n : ℕ) : Type :=
  ↥(ordPart (R := ℤ_[p]) (M := ZX (T.lvl n) ℤ_[p]) (UpAt (T.lvl n) (T.isUp n) ℤ_[p]))

/-- `def:s04-Mord` (`s04-Mord`): the transition `π_* : e ℤ_p[X_{n+2}] → e ℤ_p[X_{n+1}]` (S04-L10 `ordPush`). -/
def mordTrans (n : ℕ) : T.MordLevel (n + 1) →ₗ[ℤ_[p]] T.MordLevel n :=
  ordPush (T.isUp (n + 1)) (T.isUp n) (T.lvl_le n) ℤ_[p]

/-- `def:s04-Mord`, `thm:s04-control`(a) (`s04-Mord`, `s04-control`), for `E = ℚ_p`, formalized modulo
`Hyp.PadicOrdDecomp`: the transitions `π_* : e ℤ_p[X_{s+1}] → e ℤ_p[X_s]` are surjective (S04-L10
`ord_control_finite`). -/
theorem mordTrans_surjective (hdec : Hyp.PadicOrdDecomp p) (n : ℕ) :
    Function.Surjective (T.mordTrans n) := by
  unfold mordTrans
  exact (ord_control_finite (hp := T.hp) (hN := T.hN (n + 1)) (hN' := T.hN (n + 1 + 1)) hdec T.hM T.hpM
    (Nat.le_add_left 1 n)).1

end TowerHyp

/-- `def:s04-Mord` (`s04-Mord`), for `E = ℚ_p`: the `Λ`-adic Brandt module
`M_ord(U) = lim_{s ≥ 1} e ℤ_p[X_s(U)]` along `π_*`, as the submodule of compatible families in
`Π_s e ℤ_p[X_s]` (D-lim; level `s = n + 1`). -/
abbrev Mord {d : DefiniteData} {M p : ℕ} [Fact p.Prime] (T : TowerHyp d M p) :
    Submodule ℤ_[p] (∀ n, T.MordLevel n) :=
  Compat (M := T.MordLevel) T.mordTrans

/-- `def:s04-Mord`, `thm:s04-control`(a) (`s04-Mord`), formalized modulo `Hyp.PadicOrdDecomp`: every projection
`M_ord(U) → e ℤ_p[X_s]` is surjective (surjective transitions, `compat_proj_surjective`). -/
theorem Mord.proj_surjective {d : DefiniteData} {M p : ℕ} [Fact p.Prime] (T : TowerHyp d M p)
    (hdec : Hyp.PadicOrdDecomp p) (n : ℕ) :
    Function.Surjective (Compat.proj (M := T.MordLevel) T.mordTrans n) :=
  compat_proj_surjective (M := T.MordLevel) T.mordTrans fun t _ => T.mordTrans_surjective hdec t

/-- `def:s04-Mord`, D-Λ (`s04-Mord`): the `Lam`-module structure on `M_ord(U)` from levelwise representations
`ρ n : G n →* End (e ℤ_p[X_{n+1}])` (the diamonds `⟨t⟩`, acting through `G n = Δ_{n+1}`) commuting with `π_*`
along `π n : G (n+1) → G n` (`Compat.lamModuleOfRep`). The diamond representation itself is an argument: the
commutation of `U_p` with `diamondAct` is available since S04-L10b (`UpHom_comm_diamondAct`, `permEnd_comm_UpHom`
in `Ordinary/TowerRank.lean`), but the levelwise representation on `e ℤ_p[X_{n+1}]`, the reduction maps
`Δ_{n+2} → Δ_{n+1}` and the compatibility `hρ` are not assembled. -/
def Mord.lamModule {d : DefiniteData} {M p : ℕ} [Fact p.Prime] (T : TowerHyp d M p)
    {G : ℕ → Type*} [∀ n, CommGroup (G n)] (π : ∀ n, G (n + 1) →* G n)
    (ρ : ∀ n, G n →* Module.End ℤ_[p] (T.MordLevel n))
    (hρ : ∀ n (x : G (n + 1)), (T.mordTrans n).comp (ρ (n + 1) x) = (ρ n (π n x)).comp (T.mordTrans n)) :
    Module (Lam ℤ_[p] G π) (Mord T) :=
  Compat.lamModuleOfRep T.mordTrans ρ hρ

/-! ### The three ordinary Ribet systems -/

namespace RibetHyp

variable {d : DefiniteData} {q M p : ℕ} [Fact q.Prime] [Fact p.Prime] (H : RibetHyp d q M p)

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `U_{n+1}` is a `q`-level (`q ∤ M p^{n+1}`). -/
theorem isQ (n : ℕ) : Tree.IsQLevel d q H.hq (H.toTowerHyp.lvl n) :=
  Tree.isQLevel_Utower (H.hqN (n + 1))

include H in
/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `p ≠ q` (from `q ∤ M p`). -/
theorem p_ne_q : p ≠ q :=
  ne_of_not_dvd_tower (le_refl 1) (H.hqN 1)

/-- `thm:s04-lambdaribet`, `lem:s04-hida`(a) (`s04-lambdaribet`): `U_0(q) U_{n+1}` carries `U_p`. -/
theorem isUp0 (n : ℕ) :
    IsUpLevel d p H.hp (d.U0q q (Tree.coprime_of_not_dvd H.hq) (H.toTowerHyp.lvl n)) (K1 p (n + 1)) :=
  isUpLevel_U0q_Utower H.hM H.hpM (Nat.le_add_left 1 n) (Tree.coprime_of_not_dvd H.hq)
    (not_mem_primeFactors_of_ne H.p_ne_q)

/-! #### `π_*` on the `BG`-typed chain modules commutes with `U_p` (bridges, S04-L9 `UpAt_comm_pushforward`) -/

/-- `thm:s04-lambdaribet`, `lem:s01-Up`(b) (`s04-lambdaribet`): `π_* ∘ U_p = U_p ∘ π_*` on edge chains
(`pushBGE`, `UpBGE`). -/
theorem pushBGE_comm (n : ℕ) :
    pushBGE (H.isQ n) (H.isQ (n + 1)) ℤ_[p] ∘ₗ UpBGE (H.isQ (n + 1)) (H.isUp0 (n + 1)) ℤ_[p] =
      UpBGE (H.isQ n) (H.isUp0 n) ℤ_[p] ∘ₗ pushBGE (H.isQ n) (H.isQ (n + 1)) ℤ_[p] := by
  have := Tree.finite_XB_U0q (H.isQ n)
  have := Tree.finite_XB_U0q (H.isQ (n + 1))
  exact UpAt_comm_pushforward (R := ℤ_[p]) (H.isUp0 (n + 1)) (H.isUp0 n)
    (U0q_mono (hq := H.hq) (H.toTowerHyp.lvl_le n))

/-- `thm:s04-lambdaribet`, `lem:s01-Up`(b) (`s04-lambdaribet`): `π_* ∘ U_p = U_p ∘ π_*` on type-0 vertex chains. -/
theorem pushBGV0_comm (n : ℕ) :
    pushBGV0 (H.isQ n) (H.isQ (n + 1)) ℤ_[p] ∘ₗ UpBGV0 (H.isQ (n + 1)) (H.toTowerHyp.isUp (n + 1)) ℤ_[p] =
      UpBGV0 (H.isQ n) (H.toTowerHyp.isUp n) ℤ_[p] ∘ₗ pushBGV0 (H.isQ n) (H.isQ (n + 1)) ℤ_[p] := by
  have := Tree.finite_XB_of_isQLevel (H.isQ n)
  have := Tree.finite_XB_of_isQLevel (H.isQ (n + 1))
  exact UpAt_comm_pushforward (R := ℤ_[p]) (H.toTowerHyp.isUp (n + 1)) (H.toTowerHyp.isUp n)
    (H.toTowerHyp.lvl_le n)

/-- `thm:s04-lambdaribet`, `lem:s01-Up`(b) (`s04-lambdaribet`): `π_* ∘ U_p = U_p ∘ π_*` on type-1 vertex chains. -/
theorem pushBGV1_comm (n : ℕ) :
    pushBGV1 (H.isQ n) (H.isQ (n + 1)) ℤ_[p] ∘ₗ UpBGV1 (H.isQ (n + 1)) (H.toTowerHyp.isUp (n + 1)) ℤ_[p] =
      UpBGV1 (H.isQ n) (H.toTowerHyp.isUp n) ℤ_[p] ∘ₗ pushBGV1 (H.isQ n) (H.isQ (n + 1)) ℤ_[p] := by
  have := Tree.finite_XB_of_isQLevel (H.isQ n)
  have := Tree.finite_XB_of_isQLevel (H.isQ (n + 1))
  exact UpAt_comm_pushforward (R := ℤ_[p]) (H.toTowerHyp.isUp (n + 1)) (H.toTowerHyp.isUp n)
    (H.toTowerHyp.lvl_le n)

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `π_*` preserves degree-zero edge chains (`BG` side). -/
theorem pushBGE_mem_deg0 (n : ℕ) {x : (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))).E →₀ ℤ_[p]}
    (hx : x ∈ Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))).E ℤ_[p]) :
    pushBGE (H.isQ n) (H.isQ (n + 1)) ℤ_[p] x ∈
      Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)).E ℤ_[p] :=
  pushforward_mem_deg0 (U' := d.U0q q (Tree.coprime_of_not_dvd H.hq) (H.toTowerHyp.lvl (n + 1)))
    (U := d.U0q q (Tree.coprime_of_not_dvd H.hq) (H.toTowerHyp.lvl n)) hx

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `π_*` preserves degree-zero type-0 vertex chains (`BG` side). -/
theorem pushBGV0_mem_deg0 (n : ℕ) {x : (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))).V0 →₀ ℤ_[p]}
    (hx : x ∈ Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))).V0 ℤ_[p]) :
    pushBGV0 (H.isQ n) (H.isQ (n + 1)) ℤ_[p] x ∈
      Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)).V0 ℤ_[p] :=
  pushforward_mem_deg0 (U' := H.toTowerHyp.lvl (n + 1)) (U := H.toTowerHyp.lvl n) hx

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `π_*` preserves degree-zero type-1 vertex chains (`BG` side). -/
theorem pushBGV1_mem_deg0 (n : ℕ) {x : (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))).V1 →₀ ℤ_[p]}
    (hx : x ∈ Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))).V1 ℤ_[p]) :
    pushBGV1 (H.isQ n) (H.isQ (n + 1)) ℤ_[p] x ∈
      Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)).V1 ℤ_[p] :=
  pushforward_mem_deg0 (U' := H.toTowerHyp.lvl (n + 1)) (U := H.toTowerHyp.lvl n) hx

/-! #### The three systems -/

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`), notation: `A_{n+1} = e H₁(BG(U_{n+1}, q), ℤ_p)`. -/
abbrev ribA (n : ℕ) : Type :=
  ↥(ordPart (R := ℤ_[p])
    (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)) ℤ_[p]))
    (UpH1 (H.isQ n) H.p_ne_q (H.toTowerHyp.isUp n) (H.isUp0 n) ℤ_[p]))

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`), notation: `B_{n+1} = e ℤ_p[X(U_0(q) U_{n+1})]⁰`. -/
abbrev ribB (n : ℕ) : Type :=
  ↥(ordPart (R := ℤ_[p])
    (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)).E ℤ_[p]))
    (UpDeg0E (H.isQ n) (H.isUp0 n) ℤ_[p]))

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`), notation: `C_{n+1} = e (ℤ_p[X_{n+1}]⁰ × ℤ_p[X_{n+1}]⁰)`. -/
abbrev ribC (n : ℕ) : Type :=
  ↥(ordPart (R := ℤ_[p])
    (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)) ℤ_[p]))
    (UpDeg0Prod (H.isQ n) (H.toTowerHyp.isUp n) ℤ_[p]))

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `π_*` on `H₁` (corestriction), `H₁(BG(U_{n+2})) → H₁(BG(U_{n+1}))`. -/
def pushH1 (n : ℕ) :
    Langlandscape.Graph.H1 (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))) ℤ_[p] →ₗ[ℤ_[p]]
      Langlandscape.Graph.H1 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)) ℤ_[p] :=
  (pushBGE (H.isQ n) (H.isQ (n + 1)) ℤ_[p]).restrict
    fun _ hx => pushforward_mem_H1 ℤ_[p] (H.isQ n) (H.isQ (n + 1)) (H.toTowerHyp.lvl_le n) hx

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `π_*` on the degree-zero chains of `X(U_0(q) U_s)`. -/
def pushDeg0 (n : ℕ) :
    Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))).E ℤ_[p] →ₗ[ℤ_[p]]
      Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)).E ℤ_[p] :=
  (pushBGE (H.isQ n) (H.isQ (n + 1)) ℤ_[p]).restrict fun _ hx => H.pushBGE_mem_deg0 n hx

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `π_* × π_*` on `ℤ_p[X_s]⁰ × ℤ_p[X_s]⁰`. -/
def pushProd (n : ℕ) :
    Langlandscape.Graph.deg0Prod (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))) ℤ_[p] →ₗ[ℤ_[p]]
      Langlandscape.Graph.deg0Prod (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)) ℤ_[p] :=
  ((pushBGV0 (H.isQ n) (H.isQ (n + 1)) ℤ_[p]).prodMap (pushBGV1 (H.isQ n) (H.isQ (n + 1)) ℤ_[p])).restrict
    fun _ hx => Submodule.mem_prod.2
      ⟨H.pushBGV0_mem_deg0 n (Submodule.mem_prod.1 hx).1, H.pushBGV1_mem_deg0 n (Submodule.mem_prod.1 hx).2⟩

/-- `thm:s04-lambdaribet`, `lem:s01-Up`(b) (`s04-lambdaribet`): `π_*` commutes with `U_p` on `H₁`. -/
theorem pushH1_comm (n : ℕ) :
    H.pushH1 n ∘ₗ UpH1 (H.isQ (n + 1)) H.p_ne_q (H.toTowerHyp.isUp (n + 1)) (H.isUp0 (n + 1)) ℤ_[p] =
      UpH1 (H.isQ n) H.p_ne_q (H.toTowerHyp.isUp n) (H.isUp0 n) ℤ_[p] ∘ₗ H.pushH1 n := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h := LinearMap.congr_fun (H.pushBGE_comm n) x.1
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  simp only [LinearMap.comp_apply, pushH1, UpH1, LinearMap.coe_restrict_apply]
  exact h

/-- `thm:s04-lambdaribet`, `lem:s01-Up`(b) (`s04-lambdaribet`): `π_*` commutes with `U_p` on `ℤ_p[X(U_0(q)U_s)]⁰`. -/
theorem pushDeg0_comm (n : ℕ) :
    H.pushDeg0 n ∘ₗ UpDeg0E (H.isQ (n + 1)) (H.isUp0 (n + 1)) ℤ_[p] =
      UpDeg0E (H.isQ n) (H.isUp0 n) ℤ_[p] ∘ₗ H.pushDeg0 n := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h := LinearMap.congr_fun (H.pushBGE_comm n) x.1
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  simp only [LinearMap.comp_apply, pushDeg0, UpDeg0E, LinearMap.coe_restrict_apply]
  exact h

/-- `thm:s04-lambdaribet`, `lem:s01-Up`(b) (`s04-lambdaribet`): `π_* × π_*` commutes with `U_p × U_p`. -/
theorem pushProd_comm (n : ℕ) :
    H.pushProd n ∘ₗ UpDeg0Prod (H.isQ (n + 1)) (H.toTowerHyp.isUp (n + 1)) ℤ_[p] =
      UpDeg0Prod (H.isQ n) (H.toTowerHyp.isUp n) ℤ_[p] ∘ₗ H.pushProd n := by
  have hfull : ((pushBGV0 (H.isQ n) (H.isQ (n + 1)) ℤ_[p]).prodMap (pushBGV1 (H.isQ n) (H.isQ (n + 1)) ℤ_[p])) ∘ₗ
      ((UpBGV0 (H.isQ (n + 1)) (H.toTowerHyp.isUp (n + 1)) ℤ_[p]).prodMap
        (UpBGV1 (H.isQ (n + 1)) (H.toTowerHyp.isUp (n + 1)) ℤ_[p])) =
      ((UpBGV0 (H.isQ n) (H.toTowerHyp.isUp n) ℤ_[p]).prodMap (UpBGV1 (H.isQ n) (H.toTowerHyp.isUp n) ℤ_[p])) ∘ₗ
        ((pushBGV0 (H.isQ n) (H.isQ (n + 1)) ℤ_[p]).prodMap (pushBGV1 (H.isQ n) (H.isQ (n + 1)) ℤ_[p])) := by
    rw [LinearMap.prodMap_comp, LinearMap.prodMap_comp, H.pushBGV0_comm n, H.pushBGV1_comm n]
  unfold pushProd UpDeg0Prod
  exact restrict_comp_restrict_of_comm _ _ _ hfull _ _ _

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): the transition `A_{n+2} → A_{n+1}` (`π_*` on `e H₁`). -/
def transA (n : ℕ) : H.ribA (n + 1) →ₗ[ℤ_[p]] H.ribA n :=
  ordRestrict (R := ℤ_[p])
    (M := ↥(Langlandscape.Graph.H1 (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))) ℤ_[p]))
    (N := ↥(Langlandscape.Graph.H1 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)) ℤ_[p]))
    (H.pushH1 n) (H.pushH1_comm n)

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): the transition `B_{n+2} → B_{n+1}`. -/
def transB (n : ℕ) : H.ribB (n + 1) →ₗ[ℤ_[p]] H.ribB n :=
  ordRestrict (R := ℤ_[p])
    (M := ↥(Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))).E ℤ_[p]))
    (N := ↥(Langlandscape.Graph.deg0 (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)).E ℤ_[p]))
    (H.pushDeg0 n) (H.pushDeg0_comm n)

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): the transition `C_{n+2} → C_{n+1}`. -/
def transC (n : ℕ) : H.ribC (n + 1) →ₗ[ℤ_[p]] H.ribC n :=
  ordRestrict (R := ℤ_[p])
    (M := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q H.hq (H.toTowerHyp.lvl (n + 1)) (H.isQ (n + 1))) ℤ_[p]))
    (N := ↥(Langlandscape.Graph.deg0Prod (Tree.BG d q H.hq (H.toTowerHyp.lvl n) (H.isQ n)) ℤ_[p]))
    (H.pushProd n) (H.pushProd_comm n)

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): the inclusion `A_{n+1} = e H₁ → B_{n+1}` (S04-L12 `ordH1toDeg0`). -/
abbrev ribI (n : ℕ) : H.ribA n →ₗ[ℤ_[p]] H.ribB n :=
  ordH1toDeg0 (H.isQ n) H.p_ne_q (H.toTowerHyp.isUp n) (H.isUp0 n)

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `α = (−s_{0*}, s_{1*}) : B_{n+1} → C_{n+1}` (S04-L12 `ordAlpha`). -/
abbrev ribAlpha (n : ℕ) : H.ribB n →ₗ[ℤ_[p]] H.ribC n :=
  ordAlpha (H.isQ n) H.p_ne_q (H.toTowerHyp.isUp n) (H.isUp0 n)

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): the inclusions `A_s → B_s` commute with the transitions. -/
theorem ribI_comm (n : ℕ) : (H.ribI n).comp (H.transA n) = (H.transB n).comp (H.ribI (n + 1)) := by
  refine LinearMap.ext fun x => Subtype.ext (Subtype.ext ?_)
  simp only [LinearMap.comp_apply, ribI, ordH1toDeg0, transA, transB, ordRestrict_apply, pushH1, pushDeg0,
    LinearMap.coe_restrict_apply, Langlandscape.Graph.H1toDeg0, Submodule.coe_inclusion]

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `α` commutes with the transitions (S04-L12
`boundary_comm_pushBG`). -/
theorem ribAlpha_comm (n : ℕ) :
    (H.ribAlpha n).comp (H.transB n) = (H.transC n).comp (H.ribAlpha (n + 1)) := by
  refine LinearMap.ext fun x => Subtype.ext (Subtype.ext ?_)
  have h := LinearMap.congr_fun
    (boundary_comm_pushBG ℤ_[p] (H.isQ n) (H.isQ (n + 1)) (H.toTowerHyp.lvl_le n)) x.1.1
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  simp only [LinearMap.comp_apply, ribAlpha, ordAlpha, transB, transC, ordRestrict_apply, pushDeg0, pushProd,
    LinearMap.coe_restrict_apply, Langlandscape.Graph.boundaryDeg0, LinearMap.codRestrict_apply,
    LinearMap.domRestrict_apply]
  exact h

/-- `thm:s04-lambdaribet`(a) at level `n + 1` (`s04-lambdaribet`), for `E = ℚ_p`, formalized modulo
`Hyp.PadicOrdDecomp`: `0 → A_s → B_s → C_s → 0` is exact (S04-L12 `ordRibet_exact`), given connectivity. -/
theorem ribet_level_exact (hdec : Hyp.PadicOrdDecomp p)
    (hconn : ∀ s ≥ 1, Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s)) (Tree.isQLevel_Utower (H.hqN s)))
    (n : ℕ) :
    Function.Injective (H.ribI n) ∧ Function.Exact (H.ribI n) (H.ribAlpha n) ∧
      Function.Surjective (H.ribAlpha n) :=
  ordRibet_exact hdec (H.isQ n) (hconn (n + 1) (Nat.le_add_left 1 n)) H.p_ne_q (H.toTowerHyp.isUp n) (H.isUp0 n)

end RibetHyp

section Lim

variable {d : DefiniteData} {q M p : ℕ} [Fact q.Prime] [Fact p.Prime]

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`), for `E = ℚ_p`: `X_ord^{Dq}(U) = lim_s e H₁(Γ_{UU_s}, ℤ_p)` along the
corestrictions (`π_*` on `X(U_0(q) U_s)`-chains), as compatible families (D-lim). -/
abbrev Xord (H : RibetHyp d q M p) : Submodule ℤ_[p] (∀ n, H.ribA n) :=
  Compat (M := H.ribA) H.transA

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `lim_s e ℤ_p[X(U_0(q) U_s)]⁰` (equal to `M_ord(U_0(q)U)` by
`lem:s04-ekills`(a); the identification is not formalized here). -/
abbrev RibetLimB (H : RibetHyp d q M p) : Submodule ℤ_[p] (∀ n, H.ribB n) :=
  Compat (M := H.ribB) H.transB

/-- `thm:s04-lambdaribet` (`s04-lambdaribet`): `lim_s e (ℤ_p[X_s]⁰)²` (equal to `M_ord(U)^{⊕2}` by
`lem:s04-ekills`(a); the identification is not formalized here). -/
abbrev RibetLimC (H : RibetHyp d q M p) : Submodule ℤ_[p] (∀ n, H.ribC n) :=
  Compat (M := H.ribC) H.transC

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): the limit inclusion `X_ord → lim B`. -/
abbrev xordToLimB (H : RibetHyp d q M p) : Xord H →ₗ[ℤ_[p]] RibetLimB H :=
  Compat.map H.ribI H.ribI_comm

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`): the limit of `α = (−s_{0*}, s_{1*})`, `lim B → lim C`. -/
abbrev alphaLim (H : RibetHyp d q M p) : RibetLimB H →ₗ[ℤ_[p]] RibetLimC H :=
  Compat.map H.ribAlpha H.ribAlpha_comm

/-- `thm:s04-lambdaribet`(a) (`s04-lambdaribet`), for `E = ℚ_p`, formalized modulo `Hyp.PadicOrdDecomp`, the
connectivity of `BG(U_s, q)` for all `s ≥ 1` (`hconn`) and the surjectivity of the transitions
`e H₁(Γ_{UU_{s+1}}) → e H₁(Γ_{UU_s})` (`hA`; D-lim fallback, `Hyp.InvLimExact`):
`0 → X_ord^{Dq}(U) → lim_s e ℤ_p[X(U_0(q)U_s)]⁰ →α lim_s e (ℤ_p[X_s]⁰)² → 0` is exact. `ℤ_p`-linear; the middle and
right terms are the degree-zero limits, not identified with `M_ord(U_0(q)U)`, `M_ord(U)^{⊕2}`; no `Λ`-structure, no
Hecke equivariance. -/
theorem lim_exact_ribet (H : RibetHyp d q M p) (hdec : Hyp.PadicOrdDecomp p)
    (hconn : ∀ s ≥ 1, Tree.BGConnected d q H.hq (d.Utower M p s (H.hN s)) (Tree.isQLevel_Utower (H.hqN s)))
    (hA : ∀ n, Function.Surjective (H.transA n)) :
    Function.Injective (xordToLimB H) ∧ Function.Exact (xordToLimB H) (alphaLim H) ∧
      Function.Surjective (alphaLim H) :=
  lim_exact (M := H.ribA) (N := H.ribB) (P := H.ribC) H.ribI H.ribAlpha H.ribI_comm H.ribAlpha_comm
    (fun n => (H.ribet_level_exact hdec hconn n).1)
    (fun n => (H.ribet_level_exact hdec hconn n).2.1) (fun n => (H.ribet_level_exact hdec hconn n).2.2) hA

end Lim

end Langlandscape.Ordinary
