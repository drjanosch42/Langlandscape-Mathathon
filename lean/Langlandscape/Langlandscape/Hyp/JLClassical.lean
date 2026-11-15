/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.Hecke

/-!
# Targets as statements: classical Jacquet-Langlands (S01-L13)

`mathematics/chapters/s01/6-targets.tex`, `thm:s01-JLclassical`, `if:s01-targets`.
Hypotheses are `Prop`-valued definitions; no axiom is introduced (OVERVIEW 3.6). A theorem that uses one of them
takes it as an explicit argument.

Status: *cited* (the statement), not to be discharged in this project.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat Langlandscape.Brandt

/-- `if:s01-targets`: alias of the imported hypothesis `GL2TF.Hyp.EichlerMass` (Eichler's mass formula).
Source: the GL(2) trace formula project import; cited; not to be discharged in this project. Not redefined. -/
abbrev EichlerMass := @GL2TF.Hyp.EichlerMass

/-- Abstract stand-in for `S_k(Γ_0(N))^{D-new}` with its Hecke operators (Mathlib v4.35.0 has neither).
Tex label `thm:s01-JLclassical` (`s01-JLclassical`). -/
structure GL2CuspData (N k : ℕ) where
  S : Type
  [acg : AddCommGroup S]
  [mod : Module ℂ S]
  [fd : FiniteDimensional ℂ S]
  T : ℕ → Module.End ℂ S
  comm : ∀ m n, Commute (T m) (T n)

/-- The Eisenstein part for `k = 2`: the line of functions factoring through `Nrd` (tex `thm:s01-JLclassical`). -/
abbrev Eis : Type := ℂ

/-- `T_ℓ` acts on the Eisenstein line by `ℓ + 1` (tex `prop:s01-relations`(d), `T_ℓ 𝟏 = (ℓ+1) 𝟏`). -/
noncomputable def eisT (ℓ : ℕ) : Module.End ℂ Eis := ((ℓ : ℂ) + 1) • LinearMap.id

/-- `thm:s01-JLclassical` (`s01-JLclassical`), the `k = 2` trivial-coefficient form of classical
Jacquet-Langlands: `ℂ^{X_B(U_0(M))} ≃ S_2(Γ_0(DM))^{D-new} ⊕ Eis`, equivariant for `T_ℓ`, `ℓ ∤ DM`.

*Schematic interface; the GL₂ side is abstract data because Mathlib v4.35.0 has no Hecke operators on
`S_k(Γ_0(N))`; the hypothesis is JL only when `S` is instantiated by the true space, which cannot be checked in
Lean here.* With an arbitrary `S` it only says that `S` is a Hecke-module complement of the constants; it carries
no GL₂ content. No later theorem may be advertised as "under classical JL" without this caveat.

Plumbing change w.r.t. the brief: `Tl` needs the instance `Fact ℓ.Prime`, the non-divisibility `¬ ℓ ∣ D` and the
finiteness hypothesis `hfin`; the latter is universally quantified (it holds mathematically; formalized as `relIndex_elemT_ne_zero_U0` in
`Brandt/HeckeFinite.lean`; the `∀ hfin` form keeps the statement self-contained; no content change).

Source: Jacquet-Langlands; cited; not to be discharged in this project. -/
def JLClassical (d : DefiniteData) (M : ℕ) (hM : M.Coprime d.D) (S : GL2CuspData (d.D * M) 2) : Prop :=
  letI := S.acg
  letI := S.mod
  ∃ e : ZXdual (d.U0 M hM) ℂ ≃ₗ[ℂ] (S.S × Eis),
    ∀ (ℓ : ℕ) (hp : ℓ.Prime) (hℓ : ¬ ℓ ∣ d.D * M),
      haveI : Fact ℓ.Prime := ⟨hp⟩
      ∀ hfin : ((d.U0 M hM) ⊓ conjSub (d.U0 M hM) (elemT d ℓ (fun h => hℓ (h.mul_right M)))).relIndex
          (d.U0 M hM) ≠ 0,
        e.toLinearMap ∘ₗ Tl d (d.U0 M hM) ℓ (fun h => hℓ (h.mul_right M)) ℂ hfin =
          (LinearMap.prodMap (S.T ℓ) (eisT ℓ)) ∘ₗ e.toLinearMap

end Langlandscape.Hyp
