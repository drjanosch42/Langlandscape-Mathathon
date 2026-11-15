/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Tree.Admissible
import Langlandscape.Tree.Coset

/-!
# The action of `Γ_U` on the tree (S02-L4a, spec line `L4a-act`)

`plan/staged/stage-02-tree-quotients.tex`, `def:s02-GU`: `Γ_U` acts on `𝒯_q` through `ι_q`; by `lem:s02-tree`(b)
the action is type-preserving (no inversions). Used by `prop:s02-BG` and `prop:s02-quot`.

* `gammaQGL d q hq U : Γ_U →* GL₂(ℚ_q)`, `γ ↦ ι_q(γ) = localComponent q (ι γ)`.
* `gammaQ_mem_SLq` : `ι_q(γ) ∈ SL₂(ℚ_q)` (from `det_localComponent_finEmbed`, `nrd γ = 1`).
* `gammaQ d q hq U : Γ_U →* SLq q`.
* `MulAction` instances of `Γ_U` on `Vert q`, `Edge q`, `EdgeO q` (`MulAction.compHom` along `gammaQ`).
* `gammaU_smul_vtype` : `vtype q (γ • v) = vtype q v` (via L1's `vtype_smul`, `vdet_of_mem_SLq`).

Status: built, gate1 green.
-/

set_option autoImplicit false

namespace Langlandscape.Tree

open Langlandscape.Quat

variable {d : DefiniteData} {q : ℕ} [Fact q.Prime] {hq : ¬ q ∣ d.D} {U : Subgroup (BHat d.a d.b)ˣ}

/-- `def:s02-GU`: the homomorphism `Γ_U → GL₂(ℚ_q)`, `γ ↦ ι_q(γ)` (the `q`-component of `ι(γ) ∈ B̂^×`). -/
noncomputable def gammaQGL (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) : GammaU d q hq U →* GL (Fin 2) ℚ_[q] :=
  (localComponent d q hq).comp ((iotaU d.a d.b).comp (GammaU d q hq U).subtype)

/-- `def:s02-GU` (`s02-GU`): value of `gammaQGL`. -/
theorem gammaQGL_apply (γ : GammaU d q hq U) :
    gammaQGL d q hq U γ = localComponent d q hq (iotaU d.a d.b (γ : (QuatAlg ℚ d.a d.b)ˣ)) :=
  rfl

/-- `def:s02-GU`, `lem:s02-tree`(b) (`s02-GU`): `ι_q(Γ_U) ⊆ SL₂(ℚ_q)`, since `det ι_q(γ) = nrd γ = 1`. -/
theorem gammaQ_mem_SLq (γ : GammaU d q hq U) : gammaQGL d q hq U γ ∈ SLq q := by
  have h := det_localComponent_finEmbed (d := d) (q := q) (hq := hq) (γ : (QuatAlg ℚ d.a d.b)ˣ)
  rw [nrd_eq_one_of_mem_GammaU γ.2, Rat.cast_one] at h
  exact mem_SLq_iff.2 h

/-- `def:s02-GU`: `Γ_U → SL₂(ℚ_q)`, `γ ↦ ι_q(γ)` (`gammaQGL` with codomain restricted by `gammaQ_mem_SLq`). -/
noncomputable def gammaQ (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D)
    (U : Subgroup (BHat d.a d.b)ˣ) : GammaU d q hq U →* SLq q :=
  (gammaQGL d q hq U).codRestrict (SLq q) gammaQ_mem_SLq

/-- `def:s02-GU` (`s02-GU`): `gammaQ γ = ι_q(γ)` in `GL₂(ℚ_q)`. -/
theorem coe_gammaQ (γ : GammaU d q hq U) :
    ((gammaQ d q hq U γ : SLq q) : GL (Fin 2) ℚ_[q]) = gammaQGL d q hq U γ :=
  rfl

/-- `def:s02-GU`: `Γ_U` acts on the vertices of `𝒯_q` through `ι_q`. -/
noncomputable instance instMulActionGammaUVert : MulAction (GammaU d q hq U) (Vert q) :=
  MulAction.compHom (Vert q) (gammaQ d q hq U)

/-- `def:s02-GU`: `Γ_U` acts on the oriented edges of `𝒯_q` through `ι_q`. -/
noncomputable instance instMulActionGammaUEdge : MulAction (GammaU d q hq U) (Edge q) :=
  MulAction.compHom (Edge q) (gammaQ d q hq U)

/-- `def:s02-GU`: `Γ_U` acts on the edges `EdgeO q` (type-`0` origin) of `𝒯_q` through `ι_q`. -/
noncomputable instance instMulActionGammaUEdgeO : MulAction (GammaU d q hq U) (EdgeO q) :=
  MulAction.compHom (EdgeO q) (gammaQ d q hq U)

/-- `def:s02-GU` (`s02-GU`): `γ • v = ι_q(γ) • v` on vertices. -/
theorem gammaU_smul_vert (γ : GammaU d q hq U) (v : Vert q) : γ • v = gammaQ d q hq U γ • v :=
  rfl

/-- `def:s02-GU` (`s02-GU`): `γ • e = ι_q(γ) • e` on oriented edges. -/
theorem gammaU_smul_edge (γ : GammaU d q hq U) (e : Edge q) : γ • e = gammaQ d q hq U γ • e :=
  rfl

/-- `def:s02-GU` (`s02-GU`): `γ • e = ι_q(γ) • e` on `EdgeO q`. -/
theorem gammaU_smul_edgeO (γ : GammaU d q hq U) (e : EdgeO q) : γ • e = gammaQ d q hq U γ • e :=
  rfl

/-- `def:s02-GU`, `lem:s02-tree`(b) (`s02-GU`): the action of `Γ_U` on `𝒯_q` preserves types. -/
theorem gammaU_smul_vtype (γ : GammaU d q hq U) (v : Vert q) : vtype q (γ • v) = vtype q v := by
  have hsmul : γ • v = ((gammaQ d q hq U γ : SLq q) : GL (Fin 2) ℚ_[q]) • v := rfl
  rw [hsmul, vtype_smul, vdet_of_mem_SLq (gammaQ d q hq U γ).2, zero_add]

end Langlandscape.Tree
