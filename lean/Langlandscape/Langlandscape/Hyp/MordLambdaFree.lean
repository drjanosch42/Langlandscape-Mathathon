/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Mathlib.RingTheory.Ideal.Operations
import Langlandscape.Ordinary.Limit

/-!
# Hypothesis `MordLambdaFree`: `M_ord(U)` is `Λ`-free with control (S04-L14b, design D-Λ)

`mathematics/chapters/s04`, `thm:s04-control`(a), `Λ`-adic half. A hypothesis is a `Prop`-valued definition,
taken as an explicit argument (never an axiom, never an instance; OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

Status: tex *proved* (`thm:s04-control`(a), proof of (a)), with cross-references Hsieh Thm 4.2 and Longo–Vigni 2011, Prop 3.6; not formalized.
No stage-05/06 plan names a consumer.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Ordinary

/-- `thm:s04-control`(a), `Λ`-adic half (`s04-control`; D-Λ): `M_ord(U) = lim_s e ℤ_[p][X_s(U)]` is a free
`Λ`-module of finite rank, `Λ = Lam ℤ_[p] G π = lim ℤ_[p][Δ_s]` (`≅ ℤ_p[[1 + pℤ_p]]`), **and** the control
isomorphisms hold at every level: for each `n` (level `s = n + 1`) the projection `M_ord(U) → e ℤ_[p][X_{n+1}]`
is onto with kernel `(ker (Λ → ℤ_[p][G n])) • M_ord(U)` (stated as the `Λ`-span of the `l • m`, `l` in the kernel,
with the `Λ`-action bound explicitly, no instance search), i.e. `M_ord ⊗_Λ ℤ_[p][G n] ≅ e ℤ_[p][X_{n+1}]`.
The `Λ`-module structure is that of `Mord.lamModule`, taken from the explicit data `(ρ, hρ)` (levelwise diamond
representations `G n →* End (e ℤ_[p][X_{n+1}])` compatible with `π_*`), since no concrete diamond action on the
`Mord` levels exists yet. Cross-reference: Hsieh, Thm 4.2; Longo–Vigni 2011, Prop 3.6 (Hida theory for definite quaternion
algebras). Non-vacuity: in the toy case `Δ_s = 1` (`G n` trivial, `Λ = ℤ_[p]`) the statement says the f.g.
`ℤ_[p]`-module `M_ord` is free with `M_ord ≅ e ℤ_[p][X_{n+1}]` at all levels, which holds when the transitions are
isomorphisms.
**Scope.** The proposition is the tex theorem only at the intended data `G n = Δ_{n+1}` (`DeltaS p (n + 1)`), `π n`
the reduction `Δ_{n+2} → Δ_{n+1}`, `ρ n` the diamond action restricted to `e ℤ_p[X_{n+1}]`, with `hρ` the
compatibility of the diamonds with `π_*`; for other data it is a different and in general false proposition, so
consumers must instantiate it only there. These data **do not exist in Lean yet**: there is no reduction map
`DeltaS p (s + 1) →* DeltaS p s`, no restriction of `permEnd (deltaAct …)` to `ordPart (UpAt …)` (the commutation
`UpHom_comm_diamondAct` of S04-L10b exists, but `Limit.lean` does not import `TowerRank.lean`), hence no `ρ`, and no
proof of `hρ`. Against the tex: the rank is `∃ r` (the tex has `r = rk e ℤ_p[X_1]`, which the `n = 0` clause
determines), and "compatibly with all Hecke operators" is not part of the statement. Discharge plan: S04-L13b compatible bases
(`e ℤ_p[X_s] ≅ ℤ_p[Δ_s]^r` compatibly with `π_*`, Nakayama) and the Iwasawa algebra (post-stage). -/
def MordLambdaFree {d : Langlandscape.Quat.DefiniteData} {M p : ℕ} [Fact p.Prime] (T : TowerHyp d M p)
    {G : ℕ → Type*} [∀ n, CommGroup (G n)] (π : ∀ n, G (n + 1) →* G n)
    (ρ : ∀ n, G n →* Module.End ℤ_[p] (T.MordLevel n))
    (hρ : ∀ n (x : G (n + 1)), (T.mordTrans n).comp (ρ (n + 1) x) = (ρ n (π n x)).comp (T.mordTrans n)) :
    Prop :=
  let inst : Module (Lam ℤ_[p] G π) ↥(Mord T) := Mord.lamModule T π ρ hρ
  (∃ r : ℕ, Nonempty (@LinearEquiv (Lam ℤ_[p] G π) (Lam ℤ_[p] G π) _ _ (RingHom.id (Lam ℤ_[p] G π))
      (RingHom.id (Lam ℤ_[p] G π)) _ _ ↥(Mord T) (Fin r → Lam ℤ_[p] G π) _ _ inst _)) ∧
    ∀ n : ℕ, Function.Surjective (Compat.proj (M := T.MordLevel) T.mordTrans n) ∧
      ∀ x : ↥(Mord T), Compat.proj (M := T.MordLevel) T.mordTrans n x = 0 ↔
        x ∈ @Submodule.span (Lam ℤ_[p] G π) ↥(Mord T) _ _ inst
          {y | ∃ l ∈ RingHom.ker (Lam.proj ℤ_[p] G π n), ∃ m : ↥(Mord T),
            y = @HSMul.hSMul _ _ _ (@instHSMul _ _ inst.toDistribMulAction.toMulAction.toSMul) l m}

end Langlandscape.Hyp
