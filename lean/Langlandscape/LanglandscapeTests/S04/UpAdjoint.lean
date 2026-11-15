/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Brandt.UpAdjoint

/-! Shape tests for `Langlandscape.Brandt.UpAdjoint` (S04-L5): `U'_p`, `U_p^*`, `⟨p⟩_M`. -/

set_option autoImplicit false

namespace LanglandscapeTests.S04.UpAdjoint

open Langlandscape.Quat Langlandscape.Brandt

section Generic

variable (d : DefiniteData) (M p s : ℕ) [Fact p.Prime] (hN : (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D)
  (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hs : 1 ≤ s) (R : Type) [CommRing R]

/-- `lem:s01-Up`(d) (`s01-Up`), test: combining the adjoint with `U_p^* = ⟨p⟩_M U'_p`,
`⟨U_p a, b⟩ = ⟨a, ⟨p⟩_M U'_p b⟩` on `R[X_B(U_1(M p^s))]`. -/
theorem test_brandtPairing_UpHom_diamondM_UpPrime [Finite (XB (d.Utower M p s hN))]
    (x y : ZX (d.Utower M p s hN) R) :
    brandtPairing (d.Utower M p s hN) R (UpHom d M p s hN hp hM hpM hs R x) y =
      brandtPairing (d.Utower M p s hN) R x
        (diamondM d M p s hN hp R (UpPrime d M p s hN hp hM hpM hs R y)) := by
  rw [brandtPairing_UpHom_UpStar hM hpM hs, UpStar_eq_diamondM_UpPrime hM hpM hs, LinearMap.comp_apply]

include hM hpM in
/-- `lem:s01-Up`(c),(d) (`s01-Up`), test: the finiteness lemmas of `U'_p` and `U_p^*` apply at every tower level
`s ≥ 1`, here at `s + 1`. -/
theorem test_relIndex_succ (hN' : (M * p ^ (s + 1)).Coprime d.D) :
    (d.Utower M p (s + 1) hN' ⊓ conjSub (d.Utower M p (s + 1) hN')
        (localEmbedGL d p hp (Langlandscape.Local.diagOneP p))).relIndex (d.Utower M p (s + 1) hN') ≠ 0 ∧
      (d.Utower M p (s + 1) hN' ⊓ conjSub (d.Utower M p (s + 1) hN')
        (localEmbedGL d p hp (Langlandscape.Local.varpiDiag p))⁻¹).relIndex (d.Utower M p (s + 1) hN') ≠ 0 :=
  ⟨UpPrime_relIndex_ne_zero hM hpM (Nat.le_add_left 1 s),
    UpStar_relIndex_ne_zero hM hpM (Nat.le_add_left 1 s)⟩

/-- `lem:s01-Up`(c), trace half (`s01-Up`), test: applied form of `UpPrime_comm_trace`,
`tr (U'_p f) = U'_p (tr f)` for `f ∈ R^{X_B(U_{s+1})}`. -/
theorem test_UpPrime_comm_trace_apply (hN' : (M * p ^ (s + 1)).Coprime d.D)
    (f : ZXdual (d.Utower M p (s + 1) hN') R) :
    trace (d.Utower M p (s + 1) hN') (d.Utower M p s hN) R (relIndex_Utower_succ_ne_zero hM)
        (UpPrimeDual d M p (s + 1) hN' hp hM hpM (Nat.le_add_left 1 s) R f) =
      UpPrimeDual d M p s hN hp hM hpM hs R
        (trace (d.Utower M p (s + 1) hN') (d.Utower M p s hN) R (relIndex_Utower_succ_ne_zero hM) f) :=
  LinearMap.congr_fun (UpPrime_comm_trace hM hpM hs) f

end Generic

end LanglandscapeTests.S04.UpAdjoint
