/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Comparison.Dictionary

/-!
# Tests for `Langlandscape.Comparison.Dictionary` (S05-L1)

Shape tests for `degZero`, `theta`, `thetaDeg`, `deg_comp_thetaZX`, `heckeTHom_mem_degZero`, `deg_comp_diaZX`.
-/

set_option autoImplicit false

namespace Langlandscape.Comparison.Tests

open Langlandscape.Quat Langlandscape.Brandt
open scoped Classical

section Generic

variable (d : DefiniteData) (M p q s : ℕ) [Fact p.Prime] [Fact q.Prime] (hN : (M * p ^ s).Coprime d.D)
  (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
  (Pq : (QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)

/-- `def:s05-theta` (`s05-theta`), test: applied form of `deg_comp_thetaZX`,
`deg (θ(h) x) = thetaDeg h • deg x` on `ℤ[X_B(U_s)]`. -/
theorem test_deg_thetaZX_apply (h : HeckeSym M p q s) (x : ZX (d.Utower M p s hN) ℤ) :
    Ordinary.deg (XB (d.Utower M p s hN)) ℤ (thetaZX d M p q s hN hp hM hpM hD Pq hPq h x) =
      thetaDeg d M p q s hN hp hD h • Ordinary.deg (XB (d.Utower M p s hN)) ℤ x :=
  LinearMap.congr_fun (deg_comp_thetaZX d M p q s hN hp hM hpM hD Pq hPq h) x

/-- `def:s05-theta` (`s05-theta`), test: `θ(h)` acts on `degZero` as `thetaZX h` (`theta_apply`). -/
theorem test_theta_apply (h : HeckeSym M p q s) (x : degZero (d.Utower M p s hN) ℤ) :
    ((theta d M p q s hN hp hM hpM hD Pq hPq h x : degZero (d.Utower M p s hN) ℤ) :
        ZX (d.Utower M p s hN) ℤ) =
      thetaZX d M p q s hN hp hM hpM hD Pq hPq h (x : ZX (d.Utower M p s hN) ℤ) :=
  theta_apply d M p q s hN hp hM hpM hD Pq hPq h x

/-- `def:s05-theta` (`s05-theta`), test: `θ(U_q)` has degree factor `1`. -/
theorem test_thetaDeg_Uq : thetaDeg d M p q s hN hp hD (HeckeSym.Uq : HeckeSym M p q s) = 1 :=
  rfl

/-- `def:s05-theta` (`s05-theta`), test: `θ(⟨u⟩)` preserves degree-zero chains, from `deg_comp_diaZX`. -/
theorem test_deg_diaZX_apply (u : (ZMod (M * p ^ s))ˣ) (x : ZX (d.Utower M p s hN) ℤ) :
    Ordinary.deg (XB (d.Utower M p s hN)) ℤ (diaZX d M p s hN ℤ u x) =
      (1 : ℤ) • Ordinary.deg (XB (d.Utower M p s hN)) ℤ x :=
  LinearMap.congr_fun (deg_comp_diaZX d M p s hN ℤ u) x

end Generic

section Hecke

variable {a b : ℤ} (U : Subgroup (GL2TF.Quat.BHat a b)ˣ) (g : (GL2TF.Quat.BHat a b)ˣ) (R : Type*) [CommRing R]
  (hfin : (U ⊓ conjSub U g).relIndex U ≠ 0) [Finite (XB U)]

/-- `def:s05-theta` (`s05-theta`), test: `T_g` maps `degZero` into `degZero` (`heckeTHom_mem_degZero`). -/
theorem test_heckeTHom_mem_degZero (x : degZero U R) :
    heckeTHom U g R hfin (x : ZX U R) ∈ degZero U R :=
  heckeTHom_mem_degZero U g R hfin x.2

/-- `def:s05-theta` (`s05-theta`), test: membership in `degZero` is vanishing of `deg` (`mem_degZero`). -/
theorem test_mem_degZero (x : ZX U R) : x ∈ degZero U R ↔ Ordinary.deg (XB U) R x = 0 :=
  mem_degZero

end Hecke

end Langlandscape.Comparison.Tests
