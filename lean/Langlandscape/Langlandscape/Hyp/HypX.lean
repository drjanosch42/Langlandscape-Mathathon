/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Comparison.Dictionary

/-!
# Hypotheses `Hyp.X.char` and `Hyp.X.iso`: the comparison hypothesis (S05-L2)

`mathematics/chapters/s05/hypX.tex`, `hyp:s05-X` (X1)–(X3), `rem:s05-hypX-lean`, `if:s05-hypX`;
`mathematics/chapters/s05/subquot.tex`, `def:s05-Xiso`. A hypothesis is a `Prop`-valued definition,
taken as an explicit argument (never an axiom, never an instance; OVERVIEW §3.6). Registered in
`HYPOTHESES.md`.

* `CharGroupData M q p`: abstract stand-in for the tower of character groups `X_q(J_s)`, `s ≥ 0`.
* `Hyp.X.char d M p q hN hp hM hpM hD Pq hPq G`: `hyp:s05-X` (X1) ∧ (X2) ∧ (X3) for **one family** `φ`.
* `Hyp.X.iso 𝔞 L H`: `def:s05-Xiso` on abstract Hecke-module data, one level.

(X4) (`Hyp.X.gal`, `TateModuleData`) is in `Hyp/HypXGal.lean` (S05-L3).

Status: *hypothesis* (`\sthyp`). `Hyp.X.char` is geometric (Ribet 1990 Prop 3.1/3.7/3.8;
Deligne–Rapoport V.1.16/1.18; Raynaud Thm 5, at `Γ₀`-level only); not discharged
(`rem:s05-Xstatus`). `Hyp.X.iso`: Hsieh Thm 4.5, Helm Cor 8.11; its algebraic half is
`Comparison.xiso_of_gorenstein` (`prop:s05-Xiso`), freeness stays with stage 04's Hsieh hypotheses.

The file is not a `module`: it imports `Comparison/Dictionary.lean`, which depends on GL2TF.
-/

set_option autoImplicit false

namespace Langlandscape.Hyp.X

open Langlandscape.Brandt Langlandscape.Comparison

/-- `hyp:s05-X`, `rem:s05-hypX-lean` (`s05-hypX-lean`): abstract data standing for the tower of
character groups `X_q(J_s)` (`J_s` the Jacobian of `X_s`, `Γ_s = Γ₁(M p^s) ∩ Γ₀(q)`, `μ_N`-model,
Picard functoriality), `s ≥ 0`:
* `X s` a free finitely generated `ℤ`-module (`free`, `finite`);
* `act s : HeckeSym M p q s → End (X s)`, the action of the generators of `𝓗_s`;
* `u s` Grothendieck's monodromy pairing, normalised to be symmetric and positive definite
  (`u_symm`, `u_pos`; `rem:s05-illusie`);
* `β hss' : X s' → X s` for `s ≤ s'`, induced by Picard pullback along `X_{s'} → X_s`
  (contravariance of `X_q`).

**No relations field**: `lem:s05-consistency`(a) (the relations in the image of `𝓗_s` in
`End X_q(J_s) ⊗ ℚ`, e.g. `Π_q² = ⟨q⟩`) is a consequence of (X1) for any `G`, not data.
The claim "`G` *is* the character group of `J_s`" (G = character group) stays outside Lean
(hypothesis registry). -/
structure CharGroupData (M q p : ℕ) where
  /-- The character group `X_q(J_s)` at level `s`. -/
  X : ℕ → Type
  /-- `X s` is an abelian group. -/
  [addCommGroup : ∀ s, AddCommGroup (X s)]
  /-- `X s` is free over `ℤ`. -/
  free : ∀ s, Module.Free ℤ (X s)
  /-- `X s` is finitely generated over `ℤ`. -/
  finite : ∀ s, Module.Finite ℤ (X s)
  /-- The action of the generators of `𝓗_s` on `X s` (Picard functoriality). -/
  act : ∀ s, HeckeSym M p q s → Module.End ℤ (X s)
  /-- The monodromy pairing `u_s` on `X s`. -/
  u : ∀ s, LinearMap.BilinForm ℤ (X s)
  /-- `u_s` is symmetric. -/
  u_symm : ∀ s (x y : X s), u s x y = u s y x
  /-- `u_s` is positive definite. -/
  u_pos : ∀ s (x : X s), x ≠ 0 → 0 < u s x x
  /-- The transition `β_{s's} : X s' → X s` for `s ≤ s'` (Picard pullback, contravariance). -/
  β : ∀ {s s' : ℕ}, s ≤ s' → X s' →ₗ[ℤ] X s

attribute [instance] CharGroupData.addCommGroup

/-- `hyp:s05-X` (X1) ∧ (X2) ∧ (X3) (`s05-X`; `HypXchar(M;q)`), on abstract data `G : CharGroupData M q p`,
for the definite quaternion algebra `B = B_q` (`d`, `d.D = q`), levels `S s = X_B(U_1(M p^s))`
(`d.Utower M p s (hN s)`) and the dictionary `θ_s = theta …` (`def:s05-theta`: `⟨d⟩ ↦ ⟨d⟩⁻¹`,
`U_p ↦ N_{U_p}` for `s ≥ 1`, `T_p ↦ T_p` for `s = 0`, `U_q ↦ +Π_q`, `Pq` a uniformiser at `q`).
Data as in `hyp:s05-X`, except that `p ≥ 5` is not assumed (deviation; consumers add it).
There is a family of isomorphisms `φ_s : X s ≃ ℤ[S_s]⁰` such that:
* (X1) (Hecke) `φ_s ∘ h = θ_s(h) ∘ φ_s` for all `s ≥ 0` and all generators `h : HeckeSym M p q s`
  of `𝓗_s` (restriction inherited from `HeckeSym`: no `U_ℓ` for `ℓ ∣ M`, S05-L1 decision rule);
* (X2) (pairing) `⟨φ_s x, φ_s y⟩_w = u_s(x, y)` for all `s ≥ 0`, `x y ∈ X s`, with
  `⟨[e],[e']⟩_w = w_e δ_{ee'}` the Brandt pairing (`brandtPairing`, `if:s03-graph`);
* (X3) (naturality) for `s ≤ s'`, `φ_s ∘ β_{s's} = π_* ∘ φ_{s'}`, with `π_*` the pushforward
  `ℤ[S_{s'}]⁰ → ℤ[S_s]⁰` (`pushforward`; stated on the underlying elements of `ℤ[S_s]`).

**Deviation (deliberate, recorded in `rem:s05-hypX-lean` and `stage-05.md` §0):** the statement
quantifies over **one family** `φ : ∀ s, …` (`∃ φ, (∀ s, X1) ∧ (∀ s, X2) ∧ (∀ s ≤ s', X3)`), not the
tex Lean-track text `∀ s, ∃ φ`, because (X3) links `φ_s` and `φ_{s'}`.
The factor 2 (`rem:s05-factor2`) enters only when the pairings of (X2) are compared along (X3) at
`s = 0`, `M ≤ 2` (`normMap_pushforward_two`, `lem:s05-consistency`(c)); it is not part of (X3).
G = character group stays outside Lean: the claim that `G` is the tower of character groups `X_q(J_s)`
is registered in `HYPOTHESES.md`, not formalized. Vacuity (tex R6): on an abstract `G` the statement
is satisfiable by fiat (`G := ℤ[S_s]⁰`, S05-L4 `canonicalCharData`); theorems using it are honest
only as statements "for every `G` with these properties". -/
def char (d : Langlandscape.Quat.DefiniteData) (M p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hN : ∀ s, (M * p ^ s).Coprime d.D) (hp : ¬ p ∣ d.D) (hM : M ≠ 0) (hpM : ¬ p ∣ M) (hD : d.D = q)
    (Pq : (Langlandscape.Quat.QuatAlg ℚ_[q] d.a d.b)ˣ) (hPq : IsUniformiserElt d q Pq)
    (G : CharGroupData M q p) : Prop :=
  ∃ φ : ∀ s, G.X s ≃ₗ[ℤ] degZero (d.Utower M p s (hN s)) ℤ,
    (∀ s (h : HeckeSym M p q s) (x : G.X s),
      φ s (G.act s h x) = theta d M p q s (hN s) hp hM hpM hD Pq hPq h (φ s x)) ∧
    (∀ s (x y : G.X s),
      brandtPairing (d.Utower M p s (hN s)) ℤ
          ((φ s x : degZero (d.Utower M p s (hN s)) ℤ) : ZX (d.Utower M p s (hN s)) ℤ)
          ((φ s y : degZero (d.Utower M p s (hN s)) ℤ) : ZX (d.Utower M p s (hN s)) ℤ) =
        G.u s x y) ∧
    (∀ s s' (hss' : s ≤ s') (x : G.X s'),
      ((φ s (G.β hss' x) : degZero (d.Utower M p s (hN s)) ℤ) : ZX (d.Utower M p s (hN s)) ℤ) =
        pushforward (d.Utower M p s' (hN s')) (d.Utower M p s (hN s)) ℤ
          ((φ s' x : degZero (d.Utower M p s' (hN s')) ℤ) : ZX (d.Utower M p s' (hN s')) ℤ))

/-- `def:s05-Xiso` (`s05-Xiso`; `HypXiso(s)`), on abstract Hecke-module data at one level `s ≥ 1`:
`T` stands for the ordinary Hecke algebra `T_𝔪` of `Γ_s` localised at a good maximal ideal `𝔪`
(non-Eisenstein, Hsieh's residual condition `Hyp.HsiehCR`), `𝔞 = ker (T → T')` for the `q`-new
quotient `T'`, `L` for the Brandt side `e ℤ_p[S_s]_𝔪` (with `T` acting through `T' → T_{B,𝔪}` via
`θ_s`, `def:s05-theta`), `H` for `e H¹_par(Γ_s, ℤ_p)^±_𝔪`. `HypXiso(s)`: there is an isomorphism of
`T`-modules `L ≃ H[𝔞]` (`H[𝔞] = torsionBySet T H 𝔞`, the `q`-new submodule). Both sides are killed
by `𝔞`, so `T`-linear is `T'`-linear.

Abstracted: the actual Hecke algebras and modules (consumers instantiate at the intended data only);
the compatibility with `π_*` on the left and the trace on the right for `s ≤ s'` is **not** part of
this level-wise statement (`prop:s05-Xiso`: it needs `Λ`-adic freeness, Hida, and `Hyp.MordLambdaFree`;
status sketch). Source: Hsieh Thm 4.5, Helm Cor 8.11. Algebraic half: `Comparison.xiso_of_gorenstein`
gives `H[𝔞] ≃ T ⧸ 𝔞`; with `L ≃ T ⧸ 𝔞` (`L` free of rank one over `T'`, `prop:s05-Xiso`(iii), stage 04)
this yields `Hyp.X.iso 𝔞 L H`. -/
def iso {T : Type*} [CommRing T] (𝔞 : Ideal T) (L : Type*) [AddCommGroup L] [Module T L]
    (H : Type*) [AddCommGroup H] [Module T H] : Prop :=
  Nonempty (L ≃ₗ[T] Submodule.torsionBySet T H (𝔞 : Set T))

end Langlandscape.Hyp.X
