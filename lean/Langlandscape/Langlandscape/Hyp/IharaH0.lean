/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Ribet.IharaH0

/-!
# Hypothesis `IharaH0`: Ihara (iii), `coker α ≅ V_{U^1_p}` via `ε` (S03-L11)

`mathematics/chapters/s03/4-ihara.tex`, `thm:s03-iharaH0`(a), conventions (C1)–(C6), interface `if:s03-ihara`.
A hypothesis is a `Prop`-valued definition, taken as an explicit argument (never an axiom, never an instance;
OVERVIEW §3.6). Registered in `HYPOTHESES.md`.

Statement (clause (a) only): under the standing hypotheses of `ss:s03-ihara` (`p ≥ 5`, `p ≠ q`, `p ∤ D`, `U`
`q`-admissible and factorisable at `p`, `BG(U, q)` connected (condition (iii) of `prop:s02-BG`), `V` a finitely
generated `ℤ_p`-module with a continuous action of `U_p` (`ρ` factors through `u ↦ u_p`), `−1 ∈ U` acting trivially),
the map `Ribet.epsilon : Brandt(U, V)² → V_{U^1_p}` is well defined (`Ribet.EpsWellDefined`) and surjective, and
`ker ε = im Ribet.alphaV`.

Translation notes.
* "factorisable at `p`" is `∃ K, Tree.HasFactorAt d p hp K U` (`U = U^{(p)} × ι_p^{-1}(K)`).
* "`ρ` is a `U_p`-action": `ρ(u) = 1` whenever `u_p = 1`.
* continuity (`V` finitely generated, `p`-adic topology): for every `n` there is an open subgroup `W` of `B̂^×` such
  that `u ∈ U ∩ W` acts trivially on `V / p^n V`.
* "If `−1 ∈ U`, then `−1` acts trivially on `V`" (standing hypothesis; it loses nothing, see the tex).
* `U^1_p`-coinvariants are taken for `{u ∈ U : det ι_p(u_p) = 1}`; under the two previous items they are the tex's.
* Clause (b) (`T_g ↦ deg(UgU) [ℓ^{v_ℓ(Nrd g)}]`, cohomological operators, exponent `+1`) and the identification with
  `H_0(Γ_U, V)` are **not** part of the Lean statement (deferred to S04-L15a, when Hecke operators with coefficients
  were missing; they now exist, `Brandt/HeckeCoeff.lean`, `Brandt/UpCoeff.lean`, but clause (b) is still not stated).
* Full strong approximation (`Hyp.SA`) and the density of `Γ_U` in `U^1_p` (`if:s02-coh`, (R4)) are inputs of the
  proof, not premises: the statement is the theorem of the tex, which is unconditional given the cited results.

Faithfulness (A18). `Tree.IsQLevel` uses "`U ≤ Ô^×` of finite index" in place of "compact open" (see the module
docstring of `Langlandscape/Tree/Admissible.lean` and `Hyp.SA`), so formally the statement also covers finite-index,
possibly non-open `U`. The proof uses `U` only through `U^1 = U ∩ B̂^1`, finite indices and strong approximation
(`Hyp.SA`, which carries the Nikolov–Segal note for such `U`); for the project's levels (`Ô^×`, `U_0(N)`, `U_1(N)`,
`U_s`, all open) nothing changes. The continuity and `−1` premises are mathematically redundant (the first by Serre's
openness of finite-index subgroups of `GL₂(ℤ_p)`-type groups, the second because both sides vanish on `V^−`); they are
kept for fidelity to the tex. Stage-04 note: discharging the continuity premise for `V_k` needs the openness of
`ker(Ô^× → GL₂(ℤ/p^n))`.

Which part is cited. In the conclusion, `Ribet.EpsWellDefined` (step (a1)), `ε ∘ α = 0` (step (a2), i.e.
`range α ≤ ker ε`) and surjectivity (step (a3)) are *proved* outright in the tex (elementary, not yet formalized);
only `ker ε ≤ range α` (step (a4)) is *proved modulo cited*: it uses `cor:s03-ihara`(ii′), hence the density of `Γ_U` in
`U^1_p` (full strong approximation, (R4)). Follow-up (not this WP): prove the elementary conjuncts and reduce the
hypothesis to `ker ε ≤ range alphaV`.

Status: tex *proved modulo cited* (`thm:s03-iharaH0`; step (a4) uses `cor:s03-ihara`(ii′) and the density of `Γ_U`
in `U^1_p`); not formalized. Discharge plan: post-hackathon (needs `Hyp.SA` and `if:s02-coh`).
-/

set_option autoImplicit false

namespace Langlandscape.Hyp

open Langlandscape.Quat Langlandscape.Brandt

/-- `thm:s03-iharaH0`(a), `if:s03-ihara`: Ihara (iii) with coefficients. Let `p ≥ 5`, `p ≠ q`, `p ∤ D`, `U`
`q`-admissible, factorisable at `p`, with `BG(U, q)` connected, and `V` a finitely generated `ℤ_p`-module with a
continuous `U_p`-action `c.ρ` on which `−1 ∈ U` acts trivially. Then `ε = Ribet.epsilon c p hp` is well defined,
surjective, and `ker ε = im α` for `α = Ribet.alphaV c hU = (−s_{0*}, s_{1*})`; hence `coker α ≅ V_{U^1_p}`.
Clause (b) (Hecke action) is not included. Status: tex *proved modulo cited* (`\stpmc`; only `ker ε ≤ im α` uses the
cited density of `Γ_U` in `U^1_p`); classical analogue DT p. 445–446. Not formalized; post-hackathon. -/
def IharaH0 (d : DefiniteData) (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ d.D) (U : Subgroup (BHat d.a d.b)ˣ)
    (hU : Tree.IsQLevel d q hq U) (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ d.D)
    (V : Type*) [AddCommGroup V] [Module ℤ_[p] V] (c : Ribet.CoeffData d q hq U ℤ_[p] V) : Prop :=
  5 ≤ p → p ≠ q → Tree.IsQAdmissible d q hq U →
    (∃ K : Subgroup (GL (Fin 2) ℚ_[p]), Tree.HasFactorAt d p hp K U) →
    Tree.BGConnected d q hq U hU →
    Module.Finite ℤ_[p] V →
    (∀ u : U, localComponent d p hp (u : (BHat d.a d.b)ˣ) = 1 → c.ρ u = 1) →
    (∀ n : ℕ, ∃ W : Subgroup (BHat d.a d.b)ˣ, IsOpen (W : Set (BHat d.a d.b)ˣ) ∧
      ∀ u : U, (u : (BHat d.a d.b)ˣ) ∈ W → ∀ v : V, ∃ w : V, c.ρ u v - v = ((p : ℤ_[p]) ^ n) • w) →
    (∀ u : U, (u : (BHat d.a d.b)ˣ) = -1 → c.ρ u = 1) →
    Ribet.EpsWellDefined c p hp ∧ Function.Surjective (Ribet.epsilon c p hp) ∧
      LinearMap.ker (Ribet.epsilon c p hp) = LinearMap.range (Ribet.alphaV c hU)

end Langlandscape.Hyp
