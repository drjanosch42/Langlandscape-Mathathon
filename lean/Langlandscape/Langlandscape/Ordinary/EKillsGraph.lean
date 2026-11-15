/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Weighted
import Langlandscape.Ordinary.EKills
import Langlandscape.Quat.MassTower

/-!
# `e` kills the vertex term and `Φ^comb` on weighted graphs (S04-L11)

`mathematics/chapters/s04/ordinary.tex`, `lem:s04-ekills`(b),(c) (interface `if:s03-graph`).

**What is formalized.**
* (b) *abstract part*: if `bd : M → N` satisfies `bd ∘ Up = p • bd` (i.e. `bd` is equivariant for `Up` on `M` and
  multiplication by `p` on the vertex module `N`) and `N` is `p`-adically separated, then `ordPart Up ≤ ker bd`
  (`ordPart_le_ker_of_vertex`), and `e (ker bd) = e M` (`ordPart_ker_eq`, under `HasOrdDecomp p Up`).
  *Graph part*: for a `Graph.WGraph` all of whose edges run `a → b`, `∂ c = deg c • ([b] - [a])`, so `∂ ∘ Up = p • ∂`
  as soon as `deg ∘ Up = p • deg` (`boundary_comp_Up_of_const`); `R = ℤ_[p]` separatedness (`iInf_pow_smul_top_padic`).
  Here `ker ∂_R` (kernel over `R`) stands for `Xcomb ⊗ R`; the identification `X ⊗ R = ker ∂_R` (flatness of `ℤ_[p]`) is
  **not** formalized here.
* (c) *abstract part*: an `R`-module on which `p` is nilpotent (a finite cyclic `p`-group module) has `ordPart (p·) = ⊥`
  (`ordPart_lsmul_eq_bot_of_nilpotent`); `n • x = 0` for `n : ℕ` gives `p ^ v_p(n) • x = 0` over `ℤ_[p]`
  (`padic_pow_smul_eq_zero`); `Φ^comb ⊗ ℤ_[p]` is killed by `|E|` as soon as `Φ^comb` is, and then `e = 0` for the operator
  `p` (`ordPart_tensor_phiComb_eq_bot`). **Abstract hypotheses** (proved in the tex, not formalized here): the
  isomorphism `Φ^comb ≅ ℤ/|E|` for `w = 1` (here the input `hΦ : ∀ x, n • x = 0`) and that `U_p^*` acts on it by `p`
  (here `hU`, the column-sum computation of the tex).
* (c), valuation bound, `v_p |X_s| ≥ 2s - 2`: `card_XB_Utower` is a `ℚ`-valued mass identity under `GL2TF.Hyp.EichlerMass`; we deduce
  `p ^ (2s-2) ∣ |X_s|` (`pow_dvd_card_of_mass`) and the valuation bound (`vp_card_XB_Utower_ge`) from it **plus** the
  arithmetic input `hlev : ψ(M p^s) φ(M p^s) = p^(2s-2) · k` (`k : ℕ`), the `p`-part of the level index, which is *not*
  proved here (it needs multiplicativity of `ψ`, `φ` and the case `p ∣ M`).

Status: *formalized* for the abstract parts; hypotheses as listed.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Langlandscape.Ordinary

open Langlandscape.Quat

noncomputable section

section Abstract

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- `lem:s04-ekills`(b),(c) (`s04-ekills`), helper: the `k`-th power of multiplication by `p` is multiplication by `p ^ k`. -/
theorem pow_lsmul_apply (p : R) (k : ℕ) (m : N) :
    ((LinearMap.lsmul R N p) ^ k) m = (p ^ k) • m := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply, ih, LinearMap.lsmul_apply, smul_smul]

/-- `lem:s04-ekills`(b) (`s04-ekills`): if `N` is `p`-adically separated, multiplication by `p` has `ordPart = ⊥`. -/
theorem ordPart_lsmul_eq_bot (p : R)
    (hsep : ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R N) = ⊥) :
    ordPart (LinearMap.lsmul R N p) = ⊥ := by
  refine ordPart_eq_bot_of_topNilpotent (p := p) (fun k => ⟨k, ?_⟩) hsep
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
  rw [pow_lsmul_apply]
  exact Submodule.smul_mem_pointwise_smul y (p ^ k) ⊤ trivial

/-- `lem:s04-ekills`(c) (`s04-ekills`), abstract part: if `p ^ m` kills `N` (e.g. `N` a finite cyclic `p`-group module,
`m = v_p |N|`), then `ordPart (p ·) = ⊥`. -/
theorem ordPart_lsmul_eq_bot_of_nilpotent (p : R) {m : ℕ} (h : ∀ x : N, (p ^ m : R) • x = 0) :
    ordPart (LinearMap.lsmul R N p) = ⊥ := by
  refine ordPart_lsmul_eq_bot p ?_
  refine eq_bot_iff.2 (le_trans (iInf_le _ m) ?_)
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [h y]
  exact Submodule.zero_mem _

/-- `lem:s04-ekills`(b) (`s04-ekills`), abstract part: if `bd ∘ Up = p • bd` (`bd` is `Up`-equivariant for the action
`p` on the target) and the target is `p`-adically separated, then `e` kills the vertex term: `ordPart Up ≤ ker bd`. -/
theorem ordPart_le_ker_of_vertex (bd : M →ₗ[R] N) (Up : Module.End R M) (p : R)
    (hbd : bd.comp Up = p • bd) (hsep : ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R N) = ⊥) :
    ordPart Up ≤ LinearMap.ker bd := by
  intro x hx
  have hle := ordPart_map_le_of_comm bd Up (LinearMap.lsmul R N p) (fun y => by
    have := LinearMap.congr_fun hbd y
    simpa [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.lsmul_apply] using this)
  have hmem : bd x ∈ ordPart (LinearMap.lsmul R N p) := hle ⟨x, hx, rfl⟩
  rw [ordPart_lsmul_eq_bot p hsep, Submodule.mem_bot] at hmem
  exact hmem

/-- `lem:s04-ekills`(b) (`s04-ekills`), helper: powers of `T` commute. -/
theorem eg_pow_comm (T : Module.End R M) (n k : ℕ) (y : M) :
    (T ^ k) ((T ^ n) y) = (T ^ n) ((T ^ k) y) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.pow_pow_self T k n).eq]

/-- `lem:s04-ekills`(b) (`s04-ekills`), helper: `ordPart T` is stable under all powers of `T`. -/
theorem eg_pow_mem_ordPart (T : Module.End R M) {x : M} (hx : x ∈ ordPart T) (n : ℕ) :
    (T ^ n) x ∈ ordPart T := by
  rw [mem_ordPart]
  intro k
  obtain ⟨y, hy⟩ := mem_ordPart.1 hx k
  refine ⟨(T ^ n) y, ?_⟩
  rw [← hy]
  exact eg_pow_comm T n k y

/-- `lem:s04-ekills`(b) (`s04-ekills`): if `K` is `T`-stable, contains `ordPart T`, and `T` has an ordinary decomposition,
then `ordPart (T|_K) = ordPart T` (as a submodule of `M`): `e K = e M`. -/
theorem ordPart_restrict_eq (p : R) (T : Module.End R M) (K : Submodule R M)
    (hK : ∀ x ∈ K, T x ∈ K) (hle : ordPart T ≤ K) (hdec : HasOrdDecomp p T) :
    (ordPart (T.restrict hK)).map K.subtype = ordPart T := by
  have hcomm : K.subtype ∘ₗ (T.restrict hK) = T ∘ₗ K.subtype := LinearMap.ext fun _ => rfl
  apply le_antisymm
  · exact ordPart_map_le_of_comm _ _ _ (fun _ => rfl)
  · intro m hm
    have hc : IsCompl (ordPart T) (nilPart p T) := hdec
    refine ⟨⟨m, hle hm⟩, mem_ordPart.2 fun n => ?_, rfl⟩
    obtain ⟨z, hz⟩ := mem_ordPart.1 hm n
    have hz' : z ∈ ordPart T ⊔ nilPart p T := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz'
    have hbo : (T ^ n) b ∈ ordPart T := by
      have h1 : (T ^ n) b = m - (T ^ n) a := by
        rw [← hz, map_add]; abel
      rw [h1]
      exact Submodule.sub_mem _ hm (eg_pow_mem_ordPart T ha n)
    have hbn : (T ^ n) b ∈ nilPart p T := nilPart_pow_mem p T hb n
    have hb0 : (T ^ n) b = 0 := by
      have : (T ^ n) b ∈ ordPart T ⊓ nilPart p T := ⟨hbo, hbn⟩
      rw [hc.inf_eq_bot] at this
      exact this
    refine ⟨⟨a, hle ha⟩, ?_⟩
    apply Subtype.ext
    have := map_pow_apply hcomm n ⟨a, hle ha⟩
    rw [map_add, hb0, add_zero] at hz
    exact this.trans hz

/-- `lem:s04-ekills`(b) (`s04-ekills`), helper: `ker bd` is `Up`-stable when `bd ∘ Up = p • bd`. -/
theorem eg_ker_stable (bd : M →ₗ[R] N) (Up : Module.End R M) (p : R)
    (hbd : bd.comp Up = p • bd) : ∀ x ∈ LinearMap.ker bd, Up x ∈ LinearMap.ker bd := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have := LinearMap.congr_fun hbd x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, hx, smul_zero] at this
  exact this

/-- `lem:s04-ekills`(b) (`s04-ekills`): `e (ker bd) = e M` for a `Up`-equivariant `bd` with `bd ∘ Up = p • bd` into a
`p`-adically separated target, given the ordinary decomposition of `Up`. -/
theorem ordPart_ker_eq (bd : M →ₗ[R] N) (Up : Module.End R M) (p : R)
    (hbd : bd.comp Up = p • bd) (hsep : ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R N) = ⊥)
    (hdec : HasOrdDecomp p Up) :
    (ordPart (Up.restrict (eg_ker_stable bd Up p hbd))).map (LinearMap.ker bd).subtype = ordPart Up :=
  ordPart_restrict_eq p Up _ _ (ordPart_le_ker_of_vertex bd Up p hbd hsep) hdec

end Abstract

section Separated

/-- `lem:s04-ekills`(b) (`s04-ekills`): if `R` is `p`-adically separated (`∀ r, (∀ k, p ^ k ∣ r) → r = 0`), so is every
free module `ι →₀ R` (the vertex module). -/
theorem iInf_pow_smul_top_finsupp {R : Type*} [CommRing R] {ι : Type*} (p : R)
    (hR : ∀ r : R, (∀ k : ℕ, p ^ k ∣ r) → r = 0) :
    ⨅ k : ℕ, (p ^ k : R) • (⊤ : Submodule R (ι →₀ R)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_iInf] at hx
  rw [Submodule.mem_bot]
  ext i
  rw [Finsupp.zero_apply]
  refine hR _ fun k => ?_
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hx k)
  exact ⟨y i, by rw [← hy, Finsupp.smul_apply, smul_eq_mul]⟩

/-- `lem:s04-ekills`(b) (`s04-ekills`): `ℤ_[p]` is `p`-adically separated. -/
theorem padic_separated (p : ℕ) [Fact p.Prime] (r : ℤ_[p]) (h : ∀ k : ℕ, (p : ℤ_[p]) ^ k ∣ r) :
    r = 0 := by
  by_contra hr
  have := (PadicInt.mem_span_pow_iff_le_valuation r hr (r.valuation + 1)).1
    (Ideal.mem_span_singleton.2 (h _))
  omega

/-- `lem:s04-ekills`(b) (`s04-ekills`): the vertex module `ι →₀ ℤ_[p]` is `p`-adically separated. -/
theorem iInf_pow_smul_top_padic (p : ℕ) [Fact p.Prime] {ι : Type*} :
    ⨅ k : ℕ, ((p : ℤ_[p]) ^ k : ℤ_[p]) • (⊤ : Submodule ℤ_[p] (ι →₀ ℤ_[p])) = ⊥ :=
  iInf_pow_smul_top_finsupp _ (padic_separated p)

end Separated

section Graph

variable {R : Type*} [CommRing R]

/-- `lem:s04-ekills`(b) (`s04-ekills`, `if:s03-graph`): if all edges of `G` run from `a` to `b`, then
`∂ c = deg c • ([b] - [a])` (the `U_p`-equivariance of `∂` comes from this). -/
theorem boundary_eq_deg_smul (G : Langlandscape.Graph.WGraph) (a b : G.V)
    (hs : ∀ e, G.src e = a) (ht : ∀ e, G.tgt e = b) (c : G.E →₀ R) :
    Langlandscape.Graph.WGraph.boundary G R c =
      deg G.E R c • (Finsupp.single b (1 : R) - Finsupp.single a 1) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, add_smul, hf, hg]
  | single e r =>
    rw [Langlandscape.Graph.WGraph.boundary_single, hs, ht, deg_single, smul_sub]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- `lem:s04-ekills`(b) (`s04-ekills`, `if:s03-graph`): for a weighted graph all of whose edges run `a → b` (the DR graph
`𝒢_DR,q(UU_s)` with `V = {v₀, v₁}`), `∂ ∘ U_p = p • ∂` as soon as `deg ∘ U_p = p • deg`; i.e. `∂` is `U_p`-equivariant for
the action `p` on the vertex module. -/
theorem boundary_comp_Up_of_const (G : Langlandscape.Graph.WGraph) (a b : G.V)
    (hs : ∀ e, G.src e = a) (ht : ∀ e, G.tgt e = b)
    (Up : (G.E →₀ R) →ₗ[R] (G.E →₀ R)) (p : R) (hUp : (deg G.E R).comp Up = p • deg G.E R) :
    (Langlandscape.Graph.WGraph.boundary G R).comp Up = p • Langlandscape.Graph.WGraph.boundary G R := by
  refine LinearMap.ext fun c => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  rw [boundary_eq_deg_smul G a b hs ht, deg_Up_apply Up p hUp c, mul_smul,
    boundary_eq_deg_smul G a b hs ht]

/-- `lem:s04-ekills`(b) (`s04-ekills`, `if:s03-graph`): for `R = ℤ_[p]`, a weighted graph with all edges `a → b` and `U_p`
with `deg ∘ U_p = p • deg`: `e` kills the vertex term, `ordPart U_p ≤ ker ∂`. -/
theorem ordPart_le_ker_boundary (G : Langlandscape.Graph.WGraph) (a b : G.V)
    (hs : ∀ e, G.src e = a) (ht : ∀ e, G.tgt e = b) (p : ℕ) [Fact p.Prime]
    (Up : (G.E →₀ ℤ_[p]) →ₗ[ℤ_[p]] (G.E →₀ ℤ_[p]))
    (hUp : (deg G.E ℤ_[p]).comp Up = (p : ℤ_[p]) • deg G.E ℤ_[p]) :
    ordPart Up ≤ LinearMap.ker (Langlandscape.Graph.WGraph.boundary G ℤ_[p]) :=
  ordPart_le_ker_of_vertex _ Up (p : ℤ_[p]) (boundary_comp_Up_of_const G a b hs ht Up _ hUp)
    (iInf_pow_smul_top_padic p)

end Graph

section Phi

/-- `lem:s04-ekills`(c) (`s04-ekills`): over `ℤ_[p]`, `n • x = 0` for `n ≠ 0` implies `p ^ v_p(n) • x = 0`
(`n = p ^ v · n'` with `n'` a unit). -/
theorem padic_pow_smul_eq_zero (p : ℕ) [Fact p.Prime] {N : Type*} [AddCommGroup N] [Module ℤ_[p] N]
    {n : ℕ} (hn : n ≠ 0) {x : N} (hx : (n : ℤ_[p]) • x = 0) :
    ((p : ℤ_[p]) ^ padicValNat p n) • x = 0 := by
  have hp : p.Prime := Fact.out
  have hq : p ^ n.factorization p * (n / p ^ n.factorization p) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  have hv : n.factorization p = padicValNat p n := Nat.factorization_def n hp
  have hunit : IsUnit (((n / p ^ n.factorization p : ℕ)) : ℤ_[p]) :=
    PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 (Nat.coprime_ordCompl hp hn))
  have hcast : (n : ℤ_[p]) =
      ((n / p ^ n.factorization p : ℕ) : ℤ_[p]) * (p : ℤ_[p]) ^ n.factorization p := by
    have h := congrArg (Nat.cast : ℕ → ℤ_[p]) hq
    push_cast at h
    exact h.symm.trans (mul_comm _ _)
  rw [← hv]
  obtain ⟨u, hu⟩ := hunit
  have h1 : (((n / p ^ n.factorization p : ℕ)) : ℤ_[p]) •
      ((p : ℤ_[p]) ^ n.factorization p • x) = 0 := by
    rw [smul_smul, ← hcast]
    exact hx
  calc (p : ℤ_[p]) ^ n.factorization p • x
      = (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((n / p ^ n.factorization p : ℕ) : ℤ_[p])) •
          ((p : ℤ_[p]) ^ n.factorization p • x) := by
        rw [← hu]; simp
    _ = 0 := by rw [mul_smul, h1, smul_zero]

/-- `lem:s04-ekills`(c) (`s04-ekills`): if `n • x = 0` for all `x : Φ` (`Φ = Φ^comb`, `n = |E|`), then `(n : ℤ_[p])`
kills `ℤ_[p] ⊗_ℤ Φ`. -/
theorem tensor_natCast_smul_eq_zero (p : ℕ) [Fact p.Prime] {Φ : Type*} [AddCommGroup Φ] {n : ℕ}
    (hΦ : ∀ x : Φ, (n : ℤ) • x = 0) (t : TensorProduct ℤ ℤ_[p] Φ) : (n : ℤ_[p]) • t = 0 := by
  induction t with
  | tmul a x =>
    have e : (n : ℤ_[p]) = ((n : ℤ) : ℤ_[p]) := (Int.cast_natCast n).symm
    rw [e, Int.cast_smul_eq_zsmul ℤ_[p] (n : ℤ)]
    have h := TensorProduct.tmul_smul (R := ℤ) (n : ℤ) a x
    exact h.symm.trans (by rw [hΦ x, TensorProduct.tmul_zero])
  | add t₁ t₂ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]

/-- `lem:s04-ekills`(c) (`s04-ekills`, `if:s03-graph`): for a weighted graph `G`, if `Φ^comb(G)` is killed by `n ≠ 0`
(tex: `Φ^comb ≅ ℤ/|E|` for `w = 1`, `n = |E|`) and `U_p^*` acts on `Φ^comb ⊗ ℤ_[p]` by `p` (tex: column sums), then
`e = 0`: `ordPart U_p^* = ⊥`. The two hypotheses `hΦ`, `hU` are the abstract (non-formalized) inputs. -/
theorem ordPart_tensor_phiComb_eq_bot (G : Langlandscape.Graph.WGraph) (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : n ≠ 0) (hΦ : ∀ x : G.PhiComb, (n : ℤ) • x = 0)
    (Ustar : Module.End ℤ_[p] (TensorProduct ℤ ℤ_[p] G.PhiComb))
    (hU : Ustar = LinearMap.lsmul ℤ_[p] (TensorProduct ℤ ℤ_[p] G.PhiComb) (p : ℤ_[p])) :
    ordPart Ustar = ⊥ := by
  subst hU
  exact ordPart_lsmul_eq_bot_of_nilpotent (p : ℤ_[p]) (m := padicValNat p n) fun t =>
    padic_pow_smul_eq_zero p hn (tensor_natCast_smul_eq_zero p hΦ t)

end Phi

section Mass

/-- `lem:s04-ekills`(c), `v_p |X_s| ≥ 2s - 2` (`s04-ekills`): from a mass identity `c = φ(D)/24 · m` in `ℚ` with
`m = p^(2s-2) · k` and `p ≥ 5` prime, `p ^ (2s-2) ∣ c`. -/
theorem pow_dvd_card_of_mass {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {c D s k : ℕ} {m : ℚ}
    (hmass : (c : ℚ) = (Nat.totient D : ℚ) / 24 * m)
    (hm : m = (p : ℚ) ^ (2 * s - 2) * (k : ℚ)) : p ^ (2 * s - 2) ∣ c := by
  have h24 : (c : ℚ) * 24 = (Nat.totient D : ℚ) * ((p : ℚ) ^ (2 * s - 2) * k) := by
    rw [hmass, hm]; ring
  have h24' : c * 24 = Nat.totient D * (p ^ (2 * s - 2) * k) := by exact_mod_cast h24
  have hdvd : p ^ (2 * s - 2) ∣ c * 24 := ⟨Nat.totient D * k, by rw [h24']; ring⟩
  have hcop : Nat.Coprime (p ^ (2 * s - 2)) 24 := by
    refine Nat.Coprime.pow_left _ ?_
    have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
    have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
    have h24e : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h24e]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 h2) h3
  exact hcop.dvd_of_dvd_mul_right hdvd

/-- `lem:s04-ekills`(c), `v_p |X_s| ≥ 2s - 2` (`s04-ekills`): from `Quat.card_XB_Utower` (under
`GL2TF.Hyp.EichlerMass`) and the arithmetic input `hlev : ψ(M p^s) φ(M p^s) = p^(2s-2) · k` (`k : ℕ`; **not** proved here),
`2s - 2 ≤ v_p |X_s|`. -/
theorem vp_card_XB_Utower_ge (d : DefiniteData) {M p s : ℕ}
    (hM : GL2TF.Hyp.EichlerMass d.a d.b d.D d.O)
    (hpp : p.Prime) (hp : 5 ≤ p) (hs : 1 ≤ s) (hM0 : M ≠ 0) (hpD : p.Coprime d.D)
    (hN : (M * p ^ s).Coprime d.D)
    (hlev : ∃ k : ℕ, GL2TF.Explicit.dedekindPsi (M * p ^ s) * (Nat.totient (M * p ^ s) : ℚ) =
      (p : ℚ) ^ (2 * s - 2) * k) :
    2 * s - 2 ≤ padicValNat p (Nat.card (XB (d.Utower M p s hN))) := by
  haveI : Fact p.Prime := ⟨hpp⟩
  have key := card_XB_Utower d hM hpp hp hs hM0 hpD hN
  have hD0 : 0 < d.D := Nat.pos_of_ne_zero d.squarefree.ne_zero
  have hmp0 : 0 < M * p ^ s := Nat.pos_of_ne_zero (mul_ne_zero hM0 (pow_ne_zero _ hpp.ne_zero))
  have hpsi := Langlandscape.Quat.dedekindPsi_pos hmp0.ne'
  have hpos : (0 : ℚ) < (Nat.totient d.D : ℚ) / 24 *
      (GL2TF.Explicit.dedekindPsi (M * p ^ s) * (Nat.totient (M * p ^ s) : ℚ)) :=
    mul_pos (div_pos (Nat.cast_pos.2 (Nat.totient_pos.2 hD0)) (by norm_num))
      (mul_pos hpsi (Nat.cast_pos.2 (Nat.totient_pos.2 hmp0)))
  have hc0 : Nat.card (XB (d.Utower M p s hN)) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at key
    exact hpos.ne key
  obtain ⟨k, hk⟩ := hlev
  have hdvd := pow_dvd_card_of_mass hpp hp key hk
  exact (padicValNat_dvd_iff_le hc0).1 hdvd

end Mass

end

end Langlandscape.Ordinary
