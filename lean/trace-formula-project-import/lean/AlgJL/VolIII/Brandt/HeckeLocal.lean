import AlgJL.Meta.Tag
import AlgJL.VolIII.Brandt.Hecke
import AlgJL.VolI.P1.HeckeBasis
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The local Hecke embedding, recursion and commutativity (Q3 U3, items 28–33)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §3, second half (items 28–33 of `docs/sprints/Q3-plan.md` §1.2).
Exit `III.brandt.thm:hecke-commutative`.

Design (plan §1.1 item 5, traps 2, 6, 8, risk Q3-R1):
* "Eichler data" are the binders `O₀ : MaxOrder a b`, `hD : RamifiedExactly a b D`, `φ : LevelStructure O₀.1 M`
  (`[NeZero M]`), and `O = eichlerOrder φ` (Q2 items 27, 14, 30, 31);
* `Θ_p φ (x) := φ(ι_p(x_p)) · 1[x_q ∈ O_q^× for all q ≠ p]` with `ι_p` chosen from Q2's
  `III.qalg.thm:maximal-order-local-split` for `O₀` (at `p ∤ M`, `O_p = O₀,p`: B-only lemma
  `III.brandt.lem:eichler-local-eq-maximal`, W3) and `x_p` the image of `x` in `B_p` (coordinatewise evaluation).
  `Θ_p` is defined on all functions `GL₂(ℚ_p) → ℂ`; on Vol I's spherical Hecke algebra (`I.satake.def:spherical-hecke-algebra`,
  `K_p = 𝐊[ℚ_[p]]`) it is the algebra homomorphism of `III.brandt.thm:local-hecke-embedding-hom`;
* `ϖ_p Ô^× = ι(p) Ô^×` (the idele `p` differs from `ϖ_p` by an element of `Ẑ^× ⊆ Ô^×`); `ι(p)` is written inline.

Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

open GL2TF.HeckeModule

/-- For Eichler data `(O₀, D, φ)` with `O = O₀(M; φ)` and a prime `p ∤ D`: the map
`Θ_p : (GL₂(ℚ_p) → ℂ) → (B̂^× → ℂ)`, `Θ_p(φ)(x) = φ(ι_p(x_p)) · 1[x_q ∈ O_q^× for every prime q ≠ p]`,
with `ι_p : B_p ≃ M₂(ℚ_p)`, `ι_p(O₀,p) = M₂(ℤ_p)` (`III.qalg.thm:maximal-order-local-split`). -/
@[tf_id "III.brandt.def:local-hecke-embedding"]
noncomputable def localHeckeEmbedding {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b) (hD : RamifiedExactly a b D)
    (φ : LevelStructure O₀.1 M) (p : Nat.Primes) (hpD : ¬ (p : ℕ) ∣ D) (Φ : GL (Fin 2) ℚ_[p] → ℂ) :
    (BHat a b)ˣ → ℂ :=
  fun x =>
    Φ (Units.map ((Classical.choose (maximalOrder_local_split O₀ hD p hpD)).toRingEquiv.toRingHom.comp
        (baseChange a b (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) p))).toMonoidHom x) *
      Set.indicator
        {x : (BHat a b)ˣ | ∀ q : Nat.Primes, q ≠ p →
          baseChange a b (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q) (x : BHat a b) ∈
              localLattice q (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) ∧
            baseChange a b (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q)
                ((x⁻¹ : (BHat a b)ˣ) : BHat a b) ∈
              localLattice q (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra)}
        (fun _ => (1 : ℂ)) x

/-- For every order, every prime `p` and `k ≥ 2`: `1_{ι(p)Ô^×} · f = p^{k−2} f` for `f ∈ M_k(O; s)`. -/
@[tf_id "III.brandt.lem:central-translation"]
theorem central_translation {K : Type*} [Field K] [CharZero K] {a b : ℤ} (O : QOrder a b) (s : Splitting K a b)
    (k : ℕ) (hk : 2 ≤ k) (p : Nat.Primes) :
    ∀ f ∈ quatForms O s k,
      heckeAct (U := orderCompletionUnits O)
          ({x : (BHat a b)ˣ | ∃ u ∈ orderCompletionUnits O,
            x = Units.map (finEmbed a b).toMonoidHom
              (Units.map (algebraMap ℚ (QuatAlg ℚ a b)).toMonoidHom
                (Units.mk0 ((p : ℕ) : ℚ) (Nat.cast_ne_zero.mpr p.2.ne_zero))) * u}.indicator
            (1 : (BHat a b)ˣ → ℤ)) f =
        ((p : ℕ) : K) ^ (k - 2) • f := by
  intro f hf
  set γ : (QuatAlg ℚ a b)ˣ := Units.map (algebraMap ℚ (QuatAlg ℚ a b)).toMonoidHom
    (Units.mk0 ((p : ℕ) : ℚ) (Nat.cast_ne_zero.mpr p.2.ne_zero)) with hγ
  set P : (BHat a b)ˣ := Units.map (finEmbed a b).toMonoidHom γ with hP
  have hγval : ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = ((p : ℕ) : QuatAlg ℚ a b) := by
    simp [hγ]
  have hPval : ((P : (BHat a b)ˣ) : BHat a b) = ((p : ℕ) : BHat a b) := by
    rw [hP, Units.coe_map]
    show finEmbed a b (γ : QuatAlg ℚ a b) = _
    rw [hγval, map_natCast]
  have hcomm : ∀ x : (BHat a b)ˣ, x * P = P * x := by
    intro x
    ext
    rw [Units.val_mul, Units.val_mul, hPval]
    exact (Nat.cast_comm _ _).symm
  have hbasic := symPower_basic K (k - 2)
  have hinv : ∀ x u : (BHat a b)ˣ, u ∈ orderCompletionUnits O → f (x * u) = f x := by
    intro x u hu
    have h := hf 1 x u hu
    simp only [map_one, one_mul, Units.val_one, splitRep, hbasic.2.2.2.1, Module.End.one_apply] at h
    exact h
  have hρ : ∀ v, splitRep s k (γ : QuatAlg ℚ a b) v = ((p : ℕ) : K) ^ (k - 2) • v := by
    intro v
    have hs : s (γ : QuatAlg ℚ a b) = Matrix.scalar (Fin 2) ((p : ℕ) : K) := by
      rw [hγval, map_natCast]
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    rw [splitRep, hs, hbasic.2.2.2.2.1, LinearMap.smul_apply, Module.End.one_apply]
  funext x
  rw [Pi.smul_apply]
  unfold heckeAct
  rw [finsum_eq_single _ (QuotientGroup.mk P : (BHat a b)ˣ ⧸ orderCompletionUnits O)]
  · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O) P
    have hmem : P * (u : (BHat a b)ˣ) ∈ {x : (BHat a b)ˣ | ∃ u ∈ orderCompletionUnits O, x = P * u} :=
      ⟨u, u.2, rfl⟩
    rw [hu, Set.indicator_of_mem hmem, Pi.one_apply, one_smul, ← mul_assoc, hinv _ _ u.2, hcomm]
    have h := hf γ x 1 (one_mem _)
    rw [mul_one] at h
    exact h.trans (hρ _)
  · intro c hc
    rw [Set.indicator_of_notMem, zero_smul]
    rintro ⟨u, hu, hcu⟩
    apply hc
    rw [← QuotientGroup.out_eq' c, hcu]
    exact QuotientGroup.eq.mpr (by simpa using inv_mem hu)

/-! ### Proof helpers for `hecke_coset_count` (Q3 part 4): local–global for `Ô`, the lift `B_p → B̂`, Hermite normal
forms over `ℤ_p`, the count `|Ô_{p^r}/Ô^×| = σ₁(p^r)`, and a private copy of `normNSet_product` (lfile sees an older
build of Hecke.lean). -/

/-- Evaluation `B̂ → B_q` at a prime `q` (coordinatewise). -/
private noncomputable abbrev hl_ev {a b : ℤ} (q : Nat.Primes) : QuatAlg FinAdele a b →+* QuatAlg ℚ_[q] a b :=
  baseChange a b (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q)

private theorem hl_ev_smul {a b : ℤ} (q : Nat.Primes) (c : FinAdele) (x : BHat a b) :
    hl_ev q (c • x : BHat a b) = c q • hl_ev q x := by
  ext <;> rfl

private theorem hl_ev_finEmbed {a b : ℤ} (q : Nat.Primes) (z : QuatAlg ℚ a b) :
    hl_ev q (finEmbed a b z) = baseChange a b (algebraMap ℚ ℚ_[q]) z := by
  have h : ∀ c : ℚ, (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q) (algebraMap ℚ FinAdele c) =
      algebraMap ℚ ℚ_[q] c := fun c => by
    rw [← RingHom.comp_apply, eq_ratCast, eq_ratCast]
  ext <;> exact h _

private theorem hl_mem_range_iff (q : Nat.Primes) (x : ℚ_[q]) :
    x ∈ (algebraMap ℤ_[q] ℚ_[q]).range ↔ x ∈ PadicInt.subring q :=
  ⟨fun ⟨t, ht⟩ => ht ▸ (PadicInt.mem_subring_iff q.1).2 t.norm_le_one,
    fun h => ⟨⟨x, (PadicInt.mem_subring_iff q.1).1 h⟩, rfl⟩⟩

/-- Local–global for `Ô`: `w ∈ Ô` iff `w_q ∈ O_q` for every prime `q`. -/
private theorem hl_mem_iff_local {a b : ℤ} (O : QOrder a b) (w : BHat a b) :
    w ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∀ q : Nat.Primes, hl_ev q w ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis _ O.fg O.span_eq_top
  obtain ⟨F, hF1, -, hF3⟩ := exists_bhat_basis e f hf
  have hloc : ∀ q : Nat.Primes, ∃ Fq : Module.Basis (Fin 4) ℚ_[q] (QuatAlg ℚ_[q] a b),
      (∀ v, v ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) ↔
        ∀ i, Fq.repr v i ∈ (algebraMap ℤ_[q] ℚ_[q]).range) ∧
      ∀ i, Fq.repr (hl_ev q w) i = F.repr w i q := by
    intro q
    obtain ⟨Fq, hFq1, -⟩ := exists_baseChange_basis (S := ℚ_[q]) a b f
    refine ⟨Fq, fun v => mem_span_image_iff_repr (R := ℤ_[q]) e
      (baseChange a b (algebraMap ℚ ℚ_[q])).toAddMonoidHom Fq (fun i => by rw [← hf]; exact hFq1 i) v, ?_⟩
    have hFe : ∀ i, hl_ev q (F i) = Fq i := by
      intro i
      rw [hF1, hFq1, hl_ev_finEmbed]
    intro i
    have hw : hl_ev q w = ∑ j, F.repr w j q • Fq j := by
      conv_lhs => rw [← F.sum_repr w]
      refine (map_sum (hl_ev q) (fun j => (F.repr w j • F j : BHat a b)) Finset.univ).trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (hl_ev_smul q _ _).trans (by rw [hFe])
    rw [hw, Module.Basis.repr_sum_self]
  rw [hF3]
  constructor
  · intro h q
    obtain ⟨Fq, hFq, hrepr⟩ := hloc q
    rw [hFq]
    intro i
    rw [hrepr, hl_mem_range_iff]
    exact mem_zhat.mp (h i) q
  · intro h i
    rw [mem_zhat]
    intro q
    obtain ⟨Fq, hFq, hrepr⟩ := hloc q
    have := (hFq _).mp (h q) i
    rwa [hrepr, hl_mem_range_iff] at this



private theorem hl_ext {a b : ℤ} {x y : BHat a b} (h : ∀ q : Nat.Primes, hl_ev q x = hl_ev q y) : x = y := by
  have hx : ∀ q : Nat.Primes, (hl_ev (a := a) (b := b) q x).re = (hl_ev (a := a) (b := b) q y).re ∧
      (hl_ev (a := a) (b := b) q x).imI = (hl_ev (a := a) (b := b) q y).imI ∧
      (hl_ev (a := a) (b := b) q x).imJ = (hl_ev (a := a) (b := b) q y).imJ ∧
      (hl_ev (a := a) (b := b) q x).imK = (hl_ev (a := a) (b := b) q y).imK := fun q => by rw [h q]; simp
  show (show QuatAlg FinAdele a b from x) = (show QuatAlg FinAdele a b from y)
  ext
  · exact (hx _).1
  · exact (hx _).2.1
  · exact (hx _).2.2.1
  · exact (hx _).2.2.2

/-- The element of `B̂` that is `z` at `p` and `1` elsewhere. -/
private noncomputable def hl_lift {a b : ℤ} (p : Nat.Primes) (z : QuatAlg ℚ_[p] a b) : BHat a b :=
  show QuatAlg FinAdele a b from
  ⟨RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p z.re +
      (1 - RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p 1),
    RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p z.imI,
    RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p z.imJ,
    RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p z.imK⟩

private theorem hl_ev_lift_self {a b : ℤ} (p : Nat.Primes) (z : QuatAlg ℚ_[p] a b) :
    hl_ev p (hl_lift p z) = z := by
  ext <;> simp [hl_lift, baseChange]

private theorem hl_ev_lift_ne {a b : ℤ} (p q : Nat.Primes) (hq : q ≠ p) (z : QuatAlg ℚ_[p] a b) :
    hl_ev q (hl_lift p z) = 1 := by
  ext <;> simp [hl_lift, baseChange, RestrictedProduct.single_eq_of_ne _ _ hq]

private theorem hl_nrd_ev {a b : ℤ} (q : Nat.Primes) (x : QuatAlg FinAdele a b) :
    nrd (hl_ev q x) = nrd x q := by
  show _ = RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q (nrd x)
  simp only [nrd, map_sub, map_add, map_mul, map_pow, map_intCast]
  rfl

private theorem hl_star_ev {a b : ℤ} (q : Nat.Primes) (x : QuatAlg FinAdele a b) :
    hl_ev q (star x) = star (hl_ev q x) := by
  ext <;> simp [baseChange]

private theorem hl_star_mul_self {R : Type*} [CommRing R] {a b : ℤ} (x : QuatAlg R a b) :
    star x * x = algebraMap R (QuatAlg R a b) (nrd x) := by
  ext <;> simp [nrd, QuaternionAlgebra.algebraMap_eq] <;> ring

private theorem hl_trace_aux {K : Type*} [Field K] [CharZero K] {a b : ℤ}
    (s : QuatAlg K a b →ₐ[K] Matrix (Fin 2) (Fin 2) K)
    (u v : QuatAlg K a b) (c : K) (hc : c ≠ 0) (h1 : u * v * v = c • u) (h2 : v * u * v = -(u * v * v)) :
    (s u).trace = 0 := by
  have h3 : (s (u * v * v)).trace = 0 := by
    have e1 : (s (u * v * v)).trace = (s (v * u * v)).trace := by
      simp only [map_mul]
      rw [Matrix.trace_mul_comm, ← mul_assoc]
    rw [h2, map_neg, Matrix.trace_neg] at e1
    linear_combination e1 / 2
  rw [h1, map_smul, Matrix.trace_smul, smul_eq_zero] at h3
  exact h3.resolve_left hc

/-- `det ι(x) = nrd x` for a `K`-algebra hom `ι : B_K → M₂(K)` (the `splitting_norm_trace` argument over `K`). -/
private theorem hl_det_eq_nrd {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : QuatAlg K a b →ₐ[K] Matrix (Fin 2) (Fin 2) K) (x : QuatAlg K a b) : (s x).det = nrd x := by
  set i : QuatAlg K a b := ⟨0, 1, 0, 0⟩ with hi
  set j : QuatAlg K a b := ⟨0, 0, 1, 0⟩ with hj
  set k : QuatAlg K a b := ⟨0, 0, 0, 1⟩ with hk
  have ha' : (a : K) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hb' : (b : K) ≠ 0 := Int.cast_ne_zero.mpr hb
  have ti : (s i).trace = 0 :=
    hl_trace_aux s i j b hb' (by ext <;> simp [hi, hj]) (by ext <;> simp [hi, hj])
  have tj : (s j).trace = 0 :=
    hl_trace_aux s j i a ha' (by ext <;> simp [hi, hj]) (by ext <;> simp [hi, hj])
  have tk : (s k).trace = 0 :=
    hl_trace_aux s k i a ha' (by ext <;> simp [hi, hk]) (by ext <;> simp [hi, hk])
  have hdec : ∀ x : QuatAlg K a b,
      x = algebraMap K (QuatAlg K a b) x.re + x.imI • i + x.imJ • j + x.imK • k := by
    intro x
    ext <;> simp [hi, hj, hk, QuaternionAlgebra.algebraMap_eq]
  have htr : ∀ x : QuatAlg K a b, (s x).trace = 2 * x.re := by
    intro x
    conv_lhs => rw [hdec x]
    simp only [map_add, map_smul, AlgHom.commutes, Matrix.trace_add, Matrix.trace_smul, ti, tj, tk, smul_zero,
      add_zero]
    simp [Matrix.algebraMap_eq_diagonal, Matrix.trace_diagonal]
  have hdet : ∀ M : Matrix (Fin 2) (Fin 2) K, M.det = (M.trace ^ 2 - (M * M).trace) / 2 := by
    intro M
    simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hdet, ← map_mul, htr, htr]
  simp only [nrd, QuaternionAlgebra.re_mul]
  ring



section HNF

variable {p : ℕ} [Fact p.Prime]

/-- The Hermite normal form `(p^i x; 0 p^{r−i})` over `ℤ_p`. -/
private noncomputable def hl_hnf (p : ℕ) [Fact p.Prime] (r i x : ℕ) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  !![(p : ℤ_[p]) ^ i, (x : ℤ_[p]); 0, (p : ℤ_[p]) ^ (r - i)]

private theorem hl_det_hnf (r i x : ℕ) (hi : i ≤ r) : (hl_hnf p r i x).det = (p : ℤ_[p]) ^ r := by
  rw [hl_hnf, Matrix.det_fin_two_of, mul_zero, sub_zero, ← pow_add, Nat.add_sub_cancel' hi]

private theorem hl_p_ne_zero : (p : ℤ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

private theorem hl_norm_pow_unit (n : ℕ) (u : ℤ_[p]) (hu : IsUnit u) :
    ‖(p : ℤ_[p]) ^ n * u‖ = (p : ℝ) ^ (-(n : ℤ)) := by
  rw [norm_mul, PadicInt.norm_p_pow, PadicInt.isUnit_iff.mp hu, mul_one]

private theorem hl_pow_inj {m n : ℕ} (h : (p : ℝ) ^ (-(m : ℤ)) = (p : ℝ) ^ (-(n : ℤ))) : m = n := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have := zpow_right_injective₀ (by linarith) hp.ne' h
  omega

private theorem hl_unit_pow (x : ℤ_[p]) (hx : x ≠ 0) : ∃ (u : ℤ_[p]) (v : ℕ), IsUnit u ∧ x = (p : ℤ_[p]) ^ v * u :=
  ⟨_, _, (PadicInt.unitCoeff hx).isUnit, (PadicInt.unitCoeff_spec hx).trans (mul_comm _ _)⟩

private theorem hl_dvd_total (x y : ℤ_[p]) : x ∣ y ∨ y ∣ x := by
  by_cases hx : x = 0
  · right; rw [hx]; exact dvd_zero _
  by_cases hy : y = 0
  · left; rw [hy]; exact dvd_zero _
  obtain ⟨u, v, hu, rfl⟩ := hl_unit_pow x hx
  obtain ⟨u', v', hu', rfl⟩ := hl_unit_pow y hy
  rcases le_total v v' with h | h
  · left
    refine ⟨hu.unit⁻¹ * u' * (p : ℤ_[p]) ^ (v' - v), ?_⟩
    rw [show v' = v + (v' - v) by omega, pow_add, Nat.add_sub_cancel_left]
    have : (u : ℤ_[p]) * (hu.unit⁻¹ : ℤ_[p]ˣ) = 1 := hu.mul_val_inv
    linear_combination (-(p : ℤ_[p]) ^ v * (p : ℤ_[p]) ^ (v' - v) * u') * this
  · right
    refine ⟨hu'.unit⁻¹ * u * (p : ℤ_[p]) ^ (v - v'), ?_⟩
    rw [show v = v' + (v - v') by omega, pow_add, Nat.add_sub_cancel_left]
    have : (u' : ℤ_[p]) * (hu'.unit⁻¹ : ℤ_[p]ˣ) = 1 := hu'.mul_val_inv
    linear_combination (-(p : ℤ_[p]) ^ v' * (p : ℤ_[p]) ^ (v - v') * u) * this

private theorem hl_clear (m : Matrix (Fin 2) (Fin 2) ℤ_[p]) :
    ∃ k : Matrix (Fin 2) (Fin 2) ℤ_[p], IsUnit k.det ∧ (m * k) 1 0 = 0 := by
  rcases hl_dvd_total (m 1 1) (m 1 0) with ⟨t, ht⟩ | ⟨t, ht⟩
  · refine ⟨!![1, 0; -t, 1], by simp [Matrix.det_fin_two_of], ?_⟩
    simp [Matrix.mul_apply, Fin.sum_univ_two, ht]
  · refine ⟨!![-t, 1; 1, 0], by simp [Matrix.det_fin_two_of], ?_⟩
    simp [Matrix.mul_apply, Fin.sum_univ_two, ht]

/-- Existence of the Hermite normal form: `m = (p^i x; 0 p^{r−i}) k` with `k ∈ GL₂(ℤ_p)`. -/
private theorem hl_hnf_exists (r : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ_[p]) (u : ℤ_[p]) (hu : IsUnit u)
    (hm : m.det = (p : ℤ_[p]) ^ r * u) :
    ∃ i ≤ r, ∃ x < p ^ i, ∃ k : Matrix (Fin 2) (Fin 2) ℤ_[p], IsUnit k.det ∧ m = hl_hnf p r i x * k := by
  obtain ⟨k1, hk1, h10⟩ := hl_clear m
  set m1 := m * k1 with hm1
  have hαδ : m1 0 0 * m1 1 1 = (p : ℤ_[p]) ^ r * (u * k1.det) := by
    have : m1.det = (p : ℤ_[p]) ^ r * u * k1.det := by rw [hm1, Matrix.det_mul, hm]
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at this
    rw [this]; ring
  have hne : (p : ℤ_[p]) ^ r * (u * k1.det) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl_p_ne_zero) (hu.mul hk1).ne_zero
  have hα0 : m1 0 0 ≠ 0 := fun h => hne (by rw [← hαδ, h, zero_mul])
  have hδ0 : m1 1 1 ≠ 0 := fun h => hne (by rw [← hαδ, h, mul_zero])
  obtain ⟨u1, i, hu1, e1⟩ := hl_unit_pow _ hα0
  obtain ⟨u2, j, hu2, e2⟩ := hl_unit_pow _ hδ0
  have hij : i + j = r := by
    have h1 := congrArg norm hαδ
    rw [e1, e2, show (p : ℤ_[p]) ^ i * u1 * ((p : ℤ_[p]) ^ j * u2) = (p : ℤ_[p]) ^ (i + j) * (u1 * u2) by ring,
      hl_norm_pow_unit _ _ (hu1.mul hu2), hl_norm_pow_unit _ _ (hu.mul hk1)] at h1
    exact hl_pow_inj h1
  set β : ℤ_[p] := m1 0 1 * (hu2.unit⁻¹ : ℤ_[p]ˣ) with hβ
  set x : ℕ := β.appr i with hx
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec i β)
  have hu1i : u1 * (hu1.unit⁻¹ : ℤ_[p]ˣ) = 1 := hu1.mul_val_inv
  have hu2i : u2 * (hu2.unit⁻¹ : ℤ_[p]ˣ) = 1 := hu2.mul_val_inv
  set K : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
    k1 * !![((hu1.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), 0; 0, ((hu2.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])] * !![1, -s; 0, 1] with hK
  have hKdet : IsUnit K.det := by
    rw [hK, Matrix.det_mul, Matrix.det_mul, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
    simp only [mul_zero, sub_zero, mul_one]
    exact (hk1.mul ((Units.isUnit _).mul (Units.isUnit _)))
  have hmK : m * K = hl_hnf p r i x := by
    have hm1' : m1 = !![(p : ℤ_[p]) ^ i * u1, m1 0 1; 0, (p : ℤ_[p]) ^ j * u2] := by
      rw [← e1, ← e2, ← h10]
      exact Matrix.eta_fin_two m1
    rw [hK, ← mul_assoc, ← mul_assoc, ← hm1, hm1', hl_hnf, show r - i = j by omega]
    simp only [Matrix.mul_fin_two]
    refine Matrix.ext fun a c => ?_
    fin_cases a <;> fin_cases c <;> simp
    · linear_combination (p : ℤ_[p]) ^ i * hu1i
    · linear_combination (-1 : ℤ_[p]) * hs - (p : ℤ_[p]) ^ i * s * hu1i
    · linear_combination (p : ℤ_[p]) ^ j * hu2i
  refine ⟨i, by omega, x, PadicInt.appr_lt β i, K⁻¹, Matrix.isUnit_nonsing_inv_det K hKdet, ?_⟩
  rw [← hmK]
  exact (Matrix.mul_nonsing_inv_cancel_right (A := K) m hKdet).symm

/-- Uniqueness of the Hermite normal form modulo `GL₂(ℤ_p)` on the right. -/
private theorem hl_hnf_unique (r i i' x x' : ℕ) (hi : i ≤ r) (_hi' : i' ≤ r) (hx : x < p ^ i) (hx' : x' < p ^ i')
    (g : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hg : IsUnit g.det) (h : hl_hnf p r i' x' = hl_hnf p r i x * g) :
    i = i' ∧ x = x' := by
  have e := fun a c => congrFun (congrFun h a) c
  have e10 := e 1 0
  have e00 := e 0 0
  have e11 := e 1 1
  have e01 := e 0 1
  simp [hl_hnf, Matrix.mul_apply, Fin.sum_univ_two] at e10 e00 e11 e01
  have hp0 : (p : ℤ_[p]) ≠ 0 := hl_p_ne_zero
  have hg10 : g 1 0 = 0 := by
    rcases e10 with h' | h'
    · exact absurd h'.1 (Fact.out : p.Prime).ne_zero
    · exact h'
  rw [hg10, mul_zero, add_zero] at e00
  have hdg : g.det = g 0 0 * g 1 1 := by rw [Matrix.det_fin_two, hg10]; ring
  rw [hdg] at hg
  have hu00 : IsUnit (g 0 0) := isUnit_of_mul_isUnit_left hg
  have hu11 : IsUnit (g 1 1) := isUnit_of_mul_isUnit_right hg
  have hii : i' = i := by
    have h1 := congrArg norm e00
    rw [hl_norm_pow_unit _ _ hu00, ← mul_one ((p : ℤ_[p]) ^ i'), hl_norm_pow_unit _ _ isUnit_one] at h1
    exact hl_pow_inj h1
  subst hii
  have hg00 : g 0 0 = 1 := by
    have : (p : ℤ_[p]) ^ i' * g 0 0 = (p : ℤ_[p]) ^ i' * 1 := by rw [mul_one]; exact e00.symm
    exact mul_left_cancel₀ (pow_ne_zero _ hp0) this
  have hg11 : g 1 1 = 1 := by
    have : (p : ℤ_[p]) ^ (r - i') * g 1 1 = (p : ℤ_[p]) ^ (r - i') * 1 := by rw [mul_one]; exact e11.symm
    exact mul_left_cancel₀ (pow_ne_zero _ hp0) this
  rw [hg11, mul_one] at e01
  refine ⟨rfl, ?_⟩
  have hdvd : (p : ℤ_[p]) ^ i' ∣ (((x' : ℤ) - x : ℤ) : ℤ_[p]) := ⟨g 0 1, by push_cast; rw [e01]; ring⟩
  rw [PadicInt.pow_p_dvd_int_iff] at hdvd
  have hxz : (x : ℤ) < (p : ℤ) ^ i' := by exact_mod_cast hx
  have hxz' : (x' : ℤ) < (p : ℤ) ^ i' := by exact_mod_cast hx'
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd (by
    rw [abs_lt]; constructor <;> omega)
  omega

/-- Over `𝔽_p`: for a singular `(A B; C D)`, `[C = D = 0] + #{x : A = xC, B = xD} = 1 + p·[all zero]`. -/
private theorem hl_zmod_count (A B C D : ZMod p) (h : A * D - B * C = 0) :
    ((if C = 0 ∧ D = 0 then (1 : ℤ) else 0) +
      ∑ x : ZMod p, if A - x * C = 0 ∧ B - x * D = 0 then (1 : ℤ) else 0) =
      1 + (p : ℤ) * (if A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 then 1 else 0) := by
  by_cases hz : A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hz
    simp [ZMod.card]
  · rw [if_neg hz, mul_zero, add_zero]
    by_cases hcd : C = 0 ∧ D = 0
    · rw [if_pos hcd]
      have hno : ∀ x : ZMod p, ¬ (A - x * C = 0 ∧ B - x * D = 0) := by
        rintro x ⟨h1, h2⟩
        rw [hcd.1, mul_zero, sub_zero] at h1
        rw [hcd.2, mul_zero, sub_zero] at h2
        exact hz ⟨h1, h2, hcd⟩
      simp [hno]
    · rw [if_neg hcd, zero_add]
      have hex : ∃ x₀ : ZMod p, (A - x₀ * C = 0 ∧ B - x₀ * D = 0) ∧
          ∀ x : ZMod p, (A - x * C = 0 ∧ B - x * D = 0) → x = x₀ := by
        by_cases hc : C = 0
        · have hd : D ≠ 0 := fun hd => hcd ⟨hc, hd⟩
          have hA : A = 0 := by
            rw [hc, mul_zero, sub_zero] at h
            exact (mul_eq_zero.mp h).resolve_right hd
          refine ⟨B / D, ⟨by rw [hA, hc]; ring, by rw [div_mul_cancel₀ _ hd, sub_self]⟩, ?_⟩
          rintro x ⟨-, h2⟩
          rw [eq_div_iff hd]
          linear_combination -h2
        · refine ⟨A / C, ⟨by rw [div_mul_cancel₀ _ hc, sub_self], ?_⟩, ?_⟩
          · field_simp
            linear_combination -h
          · rintro x ⟨h1, -⟩
            rw [eq_div_iff hc]
            linear_combination -h1
      obtain ⟨x₀, hx₀, huniq⟩ := hex
      rw [Finset.sum_eq_single x₀]
      · rw [if_pos hx₀]
      · intro x _ hx
        rw [if_neg]
        exact fun h' => hx (huniq x h')
      · intro h'
        exact absurd (Finset.mem_univ _) h'

private theorem hl_sum_range_zmod (g : ZMod p → ℤ) :
    ∑ x ∈ Finset.range p, g (x : ZMod p) = ∑ z : ZMod p, g z := by
  refine Finset.sum_nbij' (fun x => (x : ZMod p)) (fun z => z.val) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_univ _
  · intro z _; exact Finset.mem_range.mpr (ZMod.val_lt z)
  · intro x hx; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hx)
  · intro z _; exact ZMod.natCast_zmod_val z
  · intro x _; rfl

private theorem hl_dvd_iff_toZMod (z : ℤ_[p]) : (p : ℤ_[p]) ∣ z ↔ PadicInt.toZMod z = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

open scoped Classical in
/-- For `X ∈ M₂(ℤ_p)` with `p ∣ det X`: the number of the `p + 1` Hermite forms `H` of determinant `p` with
`H⁻¹X` integral is `p + 1` if `p ∣ X`, and `1` otherwise. -/
private theorem hl_mat_count (X : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hX : (p : ℤ_[p]) ∣ X.det) :
    (∑ t : (Σ i : Fin (1 + 1), Fin (p ^ (i : ℕ))),
        if ∃ M, X = hl_hnf p 1 t.1 t.2 * M then (1 : ℤ) else 0) =
      1 + (p : ℤ) * (if ∃ M, X = (p : ℤ_[p]) • M then 1 else 0) := by
  classical
  set A := PadicInt.toZMod (X 0 0)
  set B := PadicInt.toZMod (X 0 1)
  set C := PadicInt.toZMod (X 1 0)
  set D := PadicInt.toZMod (X 1 1)
  have hdet : A * D - B * C = 0 := by
    have := (hl_dvd_iff_toZMod _).mp hX
    rw [Matrix.det_fin_two, map_sub, map_mul, map_mul] at this
    exact this
  have e0 : (∃ M, X = hl_hnf p 1 0 0 * M) ↔ C = 0 ∧ D = 0 := by
    rw [← hl_dvd_iff_toZMod, ← hl_dvd_iff_toZMod]
    constructor
    · rintro ⟨M, hM⟩
      rw [hM]
      simp [hl_hnf, Matrix.mul_apply, Fin.sum_univ_two]
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨!![X 0 0, X 0 1; m1, m2], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hl_hnf, Matrix.mul_apply, Fin.sum_univ_two, h1, h2]
  have e1 : ∀ x : ℕ, (∃ M, X = hl_hnf p 1 1 x * M) ↔
      A - (x : ZMod p) * C = 0 ∧ B - (x : ZMod p) * D = 0 := by
    intro x
    have hA : A - (x : ZMod p) * C = PadicInt.toZMod (X 0 0 - (x : ℤ_[p]) * X 1 0) := by
      simp [A, C]
    have hB : B - (x : ZMod p) * D = PadicInt.toZMod (X 0 1 - (x : ℤ_[p]) * X 1 1) := by
      simp [B, D]
    rw [hA, hB, ← hl_dvd_iff_toZMod, ← hl_dvd_iff_toZMod]
    constructor
    · rintro ⟨M, hM⟩
      rw [hM]
      simp only [hl_hnf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_cons, Nat.sub_self, pow_zero, pow_one, zero_mul, one_mul, zero_add]
      exact ⟨⟨M 0 0, by ring⟩, ⟨M 0 1, by ring⟩⟩
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩
      refine ⟨!![m1, m2; X 1 0, X 1 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hl_hnf, Matrix.mul_apply, Fin.sum_univ_two]
      · have h1' := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) h1
        push_cast at h1'
        linear_combination h1'
      · have h2' := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) h2
        push_cast at h2'
        linear_combination h2'
  have e2 : (∃ M, X = (p : ℤ_[p]) • M) ↔ A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
    simp only [A, B, C, D, ← hl_dvd_iff_toZMod]
    constructor
    · rintro ⟨M, hM⟩
      rw [hM]
      simp
    · rintro ⟨⟨m1, h1⟩, ⟨m2, h2⟩, ⟨m3, h3⟩, ⟨m4, h4⟩⟩
      refine ⟨!![m1, m2; m3, m4], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]
  rw [Fintype.sum_sigma, Fin.sum_univ_two]
  have hs : ∀ (i : ℕ) (g : ℕ → ℤ), ∑ x : Fin (p ^ i), g x = ∑ x ∈ Finset.range (p ^ i), g x :=
    fun i g => Fin.sum_univ_eq_sum_range g (p ^ i)
  simp only [Fin.val_zero, Fin.val_one]
  rw [hs 0 (fun x => if ∃ M, X = hl_hnf p 1 0 x * M then (1 : ℤ) else 0),
    hs 1 (fun x => if ∃ M, X = hl_hnf p 1 1 x * M then (1 : ℤ) else 0)]
  simp only [pow_zero, pow_one, Finset.range_one, Finset.sum_singleton]
  simp only [e0, e1, e2]
  rw [hl_sum_range_zmod (fun z => if A - z * C = 0 ∧ B - z * D = 0 then (1 : ℤ) else 0)]
  exact hl_zmod_count A B C D hdet

end HNF



private theorem hl_zhat_smul {a b : ℤ} (c : Zhat) (x : BHat a b) :
    (show QuatAlg FinAdele a b from c • x) = (c : FinAdele) • (show QuatAlg FinAdele a b from x) := rfl

private theorem hl_star_smul {R : Type*} [CommRing R] {a b : ℤ} (c : R) (x : QuatAlg R a b) :
    c • star x = star (c • x) := by
  ext <;> simp

private theorem hl_star_mem {a b : ℤ} (O : QOrder a b) {y : BHat a b}
    (hy : y ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    ∃ z : BHat a b, (show QuatAlg FinAdele a b from z) = star (show QuatAlg FinAdele a b from y) ∧
      z ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
  rw [latticeCompletion] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨finEmbed a b (star z), ?_, Submodule.subset_span ⟨star z, star_mem_order O hz, rfl⟩⟩
    show baseChange a b (algebraMap ℚ FinAdele) (star z) = star (baseChange a b (algebraMap ℚ FinAdele) z)
    ext <;> simp [baseChange]
  | zero =>
    refine ⟨0, ?_, Submodule.zero_mem _⟩
    show (0 : QuatAlg FinAdele a b) = star (0 : QuatAlg FinAdele a b)
    rw [star_zero]
  | add x z _ _ hx hz =>
    obtain ⟨x', hx'1, hx'2⟩ := hx
    obtain ⟨z', hz'1, hz'2⟩ := hz
    refine ⟨x' + z', ?_, Submodule.add_mem _ hx'2 hz'2⟩
    show (show QuatAlg FinAdele a b from x') + (show QuatAlg FinAdele a b from z') =
      star ((show QuatAlg FinAdele a b from x) + (show QuatAlg FinAdele a b from z))
    rw [star_add, hx'1, hz'1]
  | smul c x _ hx =>
    obtain ⟨x', hx'1, hx'2⟩ := hx
    refine ⟨c • x', ?_, Submodule.smul_mem _ c hx'2⟩
    rw [hl_zhat_smul, hl_zhat_smul, hx'1, hl_star_smul]

private theorem hl_ev_mul {a b : ℤ} (q : Nat.Primes) (x y : BHat a b) :
    hl_ev q (x * y : BHat a b) = hl_ev q x * hl_ev q y :=
  map_mul (hl_ev q) x y

private theorem hl_ev_one {a b : ℤ} (q : Nat.Primes) : hl_ev q (1 : BHat a b) = 1 :=
  map_one (hl_ev q)

private theorem hl_ev_units {a b : ℤ} (q : Nat.Primes) (v : (BHat a b)ˣ) :
    hl_ev q ((v : BHat a b)) * hl_ev q (((v⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
  rw [← hl_ev_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, hl_ev_one]

private theorem hl_one_mem_local {a b : ℤ} (O : QOrder a b) (q : Nat.Primes) :
    (1 : QuatAlg ℚ_[q] a b) ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) :=
  Submodule.subset_span ⟨1, O.toSubalgebra.one_mem, map_one _⟩

private theorem hl_units_iff {a b : ℤ} (O : QOrder a b) (v : (BHat a b)ˣ) :
    v ∈ orderCompletionUnits O ↔ ∀ q : Nat.Primes,
      hl_ev q (v : BHat a b) ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) ∧
      hl_ev q ((v⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) := by
  show (_ ∧ _) ↔ _
  rw [hl_mem_iff_local, hl_mem_iff_local]
  exact ⟨fun h q => ⟨h.1 q, h.2 q⟩, fun h => ⟨fun q => (h q).1, fun q => (h q).2⟩⟩

/-- The unit of `B̂^×` that is `z` at `p` and `1` elsewhere. -/
private noncomputable def hl_liftUnit {a b : ℤ} (p : Nat.Primes) (z : (QuatAlg ℚ_[p] a b)ˣ) : (BHat a b)ˣ where
  val := hl_lift p z
  inv := hl_lift p (z⁻¹ : (QuatAlg ℚ_[p] a b)ˣ)
  val_inv := hl_ext fun q => by
    rw [hl_ev_mul, hl_ev_one]
    by_cases hq : q = p
    · subst hq; rw [hl_ev_lift_self, hl_ev_lift_self, Units.mul_inv]
    · rw [hl_ev_lift_ne _ _ hq, hl_ev_lift_ne _ _ hq, one_mul]
  inv_val := hl_ext fun q => by
    rw [hl_ev_mul, hl_ev_one]
    by_cases hq : q = p
    · subst hq; rw [hl_ev_lift_self, hl_ev_lift_self, Units.inv_mul]
    · rw [hl_ev_lift_ne _ _ hq, hl_ev_lift_ne _ _ hq, one_mul]

private theorem hl_ev_liftUnit {a b : ℤ} (p q : Nat.Primes) (z : (QuatAlg ℚ_[p] a b)ˣ) :
    hl_ev q ((hl_liftUnit p z : (BHat a b)ˣ) : BHat a b) = if h : q = p then h ▸ (z : QuatAlg ℚ_[p] a b) else 1 := by
  by_cases hq : q = p
  · subst hq; rw [dite_eq_left rfl]; exact hl_ev_lift_self _ _
  · rw [dite_eq_right hq]; exact hl_ev_lift_ne _ _ hq _

private theorem hl_ev_liftUnit_self {a b : ℤ} (p : Nat.Primes) (z : (QuatAlg ℚ_[p] a b)ˣ) :
    hl_ev p ((hl_liftUnit p z : (BHat a b)ˣ) : BHat a b) = z := hl_ev_lift_self _ _

private theorem hl_ev_liftUnit_inv_self {a b : ℤ} (p : Nat.Primes) (z : (QuatAlg ℚ_[p] a b)ˣ) :
    hl_ev p (((hl_liftUnit p z)⁻¹ : (BHat a b)ˣ) : BHat a b) = (z⁻¹ : (QuatAlg ℚ_[p] a b)ˣ) :=
  hl_ev_lift_self _ _

private theorem hl_ev_liftUnit_ne {a b : ℤ} (p q : Nat.Primes) (hq : q ≠ p) (z : (QuatAlg ℚ_[p] a b)ˣ) :
    hl_ev q ((hl_liftUnit p z : (BHat a b)ˣ) : BHat a b) = 1 := hl_ev_lift_ne _ _ hq _

private theorem hl_ev_liftUnit_inv_ne {a b : ℤ} (p q : Nat.Primes) (hq : q ≠ p) (z : (QuatAlg ℚ_[p] a b)ˣ) :
    hl_ev q (((hl_liftUnit p z)⁻¹ : (BHat a b)ˣ) : BHat a b) = 1 := hl_ev_lift_ne _ _ hq _

/-- `p` is a unit of `ℤ_q` for primes `q ≠ p`. -/
private theorem hl_isUnit_p (p q : Nat.Primes) (hq : q ≠ p) : IsUnit ((p : ℕ) : ℤ_[q]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hq ?_)
  rw [PadicInt.norm_natCast_lt_one_iff] at h
  exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp h)

/-- For `w ∈ Ô_{p^r}` and `q ≠ p`: `(w⁻¹)_q ∈ O_q`. -/
private theorem hl_inv_mem_of_ne {a b : ℤ} (O : QOrder a b) (p q : Nat.Primes) (hq : q ≠ p) (r : ℕ)
    (w : (BHat a b)ˣ) (hw : w ∈ normNSet O ((p : ℕ) ^ r)) :
    hl_ev q (((w⁻¹ : (BHat a b)ˣ) : BHat a b)) ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) := by
  obtain ⟨hwO, u, hu⟩ := hw
  obtain ⟨S, hS, hSO⟩ := hl_star_mem O hwO
  have hSq := (hl_mem_iff_local O S).mp hSO q
  obtain ⟨v, hv⟩ := (zhat_units_explicit ((u : Zhat) : FinAdele)).mp ⟨u, rfl⟩ q
  set X := hl_ev q (w : BHat a b) with hX
  set X' := hl_ev q (((w⁻¹ : (BHat a b)ˣ) : BHat a b)) with hX'
  have hc : nrd X = (((hl_isUnit_p p q hq).unit ^ r * v : ℤ_[q]ˣ) : ℚ_[q]) := by
    rw [hX]
    erw [hl_nrd_ev q, hu]
    rw [RestrictedProduct.mul_apply, ← hv, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    congr 1
    show RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q (((p : ℕ) ^ r : ℕ) : FinAdele) = _
    rw [map_natCast, Nat.cast_pow]
  set P : ℤ_[q]ˣ := (hl_isUnit_p p q hq).unit ^ r * v with hP
  have hXX' : X * X' = 1 := hl_ev_units q w
  have hstar : (nrd X) • X' = star X := by
    rw [← mul_one (star X), ← hXX', ← mul_assoc, hl_star_mul_self, Algebra.smul_def]
  have hSX : hl_ev q S = star X := (congrArg (hl_ev q) hS).trans (hl_star_ev q _)
  have hX'eq : X' = ((P⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) • star X := by
    rw [← hstar, hc, ← algebraMap_smul ℚ_[q], smul_smul]
    have : algebraMap ℤ_[q] ℚ_[q] ((P⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) * ((P : ℤ_[q]) : ℚ_[q]) = 1 := by
      show ((((P⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q])) * _ = 1
      rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
    rw [this, one_smul]
  rw [hX'eq, ← hSX]
  exact Submodule.smul_mem _ _ hSq



private theorem hl_algebraMap_apply (q : Nat.Primes) (c : ℚ) :
    (algebraMap ℚ FinAdele c) q = algebraMap ℚ ℚ_[q] c := by
  show (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q) (algebraMap ℚ FinAdele c) = _
  rw [← RingHom.comp_apply, eq_ratCast, eq_ratCast]

/-- Representatives of `Ô_{p^r}/Ô^×` for an order `O` with `ι_p(O_p) = M₂(ℤ_p)`: the Hermite normal forms at `p`,
`1` elsewhere. -/
private theorem hl_reps {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) (r : ℕ) :
    ∃ Y : (Σ i : Fin (r + 1), Fin ((p : ℕ) ^ (i : ℕ))) → (BHat a b)ˣ,
      (∀ t, ι (hl_ev p ((Y t : (BHat a b)ˣ) : BHat a b)) =
        (hl_hnf (p : ℕ) r t.1 t.2).map (algebraMap ℤ_[p] ℚ_[p])) ∧
      (∀ t, ∀ q : Nat.Primes, q ≠ p → hl_ev q (((Y t)⁻¹ : (BHat a b)ˣ) : BHat a b) = 1) ∧
      (∀ t, Y t ∈ normNSet O ((p : ℕ) ^ r)) ∧
      (∀ t t', (QuotientGroup.mk (Y t) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk (Y t') → t = t') ∧
      (∀ w ∈ normNSet O ((p : ℕ) ^ r), ∃ t,
        (QuotientGroup.mk (Y t) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk w) := by
  classical
  set f := algebraMap ℤ_[p] ℚ_[p] with hf
  have hfinj : Function.Injective f := fun x y h => Subtype.ext h
  have hfp : f (p : ℤ_[p]) = ((p : ℕ) : ℚ_[p]) := map_natCast f _
  have hmapone : (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hdetmap : ∀ m : Matrix (Fin 2) (Fin 2) ℤ_[p], (m.map f).det = f m.det := fun m => (RingHom.map_det f m).symm
  have hdetι : ∀ z : QuatAlg ℚ_[p] a b, (ι z).det = nrd z := fun z =>
    hl_det_eq_nrd ha hb (ι : QuatAlg ℚ_[p] a b →ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) z
  have hpr0 : ((p : ℕ) : ℚ_[p]) ^ r ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr p.2.ne_zero)
  have hHu : ∀ i x : ℕ, i ≤ r → IsUnit ((hl_hnf p r i x).map f) := by
    intro i x hi
    rw [Matrix.isUnit_iff_isUnit_det, hdetmap, hl_det_hnf r i x hi, map_pow, hfp]
    exact isUnit_iff_ne_zero.mpr hpr0
  -- the index set and the representatives
  let T := Σ i : Fin (r + 1), Fin ((p : ℕ) ^ (i : ℕ))
  let Z : T → (QuatAlg ℚ_[p] a b)ˣ := fun t => ((hHu t.1 t.2 (by omega)).map ι.symm).unit
  have hZ : ∀ t : T, ι (Z t : QuatAlg ℚ_[p] a b) = (hl_hnf p r t.1 t.2).map f := by
    intro t
    show ι (((hHu t.1 t.2 (by omega)).map ι.symm).unit : QuatAlg ℚ_[p] a b) = _
    rw [IsUnit.unit_spec]
    exact ι.apply_symm_apply _
  let Y : T → (BHat a b)ˣ := fun t => hl_liftUnit p (Z t)
  have hιinv : ∀ z : (QuatAlg ℚ_[p] a b)ˣ, ι ((z⁻¹ : (QuatAlg ℚ_[p] a b)ˣ) : QuatAlg ℚ_[p] a b) * ι z = 1 := by
    intro z
    rw [← map_mul, Units.inv_mul, map_one]
  have hinvmap : ∀ V : (BHat a b)ˣ, ∀ k : Matrix (Fin 2) (Fin 2) ℤ_[p], IsUnit k.det →
      ι (hl_ev p (V : BHat a b)) = k.map f → ι (hl_ev p ((V⁻¹ : (BHat a b)ˣ) : BHat a b)) = k⁻¹.map f := by
    intro V k hk hkV
    have h1 : ι (hl_ev p (V : BHat a b)) * ι (hl_ev p ((V⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
      rw [← map_mul, hl_ev_units, map_one]
    have h2 : (k⁻¹.map f) * (k.map f) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hk, hmapone]
    calc ι (hl_ev p ((V⁻¹ : (BHat a b)ˣ) : BHat a b))
        = (k⁻¹.map f * k.map f) * ι (hl_ev p ((V⁻¹ : (BHat a b)ˣ) : BHat a b)) := by rw [h2, one_mul]
      _ = k⁻¹.map f := by rw [mul_assoc, ← hkV, h1, mul_one]
  -- (1) the representatives lie in `Ô_{p^r}`
  have hY1 : ∀ t : T, Y t ∈ normNSet O ((p : ℕ) ^ r) := by
    intro t
    have hnrdZ : nrd (Z t : QuatAlg ℚ_[p] a b) = ((p : ℕ) : ℚ_[p]) ^ r := by
      rw [← hdetι, hZ, hdetmap, hl_det_hnf r _ _ (by omega), map_pow, hfp]
    refine ⟨?_, ?_⟩
    · rw [hl_mem_iff_local]
      intro q
      have hpcase : hl_ev p ((Y t : (BHat a b)ˣ) : BHat a b) ∈
          localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
        rw [hl_ev_liftUnit_self, hι]; exact ⟨_, hZ t⟩
      by_cases hq : q = p
      · subst hq; exact hpcase
      · rw [hl_ev_liftUnit_ne _ _ hq]; exact hl_one_mem_local O q
    · set x : FinAdele := algebraMap ℚ FinAdele ((((p : ℕ) : ℚ) ^ r)⁻¹) *
        nrd (show QuatAlg FinAdele a b from ((Y t : (BHat a b)ˣ) : BHat a b)) with hx
      have hxq : ∀ q : Nat.Primes, ∃ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = x q := by
        intro q
        have hpcase : ∃ u : ℤ_[p]ˣ, ((u : ℤ_[p]) : ℚ_[p]) = x p := by
          refine ⟨1, ?_⟩
          rw [hx, RestrictedProduct.mul_apply, hl_algebraMap_apply, ← hl_nrd_ev]
          erw [hl_ev_liftUnit_self]
          rw [hnrdZ, map_inv₀, map_pow, map_natCast, inv_mul_cancel₀ hpr0]
          rfl
        by_cases hq : q = p
        · subst hq; exact hpcase
        · refine ⟨((hl_isUnit_p p q hq).unit ^ r)⁻¹, ?_⟩
          rw [hx, RestrictedProduct.mul_apply, hl_algebraMap_apply, ← hl_nrd_ev]
          erw [hl_ev_liftUnit_ne _ _ hq]
          have hn1 : nrd (1 : QuatAlg ℚ_[q] a b) = 1 := by simp [nrd]
          rw [hn1, mul_one, map_inv₀, map_pow, map_natCast]
          have hu : ((((hl_isUnit_p p q hq).unit ^ r : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) = ((p : ℕ) : ℚ_[q]) ^ r := by
            rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, PadicInt.coe_pow, PadicInt.coe_natCast]
          rw [← hu]
          exact (eq_inv_of_mul_eq_one_left (by rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]))
      obtain ⟨u, hu⟩ := (zhat_units_explicit x).mpr hxq
      refine ⟨u, ?_⟩
      rw [hu, hx, ← mul_assoc]
      have : (((p : ℕ) ^ r : ℕ) : FinAdele) * algebraMap ℚ FinAdele ((((p : ℕ) : ℚ) ^ r)⁻¹) = 1 := by
        rw [← map_natCast (algebraMap ℚ FinAdele), ← map_mul, Nat.cast_pow,
          mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.2.ne_zero)), map_one]
      rw [this, one_mul]
  -- (2) distinct representatives give distinct cosets
  have hY2 : ∀ t t' : T, (QuotientGroup.mk (Y t) : (BHat a b)ˣ ⧸ orderCompletionUnits O) =
      QuotientGroup.mk (Y t') → t = t' := by
    intro t t' htt
    have hV := QuotientGroup.eq.mp htt
    set V := (Y t)⁻¹ * Y t' with hVdef
    obtain ⟨hV1, hV2⟩ := (hl_units_iff O V).mp hV p
    obtain ⟨g, hg⟩ := (hι _).mp hV1
    obtain ⟨g', hg'⟩ := (hι _).mp hV2
    have hgg : g * g' = 1 := by
      apply Matrix.map_injective hfinj
      show (g * g').map f = (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map f
      rw [Matrix.map_mul, ← hg, ← hg', ← map_mul, hl_ev_units, map_one, hmapone]
    have hgdet : IsUnit g.det := isUnit_of_mul_isUnit_left (y := g'.det)
      (by rw [← Matrix.det_mul, hgg, Matrix.det_one]; exact isUnit_one)
    have hYV : Y t' = Y t * V := by rw [hVdef, mul_inv_cancel_left]
    have hH : hl_hnf p r t'.1 t'.2 = hl_hnf p r t.1 t.2 * g := by
      apply Matrix.map_injective hfinj
      show (hl_hnf p r t'.1 t'.2).map f = (hl_hnf p r t.1 t.2 * g).map f
      rw [Matrix.map_mul, ← hZ, ← hZ, ← hg, ← map_mul]
      rw [← hl_ev_liftUnit_self p (Z t'), ← hl_ev_liftUnit_self p (Z t), ← hl_ev_mul]
      show ι (hl_ev p ((Y t' : (BHat a b)ˣ) : BHat a b)) = ι (hl_ev p (((Y t : (BHat a b)ˣ) : BHat a b) * (V : BHat a b)))
      rw [hYV, Units.val_mul]
    obtain ⟨h1, h2⟩ := hl_hnf_unique r t.1 t'.1 t.2 t'.2 (by omega) (by omega) t.2.2 t'.2.2 g hgdet hH
    obtain ⟨⟨i, hi⟩, ⟨x, hx⟩⟩ := t
    obtain ⟨⟨i', hi'⟩, ⟨x', hx'⟩⟩ := t'
    simp only at h1 h2
    subst h1 h2
    rfl
  -- (3) every coset of `Ô_{p^r}` contains a representative
  have hY3 : ∀ w ∈ normNSet O ((p : ℕ) ^ r), ∃ t : T,
      (QuotientGroup.mk (Y t) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk w := by
    intro w hw
    obtain ⟨hwO, u, hu⟩ := hw
    obtain ⟨m, hm⟩ := (hι _).mp ((hl_mem_iff_local O _).mp hwO p)
    obtain ⟨v, hv⟩ := (zhat_units_explicit ((u : Zhat) : FinAdele)).mp ⟨u, rfl⟩ p
    have hdet : m.det = (p : ℤ_[p]) ^ r * (v : ℤ_[p]) := by
      apply hfinj
      rw [← hdetmap, ← hm, hdetι]
      erw [hl_nrd_ev p, hu]
      rw [RestrictedProduct.mul_apply, ← hv, map_mul, map_pow, hfp]
      congr 1
      show RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) p (((p : ℕ) ^ r : ℕ) : FinAdele) = _
      rw [map_natCast, Nat.cast_pow]
    obtain ⟨i, hi, x, hx, k, hk, hmk⟩ := hl_hnf_exists r m v v.isUnit hdet
    let t : T := ⟨⟨i, by omega⟩, ⟨x, hx⟩⟩
    refine ⟨t, QuotientGroup.eq.mpr ?_⟩
    set V := (Y t)⁻¹ * w with hVdef
    have hVinv : V⁻¹ = w⁻¹ * Y t := by rw [hVdef, mul_inv_rev, inv_inv]
    rw [hl_units_iff]
    intro q
    have hpcase : hl_ev p (V : BHat a b) ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ∧
        hl_ev p ((V⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
      have hVk : ι (hl_ev p (V : BHat a b)) = k.map f := by
        rw [hVdef, Units.val_mul, hl_ev_mul, map_mul, hm, hmk, Matrix.map_mul]
        show ι (hl_ev p (((hl_liftUnit p (Z t))⁻¹ : (BHat a b)ˣ) : BHat a b)) * _ = _
        rw [hl_ev_liftUnit_inv_self, ← hZ t, ← mul_assoc, hιinv, one_mul]
      refine ⟨(hι _).mpr ⟨k, hVk⟩, (hι _).mpr ⟨k⁻¹, hinvmap V k hk hVk⟩⟩
    by_cases hq : q = p
    · subst hq; exact hpcase
    · have hYq : hl_ev q ((Y t : (BHat a b)ˣ) : BHat a b) = 1 := hl_ev_liftUnit_ne _ _ hq _
      have hYq' : hl_ev q (((Y t)⁻¹ : (BHat a b)ˣ) : BHat a b) = 1 := hl_ev_liftUnit_inv_ne _ _ hq _
      refine ⟨?_, ?_⟩
      · rw [hVdef, Units.val_mul, hl_ev_mul, hYq', one_mul]
        exact (hl_mem_iff_local O _).mp hwO q
      · rw [hVinv, Units.val_mul, hl_ev_mul, hYq, mul_one]
        exact hl_inv_mem_of_ne O p q hq r w ⟨hwO, u, hu⟩
  exact ⟨Y, fun t => (congrArg ι (hl_ev_liftUnit_self p (Z t))).trans (hZ t),
    fun t q hq => hl_ev_liftUnit_inv_ne _ _ hq _, hY1, hY2, hY3⟩

/-- `|Ô_{p^r}/Ô^×| = 1 + p + ⋯ + p^r` for an order `O` with `ι_p(O_p) = M₂(ℤ_p)`. -/
private theorem hl_count_prime_pow {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) (r : ℕ) :
    Nat.card (QuotientGroup.mk '' normNSet O ((p : ℕ) ^ r) :
        Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) = ∑ i ∈ Finset.range (r + 1), (p : ℕ) ^ i := by
  obtain ⟨Y, -, -, hY1, hY2, hY3⟩ := hl_reps ha hb O p ι hι r
  have hbij : Function.Bijective (fun t : (Σ i : Fin (r + 1), Fin ((p : ℕ) ^ (i : ℕ))) =>
      (⟨QuotientGroup.mk (Y t), Y t, hY1 t, rfl⟩ :
        (QuotientGroup.mk '' normNSet O ((p : ℕ) ^ r) : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)))) := by
    refine ⟨fun t t' h => hY2 t t' (congrArg Subtype.val h), ?_⟩
    rintro ⟨_, w, hw, rfl⟩
    obtain ⟨t, ht⟩ := hY3 w hw
    exact ⟨t, Subtype.ext ht⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun i => (p : ℕ) ^ i) (r + 1)




/-! ### Proof helpers for `localHeckeEmbedding_hom` (Q3 part 5): for an order `O` and `ι : B_p ≃ M₂(ℚ_p)` with
`ι(O_p) = M₂(ℤ_p)`, the map `π : B̂^× → GL₂(ℚ_p)`, `x ↦ ι(x_p)`, and the set `R = {x : x_q ∈ O_q^× for q ≠ p}`:
`Ô^× = R ∩ π⁻¹(K_p)`, `R` is a subgroup, `π` is onto from `R`, and `π` induces a bijection `R/Ô^× ≃ GL₂(ℚ_p)/K_p`. -/

/-- `O_q` is closed under multiplication. -/
private theorem hl_loc_mul {a b : ℤ} (O : QOrder a b) (q : Nat.Primes) {x y : QuatAlg ℚ_[q] a b}
    (hx : x ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra))
    (hy : y ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra)) :
    x * y ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) := by
  have hlift : ∀ z, z ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) →
      hl_lift q z ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    intro z hz
    rw [hl_mem_iff_local]
    intro q'
    by_cases hq : q' = q
    · rw [hq, hl_ev_lift_self]; exact hz
    · rw [hl_ev_lift_ne _ _ hq]; exact hl_one_mem_local O q'
  have h := (hl_mem_iff_local O _).mp (mul_mem_orderCompletion O (hlift x hx) (hlift y hy)) q
  rwa [hl_ev_mul, hl_ev_lift_self, hl_ev_lift_self] at h

/-- The set `R = {x ∈ B̂^× : x_q, (x⁻¹)_q ∈ O_q for every prime q ≠ p}`. -/
private def hl_R {a b : ℤ} (O : QOrder a b) (p : Nat.Primes) : Set (BHat a b)ˣ :=
  {x | ∀ q : Nat.Primes, q ≠ p →
    hl_ev q (x : BHat a b) ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) ∧
      hl_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra)}

private theorem hl_R_mul {a b : ℤ} (O : QOrder a b) (p : Nat.Primes) {x y : (BHat a b)ˣ}
    (hx : x ∈ hl_R O p) (hy : y ∈ hl_R O p) : x * y ∈ hl_R O p := by
  intro q hq
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, hl_ev_mul]; exact hl_loc_mul O q (hx q hq).1 (hy q hq).1
  · rw [mul_inv_rev, Units.val_mul, hl_ev_mul]; exact hl_loc_mul O q (hy q hq).2 (hx q hq).2

private theorem hl_R_inv {a b : ℤ} (O : QOrder a b) (p : Nat.Primes) {x : (BHat a b)ˣ}
    (hx : x ∈ hl_R O p) : x⁻¹ ∈ hl_R O p := by
  intro q hq
  rw [inv_inv]
  exact ⟨(hx q hq).2, (hx q hq).1⟩

private theorem hl_U_sub_R {a b : ℤ} (O : QOrder a b) (p : Nat.Primes) {u : (BHat a b)ˣ}
    (hu : u ∈ orderCompletionUnits O) : u ∈ hl_R O p :=
  fun q _ => (hl_units_iff O u).mp hu q

/-- Matrices over `ℚ_p` with entries in `ℤ_p`. -/
private theorem hl_integral_iff {p : Nat.Primes} (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) :
    (∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], A = m.map (algebraMap ℤ_[p] ℚ_[p])) ↔
      ∀ i j, A i j ∈ PadicInt.subring p := by
  constructor
  · rintro ⟨m, rfl⟩ i j
    exact (PadicInt.mem_subring_iff p).2 (m i j).norm_le_one
  · intro h
    exact ⟨fun i j => ⟨A i j, (PadicInt.mem_subring_iff p).1 (h i j)⟩, by ext i j; rfl⟩

/-- The map `π : B̂^× → GL₂(ℚ_p)`, `x ↦ ι(x_p)`. -/
private noncomputable abbrev hl_pi {a b : ℤ} (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) : (BHat a b)ˣ →* GL (Fin 2) ℚ_[p] :=
  Units.map (ι.toRingEquiv.toRingHom.comp (hl_ev p)).toMonoidHom

private theorem hl_pi_val {a b : ℤ} (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) (x : (BHat a b)ˣ) :
    ((hl_pi p ι x : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = ι (hl_ev p (x : BHat a b)) := rfl

private theorem hl_pi_inv_val {a b : ℤ} (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) (x : (BHat a b)ˣ) :
    (((hl_pi p ι x)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      ι (hl_ev p ((x⁻¹ : (BHat a b)ˣ) : BHat a b)) := by
  rw [← map_inv]; rfl

/-- `π x ∈ K_p` iff `x_p, (x⁻¹)_p ∈ O_p`. -/
private theorem hl_pi_mem_K {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) (x : (BHat a b)ˣ) :
    hl_pi p ι x ∈ 𝐊[ℚ_[p]] ↔
      hl_ev p (x : BHat a b) ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ∧
        hl_ev p ((x⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) := by
  rw [GL2TF.mem_Kp_iff, hι, hι, hl_integral_iff, hl_integral_iff, ← hl_pi_val, ← hl_pi_inv_val]
  exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩

/-- `Ô^× = R ∩ π⁻¹(K_p)`. -/
private theorem hl_U_iff {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) (x : (BHat a b)ˣ) :
    x ∈ orderCompletionUnits O ↔ x ∈ hl_R O p ∧ hl_pi p ι x ∈ 𝐊[ℚ_[p]] := by
  rw [hl_units_iff, hl_pi_mem_K O p ι hι]
  constructor
  · intro h; exact ⟨fun q _ => h q, h p⟩
  · rintro ⟨hR, hp⟩ q
    by_cases hq : q = p
    · rw [hq]; exact hp
    · exact hR q hq

/-- For `x, y ∈ R`: `xÔ^× = yÔ^×` iff `π(x)K_p = π(y)K_p`. -/
private theorem hl_coset_iff {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) {x y : (BHat a b)ˣ}
    (hx : x ∈ hl_R O p) (hy : y ∈ hl_R O p) :
    (QuotientGroup.mk x : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk y ↔
      (QuotientGroup.mk (hl_pi p ι x) : GL (Fin 2) ℚ_[p] ⧸ 𝐊[ℚ_[p]]) = QuotientGroup.mk (hl_pi p ι y) := by
  rw [QuotientGroup.eq, QuotientGroup.eq, hl_U_iff O p ι hι, ← map_inv, ← map_mul]
  exact ⟨fun h => h.2, fun h => ⟨hl_R_mul O p (hl_R_inv O p hx) hy, h⟩⟩

/-- `π` maps `R` onto `GL₂(ℚ_p)`. -/
private theorem hl_pi_surj {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) (g : GL (Fin 2) ℚ_[p]) :
    ∃ x ∈ hl_R O p, hl_pi p ι x = g := by
  refine ⟨hl_liftUnit p (Units.map ι.symm.toRingEquiv.toRingHom.toMonoidHom g), fun q hq => ?_, ?_⟩
  · rw [hl_ev_liftUnit_ne _ _ hq, hl_ev_liftUnit_inv_ne _ _ hq]
    exact ⟨hl_one_mem_local O q, hl_one_mem_local O q⟩
  · apply Units.ext
    rw [hl_pi_val, hl_ev_liftUnit_self]
    exact ι.apply_symm_apply _

/-- The indicator of `R` is invariant under `Ô^×` on both sides. -/
private theorem hl_R_mul_unit {a b : ℤ} (O : QOrder a b) (p : Nat.Primes) {u : (BHat a b)ˣ}
    (hu : u ∈ orderCompletionUnits O) (x : (BHat a b)ˣ) :
    (u * x ∈ hl_R O p ↔ x ∈ hl_R O p) ∧ (x * u ∈ hl_R O p ↔ x ∈ hl_R O p) := by
  have huR := hl_U_sub_R O p hu
  have huR' := hl_R_inv O p huR
  refine ⟨⟨fun h => ?_, fun h => hl_R_mul O p huR h⟩, ⟨fun h => ?_, fun h => hl_R_mul O p h huR⟩⟩
  · have := hl_R_mul O p huR' h; rwa [inv_mul_cancel_left] at this
  · have := hl_R_mul O p h huR'; rwa [mul_inv_cancel_right] at this

/-- `Θ(Φ)(x) = Φ(π x) · 1_R(x)`. -/
private noncomputable def hl_theta {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) (Φ : GL (Fin 2) ℚ_[p] → ℂ) :
    (BHat a b)ˣ → ℂ :=
  fun x => Φ (hl_pi p ι x) * (hl_R O p).indicator (1 : (BHat a b)ˣ → ℂ) x

private theorem hl_out_R {a b : ℤ} (O : QOrder a b) (p : Nat.Primes) {x : (BHat a b)ˣ} (hx : x ∈ hl_R O p) :
    Quotient.out (QuotientGroup.mk x : (BHat a b)ˣ ⧸ orderCompletionUnits O) ∈ hl_R O p := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O) x
  rw [hu]
  exact hl_R_mul O p hx (hl_U_sub_R O p u.2)

private theorem hl_pi_out {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) (x : (BHat a b)ˣ) :
    (QuotientGroup.mk (hl_pi p ι (Quotient.out (QuotientGroup.mk x : (BHat a b)ˣ ⧸ orderCompletionUnits O))) :
      GL (Fin 2) ℚ_[p] ⧸ 𝐊[ℚ_[p]]) = QuotientGroup.mk (hl_pi p ι x) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O) x
  rw [hu, map_mul]
  exact QuotientGroup.mk_mul_of_mem _ ((hl_U_iff O p ι hι u).mp u.2).2

/-- (1) `Θ(Φ)` is a Hecke function for `Φ ∈ H(GL₂(ℚ_p), K_p)`. -/
private theorem hl_theta_hecke {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p]))
    (Φ : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) :
    HeckePair.IsHeckeFun (U := orderCompletionUnits O) (hl_theta O p ι (Φ : GL (Fin 2) ℚ_[p] → ℂ)) := by
  classical
  refine ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩
  · simp only [hl_theta, Set.indicator_apply, (hl_R_mul_unit O p hu x).1, map_mul, Pi.one_apply,
      HeckePair.apply_left_mul Φ ((hl_U_iff O p ι hι u).mp hu).2]
  · simp only [hl_theta, Set.indicator_apply, (hl_R_mul_unit O p hu x).2, map_mul, Pi.one_apply,
      HeckePair.apply_mul_right Φ ((hl_U_iff O p ι hι u).mp hu).2]
  · set S := (QuotientGroup.mk '' Function.support (hl_theta O p ι (Φ : GL (Fin 2) ℚ_[p] → ℂ)) :
      Set ((BHat a b)ˣ ⧸ orderCompletionUnits O))
    have hsupp : ∀ x, x ∈ Function.support (hl_theta O p ι (Φ : GL (Fin 2) ℚ_[p] → ℂ)) →
        x ∈ hl_R O p ∧ (Φ : GL (Fin 2) ℚ_[p] → ℂ) (hl_pi p ι x) ≠ 0 := by
      intro x hx
      simp only [Function.mem_support, hl_theta] at hx
      refine ⟨?_, left_ne_zero_of_mul hx⟩
      by_contra h
      exact hx (by rw [Set.indicator_of_notMem h, mul_zero])
    have hSR : ∀ c ∈ S, Quotient.out c ∈ hl_R O p := by
      rintro _ ⟨x, hx, rfl⟩
      exact hl_out_R O p (hsupp x hx).1
    let F : (BHat a b)ˣ ⧸ orderCompletionUnits O → GL (Fin 2) ℚ_[p] ⧸ 𝐊[ℚ_[p]] :=
      fun c => QuotientGroup.mk (hl_pi p ι (Quotient.out c))
    refine Set.Finite.of_finite_image (f := F) ((HeckePair.finite_cosets Φ).subset ?_) ?_
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨hl_pi p ι x, (hsupp x hx).2, (hl_pi_out O p ι hι x).symm⟩
    · intro c hc c' hc' h
      have := (hl_coset_iff O p ι hι (hSR c hc) (hSR c' hc')).mpr h
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

/-- (2) `Θ(1) = 1_{Ô^×}`. -/
private theorem hl_theta_one {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) :
    hl_theta O p ι ((1 : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) : GL (Fin 2) ℚ_[p] → ℂ) =
      ((1 : HeckePair.HeckeAlgebra (orderCompletionUnits O) ℂ) : (BHat a b)ˣ → ℂ) := by
  classical
  funext x
  simp only [hl_theta, HeckePair.coe_one, Set.indicator_apply, SetLike.mem_coe, hl_U_iff O p ι hι x]
  by_cases h1 : x ∈ hl_R O p <;> by_cases h2 : hl_pi p ι x ∈ 𝐊[ℚ_[p]] <;> simp [h1, h2]

/-- (3) `Θ(Φ₁ ∗ Φ₂) = Θ(Φ₁) ∗ Θ(Φ₂)`. -/
private theorem hl_theta_mul {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p]))
    (Φ₁ Φ₂ : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) :
    hl_theta O p ι ((Φ₁ * Φ₂ : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) : GL (Fin 2) ℚ_[p] → ℂ) =
      ((⟨_, hl_theta_hecke O p ι hι Φ₁⟩ * ⟨_, hl_theta_hecke O p ι hι Φ₂⟩ :
        HeckePair.HeckeAlgebra (orderCompletionUnits O) ℂ) : (BHat a b)ˣ → ℂ) := by
  classical
  funext x
  rw [HeckePair.mul_apply]
  set Θ₁ : HeckePair.HeckeAlgebra (orderCompletionUnits O) ℂ := ⟨_, hl_theta_hecke O p ι hι Φ₁⟩
  set Θ₂ : HeckePair.HeckeAlgebra (orderCompletionUnits O) ℂ := ⟨_, hl_theta_hecke O p ι hι Φ₂⟩
  have hterm : ∀ c : (BHat a b)ˣ ⧸ orderCompletionUnits O, HeckePair.convTerm Θ₁ Θ₂ x c =
      hl_theta O p ι (Φ₁ : GL (Fin 2) ℚ_[p] → ℂ) (Quotient.out c) *
        hl_theta O p ι (Φ₂ : GL (Fin 2) ℚ_[p] → ℂ) ((Quotient.out c)⁻¹ * x) := by
    intro c
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  show ((Φ₁ * Φ₂ : HeckePair.HeckeAlgebra 𝐊[ℚ_[p]] ℂ) : GL (Fin 2) ℚ_[p] → ℂ) (hl_pi p ι x) *
    (hl_R O p).indicator (1 : (BHat a b)ˣ → ℂ) x = _
  by_cases hx : x ∈ hl_R O p
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one, HeckePair.mul_apply]
    set S : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O) := {c | Quotient.out c ∈ hl_R O p} with hS
    have hsupp : Function.support (HeckePair.convTerm Θ₁ Θ₂ x) ⊆ S := by
      intro c hc
      rw [Function.mem_support, hterm] at hc
      by_contra h
      have h' : Quotient.out c ∉ hl_R O p := h
      apply hc
      simp only [hl_theta, Set.indicator_of_notMem h', mul_zero, zero_mul]
    rw [← Set.indicator_eq_self.mpr hsupp, ← finsum_mem_def, ← finsum_mem_univ]
    symm
    refine finsum_mem_eq_of_bijOn (fun c => (QuotientGroup.mk (hl_pi p ι (Quotient.out c)) :
      GL (Fin 2) ℚ_[p] ⧸ 𝐊[ℚ_[p]])) ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩ ?_
    · intro c hc c' hc' h
      have := (hl_coset_iff O p ι hι hc hc').mpr h
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
    · intro d _
      obtain ⟨y, hyR, hy⟩ := hl_pi_surj O p ι (Quotient.out d)
      refine ⟨QuotientGroup.mk y, hl_out_R O p hyR, ?_⟩
      show (QuotientGroup.mk (hl_pi p ι (Quotient.out (QuotientGroup.mk y :
        (BHat a b)ˣ ⧸ orderCompletionUnits O))) : GL (Fin 2) ℚ_[p] ⧸ 𝐊[ℚ_[p]]) = d
      rw [hl_pi_out O p ι hι y, hy, QuotientGroup.out_eq']
    · intro c hc
      have hc0 : Quotient.out c ∈ hl_R O p := hc
      rw [hterm, HeckePair.convTerm_mk]
      have hc' : (Quotient.out c)⁻¹ * x ∈ hl_R O p := hl_R_mul O p (hl_R_inv O p hc0) hx
      simp only [hl_theta, Set.indicator_of_mem hc0, Set.indicator_of_mem hc', Pi.one_apply, mul_one, map_mul,
        map_inv]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
    rw [hterm]
    by_cases hc : Quotient.out c ∈ hl_R O p
    · have hc' : (Quotient.out c)⁻¹ * x ∉ hl_R O p := by
        intro h
        apply hx
        have := hl_R_mul O p hc h
        rwa [mul_inv_cancel_left] at this
      simp only [hl_theta, Set.indicator_of_notMem hc', mul_zero]
    · simp only [hl_theta, Set.indicator_of_notMem hc, mul_zero, zero_mul]

open ValuativeRel in
open scoped Pointwise in
/-- `t_{1,1} = ϖ_p·1 ∈ ι(p) K_p`: there is `k ∈ K_p` with `ι(p)·k = t_{1,1}` (scalars `ϖ/p ∈ ℤ_p^×`). -/
private theorem hl_unif_scalar (p : Nat.Primes) :
    ∃ k ∈ 𝐊[ℚ_[p]], ∀ g : GL (Fin 2) ℚ_[p], (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = ((p : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[p]) →
      g * k = Local.cartanElement ℚ_[p] 1 1 := by
  set ϖ : ℚ_[p] := ((Local.unif ℚ_[p] : 𝒪[ℚ_[p]]) : ℚ_[p]) with hϖ
  have hset := Local.padic_unif_zpow_smul_integer (p := (p : ℕ)) 1
  simp only [zpow_one] at hset
  have hp0 : ((p : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  obtain ⟨A, hA, hAeq⟩ : ϖ ∈ ((p : ℕ) : ℚ_[p]) • (PadicInt.subring p : Set ℚ_[p]) := by
    rw [← hset]; exact ⟨1, Subring.one_mem _, by simp [hϖ]⟩
  obtain ⟨B, hB, hBeq⟩ : ((p : ℕ) : ℚ_[p]) ∈ ϖ • (𝒪[ℚ_[p]] : Set ℚ_[p]) := by
    rw [hset]; exact ⟨1, Subring.one_mem _, by simp⟩
  simp only [smul_eq_mul] at hAeq hBeq
  have hB' : B ∈ PadicInt.subring p := by
    rw [PadicInt.mem_subring_iff, ← GL2TF.padic_mem_integer_iff]; exact hB
  have hAB : A * B = 1 := by
    have : ((p : ℕ) : ℚ_[p]) * (A * B) = ((p : ℕ) : ℚ_[p]) * 1 := by
      rw [mul_one, ← mul_assoc, hAeq, hBeq]
    exact mul_left_cancel₀ hp0 this
  let k : GL (Fin 2) ℚ_[p] :=
    ⟨Matrix.scalar (Fin 2) A, Matrix.scalar (Fin 2) B, by rw [← map_mul, hAB, map_one],
      by rw [← map_mul, mul_comm, hAB, map_one]⟩
  refine ⟨k, ?_, fun g hg => ?_⟩
  · rw [GL2TF.mem_Kp_iff]
    intro i j
    have hkinv : ((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.scalar (Fin 2) B := rfl
    rw [hkinv]
    show Matrix.scalar (Fin 2) A i j ∈ _ ∧ Matrix.scalar (Fin 2) B i j ∈ _
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      exact ⟨hA, hB'⟩
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Subring.zero_mem]
  · apply Units.ext
    rw [Units.val_mul, hg, Local.cartanElement_val]
    show ((p : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[p]) * Matrix.scalar (Fin 2) A = _
    rw [show ((p : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.scalar (Fin 2) ((p : ℕ) : ℚ_[p]) from
      (map_natCast (Matrix.scalar (Fin 2)) _).symm, ← map_mul, hAeq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hϖ]

/-- (5) `Θ(c_{1,1}) = 1_{ι(p)Ô^×}`. -/
private theorem hl_theta_c11 {a b : ℤ} (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) :
    hl_theta O p ι ((Local.heckeBasis ℚ_[p] 1 1 : Local.sphericalHeckeAlgebra ℚ_[p]) : GL (Fin 2) ℚ_[p] → ℂ) =
      {x : (BHat a b)ˣ | ∃ u ∈ orderCompletionUnits O,
        x = Units.map (finEmbed a b).toMonoidHom
          (Units.map (algebraMap ℚ (QuatAlg ℚ a b)).toMonoidHom
            (Units.mk0 ((p : ℕ) : ℚ) (Nat.cast_ne_zero.mpr p.2.ne_zero))) * u}.indicator (1 : (BHat a b)ˣ → ℂ) := by
  classical
  set γ : (QuatAlg ℚ a b)ˣ := Units.map (algebraMap ℚ (QuatAlg ℚ a b)).toMonoidHom
    (Units.mk0 ((p : ℕ) : ℚ) (Nat.cast_ne_zero.mpr p.2.ne_zero)) with hγ
  set P : (BHat a b)ˣ := Units.map (finEmbed a b).toMonoidHom γ with hP
  have hγval : ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = ((p : ℕ) : QuatAlg ℚ a b) := by
    simp [hγ]
  have hPval : ((P : (BHat a b)ˣ) : BHat a b) = ((p : ℕ) : BHat a b) := by
    rw [hP, Units.coe_map]
    show finEmbed a b (γ : QuatAlg ℚ a b) = _
    rw [hγval, map_natCast]
  have hevP : ∀ q : Nat.Primes, hl_ev q ((P : (BHat a b)ˣ) : BHat a b) = ((p : ℕ) : QuatAlg ℚ_[q] a b) := by
    intro q
    rw [hPval]
    exact map_natCast (hl_ev q) (p : ℕ)
  have hPR : P ∈ hl_R O p := by
    intro q hq
    refine ⟨?_, ?_⟩
    · rw [hevP, ← nsmul_one]
      exact nsmul_mem (hl_one_mem_local O q) _
    · have h1 := hl_ev_units q P
      rw [hevP] at h1
      have hu1 : ((((hl_isUnit_p p q hq).unit⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) * ((p : ℕ) : ℚ_[q]) = 1 := by
        have := congrArg (fun z : ℤ_[q] => (z : ℚ_[q])) (hl_isUnit_p p q hq).val_inv_mul
        simpa only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] using this
      have hw : hl_ev q (((P⁻¹ : (BHat a b)ˣ)) : BHat a b) =
          (((hl_isUnit_p p q hq).unit⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) • (1 : QuatAlg ℚ_[q] a b) := by
        rw [← h1, ← algebraMap_smul ℚ_[q], ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ_[q], smul_smul]
        show _ = (((((hl_isUnit_p p q hq).unit⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) * ((p : ℕ) : ℚ_[q])) • _
        rw [hu1, one_smul]
      rw [hw]
      exact Submodule.smul_mem _ _ (hl_one_mem_local O q)
  have hπP : ((hl_pi p ι P : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      ((p : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    rw [hl_pi_val, hevP, map_natCast]
  obtain ⟨k, hk, hkP⟩ := hl_unif_scalar p
  have ht := hkP _ hπP
  have hmem : ∀ x : (BHat a b)ˣ, x ∈ {x : (BHat a b)ˣ | ∃ u ∈ orderCompletionUnits O, x = P * u} ↔
      x ∈ hl_R O p ∧ hl_pi p ι x ∈ DoubleCoset.doubleCoset (Local.cartanElement ℚ_[p] 1 1) 𝐊[ℚ_[p]] 𝐊[ℚ_[p]] := by
    intro x
    rw [Local.mem_doubleCoset_diag_iff, ← ht, QuotientGroup.mk_mul_of_mem _ hk, eq_comm, QuotientGroup.eq,
      ← map_inv, ← map_mul]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨hl_R_mul O p hPR (hl_U_sub_R O p hu), ?_⟩
      rw [inv_mul_cancel_left]
      exact ((hl_U_iff O p ι hι u).mp hu).2
    · rintro ⟨hxR, hK⟩
      exact ⟨P⁻¹ * x, (hl_U_iff O p ι hι _).mpr ⟨hl_R_mul O p (hl_R_inv O p hPR) hxR, hK⟩,
        by rw [mul_inv_cancel_left]⟩
  funext x
  simp only [hl_theta]
  by_cases hx : x ∈ hl_R O p ∧
      hl_pi p ι x ∈ DoubleCoset.doubleCoset (Local.cartanElement ℚ_[p] 1 1) 𝐊[ℚ_[p]] 𝐊[ℚ_[p]]
  · rw [Set.indicator_of_mem ((hmem x).mpr hx), Local.heckeBasis_apply_of_mem hx.2, Set.indicator_of_mem hx.1]
    simp
  · rw [Set.indicator_of_notMem (fun h => hx ((hmem x).mp h))]
    by_cases hR : x ∈ hl_R O p
    · rw [Local.heckeBasis_apply_of_notMem (fun h => hx ⟨hR, h⟩), zero_mul]
    · rw [Set.indicator_of_notMem hR, mul_zero]

/-! #### Clause (4): `Θ(Σ_{a+b=r} c_{a,b}) = 1_{Ô_{p^r}}` -/

/-- `O_q` is stable under conjugation. -/
private theorem hl_loc_star {a b : ℤ} (O : QOrder a b) (q : Nat.Primes) {z : QuatAlg ℚ_[q] a b}
    (hz : z ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra)) :
    star z ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) := by
  unfold localLattice at hz ⊢
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine Submodule.subset_span ⟨star w, star_mem_order O hw, ?_⟩
    ext <;> simp [baseChange]
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have hsm : ∀ y : ℚ_[q], c • y = (c : ℚ_[q]) * y := fun y => Algebra.smul_def c y
    rw [show star (c • x) = c • star x by ext <;> simp [hsm]]
    exact Submodule.smul_mem _ c hx

/-- `trd(O_q), nrd(O_q) ⊆ ℤ_q`. -/
private theorem hl_loc_trd_nrd {a b : ℤ} (O : QOrder a b) (q : Nat.Primes) {z : QuatAlg ℚ_[q] a b}
    (hz : z ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra)) :
    ‖trd z‖ ≤ 1 ∧ ‖nrd z‖ ≤ 1 := by
  have htrd : ∀ z ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra), ‖trd z‖ ≤ 1 := by
    intro z hz
    unfold localLattice at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨⟨n, hn⟩, -⟩ := trd_nrd_int_of_mem O hw
      rw [((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 ℚ_[q] (algebraMap ℚ ℚ_[q]) w).2, hn, map_intCast]
      exact Padic.norm_int_le_one n
    | zero => simp [trd]
    | add x y _ _ hx hy =>
      rw [show trd (x + y) = trd x + trd y by simp [trd]; ring]
      exact (Padic.nonarchimedean _ _).trans (max_le hx hy)
    | smul c x _ hx =>
      have hsm : ∀ y : ℚ_[q], c • y = (c : ℚ_[q]) * y := fun y => Algebra.smul_def c y
      rw [show trd (c • x) = (c : ℚ_[q]) * trd x by
        simp [trd, hsm]; ring, norm_mul]
      exact mul_le_one₀ c.norm_le_one (norm_nonneg _) hx
  refine ⟨htrd z hz, ?_⟩
  unfold localLattice at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨-, ⟨n, hn⟩⟩ := trd_nrd_int_of_mem O hw
    rw [((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 ℚ_[q] (algebraMap ℚ ℚ_[q]) w).1, hn, map_intCast]
    exact Padic.norm_int_le_one n
  | zero => simp [nrd]
  | add x y hxm hym hx hy =>
    rw [show nrd (x + y) = nrd x + nrd y + trd (x * star y) by simp [nrd, trd]; ring]
    have h3 := htrd _ (hl_loc_mul O q hxm (hl_loc_star O q hym))
    exact (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le hx hy)) h3)
  | smul c x _ hx =>
    have hsm : ∀ y : ℚ_[q], c • y = (c : ℚ_[q]) * y := fun y => Algebra.smul_def c y
    rw [show nrd (c • x) = (c : ℚ_[q]) ^ 2 * nrd x by
      simp [nrd, hsm]; ring, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) c.norm_le_one) (norm_nonneg _) hx

/-- An element of norm `1` of `ℚ_p` is a unit of `ℤ_p`. -/
private theorem hl_unit_of_norm {q : Nat.Primes} (z : ℚ_[q]) (hz : ‖z‖ = 1) :
    ∃ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = z :=
  ⟨(PadicInt.isUnit_iff.mpr (show ‖(⟨z, hz.le⟩ : ℤ_[q])‖ = 1 from hz)).unit, rfl⟩

open ValuativeRel in
open scoped Pointwise in
/-- `‖ϖ_p‖ = p⁻¹` (`ϖ_p = p·A` with `A ∈ ℤ_p^×`). -/
private theorem hl_norm_unif (p : Nat.Primes) :
    ‖((Local.unif ℚ_[p] : 𝒪[ℚ_[p]]) : ℚ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  set ϖ : ℚ_[p] := ((Local.unif ℚ_[p] : 𝒪[ℚ_[p]]) : ℚ_[p]) with hϖ
  have hset := Local.padic_unif_zpow_smul_integer (p := (p : ℕ)) 1
  simp only [zpow_one] at hset
  have hp0 : ((p : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  obtain ⟨A, hA, hAeq⟩ : ϖ ∈ ((p : ℕ) : ℚ_[p]) • (PadicInt.subring p : Set ℚ_[p]) := by
    rw [← hset]; exact ⟨1, Subring.one_mem _, by simp [hϖ]⟩
  obtain ⟨B, hB, hBeq⟩ : ((p : ℕ) : ℚ_[p]) ∈ ϖ • (𝒪[ℚ_[p]] : Set ℚ_[p]) := by
    rw [hset]; exact ⟨1, Subring.one_mem _, by simp⟩
  simp only [smul_eq_mul] at hAeq hBeq
  have hB' : ‖B‖ ≤ 1 := (GL2TF.padic_mem_integer_iff p B).mp hB
  have hA' : ‖A‖ ≤ 1 := (PadicInt.mem_subring_iff p).mp hA
  have hAB : A * B = 1 := by
    have : ((p : ℕ) : ℚ_[p]) * (A * B) = ((p : ℕ) : ℚ_[p]) * 1 := by
      rw [mul_one, ← mul_assoc, hAeq, hBeq]
    exact mul_left_cancel₀ hp0 this
  have hnA : ‖A‖ = 1 := by
    have h1 : ‖A‖ * ‖B‖ = 1 := by rw [← norm_mul, hAB, norm_one]
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
    have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
    nlinarith
  rw [← hAeq, norm_mul, Padic.norm_p, hnA, mul_one]

/-- The predicate `P_r(g)`: `g` has entries in `ℤ_p` and `‖det g‖ = p^{−r}`. -/
private def hl_Pr (p : Nat.Primes) (r : ℕ) (g : GL (Fin 2) ℚ_[p]) : Prop :=
  (∀ i j, (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j ∈ PadicInt.subring p) ∧
    ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ = ((p : ℕ) : ℝ) ^ (-(r : ℤ))

private theorem hl_int_mul {p : Nat.Primes} {M N : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    (hM : ∀ i j, M i j ∈ PadicInt.subring p) (hN : ∀ i j, N i j ∈ PadicInt.subring p) :
    ∀ i j, (M * N) i j ∈ PadicInt.subring p := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact Subring.add_mem _ (Subring.mul_mem _ (hM _ _) (hN _ _)) (Subring.mul_mem _ (hM _ _) (hN _ _))

private theorem hl_Pr_mul_K {p : Nat.Primes} (r : ℕ) {k : GL (Fin 2) ℚ_[p]} (hk : k ∈ 𝐊[ℚ_[p]])
    (g : GL (Fin 2) ℚ_[p]) : (hl_Pr p r (k * g) ↔ hl_Pr p r g) ∧ (hl_Pr p r (g * k) ↔ hl_Pr p r g) := by
  have hK := (GL2TF.mem_Kp_iff p k).mp hk
  have hKi := (GL2TF.mem_Kp_iff p k⁻¹).mp (inv_mem hk)
  have hk1 : ∀ i j, (k : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j ∈ PadicInt.subring p := fun i j => (hK i j).1
  have hk2 : ∀ i j, ((k⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j ∈ PadicInt.subring p :=
    fun i j => (hK i j).2
  have hdk := GL2TF.Kp_det_norm p k hk
  have hdk' := GL2TF.Kp_det_norm p k⁻¹ (inv_mem hk)
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have e : g = k⁻¹ * (k * g) := by group
    refine ⟨?_, ?_⟩
    · rw [e, Units.val_mul]; exact hl_int_mul hk2 h.1
    · rw [e, Units.val_mul, Matrix.det_mul, norm_mul, hdk', one_mul]; exact h.2
  · refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact hl_int_mul hk1 h.1
    · rw [Units.val_mul, Matrix.det_mul, norm_mul, hdk, one_mul]; exact h.2
  · have e : g = (g * k) * k⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [e, Units.val_mul]; exact hl_int_mul h.1 hk2
    · rw [e, Units.val_mul, Matrix.det_mul, norm_mul, hdk', mul_one]; exact h.2
  · refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact hl_int_mul h.1 hk1
    · rw [Units.val_mul, Matrix.det_mul, norm_mul, hdk, mul_one]; exact h.2

open ValuativeRel in
private theorem hl_Pr_cartan (p : Nat.Primes) (r : ℕ) {a b : ℤ} (hab : b ≤ a) :
    hl_Pr p r (Local.cartanElement ℚ_[p] a b) ↔ 0 ≤ b ∧ a + b = r := by
  have hn := hl_norm_unif p
  set ϖ := ((Local.unif ℚ_[p] : 𝒪[ℚ_[p]]) : ℚ_[p]) with hϖ
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have hnz : ∀ n : ℤ, ‖ϖ ^ n‖ = ((p : ℕ) : ℝ) ^ (-n) := by
    intro n; rw [norm_zpow, hn, inv_zpow']
  have hint : ∀ n : ℤ, ϖ ^ n ∈ PadicInt.subring p ↔ 0 ≤ n := by
    intro n
    rw [PadicInt.mem_subring_iff, hnz]
    constructor
    · intro h; by_contra hc; push_neg at hc
      have : (1 : ℝ) < ((p : ℕ) : ℝ) ^ (-n) := one_lt_zpow₀ hp1 (by omega)
      linarith
    · intro h; exact zpow_le_one_of_nonpos₀ hp1.le (by omega)
  unfold hl_Pr
  rw [Local.cartanElement_val, Matrix.det_fin_two_of, mul_zero, sub_zero, norm_mul, hnz, hnz,
    ← zpow_add₀ (by positivity : ((p : ℕ) : ℝ) ≠ 0)]
  constructor
  · rintro ⟨h1, h2⟩
    have hb := (hint b).mp (by simpa using h1 1 1)
    refine ⟨hb, ?_⟩
    have := zpow_right_injective₀ (by positivity : (0 : ℝ) < ((p : ℕ) : ℝ)) hp1.ne' h2
    omega
  · rintro ⟨hb, hr⟩
    refine ⟨fun i j => ?_, by rw [show -a + -b = -(r : ℤ) by omega]⟩
    fin_cases i <;> fin_cases j
    exacts [(hint a).mpr (by omega), Subring.zero_mem _, Subring.zero_mem _, (hint b).mpr hb]

open scoped Classical in
/-- `(Σ_{a+b=r, a≥b≥0} c_{a,b})(g) = 1` if `P_r(g)` and `0` otherwise. -/
private theorem hl_sum_cartan_apply (p : Nat.Primes) (r : ℕ) (g : GL (Fin 2) ℚ_[p]) :
    ((∑ j ∈ Finset.range (r / 2 + 1), Local.heckeBasis ℚ_[p] ((r - j : ℕ) : ℤ) (j : ℤ) :
      Local.sphericalHeckeAlgebra ℚ_[p]) : GL (Fin 2) ℚ_[p] → ℂ) g =
      if hl_Pr p r g then 1 else 0 := by
  classical
  obtain ⟨⟨a, b⟩, ⟨hab, hg⟩, -⟩ := Local.cartan_decomposition ℚ_[p] g
  simp only at hab hg
  have hPr : hl_Pr p r g ↔ 0 ≤ b ∧ a + b = r := by
    obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    rw [(hl_Pr_mul_K r hk' _).2, (hl_Pr_mul_K r hk _).1, hl_Pr_cartan p r hab]
  rw [Submodule.coe_sum, Finset.sum_apply]
  have hterm : ∀ j ∈ Finset.range (r / 2 + 1),
      ((Local.heckeBasis ℚ_[p] ((r - j : ℕ) : ℤ) (j : ℤ) : Local.sphericalHeckeAlgebra ℚ_[p]) :
        GL (Fin 2) ℚ_[p] → ℂ) g = if (((r - j : ℕ) : ℤ), (j : ℤ)) = (a, b) then 1 else 0 := by
    intro j hj
    have hj' : j ≤ r / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Local.hecke_apply_eq_cartan _ hg, Local.heckeBasis_apply_cartan (by omega) hab]
  rw [Finset.sum_congr rfl hterm, hPr]
  by_cases h : 0 ≤ b ∧ a + b = r
  · rw [if_pos h, Finset.sum_eq_single b.toNat]
    · rw [if_pos]; ext <;> simp <;> omega
    · intro j _ hj
      rw [if_neg]
      intro he
      apply hj
      simp only [Prod.mk.injEq] at he
      omega
    · intro hb
      exfalso
      apply hb
      rw [Finset.mem_range]
      omega
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg]
    intro he
    simp only [Prod.mk.injEq] at he
    have hj' : j ≤ r / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact h ⟨by omega, by omega⟩

/-- `Ô_{p^r} = R ∩ π⁻¹{g : P_r(g)}`. -/
private theorem hl_normNSet_iff {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) (r : ℕ) (x : (BHat a b)ˣ) :
    x ∈ normNSet O ((p : ℕ) ^ r) ↔ x ∈ hl_R O p ∧ hl_Pr p r (hl_pi p ι x) := by
  have hdetι : ∀ z : QuatAlg ℚ_[p] a b, (ι z).det = nrd z := fun z =>
    hl_det_eq_nrd ha hb (ι : QuatAlg ℚ_[p] a b →ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p]) z
  have hp1 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hnpr : ‖((p : ℕ) : ℚ_[p]) ^ r‖ = ((p : ℕ) : ℝ) ^ (-(r : ℤ)) := by
    rw [norm_pow, Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]
  have hdetx : (((hl_pi p ι x : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p])).det =
      nrd ((x : BHat a b) : QuatAlg FinAdele a b) p := by
    rw [hl_pi_val, hdetι]
    exact hl_nrd_ev p _
  constructor
  · intro hx
    obtain ⟨hxO, u, hu⟩ := hx
    refine ⟨fun q hq => ⟨(hl_mem_iff_local O _).mp hxO q, hl_inv_mem_of_ne O p q hq r x ⟨hxO, u, hu⟩⟩, ?_, ?_⟩
    · rw [hl_pi_val, ← hl_integral_iff, ← hι]
      exact (hl_mem_iff_local O _).mp hxO p
    · obtain ⟨v, hv⟩ := (zhat_units_explicit ((u : Zhat) : FinAdele)).mp ⟨u, rfl⟩ p
      rw [hdetx]
      erw [hu]
      rw [RestrictedProduct.mul_apply, ← hv, norm_mul]
      have hv1 : ‖((v : ℤ_[p]) : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp v.isUnit
      rw [hv1, mul_one]
      show ‖RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) p (((p : ℕ) ^ r : ℕ) : FinAdele)‖ = _
      rw [map_natCast, Nat.cast_pow, hnpr]
  · rintro ⟨hR, hent, hdet⟩
    have hxO : (x : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
      rw [hl_mem_iff_local]
      intro q
      by_cases hq : q = p
      · rw [hq, hι, ← hl_pi_val, hl_integral_iff]; exact hent
      · exact (hR q hq).1
    refine ⟨hxO, ?_⟩
    set y : FinAdele := algebraMap ℚ FinAdele ((((p : ℕ) : ℚ) ^ r)⁻¹) *
      nrd ((x : BHat a b) : QuatAlg FinAdele a b) with hy
    have hyq : ∀ q : Nat.Primes, ∃ u : ℤ_[q]ˣ, ((u : ℤ_[q]) : ℚ_[q]) = y q := by
      intro q
      apply hl_unit_of_norm
      rw [hy, RestrictedProduct.mul_apply, hl_algebraMap_apply,
        show (nrd ((x : BHat a b) : QuatAlg FinAdele a b)) q = nrd (hl_ev q (x : BHat a b)) from
          (hl_nrd_ev q _).symm, norm_mul, map_inv₀, map_pow, map_natCast, norm_inv, norm_pow]
      by_cases hq : q = p
      · subst hq
        rw [show nrd (hl_ev q (x : BHat a b)) = (((hl_pi q ι x : GL (Fin 2) ℚ_[q]) :
          Matrix (Fin 2) (Fin 2) ℚ_[q])).det from (hdetx.trans (hl_nrd_ev q _).symm).symm, hdet, Padic.norm_p, inv_pow, inv_inv, zpow_neg, zpow_natCast,
          mul_inv_cancel₀ (pow_ne_zero _ hp1.ne')]
      · have hpq : ‖((p : ℕ) : ℚ_[q])‖ = 1 := by
          have := PadicInt.isUnit_iff.mp (hl_isUnit_p p q hq)
          rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
        have h1 := (hl_loc_trd_nrd O q (hR q hq).1).2
        have h2 := (hl_loc_trd_nrd O q (hR q hq).2).2
        have hm : nrd (hl_ev q (x : BHat a b)) * nrd (hl_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
          rw [← (nrd_trd_basic.{0, 0} (R := ℚ_[q]) (a := a) (b := b)).2.1, hl_ev_units]
          simp [nrd]
        have hn1 : ‖nrd (hl_ev q (x : BHat a b))‖ = 1 := by
          have h3 : ‖nrd (hl_ev q (x : BHat a b))‖ * ‖nrd (hl_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b))‖ = 1 := by
            rw [← norm_mul, hm, norm_one]
          have := norm_nonneg (nrd (hl_ev q (x : BHat a b)))
          have := norm_nonneg (nrd (hl_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b)))
          nlinarith
        rw [hpq, one_pow, inv_one, one_mul, hn1]
    obtain ⟨u, hu⟩ := (zhat_units_explicit y).mpr hyq
    refine ⟨u, ?_⟩
    rw [hu, hy, ← mul_assoc]
    have : (((p : ℕ) ^ r : ℕ) : FinAdele) * algebraMap ℚ FinAdele ((((p : ℕ) : ℚ) ^ r)⁻¹) = 1 := by
      rw [← map_natCast (algebraMap ℚ FinAdele), ← map_mul, Nat.cast_pow,
        mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.2.ne_zero)), map_one]
    rw [this, one_mul]

open scoped Classical in
/-- (4) `Θ(Σ_{a+b=r, a≥b≥0} c_{a,b}) = 1_{Ô_{p^r}}`. -/
private theorem hl_theta_sum {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (O : QOrder a b) (p : Nat.Primes)
    (ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hι : ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule O.toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p])) (r : ℕ) :
    hl_theta O p ι ((∑ j ∈ Finset.range (r / 2 + 1), Local.heckeBasis ℚ_[p] ((r - j : ℕ) : ℤ) (j : ℤ) :
          Local.sphericalHeckeAlgebra ℚ_[p]) : GL (Fin 2) ℚ_[p] → ℂ) =
      (normNSet O ((p : ℕ) ^ r)).indicator (1 : (BHat a b)ˣ → ℂ) := by
  funext x
  simp only [hl_theta]
  rw [hl_sum_cartan_apply]
  by_cases hx : x ∈ normNSet O ((p : ℕ) ^ r)
  · obtain ⟨hR, hP⟩ := (hl_normNSet_iff ha hb O p ι hι r x).mp hx
    rw [if_pos hP, Set.indicator_of_mem hR, Set.indicator_of_mem hx]
    simp
  · rw [Set.indicator_of_notMem hx]
    by_cases hR : x ∈ hl_R O p
    · rw [if_neg (fun hP => hx ((hl_normNSet_iff ha hb O p ι hι r x).mpr ⟨hR, hP⟩)), zero_mul]
    · rw [Set.indicator_of_notMem hR, mul_zero]

/-- The isomorphism `ι_p` chosen in `localHeckeEmbedding` maps the Eichler order at `p ∤ DM` onto `M₂(ℤ_p)`. -/
private theorem hl_choose_split {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b) (hD : RamifiedExactly a b D)
    (φ : LevelStructure O₀.1 M) (p : Nat.Primes) (hpD : ¬ (p : ℕ) ∣ D) (hpM : ¬ (p : ℕ) ∣ M) :
    ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) ↔
      ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p],
        (Classical.choose (maximalOrder_local_split O₀ hD p hpD)) z = m.map (algebraMap ℤ_[p] ℚ_[p]) := by
  have hι := Classical.choose_spec (maximalOrder_local_split O₀ hD p hpD)
  set ι := Classical.choose (maximalOrder_local_split O₀ hD p hpD)
  have hloc : localLattice p (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) =
      localLattice p (Subalgebra.toSubmodule O₀.1.toSubalgebra) :=
    (localLattice_basic p _ O₀.1.fg O₀.1.span_eq_top).2.2.1 _ (eichlerOrder φ).fg (eichlerOrder φ).span_eq_top
      (fun x hx => eichlerSubalgebra_le φ hx) (by rw [(eichlerOrder_index φ).1]; exact hpM)
  intro z
  rw [hloc]
  constructor
  · intro hz
    have : ι z ∈ ι '' (localLattice p (Subalgebra.toSubmodule O₀.1.toSubalgebra) : Set (QuatAlg ℚ_[p] a b)) :=
      ⟨z, hz, rfl⟩
    rw [hι] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩
    have : ι z ∈ ι '' (localLattice p (Subalgebra.toSubmodule O₀.1.toSubalgebra) : Set (QuatAlg ℚ_[p] a b)) := by
      rw [hι]; exact ⟨m, hm.symm⟩
    obtain ⟨z', hz', hzz⟩ := this
    rwa [← ι.injective hzz]

/-- Eichler data, `p ∤ DM`: `Θ_p` maps `H(GL₂(ℚ_p), K_p)` into `H(B̂^×, Ô^×; ℂ)` and is a unital ring homomorphism
there; `Θ_p(Σ_{a+b=r, a≥b≥0} c_{a,b}) = 1_{Ô_{p^r}}` for `r ≥ 0`; and `Θ_p(c_{1,1}) = 1_{ι(p)Ô^×}`. -/
@[tf_id "III.brandt.thm:local-hecke-embedding-hom"]
theorem localHeckeEmbedding_hom {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b) (hD : RamifiedExactly a b D)
    (φ : LevelStructure O₀.1 M) (p : Nat.Primes) (hpD : ¬ (p : ℕ) ∣ D) (hpM : ¬ (p : ℕ) ∣ M) :
    (∀ Φ : Local.sphericalHeckeAlgebra ℚ_[p], HeckePair.IsHeckeFun (U := orderCompletionUnits (eichlerOrder φ))
      (localHeckeEmbedding O₀ hD φ p hpD (Φ : GL (Fin 2) ℚ_[p] → ℂ))) ∧
    (∃ h : HeckePair.IsHeckeFun (U := orderCompletionUnits (eichlerOrder φ))
        (localHeckeEmbedding O₀ hD φ p hpD ((1 : Local.sphericalHeckeAlgebra ℚ_[p]) : GL (Fin 2) ℚ_[p] → ℂ)),
      (⟨_, h⟩ : HeckePair.HeckeAlgebra (orderCompletionUnits (eichlerOrder φ)) ℂ) = 1) ∧
    (∀ Φ₁ Φ₂ : Local.sphericalHeckeAlgebra ℚ_[p],
      ∃ (h₁ : HeckePair.IsHeckeFun (U := orderCompletionUnits (eichlerOrder φ))
          (localHeckeEmbedding O₀ hD φ p hpD (Φ₁ : GL (Fin 2) ℚ_[p] → ℂ)))
        (h₂ : HeckePair.IsHeckeFun (U := orderCompletionUnits (eichlerOrder φ))
          (localHeckeEmbedding O₀ hD φ p hpD (Φ₂ : GL (Fin 2) ℚ_[p] → ℂ)))
        (h₁₂ : HeckePair.IsHeckeFun (U := orderCompletionUnits (eichlerOrder φ))
          (localHeckeEmbedding O₀ hD φ p hpD ((Φ₁ * Φ₂ : Local.sphericalHeckeAlgebra ℚ_[p]) : GL (Fin 2) ℚ_[p] → ℂ))),
        (⟨_, h₁⟩ * ⟨_, h₂⟩ : HeckePair.HeckeAlgebra (orderCompletionUnits (eichlerOrder φ)) ℂ) = ⟨_, h₁₂⟩) ∧
    (∀ r : ℕ, localHeckeEmbedding O₀ hD φ p hpD
        ((∑ j ∈ Finset.range (r / 2 + 1), Local.heckeBasis ℚ_[p] ((r - j : ℕ) : ℤ) (j : ℤ) :
          Local.sphericalHeckeAlgebra ℚ_[p]) : GL (Fin 2) ℚ_[p] → ℂ) =
      (normNSet (eichlerOrder φ) ((p : ℕ) ^ r)).indicator (1 : (BHat a b)ˣ → ℂ)) ∧
    localHeckeEmbedding O₀ hD φ p hpD ((Local.heckeBasis ℚ_[p] 1 1 : Local.sphericalHeckeAlgebra ℚ_[p]) :
        GL (Fin 2) ℚ_[p] → ℂ) =
      {x : (BHat a b)ˣ | ∃ u ∈ orderCompletionUnits (eichlerOrder φ),
        x = Units.map (finEmbed a b).toMonoidHom
          (Units.map (algebraMap ℚ (QuatAlg ℚ a b)).toMonoidHom
            (Units.mk0 ((p : ℕ) : ℚ) (Nat.cast_ne_zero.mpr p.2.ne_zero))) * u}.indicator (1 : (BHat a b)ˣ → ℂ) := by
  have ha : a ≠ 0 := hD.1.ne
  have hb : b ≠ 0 := hD.2.1.ne
  have hι := hl_choose_split O₀ hD φ p hpD hpM
  set ι := Classical.choose (maximalOrder_local_split O₀ hD p hpD) with hιdef
  set O := eichlerOrder φ with hO
  exact ⟨fun Φ => hl_theta_hecke O p ι hι Φ,
    ⟨hl_theta_hecke O p ι hι 1, Subtype.ext (hl_theta_one O p ι hι)⟩,
    fun Φ₁ Φ₂ => ⟨hl_theta_hecke O p ι hι Φ₁, hl_theta_hecke O p ι hι Φ₂, hl_theta_hecke O p ι hι (Φ₁ * Φ₂),
      Subtype.ext (hl_theta_mul O p ι hι Φ₁ Φ₂).symm⟩,
    fun r => hl_theta_sum ha hb O p ι hι r,
    hl_theta_c11 O p ι hι⟩

/-- `ι_p(O_p) = M₂(ℤ_p)` for the Eichler order at `p ∤ DM`, in membership form. -/
private theorem hl_eichler_split {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b) (hD : RamifiedExactly a b D)
    (φ : LevelStructure O₀.1 M) (p : ℕ) [Fact p.Prime] (hpD : ¬ p ∣ D) (hpM : ¬ p ∣ M) :
    ∃ ι : QuatAlg ℚ_[p] a b ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p],
      ∀ z, z ∈ localLattice p (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) ↔
        ∃ m : Matrix (Fin 2) (Fin 2) ℤ_[p], ι z = m.map (algebraMap ℤ_[p] ℚ_[p]) := by
  obtain ⟨ι, hι⟩ := maximalOrder_local_split O₀ hD p hpD
  have hloc : localLattice p (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) =
      localLattice p (Subalgebra.toSubmodule O₀.1.toSubalgebra) :=
    (localLattice_basic p _ O₀.1.fg O₀.1.span_eq_top).2.2.1 _ (eichlerOrder φ).fg (eichlerOrder φ).span_eq_top
      (fun x hx => eichlerSubalgebra_le φ hx) (by rw [(eichlerOrder_index φ).1]; exact hpM)
  refine ⟨ι, fun z => ?_⟩
  rw [hloc]
  constructor
  · intro hz
    have : ι z ∈ ι '' (localLattice p (Subalgebra.toSubmodule O₀.1.toSubalgebra) : Set (QuatAlg ℚ_[p] a b)) :=
      ⟨z, hz, rfl⟩
    rw [hι] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, hm⟩
    have : ι z ∈ ι '' (localLattice p (Subalgebra.toSubmodule O₀.1.toSubalgebra) : Set (QuatAlg ℚ_[p] a b)) := by
      rw [hι]; exact ⟨m, hm.symm⟩
    obtain ⟨z', hz', hzz⟩ := this
    rwa [← ι.injective hzz]

/-- Eichler data, `n ≥ 1` prime to `DM`: `|Ô_n / Ô^×| = σ₁(n)`. -/
@[tf_id "III.brandt.thm:hecke-coset-count"]
theorem hecke_coset_count {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b) (hD : RamifiedExactly a b D)
    (φ : LevelStructure O₀.1 M) (n : ℕ) (hn : 0 < n) (hnDM : Nat.Coprime n (D * M)) :
    Nat.card (QuotientGroup.mk '' normNSet (eichlerOrder φ) n :
        Set ((BHat a b)ˣ ⧸ orderCompletionUnits (eichlerOrder φ))) =
      ArithmeticFunction.sigma 1 n := by
  have ha : a ≠ 0 := hD.1.ne
  have hb : b ≠ 0 := hD.2.1.ne
  set O := eichlerOrder φ with hO
  have hpp : ∀ p : ℕ, p.Prime → ¬ p ∣ D * M → ∀ r : ℕ,
      Nat.card (QuotientGroup.mk '' normNSet O (p ^ r) : Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) =
        ArithmeticFunction.sigma 1 (p ^ r) := by
    intro p hp hpDM r
    have := Fact.mk hp
    obtain ⟨ι, hι⟩ := hl_eichler_split O₀ hD φ p (fun h => hpDM (dvd_mul_of_dvd_left h M))
      (fun h => hpDM (dvd_mul_of_dvd_right h D))
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    exact hl_count_prime_pow ha hb O ⟨p, hp⟩ ι hι r
  revert hn hnDM
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow q j hq hj =>
    intro _ hqj
    have hqDM : ¬ q ∣ D * M := by
      have := Nat.Coprime.coprime_dvd_left (dvd_pow_self q hj.ne') hqj
      exact (Nat.Prime.coprime_iff_not_dvd hq).mp this
    exact hpp q hq hqDM j
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ _
    rw [(normNSet_basic O 1 Nat.one_pos).2.2.1]
    have : (QuotientGroup.mk '' ((orderCompletionUnits O : Subgroup (BHat a b)ˣ) : Set (BHat a b)ˣ) :
        Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) = {QuotientGroup.mk 1} := by
      ext c
      simp only [Set.mem_image, SetLike.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact QuotientGroup.eq.mpr (by simpa using inv_mem hx)
      · rintro rfl; exact ⟨1, one_mem _, rfl⟩
    rw [this, Nat.card_coe_set_eq, Set.ncard_singleton]
    simp
  | coprime a' b' ha' hb' hab iha ihb =>
    intro _ habDM
    have haDM := Nat.Coprime.coprime_dvd_left (dvd_mul_right a' b') habDM
    have hbDM := Nat.Coprime.coprime_dvd_left (dvd_mul_left b' a') habDM
    rw [(normNSet_product O a' b' (by omega) (by omega) hab).2.2.2, iha (by omega) haDM, ihb (by omega) hbDM,
      ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (ArithmeticFunction.isMultiplicative_sigma (k := 1)) hab]

/-! ### Proof helpers for `hecke_recursion` (Q3 part 5): products and quotients of the sets `Ô_n`, and `ι(p) ∈ Ô_{p²}`. -/

private theorem hl_nrd_mulB {a b : ℤ} (x y : BHat a b) :
    nrd (show QuatAlg FinAdele a b from x * y) =
      nrd (show QuatAlg FinAdele a b from x) * nrd (show QuatAlg FinAdele a b from y) :=
  (nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).2.1 x y

/-- `Ô_m Ô_n ⊆ Ô_{mn}`. -/
private theorem hl_mul_mem {a b : ℤ} (O : QOrder a b) {m n : ℕ} {y z : (BHat a b)ˣ}
    (hy : y ∈ normNSet O m) (hz : z ∈ normNSet O n) : y * z ∈ normNSet O (m * n) := by
  obtain ⟨hyO, u, hu⟩ := hy
  obtain ⟨hzO, v, hv⟩ := hz
  refine ⟨?_, u * v, ?_⟩
  · rw [Units.val_mul]
    exact mul_mem_orderCompletion O hyO hzO
  · rw [Units.val_mul, hl_nrd_mulB]
    erw [hu, hv]
    simp only [Units.val_mul, Subring.coe_mul, Nat.cast_mul]
    ring

/-- For `y ∈ Ô_m`, `x ∈ Ô_{mn}` (`m ≥ 1`) with `y⁻¹x ∈ Ô`: `y⁻¹x ∈ Ô_n`. -/
private theorem hl_div_mem {a b : ℤ} (O : QOrder a b) {m n : ℕ} (hm : 0 < m) {y x : (BHat a b)ˣ}
    (hy : y ∈ normNSet O m) (hx : x ∈ normNSet O (m * n))
    (hO : ((y⁻¹ * x : (BHat a b)ˣ) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    y⁻¹ * x ∈ normNSet O n := by
  obtain ⟨-, u, hu⟩ := hy
  obtain ⟨-, v, hv⟩ := hx
  refine ⟨hO, u⁻¹ * v, ?_⟩
  have h : nrd (show QuatAlg FinAdele a b from (y : BHat a b)) *
      nrd (show QuatAlg FinAdele a b from ((y⁻¹ * x : (BHat a b)ˣ) : BHat a b)) =
      nrd (show QuatAlg FinAdele a b from (x : BHat a b)) := by
    rw [← hl_nrd_mulB, ← Units.val_mul, mul_inv_cancel_left]
  erw [hu, hv] at h
  have e1 : (m : FinAdele) * algebraMap ℚ FinAdele ((m : ℚ)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℚ FinAdele), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm.ne'), map_one]
  have e2 : ((u : Zhat) : FinAdele) * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele) = 1 := by
    have := congrArg (fun z : Zhat => (z : FinAdele)) u.mul_inv
    simpa only [Subring.coe_mul, Subring.coe_one] using this
  set N := nrd (show QuatAlg FinAdele a b from ((y⁻¹ * x : (BHat a b)ˣ) : BHat a b)) with hN
  show N = _
  simp only [Units.val_mul, Subring.coe_mul, Nat.cast_mul] at h ⊢
  linear_combination (algebraMap ℚ FinAdele ((m : ℚ)⁻¹) * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele)) * h -
    (N - (n : FinAdele) * ((((u⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((v : Zhat) : FinAdele))) * e1 -
    (N * (m : FinAdele) * algebraMap ℚ FinAdele ((m : ℚ)⁻¹)) * e2

/-- The central unit `ι(p)` (any `p`) lies in `Ô_{p²}`. -/
private theorem hl_P_mem {a b : ℤ} (O : QOrder a b) (p : ℕ) {P : (BHat a b)ˣ}
    (hP : (P : BHat a b) = ((p : ℕ) : BHat a b)) : P ∈ normNSet O (p ^ 2) := by
  refine ⟨?_, 1, ?_⟩
  · rw [hP, ← nsmul_one]
    exact nsmul_mem (one_mem_orderCompletion O) p
  · rw [hP]
    show nrd ((p : ℕ) : QuatAlg FinAdele a b) = _
    simp [nrd]

/-- Eichler data, a prime `p ∤ DM`, `r ≥ 1`, `k ≥ 2`: `T_p T_{p^r} = T_{p^{r+1}} + p^{k−1} T_{p^{r−1}}` on `M_k(O; s)`. -/
@[tf_id "III.brandt.thm:hecke-recursion"]
theorem hecke_recursion {K : Type*} [Field K] [CharZero K] {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b)
    (hD : RamifiedExactly a b D) (φ : LevelStructure O₀.1 M) (s : Splitting K a b) (k : ℕ) (hk : 2 ≤ k)
    (p : ℕ) (hp : p.Prime) (hpDM : ¬ p ∣ D * M) (r : ℕ) (hr : 1 ≤ r) :
    ∀ f ∈ quatForms (eichlerOrder φ) s k,
      heckeOperator (eichlerOrder φ) p (heckeOperator (eichlerOrder φ) (p ^ r) f) =
        heckeOperator (eichlerOrder φ) (p ^ (r + 1)) f +
          ((p : K) ^ (k - 1)) • heckeOperator (eichlerOrder φ) (p ^ (r - 1)) f := by
  classical
  intro f hf
  have ha : a ≠ 0 := hD.1.ne
  have hb : b ≠ 0 := hD.2.1.ne
  obtain ⟨pp, rfl⟩ : ∃ pp : Nat.Primes, (pp : ℕ) = p := ⟨⟨p, hp⟩, rfl⟩
  set O := eichlerOrder φ with hO
  obtain ⟨ι, hι⟩ := hl_eichler_split O₀ hD φ (pp : ℕ) (fun h => hpDM (dvd_mul_of_dvd_left h M))
    (fun h => hpDM (dvd_mul_of_dvd_right h D))
  have hppos : 0 < (pp : ℕ) := pp.2.pos
  -- the central element `P = ι(p)`
  set γ : (QuatAlg ℚ a b)ˣ := Units.map (algebraMap ℚ (QuatAlg ℚ a b)).toMonoidHom
    (Units.mk0 ((pp : ℕ) : ℚ) (Nat.cast_ne_zero.mpr pp.2.ne_zero)) with hγ
  set P : (BHat a b)ˣ := Units.map (finEmbed a b).toMonoidHom γ with hP
  have hγval : ((γ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = ((pp : ℕ) : QuatAlg ℚ a b) := by
    simp [hγ]
  have hPval : ((P : (BHat a b)ˣ) : BHat a b) = ((pp : ℕ) : BHat a b) := by
    rw [hP, Units.coe_map]
    show finEmbed a b (γ : QuatAlg ℚ a b) = _
    rw [hγval, map_natCast]
  have hcomm : ∀ x : (BHat a b)ˣ, x * P = P * x := by
    intro x
    ext
    rw [Units.val_mul, Units.val_mul, hPval]
    exact (Nat.cast_comm _ _).symm
  have hP2 : P ∈ normNSet O ((pp : ℕ) ^ 2) := hl_P_mem O pp hPval
  -- Hecke functions
  have hH : ∀ n : ℕ, 0 < n → HeckePair.IsHeckeFun (U := orderCompletionUnits O)
      ((normNSet O n).indicator (1 : (BHat a b)ˣ → ℤ)) := fun n hn => (normNSet_basic O n hn).2.2.2.2 ℤ
  set N := normNSet O ((pp : ℕ) ^ (r - 1)) with hNdef
  have hN := hH ((pp : ℕ) ^ (r - 1)) (pow_pos hppos _)
  set g : (BHat a b)ˣ → ℤ := fun x => N.indicator (1 : (BHat a b)ˣ → ℤ) (P⁻¹ * x) with hgdef
  have hg : HeckePair.IsHeckeFun (U := orderCompletionUnits O) g := by
    refine ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩
    · show N.indicator (1 : (BHat a b)ˣ → ℤ) (P⁻¹ * (u * x)) = N.indicator (1 : (BHat a b)ˣ → ℤ) (P⁻¹ * x)
      have hc : P⁻¹ * u = u * P⁻¹ := ((Commute.inv_right (hcomm u : Commute u P))).eq.symm
      rw [← mul_assoc, hc, mul_assoc]
      exact hN.left_inv u hu _
    · show N.indicator (1 : (BHat a b)ˣ → ℤ) (P⁻¹ * (x * u)) = N.indicator (1 : (BHat a b)ˣ → ℤ) (P⁻¹ * x)
      rw [← mul_assoc]
      exact hN.right_inv u hu _
    · refine (hN.finite_cosets.image (fun c => P • c)).subset ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨QuotientGroup.mk (P⁻¹ * x), ⟨P⁻¹ * x, hx, rfl⟩, ?_⟩
      show P • (QuotientGroup.mk (P⁻¹ * x) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk x
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_inv_cancel_left]
  -- local data at `p`
  set f₀ := algebraMap ℤ_[pp] ℚ_[pp] with hf₀
  have hfinj : Function.Injective f₀ := fun x y h => Subtype.ext h
  have hfp : f₀ ((pp : ℕ) : ℤ_[pp]) = ((pp : ℕ) : ℚ_[pp]) := map_natCast f₀ _
  have hdetmap : ∀ m : Matrix (Fin 2) (Fin 2) ℤ_[pp], (m.map f₀).det = f₀ m.det :=
    fun m => (RingHom.map_det f₀ m).symm
  have hdetι : ∀ z : QuatAlg ℚ_[pp] a b, (ι z).det = nrd z := fun z =>
    hl_det_eq_nrd ha hb (ι : QuatAlg ℚ_[pp] a b →ₐ[ℚ_[pp]] Matrix (Fin 2) (Fin 2) ℚ_[pp]) z
  have hpne : ((pp : ℕ) : ℚ_[pp]) ≠ 0 := Nat.cast_ne_zero.mpr pp.2.ne_zero
  have hnat : ∀ A : Matrix (Fin 2) (Fin 2) ℚ_[pp],
      ((pp : ℕ) : Matrix (Fin 2) (Fin 2) ℚ_[pp]) * A = ((pp : ℕ) : ℚ_[pp]) • A := by
    intro A
    rw [← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  have hsm : ∀ M : Matrix (Fin 2) (Fin 2) ℤ_[pp],
      (((pp : ℕ) : ℤ_[pp]) • M).map f₀ = ((pp : ℕ) : ℚ_[pp]) • M.map f₀ := by
    intro M
    ext i j
    simp [hf₀]
  have hw : ∀ (q : Nat.Primes) (x : (BHat a b)ˣ),
      ((pp : ℕ) : QuatAlg ℚ_[q] a b) * hl_ev q ((P⁻¹ * x : (BHat a b)ˣ) : BHat a b) = hl_ev q (x : BHat a b) := by
    intro q x
    rw [show ((pp : ℕ) : QuatAlg ℚ_[q] a b) = hl_ev q ((P : (BHat a b)ˣ) : BHat a b) by
        rw [hPval]; exact (map_natCast (hl_ev q) (pp : ℕ)).symm,
      ← hl_ev_mul, ← Units.val_mul, mul_inv_cancel_left]
  -- the convolution identity `1_{Ô_p} ∗ 1_{Ô_{p^r}} = 1_{Ô_{p^{r+1}}} + p · 1_{ι(p) Ô_{p^{r-1}}}`
  have key : (⟨_, hH (pp : ℕ) hppos⟩ * ⟨_, hH ((pp : ℕ) ^ r) (pow_pos hppos _)⟩ :
      HeckePair.HeckeAlgebra (orderCompletionUnits O) ℤ) =
      ⟨_, hH ((pp : ℕ) ^ (r + 1)) (pow_pos hppos _)⟩ + ((pp : ℕ) : ℤ) • ⟨g, hg⟩ := by
    ext x
    rw [HeckePair.mul_apply, HeckePair.coe_apply_add, HeckePair.coe_apply_smul]
    have hterm : ∀ y : (BHat a b)ˣ, HeckePair.convTerm ⟨_, hH (pp : ℕ) hppos⟩
        ⟨_, hH ((pp : ℕ) ^ r) (pow_pos hppos _)⟩ x (QuotientGroup.mk y) =
        (normNSet O (pp : ℕ)).indicator (1 : (BHat a b)ˣ → ℤ) y *
          (normNSet O ((pp : ℕ) ^ r)).indicator (1 : (BHat a b)ˣ → ℤ) (y⁻¹ * x) := fun y => rfl
    show _ = (normNSet O ((pp : ℕ) ^ (r + 1))).indicator (1 : (BHat a b)ˣ → ℤ) x + ((pp : ℕ) : ℤ) * g x
    by_cases hx : x ∈ normNSet O ((pp : ℕ) ^ (r + 1))
    · obtain ⟨Y, hYp, hYq, hY1, hY2, hY3⟩ := hl_reps ha hb O pp ι hι 1
      have hY1' : ∀ t, Y t ∈ normNSet O (pp : ℕ) := fun t => by simpa only [pow_one] using hY1 t
      have hx' : x ∈ normNSet O ((pp : ℕ) * (pp : ℕ) ^ r) := by rwa [← pow_succ']
      have hxO := hx.1
      obtain ⟨X, hX⟩ := (hι _).mp ((hl_mem_iff_local O _).mp hxO pp)
      have hXdet : ((pp : ℕ) : ℤ_[pp]) ∣ X.det := by
        obtain ⟨-, u, hu⟩ := hx
        obtain ⟨v, hv⟩ := (zhat_units_explicit ((u : Zhat) : FinAdele)).mp ⟨u, rfl⟩ pp
        have hdet : X.det = ((pp : ℕ) : ℤ_[pp]) ^ (r + 1) * (v : ℤ_[pp]) := by
          apply hfinj
          rw [← hdetmap, ← hX, hdetι]
          erw [hl_nrd_ev pp, hu]
          rw [RestrictedProduct.mul_apply, ← hv, map_mul, map_pow, hfp]
          congr 1
          show RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) pp
            ((((pp : ℕ) ^ (r + 1) : ℕ)) : FinAdele) = _
          rw [map_natCast, Nat.cast_pow]
        exact ⟨((pp : ℕ) : ℤ_[pp]) ^ r * (v : ℤ_[pp]), by rw [hdet]; ring⟩
      -- the local criterion for `Y_t⁻¹ x ∈ Ô_{p^r}`
      have hdiv : ∀ t, (Y t)⁻¹ * x ∈ normNSet O ((pp : ℕ) ^ r) ↔
          ∃ M, X = hl_hnf (pp : ℕ) 1 t.1 t.2 * M := by
        intro t
        have hYu : IsUnit ((hl_hnf (pp : ℕ) 1 t.1 t.2).map f₀) := by
          rw [← hYp t]
          exact (((Y t).isUnit).map (hl_ev pp)).map ι
        have h1 : ι (hl_ev pp ((Y t : (BHat a b)ˣ) : BHat a b)) *
            ι (hl_ev pp (((Y t)⁻¹ * x : (BHat a b)ˣ) : BHat a b)) = X.map f₀ := by
          rw [← map_mul, ← hl_ev_mul, ← Units.val_mul, mul_inv_cancel_left, hX]
        rw [hYp t] at h1
        constructor
        · intro h
          obtain ⟨M, hM⟩ := (hι _).mp ((hl_mem_iff_local O _).mp h.1 pp)
          refine ⟨M, Matrix.map_injective hfinj ?_⟩
          show X.map f₀ = (hl_hnf (pp : ℕ) 1 t.1 t.2 * M).map f₀
          rw [Matrix.map_mul, ← h1, hM]
        · rintro ⟨M, hM⟩
          refine hl_div_mem O hppos (hY1' t) hx' ?_
          rw [hl_mem_iff_local]
          intro q
          by_cases hq : q = pp
          · rw [hq, hι]
            refine ⟨M, hYu.mul_left_cancel ?_⟩
            rw [h1, hM, Matrix.map_mul]
          · rw [Units.val_mul, hl_ev_mul, hYq t q hq, one_mul]
            exact (hl_mem_iff_local O _).mp hxO q
      have hLHS : ∑ᶠ c, HeckePair.convTerm ⟨_, hH (pp : ℕ) hppos⟩
          ⟨_, hH ((pp : ℕ) ^ r) (pow_pos hppos _)⟩ x c =
          ∑ t : (Σ i : Fin (1 + 1), Fin ((pp : ℕ) ^ (i : ℕ))),
            if ∃ M, X = hl_hnf (pp : ℕ) 1 t.1 t.2 * M then (1 : ℤ) else 0 := by
        have hsupp : Function.support (HeckePair.convTerm ⟨_, hH (pp : ℕ) hppos⟩
            ⟨_, hH ((pp : ℕ) ^ r) (pow_pos hppos _)⟩ x) ⊆
            ((Finset.univ.image (fun t => (QuotientGroup.mk (Y t) : (BHat a b)ˣ ⧸ orderCompletionUnits O))) :
              Set ((BHat a b)ˣ ⧸ orderCompletionUnits O)) := by
          intro c hc
          obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
          rw [Function.mem_support, hterm] at hc
          have hy : y ∈ normNSet O (pp : ℕ) := by
            by_contra h
            rw [Set.indicator_of_notMem h, zero_mul] at hc
            exact hc rfl
          obtain ⟨t, ht⟩ := hY3 y (by simpa only [pow_one] using hy)
          simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
          exact ⟨t, ht⟩
        rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun t _ t' _ h => hY2 t t' h)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hterm, Set.indicator_of_mem (hY1' t), Pi.one_apply, one_mul]
        by_cases hM : ∃ M, X = hl_hnf (pp : ℕ) 1 t.1 t.2 * M
        · rw [if_pos hM, Set.indicator_of_mem ((hdiv t).mpr hM), Pi.one_apply]
        · rw [if_neg hM, Set.indicator_of_notMem (fun h => hM ((hdiv t).mp h))]
      have hRHS : g x = if ∃ M, X = ((pp : ℕ) : ℤ_[pp]) • M then (1 : ℤ) else 0 := by
        show N.indicator (1 : (BHat a b)ˣ → ℤ) (P⁻¹ * x) = _
        by_cases hM : ∃ M, X = ((pp : ℕ) : ℤ_[pp]) • M
        · rw [if_pos hM, Set.indicator_of_mem, Pi.one_apply]
          obtain ⟨M, hM⟩ := hM
          have hx'' : x ∈ normNSet O ((pp : ℕ) ^ 2 * (pp : ℕ) ^ (r - 1)) := by
            rw [← pow_add, show 2 + (r - 1) = r + 1 by omega]
            exact hx
          refine hl_div_mem O (pow_pos hppos 2) hP2 hx'' ?_
          rw [hl_mem_iff_local]
          intro q
          by_cases hq : q = pp
          · rw [hq, hι]
            refine ⟨M, ?_⟩
            have h1 := congrArg ι (hw pp x)
            rw [map_mul, map_natCast, hX, hM, hnat, hsm] at h1
            exact smul_right_injective _ hpne h1
          · have hxq := (hl_mem_iff_local O _).mp hxO q
            have hu1 : ((((hl_isUnit_p pp q hq).unit⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) * ((pp : ℕ) : ℚ_[q]) = 1 := by
              have := congrArg (fun z : ℤ_[q] => (z : ℚ_[q])) (hl_isUnit_p pp q hq).val_inv_mul
              simpa only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] using this
            have hweq : hl_ev q ((P⁻¹ * x : (BHat a b)ˣ) : BHat a b) =
                (((hl_isUnit_p pp q hq).unit⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) • hl_ev q (x : BHat a b) := by
              rw [← hw q x, ← algebraMap_smul ℚ_[q], ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ_[q], smul_smul]
              show _ = (((((hl_isUnit_p pp q hq).unit⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℚ_[q]) * ((pp : ℕ) : ℚ_[q])) • _
              rw [hu1, one_smul]
            rw [hweq]
            exact Submodule.smul_mem _ _ hxq
        · rw [if_neg hM, Set.indicator_of_notMem]
          intro hmem
          apply hM
          obtain ⟨W, hW⟩ := (hι _).mp ((hl_mem_iff_local O _).mp hmem.1 pp)
          refine ⟨W, Matrix.map_injective hfinj ?_⟩
          show X.map f₀ = (((pp : ℕ) : ℤ_[pp]) • W).map f₀
          have h1 := congrArg ι (hw pp x)
          rw [map_mul, map_natCast, hX, hW, hnat] at h1
          rw [hsm, ← h1]
      rw [hLHS, Set.indicator_of_mem hx, Pi.one_apply, hRHS]
      exact hl_mat_count X hXdet
    · rw [Set.indicator_of_notMem hx]
      have hg0 : g x = 0 := by
        show N.indicator (1 : (BHat a b)ˣ → ℤ) (P⁻¹ * x) = 0
        rw [Set.indicator_of_notMem]
        intro hmem
        apply hx
        have := hl_mul_mem O hP2 hmem
        rwa [mul_inv_cancel_left, ← pow_add, show 2 + (r - 1) = r + 1 by omega] at this
      rw [hg0, mul_zero, add_zero]
      refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
      rw [hterm]
      by_cases hy : y ∈ normNSet O (pp : ℕ)
      · by_cases hz : y⁻¹ * x ∈ normNSet O ((pp : ℕ) ^ r)
        · exfalso
          apply hx
          have := hl_mul_mem O hy hz
          rwa [mul_inv_cancel_left, ← pow_succ'] at this
        · rw [Set.indicator_of_notMem hz, mul_zero]
      · rw [Set.indicator_of_notMem hy, zero_mul]
  -- the action
  have hbasic := symPower_basic K (k - 2)
  have hinv : ∀ x u : (BHat a b)ˣ, u ∈ orderCompletionUnits O → f (x * u) = f x := by
    intro x u hu
    have h := hf 1 x u hu
    simp only [map_one, one_mul, Units.val_one, splitRep, hbasic.2.2.2.1, Module.End.one_apply] at h
    exact h
  have hPf : ∀ z, f (P * z) = ((pp : ℕ) : K) ^ (k - 2) • f z := by
    intro z
    have hs : s (γ : QuatAlg ℚ a b) = Matrix.scalar (Fin 2) ((pp : ℕ) : K) := by
      rw [hγval, map_natCast]
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    have h := hf γ z 1 (one_mem _)
    rw [mul_one] at h
    refine h.trans ?_
    show splitRep s k (γ : QuatAlg ℚ a b) (f z) = _
    rw [splitRep, hs, hbasic.2.2.2.2.1, LinearMap.smul_apply, Module.End.one_apply]
  have hmod := heckeAct_module K (R₀ := ℤ) (Units.map (finEmbed a b).toMonoidHom) (orderCompletionUnits O)
    (fun γ => splitRep s k (γ : QuatAlg ℚ a b))
    (by
      show splitRep s k ((1 : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1
      rw [Units.val_one, splitRep, map_one, (symPower_basic K (k - 2)).2.2.2.1])
    (fun γ r v => map_zsmul _ r v)
  have hgact : heckeAct (U := orderCompletionUnits O) g f =
      ((pp : ℕ) : K) ^ (k - 2) • heckeAct (U := orderCompletionUnits O) (N.indicator (1 : (BHat a b)ˣ → ℤ)) f := by
    funext x
    rw [Pi.smul_apply]
    unfold heckeAct
    set τ : (BHat a b)ˣ → symPowerModule K (k - 2) := fun z => g z • f (x * z) with hτdef
    have hτ : ∀ z, ∀ u ∈ orderCompletionUnits O, τ (z * u) = τ z := by
      intro z u hu
      simp only [hτdef]
      rw [hg.right_inv u hu z, ← mul_assoc, hinv _ _ hu]
    have hfin : (Function.support fun c : (BHat a b)ˣ ⧸ orderCompletionUnits O =>
        (N.indicator (1 : (BHat a b)ˣ → ℤ)) (Quotient.out c) • f (x * Quotient.out c)).Finite :=
      heckeAct_support_finite ⟨_, hN⟩ f x
    refine (coset_finsum_translate hτ P).symm.trans ?_
    rw [smul_finsum' _ hfin]
    refine finsum_congr fun c => ?_
    simp only [hτdef, hgdef]
    rw [inv_mul_cancel_left, ← mul_assoc, hcomm x, mul_assoc, hPf]
    exact smul_comm _ _ _
  unfold heckeOperator
  have h1 := hmod.2.2.1 ⟨_, hH (pp : ℕ) hppos⟩ ⟨_, hH ((pp : ℕ) ^ r) (pow_pos hppos _)⟩ f hf
  refine h1.symm.trans ?_
  rw [key, hmod.2.2.2.1 _ _ f hf, hmod.2.2.2.2.1 _ _ f hf]
  show heckeAct (U := orderCompletionUnits O) ((normNSet O ((pp : ℕ) ^ (r + 1))).indicator (1 : (BHat a b)ˣ → ℤ)) f +
      ((pp : ℕ) : ℤ) • heckeAct (U := orderCompletionUnits O) g f = _
  rw [hgact, ← Int.cast_smul_eq_zsmul K, smul_smul]
  congr 2
  push_cast
  rw [← pow_succ']
  congr 1
  omega

/-- **Exit.** Eichler data, `m, n` prime to `DM`: `T_m T_n = T_n T_m` on `M_k(O; s)`, for every field `K` of
characteristic `0` and every splitting `s`. -/
@[tf_id "III.brandt.thm:hecke-commutative"]
theorem hecke_commutative {K : Type*} [Field K] [CharZero K] {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b)
    (hD : RamifiedExactly a b D) (φ : LevelStructure O₀.1 M) (s : Splitting K a b) (k : ℕ) (m n : ℕ)
    (hm : Nat.Coprime m (D * M)) (hn : Nat.Coprime n (D * M)) :
    ∀ f ∈ quatForms (eichlerOrder φ) s k,
      heckeOperator (eichlerOrder φ) m (heckeOperator (eichlerOrder φ) n f) =
        heckeOperator (eichlerOrder φ) n (heckeOperator (eichlerOrder φ) m f) := by
  -- weights `k < 2` are weight 2 (`k − 2` is truncated), so it suffices to treat `k ≥ 2`
  suffices H : ∀ k' : ℕ, 2 ≤ k' → ∀ f ∈ quatForms (eichlerOrder φ) s k',
      heckeOperator (eichlerOrder φ) m (heckeOperator (eichlerOrder φ) n f) =
        heckeOperator (eichlerOrder φ) n (heckeOperator (eichlerOrder φ) m f) by
    rcases le_or_gt 2 k with hk | hk
    · exact H k hk
    · intro f hf
      interval_cases k
      · exact H 2 le_rfl f hf
      · exact H 2 le_rfl f hf
  intro k hk f hf
  revert m n
  set O := eichlerOrder φ with hO
  set W := quatForms O s k with hW
  have hmod := heckeAct_module K (R₀ := ℤ) (Units.map (finEmbed a b).toMonoidHom) (orderCompletionUnits O)
    (fun γ => splitRep s k (γ : QuatAlg ℚ a b))
    (by
      show splitRep s k ((1 : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1
      rw [Units.val_one, splitRep, map_one, (symPower_basic K (k - 2)).2.2.2.1])
    (fun γ r v => map_zsmul _ r v)
  have hH : ∀ j : ℕ, 0 < j → HeckePair.IsHeckeFun (U := orderCompletionUnits O)
      ((normNSet O j).indicator (1 : (BHat a b)ˣ → ℤ)) := fun j hj => (normNSet_basic O j hj).2.2.2.2 ℤ
  have hT0 : ∀ g : (BHat a b)ˣ → symPowerModule K (k - 2), heckeOperator O 0 g = 0 := by
    intro g
    have hempty : normNSet O 0 = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, u, hu⟩
      rw [Nat.cast_zero, zero_mul] at hu
      have h := congrArg (fun z : FinAdele => z * nrd (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b))) hu
      simp only [zero_mul] at h
      have h1 : nrd (show QuatAlg FinAdele a b from (y : BHat a b)) *
          nrd (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
        rw [← (nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).2.1]
        show nrd (show QuatAlg FinAdele a b from ((y * y⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1
        rw [mul_inv_cancel, Units.val_one]
        show nrd (1 : QuatAlg FinAdele a b) = 1
        simp [nrd]
      rw [h1] at h
      have h2 := congrArg (fun z : FinAdele => z ⟨2, Nat.prime_two⟩) h
      simp only [RestrictedProduct.one_apply, RestrictedProduct.zero_apply] at h2
      exact one_ne_zero h2
    funext x
    simp [heckeOperator, heckeAct, hempty]
  have hT1 : ∀ g ∈ W, heckeOperator O 1 g = g := by
    intro g hg
    have h := hmod.2.1 g hg
    rw [HeckePair.coe_one] at h
    rw [heckeOperator, (normNSet_basic O 1 Nat.one_pos).2.2.1]
    exact h
  have hTW : ∀ j : ℕ, ∀ g ∈ W, heckeOperator O j g ∈ W := by
    intro j g hg
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [hT0]; exact Submodule.zero_mem _
    · exact hmod.1 ⟨_, hH j hj⟩ g hg
  have hsmul : ∀ (j : ℕ) (c : K) (g : (BHat a b)ˣ → symPowerModule K (k - 2)),
      heckeOperator O j (c • g) = c • heckeOperator O j g := by
    intro j c g
    funext x
    simp only [heckeOperator, heckeAct, Pi.smul_apply]
    rw [smul_finsum]
    exact finsum_congr fun C => smul_comm _ _ _
  have hlin : ∀ j : ℕ, ∀ g ∈ W, ∀ h ∈ W, ∀ c : K,
      heckeOperator O j (g - c • h) = heckeOperator O j g - c • heckeOperator O j h := by
    intro j g hg h hh c
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hT0]
    · have h1 := hmod.2.2.2.2.2 ⟨_, hH j hj⟩ (g - c • h)
        (Submodule.sub_mem _ hg (Submodule.smul_mem _ _ hh)) (c • h) (Submodule.smul_mem _ _ hh)
      change heckeOperator O j (g - c • h + c • h) =
        heckeOperator O j (g - c • h) + heckeOperator O j (c • h) at h1
      rw [sub_add_cancel, hsmul] at h1
      rw [h1, add_sub_cancel_right]
  have hmul : ∀ a' b' : ℕ, 0 < a' → 0 < b' → Nat.Coprime a' b' → ∀ g ∈ W,
      heckeOperator O a' (heckeOperator O b' g) = heckeOperator O (a' * b') g :=
    fun a' b' ha' hb' hab g hg => ((hecke_multiplicative O s k a' b' ha' hb' hab).2 g hg).1
  -- prime powers of one prime commute
  have hpp : ∀ p : ℕ, p.Prime → ¬ p ∣ D * M → ∀ r t : ℕ, ∀ g ∈ W,
      heckeOperator O (p ^ r) (heckeOperator O (p ^ t) g) = heckeOperator O (p ^ t) (heckeOperator O (p ^ r) g) := by
    intro p hp hpDM
    have hp0 : 0 < p := hp.pos
    set c : K := (p : K) ^ (k - 1)
    have hrec : ∀ t : ℕ, ∀ g ∈ W, heckeOperator O (p ^ (t + 1 + 1)) g =
        heckeOperator O p (heckeOperator O (p ^ (t + 1)) g) - c • heckeOperator O (p ^ t) g := by
      intro t g hg
      have h := hecke_recursion O₀ hD φ s k hk p hp hpDM (t + 1) (by omega) g hg
      rw [Nat.add_sub_cancel] at h
      rw [h]
      abel
    -- `T_p` commutes with every `T_{p^r}`
    have step1 : ∀ r : ℕ, (∀ g ∈ W, heckeOperator O p (heckeOperator O (p ^ r) g) =
        heckeOperator O (p ^ r) (heckeOperator O p g)) ∧
        (∀ g ∈ W, heckeOperator O p (heckeOperator O (p ^ (r + 1)) g) =
        heckeOperator O (p ^ (r + 1)) (heckeOperator O p g)) := by
      intro r
      induction r with
      | zero =>
        refine ⟨fun g hg => ?_, fun g hg => ?_⟩
        · rw [pow_zero, hT1 g hg, hT1 _ (hTW p g hg)]
        · rw [zero_add, pow_one]
      | succ r ih =>
        refine ⟨ih.2, fun g hg => ?_⟩
        rw [hrec r g hg, hrec r _ (hTW p g hg), ← ih.2 g hg, ← ih.1 g hg,
          hlin p _ (hTW _ _ (hTW _ g hg)) _ (hTW _ g hg)]
    have step2 : ∀ t : ℕ, (∀ r : ℕ, ∀ g ∈ W, heckeOperator O (p ^ t) (heckeOperator O (p ^ r) g) =
        heckeOperator O (p ^ r) (heckeOperator O (p ^ t) g)) ∧
        (∀ r : ℕ, ∀ g ∈ W, heckeOperator O (p ^ (t + 1)) (heckeOperator O (p ^ r) g) =
        heckeOperator O (p ^ r) (heckeOperator O (p ^ (t + 1)) g)) := by
      intro t
      induction t with
      | zero =>
        refine ⟨fun r g hg => ?_, fun r g hg => ?_⟩
        · rw [pow_zero, hT1 _ (hTW _ g hg), hT1 g hg]
        · rw [zero_add, pow_one]
          exact (step1 r).1 g hg
      | succ t ih =>
        refine ⟨ih.2, fun r g hg => ?_⟩
        rw [hrec t _ (hTW _ g hg), hrec t g hg, ih.2 r g hg, ih.1 r g hg,
          (step1 r).1 _ (hTW _ g hg), hlin (p ^ r) _ (hTW _ _ (hTW _ g hg)) _ (hTW _ g hg)]
    intro r t g hg
    exact (step2 r).1 t g hg
  -- `T_{p^r}` commutes with every `T_n`, `n` prime to `DM`
  have hA : ∀ p : ℕ, p.Prime → ¬ p ∣ D * M → ∀ r : ℕ, ∀ n : ℕ, Nat.Coprime n (D * M) → ∀ g ∈ W,
      heckeOperator O (p ^ r) (heckeOperator O n g) = heckeOperator O n (heckeOperator O (p ^ r) g) := by
    intro p hp hpDM r n
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow q j hq hj =>
      intro hqj g hg
      have hqDM : ¬ q ∣ D * M := by
        have := Nat.Coprime.coprime_dvd_left (dvd_pow_self q hj.ne') hqj
        exact (Nat.Prime.coprime_iff_not_dvd hq).mp this
      by_cases hpq : p = q
      · subst hpq
        exact hpp p hp hpDM r j g hg
      · have hcop : Nat.Coprime (p ^ r) (q ^ j) :=
          Nat.Coprime.pow r j ((Nat.coprime_primes hp hq).mpr hpq)
        rw [hmul _ _ (pow_pos hp.pos r) (pow_pos hq.pos j) hcop g hg,
          hmul _ _ (pow_pos hq.pos j) (pow_pos hp.pos r) hcop.symm g hg, mul_comm]
    | zero =>
      intro _ g hg
      rw [hT0, hT0]
      funext x
      simp [heckeOperator, heckeAct]
    | one =>
      intro _ g hg
      rw [hT1 g hg, hT1 _ (hTW _ g hg)]
    | coprime a' b' ha' hb' hab iha ihb =>
      intro habDM g hg
      have haDM := Nat.Coprime.coprime_dvd_left (dvd_mul_right a' b') habDM
      have hbDM := Nat.Coprime.coprime_dvd_left (dvd_mul_left b' a') habDM
      rw [← hmul a' b' (by omega) (by omega) hab g hg, iha haDM _ (hTW _ g hg), ihb hbDM g hg,
        hmul a' b' (by omega) (by omega) hab _ (hTW _ g hg)]
  intro m n hm hn
  induction m using Nat.recOnPosPrimePosCoprime generalizing f with
  | prime_pow p r hp hr =>
    have hpDM : ¬ p ∣ D * M := by
      have := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hr.ne') hm
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp this
    exact hA p hp hpDM r n hn f hf
  | zero =>
    rw [hT0, hT0]
    funext x
    simp [heckeOperator, heckeAct]
  | one =>
    rw [hT1 _ (hTW _ f hf), hT1 f hf]
  | coprime a' b' ha' hb' hab iha ihb =>
    have haDM := Nat.Coprime.coprime_dvd_left (dvd_mul_right a' b') hm
    have hbDM := Nat.Coprime.coprime_dvd_left (dvd_mul_left b' a') hm
    rw [← hmul a' b' (by omega) (by omega) hab _ (hTW _ f hf), ihb _ hf hbDM, iha _ (hTW _ f hf) haDM,
      hmul a' b' (by omega) (by omega) hab _ hf]

end GL2TF.Quat
