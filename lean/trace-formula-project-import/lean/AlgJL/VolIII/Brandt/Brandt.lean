import AlgJL.Meta.Tag
import AlgJL.VolIII.Brandt.Trace

/-!
# Brandt matrices (Q3 U4, items 37–42)

Lean counterpart of `vol3/ch-iii-08-brandt.tex` §4 (items 37–42 of `docs/sprints/Q3-plan.md` §1.2).
Exit `III.brandt.thm:brandt-eq-hecke`.

Design (plan §1.1 items 7, 8, traps 3, 4; conventions row N6):
* `B(n)_{cc'} := #{yÔ^× ⊆ Ô_n : [x_c y] = c'}` (adelic definition, representatives `x_c = c.out`), a matrix indexed by
  `X(O)` with entries in `ℕ`; `B(n)` acts on column vectors: `(T_n f)(x_c) = Σ_{c'} B(n)_{cc'} f(x_{c'})`;
* the ideal form uses the colon condition `γ L_{c'} ⊆ L_c` (no inverse lattices) and `N(L_x) = ν(x)⁻¹`, so the norm
  condition `nrd γ = n N(L_c)/N(L_{c'})` reads `nrd γ = n ν(x_{c'})/ν(x_c)`;
* "locally principal" is written inline: `J_p = β_p O_p` with `β_p ∈ B_p^×` for every prime `p`;
* matrix products are written as `finsum`s over `X(O)` (no `Fintype` instance on the class set is assumed).

Owner: Q3 A author/formalizer (MAIN).
-/

set_option autoImplicit false

namespace GL2TF.Quat

/-! ### Proof helpers for `hecke_neighbour_form` (Q3 part 5): `L_a = L_b ⟺ aÔ^× = bÔ^×` and `γL_x = L_{ι(γ)x}`. -/

open scoped Pointwise in
/-- `L_a = L_b` iff `aÔ^× = bÔ^×`. -/
private theorem nf_lattice_eq_iff {a b : ℤ} (O : QOrder a b) (x y : (BHat a b)ˣ) :
    finiteIdeleLattice O x = finiteIdeleLattice O y ↔
      (QuotientGroup.mk x : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk y := by
  constructor
  · intro h
    have hx := (finiteIdeleLattice_props O x).2.2
    have hy := (finiteIdeleLattice_props O y).2.2
    rw [h, hy] at hx
    have h1 : (x : BHat a b) ∈ (y : BHat a b) • (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) :
        Set (BHat a b)) := by
      rw [hx]; exact ⟨1, one_mem_orderCompletion O, by simp⟩
    have h2 : (y : BHat a b) ∈ (x : BHat a b) • (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) :
        Set (BHat a b)) := by
      rw [← hx]; exact ⟨1, one_mem_orderCompletion O, by simp⟩
    obtain ⟨s, hs, hsx⟩ := h1
    obtain ⟨t, ht, hty⟩ := h2
    simp only [smul_eq_mul] at hsx hty
    rw [QuotientGroup.eq]
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, ← hty, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      exact ht
    · rw [mul_inv_rev, inv_inv, Units.val_mul, ← hsx, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_mul]
      exact hs
  · intro h
    obtain ⟨hu1, hu2⟩ := QuotientGroup.eq.mp h
    set u := x⁻¹ * y with hu
    have hy : y = x * u := by rw [hu, mul_inv_cancel_left]
    ext w
    constructor
    · rintro ⟨v, hv, hw⟩
      refine ⟨((u⁻¹ : (BHat a b)ˣ) : BHat a b) * v, mul_mem_orderCompletion O hu2 hv, ?_⟩
      rw [hw, hy, Units.val_mul, mul_assoc, ← mul_assoc (u : BHat a b), ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    · rintro ⟨v, hv, hw⟩
      refine ⟨(u : BHat a b) * v, mul_mem_orderCompletion O hu1 hv, ?_⟩
      rw [hw, hy, Units.val_mul, mul_assoc]

/-- `γ L_x = L_{ι(γ)x}`. -/
private theorem nf_lattice_map {a b : ℤ} (O : QOrder a b) (γ : (QuatAlg ℚ a b)ˣ) (x : (BHat a b)ˣ) :
    (finiteIdeleLattice O x).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ a b)) =
      finiteIdeleLattice O (Units.map (finEmbed a b).toMonoidHom γ * x) := by
  have hιγ : ((Units.map (finEmbed a b).toMonoidHom γ * x : (BHat a b)ˣ) : BHat a b) =
      finEmbed a b (γ : QuatAlg ℚ a b) * (x : BHat a b) := by
    rw [Units.val_mul, Units.coe_map]; rfl
  ext w
  constructor
  · rintro ⟨v, ⟨y, hy, hv⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [hιγ, LinearMap.mulLeft_apply, map_mul, hv, mul_assoc]
  · rintro ⟨y, hy, hw⟩
    rw [hιγ] at hw
    refine ⟨((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) * w, ⟨y, hy, ?_⟩, ?_⟩
    · rw [map_mul, hw, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    · rw [LinearMap.mulLeft_apply, ← mul_assoc, Units.mul_inv, one_mul]

/-! ### Proof helpers for `hecke_neighbour_form` (a), (c) (Q3 part 6): the index `[L_x : L_{xy}] = nrd(y)²` up to a unit of
`Ẑ` (change of basis over `𝔸_f`, `det(y·) = nrd(y)²`), local–global for lattices, `(L_x)_q = x_q O_q`, and the idele
assembled from local generators. The local–global helpers are private copies of the HeckeLocal ones (generalised from `O`
to any lattice); a later cleanup can move them upstream. -/

section NeighbourIndex

open scoped Pointwise

/-- Left multiplication on `B_R` has determinant `nrd(x)²` (any commutative ring `R`). -/
private theorem nf_det_mulLeft {R : Type*} [CommRing R] {a b : ℤ} (x : QuatAlg R a b) :
    LinearMap.det (LinearMap.mulLeft R x) = nrd x ^ 2 := by
  rw [← LinearMap.det_toMatrix (QuaternionAlgebra.basisOneIJK _ _ _)]
  have h : LinearMap.toMatrix (QuaternionAlgebra.basisOneIJK (a : R) 0 (b : R))
      (QuaternionAlgebra.basisOneIJK (a : R) 0 (b : R)) (LinearMap.mulLeft R x) =
      !![x.re, a * x.imI, b * x.imJ, -(a * b) * x.imK;
         x.imI, x.re, b * x.imK, -b * x.imJ;
         x.imJ, -a * x.imK, x.re, a * x.imI;
         x.imK, -x.imJ, x.imI, x.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply, QuaternionAlgebra.basisOneIJK]
  rw [h, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, nrd, Fin.succAbove]
  ring

/-- A ℤ-lattice with basis `e` (and the same vectors as a ℚ-basis `f`) is the additive closure of `f`. -/
private theorem nf_closure {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (e : Module.Basis (Fin 4) ℤ L)
    (f : Module.Basis (Fin 4) ℚ (QuatAlg ℚ a b)) (hf : ∀ i, f i = (e i : QuatAlg ℚ a b)) :
    L.toAddSubgroup = AddSubgroup.closure (Set.range f) := by
  have h1 : L = Submodule.span ℤ (Set.range f) := by
    have hr : Set.range f = L.subtype '' Set.range e := by
      rw [← Set.range_comp]; exact congrArg Set.range (funext hf)
    rw [hr, ← Submodule.map_span, e.span_eq, Submodule.map_top, Submodule.range_subtype]
  rw [h1, Submodule.span_int_eq_addSubgroupClosure]

/-- A matrix over `𝔸_f` with entries in `Ẑ` has determinant in `Ẑ`. -/
private theorem nf_det_zhat (M : Matrix (Fin 4) (Fin 4) FinAdele) (h : ∀ i j, M i j ∈ Zhat) : M.det ∈ Zhat := by
  let M' : Matrix (Fin 4) (Fin 4) Zhat := fun i j => ⟨M i j, h i j⟩
  have hM : M = (Zhat.subtype).mapMatrix M' := by ext i j; rfl
  rw [hM, ← RingHom.map_det]
  exact (M'.det).2

/-- Naturals that agree up to a unit of `Ẑ` are equal. -/
private theorem nf_nat_eq (m k : ℕ) (hk : 0 < k) (u : Zhatˣ) (h : (m : FinAdele) = k * ((u : Zhat) : FinAdele)) :
    m = k := by
  have hinv : (((u : Zhat) : FinAdele)) * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele) = 1 := by
    have := congrArg (fun z : Zhat => (z : FinAdele)) u.mul_inv
    simpa only [Subring.coe_mul, Subring.coe_one] using this
  have hm : m ≠ 0 := by
    rintro rfl
    have h2 := congrArg (· * (((u⁻¹ : Zhatˣ) : Zhat) : FinAdele)) h
    simp only [Nat.cast_zero, zero_mul, mul_assoc, hinv, mul_one] at h2
    have h3 := congrArg (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) ⟨2, Nat.prime_two⟩) h2
    rw [map_zero, map_natCast] at h3
    exact hk.ne' (by exact_mod_cast h3.symm)
  have hdvd : ∀ (s t : ℕ) (w : Zhat), s ≠ 0 → (t : FinAdele) = s * (w : FinAdele) → s ∣ t := by
    intro s t w hs hst
    have hmem : algebraMap ℚ FinAdele (t : ℚ) ∈ algebraMap ℚ FinAdele 0 +ᵥ ((s : FinAdele) • (Zhat : Set FinAdele)) := by
      rw [map_natCast, map_zero, zero_vadd]
      exact ⟨w, w.2, by rw [hst]; exact smul_eq_mul _ _⟩
    obtain ⟨z, hz⟩ := (rat_mem_vadd_natCast_smul_zhat_iff 0 (t : ℚ) hs).mp hmem
    rw [zero_add] at hz
    have hz' : (t : ℤ) = s * z := by exact_mod_cast hz
    exact Int.natCast_dvd_natCast.mp ⟨z, hz'⟩
  exact Nat.dvd_antisymm (hdvd m k ((u⁻¹ : Zhatˣ) : Zhat) hm (by rw [h, mul_assoc, hinv, mul_one]))
    (hdvd k m (u : Zhat) hk.ne' h)

private theorem nf_nrd_mul {a b : ℤ} (x y : BHat a b) :
    nrd (show QuatAlg FinAdele a b from x * y) =
      nrd (show QuatAlg FinAdele a b from x) * nrd (show QuatAlg FinAdele a b from y) :=
  (nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).2.1 x y

/-- `nrd(xyx⁻¹) = nrd(y)` in `B̂^×`. -/
private theorem nf_nrd_conj {a b : ℤ} (x y : (BHat a b)ˣ) :
    nrd (show QuatAlg FinAdele a b from ((x * y * x⁻¹ : (BHat a b)ˣ) : BHat a b)) =
      nrd (show QuatAlg FinAdele a b from (y : BHat a b)) := by
  have h1 : nrd (show QuatAlg FinAdele a b from (x : BHat a b)) *
      nrd (show QuatAlg FinAdele a b from ((x⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
    rw [← nf_nrd_mul, Units.mul_inv]
    show nrd (1 : QuatAlg FinAdele a b) = 1
    simp [nrd]
  rw [Units.val_mul, Units.val_mul, nf_nrd_mul, nf_nrd_mul]
  linear_combination (nrd (show QuatAlg FinAdele a b from (y : BHat a b))) * h1

/-- `[L_x : L_{xy}] = nrd(y)²` up to a unit of `Ẑ`, for `y ∈ Ô ∩ B̂^×` (the index is `|det|` of the change of basis,
which over `𝔸_f` is `det(y·) = nrd(y)²` times the determinant of a `Ẑ`-change of basis). -/
private theorem nf_index {a b : ℤ} (O : QOrder a b) (x y : (BHat a b)ˣ)
    (hy : (y : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra)) :
    ∃ u : Zhatˣ, (((finiteIdeleLattice O (x * y)).toAddSubgroup.relIndex
      (finiteIdeleLattice O x).toAddSubgroup : ℕ) : FinAdele) =
      nrd (show QuatAlg FinAdele a b from (y : BHat a b)) ^ 2 * ((u : Zhat) : FinAdele) := by
  classical
  set L₁ := finiteIdeleLattice O (x * y) with hL₁
  set L₂ := finiteIdeleLattice O x with hL₂
  have hle : L₁ ≤ L₂ := by
    rintro w ⟨v, hv, hw⟩
    exact ⟨(y : BHat a b) * v, mul_mem_orderCompletion O hy hv, by rw [hw, Units.val_mul, mul_assoc]⟩
  obtain ⟨hfg₁, hsp₁, hc₁⟩ := finiteIdeleLattice_props O (x * y)
  obtain ⟨hfg₂, hsp₂, hc₂⟩ := finiteIdeleLattice_props O x
  obtain ⟨e₁, f₁, hf₁⟩ := exists_lattice_basis L₁ hfg₁ hsp₁
  obtain ⟨e₂, f₂, hf₂⟩ := exists_lattice_basis L₂ hfg₂ hsp₂
  obtain ⟨F₁, hF₁, -, hF₁m⟩ := exists_bhat_basis e₁ f₁ hf₁
  obtain ⟨F₂, hF₂, hF₂r, hF₂m⟩ := exists_bhat_basis e₂ f₂ hf₂
  have hidx : ((L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℕ) : ℚ) = |f₂.det f₁| :=
    AddSubgroup.relIndex_eq_abs_det L₁.toAddSubgroup L₂.toAddSubgroup (fun w hw => hle hw) f₁ f₂
      (nf_closure L₁ e₁ f₁ hf₁) (nf_closure L₂ e₂ f₂ hf₂)
  set g : (BHat a b)ˣ := x * y * x⁻¹ with hg
  let Lg : BHat a b ≃ₗ[FinAdele] BHat a b :=
    LinearEquiv.ofLinearMap (LinearMap.mulLeft FinAdele (g : BHat a b))
      (LinearMap.mulLeft FinAdele ((g⁻¹ : (BHat a b)ˣ) : BHat a b))
      (LinearMap.ext fun w => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply]
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul])
      (LinearMap.ext fun w => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply]
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul])
  set G := F₂.map Lg with hG
  have hdet : algebraMap ℚ FinAdele (f₂.det f₁) = F₂.det F₁ := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, hF₁,
      hF₂r]
  have hmul : F₂.det F₁ = F₂.det G * G.det F₁ := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  have hGdet : F₂.det G = nrd (show QuatAlg FinAdele a b from (y : BHat a b)) ^ 2 := by
    rw [Module.Basis.det_apply]
    have : F₂.toMatrix G = LinearMap.toMatrix F₂ F₂ (LinearMap.mulLeft FinAdele (g : BHat a b)) := by
      ext i j
      rw [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply, hG, Module.Basis.map_apply]
      rfl
    rw [this, LinearMap.det_toMatrix, ← nf_nrd_conj x y]
    exact nf_det_mulLeft (show QuatAlg FinAdele a b from (g : BHat a b))
  have hu1 : g⁻¹ * (x * y) = x := by rw [hg]; group
  have hu2 : g * x = x * y := by rw [hg]; group
  have hU1 : ∀ i j, G.toMatrix F₁ i j ∈ Zhat := by
    intro i j
    have hm : (e₁ j : QuatAlg ℚ a b) ∈ L₁ := (e₁ j).2
    obtain ⟨v, hv, hev⟩ := hm
    have heq : Lg.symm (F₁ j) = (x : BHat a b) * v := by
      show ((g⁻¹ : (BHat a b)ˣ) : BHat a b) * F₁ j = _
      rw [hF₁, hf₁, hev, ← mul_assoc, ← Units.val_mul, hu1]
    have hmem : (x : BHat a b) * v ∈ (latticeCompletion L₂ : Set (BHat a b)) := by
      rw [hc₂]; exact ⟨v, hv, rfl⟩
    rw [Module.Basis.toMatrix_apply, hG, Module.Basis.map_repr, LinearEquiv.trans_apply, heq]
    exact (hF₂m _).mp hmem i
  have hU2 : ∀ i j, F₁.toMatrix G i j ∈ Zhat := by
    intro i j
    have hm : (e₂ j : QuatAlg ℚ a b) ∈ L₂ := (e₂ j).2
    obtain ⟨v, hv, hev⟩ := hm
    have heq : G j = ((x * y : (BHat a b)ˣ) : BHat a b) * v := by
      rw [hG, Module.Basis.map_apply]
      show (g : BHat a b) * F₂ j = _
      rw [hF₂, hf₂, hev, ← mul_assoc, ← Units.val_mul, hu2]
    have hmem : ((x * y : (BHat a b)ˣ) : BHat a b) * v ∈ (latticeCompletion L₁ : Set (BHat a b)) := by
      rw [hc₁]; exact ⟨v, hv, rfl⟩
    rw [Module.Basis.toMatrix_apply, heq]
    exact (hF₁m _).mp hmem i
  have hd1 := nf_det_zhat _ hU1
  have hd2 := nf_det_zhat _ hU2
  have hprod : (G.toMatrix F₁).det * (F₁.toMatrix G).det = 1 := by
    rw [← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  have hprod' : (F₁.toMatrix G).det * (G.toMatrix F₁).det = 1 := by rw [mul_comm]; exact hprod
  let d : Zhatˣ := ⟨⟨_, hd1⟩, ⟨_, hd2⟩, Subtype.ext hprod, Subtype.ext hprod'⟩
  rcases abs_choice (f₂.det f₁) with hab | hab
  · refine ⟨d, ?_⟩
    rw [← map_natCast (algebraMap ℚ FinAdele), hidx, hab, hdet, hmul, hGdet, Module.Basis.det_apply]
  · refine ⟨-d, ?_⟩
    rw [← map_natCast (algebraMap ℚ FinAdele), hidx, hab, map_neg, hdet, hmul, hGdet, Module.Basis.det_apply]
    have : (((-d : Zhatˣ) : Zhat) : FinAdele) = -(G.toMatrix F₁).det := rfl
    rw [this]
    ring

/-- (a): `[L_x : L_{xy}] = n²` for `y ∈ Ô_n`. -/
private theorem nf_index_eq {a b : ℤ} (O : QOrder a b) (n : ℕ) (hn : 0 < n) (x y : (BHat a b)ˣ)
    (hy : y ∈ normNSet O n) :
    (finiteIdeleLattice O (x * y)).toAddSubgroup.relIndex (finiteIdeleLattice O x).toAddSubgroup = n ^ 2 := by
  obtain ⟨hyO, w, hw⟩ := hy
  obtain ⟨u, hu⟩ := nf_index O x y hyO
  refine nf_nat_eq _ _ (pow_pos hn 2) (w ^ 2 * u) ?_
  rw [hu, hw, Units.val_mul, Units.val_pow_eq_pow_val, Subring.coe_mul, SubmonoidClass.coe_pow]
  push_cast
  ring

/-! Local–global helpers (private copies of the HeckeLocal ones, generalised from `O` to any lattice). -/

/-- Evaluation `B̂ → B_q` at a prime `q` (coordinatewise). -/
private noncomputable abbrev nf_ev {a b : ℤ} (q : Nat.Primes) : QuatAlg FinAdele a b →+* QuatAlg ℚ_[q] a b :=
  baseChange a b (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q)

private theorem nf_ev_smul {a b : ℤ} (q : Nat.Primes) (c : FinAdele) (x : BHat a b) :
    nf_ev q (c • x : BHat a b) = c q • nf_ev q x := by
  ext <;> rfl

private theorem nf_ev_mul {a b : ℤ} (q : Nat.Primes) (x y : BHat a b) :
    nf_ev q (x * y : BHat a b) = nf_ev q x * nf_ev q y :=
  map_mul (nf_ev q) x y

private theorem nf_ev_finEmbed {a b : ℤ} (q : Nat.Primes) (z : QuatAlg ℚ a b) :
    nf_ev q (finEmbed a b z) = baseChange a b (algebraMap ℚ ℚ_[q]) z := by
  have h : ∀ c : ℚ, (RestrictedProduct.evalRingHom (fun q : Nat.Primes ↦ ℚ_[q]) q) (algebraMap ℚ FinAdele c) =
      algebraMap ℚ ℚ_[q] c := fun c => by
    rw [← RingHom.comp_apply, eq_ratCast, eq_ratCast]
  ext <;> exact h _

private theorem nf_mem_range_iff (q : Nat.Primes) (x : ℚ_[q]) :
    x ∈ (algebraMap ℤ_[q] ℚ_[q]).range ↔ x ∈ PadicInt.subring q :=
  ⟨fun ⟨t, ht⟩ => ht ▸ (PadicInt.mem_subring_iff q.1).2 t.norm_le_one,
    fun h => ⟨⟨x, (PadicInt.mem_subring_iff q.1).1 h⟩, rfl⟩⟩

/-- Local–global for `L̂`: `w ∈ L̂` iff `w_q ∈ L_q` for every prime `q`. -/
private theorem nf_mem_iff_local {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hL : L.FG)
    (hLs : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) (w : BHat a b) :
    w ∈ latticeCompletion L ↔ ∀ q : Nat.Primes, nf_ev q w ∈ localLattice q L := by
  obtain ⟨e, f, hf⟩ := exists_lattice_basis L hL hLs
  obtain ⟨F, hF1, -, hF3⟩ := exists_bhat_basis e f hf
  have hloc : ∀ q : Nat.Primes, ∃ Fq : Module.Basis (Fin 4) ℚ_[q] (QuatAlg ℚ_[q] a b),
      (∀ v, v ∈ localLattice q L ↔ ∀ i, Fq.repr v i ∈ (algebraMap ℤ_[q] ℚ_[q]).range) ∧
      ∀ i, Fq.repr (nf_ev q w) i = F.repr w i q := by
    intro q
    obtain ⟨Fq, hFq1, -⟩ := exists_baseChange_basis (S := ℚ_[q]) a b f
    refine ⟨Fq, fun v => mem_span_image_iff_repr (R := ℤ_[q]) e
      (baseChange a b (algebraMap ℚ ℚ_[q])).toAddMonoidHom Fq (fun i => by rw [← hf]; exact hFq1 i) v, ?_⟩
    have hFe : ∀ i, nf_ev q (F i) = Fq i := by
      intro i
      rw [hF1, hFq1, nf_ev_finEmbed]
    intro i
    have hw : nf_ev q w = ∑ j, F.repr w j q • Fq j := by
      conv_lhs => rw [← F.sum_repr w]
      refine (map_sum (nf_ev q) (fun j => (F.repr w j • F j : BHat a b)) Finset.univ).trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (nf_ev_smul q _ _).trans (by rw [hFe])
    rw [hw, Module.Basis.repr_sum_self]
  rw [hF3]
  constructor
  · intro h q
    obtain ⟨Fq, hFq, hrepr⟩ := hloc q
    rw [hFq]
    intro i
    rw [hrepr, nf_mem_range_iff]
    exact mem_zhat.mp (h i) q
  · intro h i
    rw [mem_zhat]
    intro q
    obtain ⟨Fq, hFq, hrepr⟩ := hloc q
    have := (hFq _).mp (h q) i
    rwa [hrepr, nf_mem_range_iff] at this

/-- Local–global for lattices: `z ∈ L` iff `z ∈ L_q` for every prime `q`. -/
private theorem nf_mem_lattice_iff {a b : ℤ} (L : Submodule ℤ (QuatAlg ℚ a b)) (hL : L.FG)
    (hLs : Submodule.span ℚ (L : Set (QuatAlg ℚ a b)) = ⊤) (z : QuatAlg ℚ a b) :
    z ∈ L ↔ ∀ q : Nat.Primes, baseChange a b (algebraMap ℚ ℚ_[q]) z ∈ localLattice q L := by
  have h := preimage_latticeCompletion L hL hLs
  rw [← SetLike.mem_coe, ← h, Set.mem_preimage, SetLike.mem_coe, nf_mem_iff_local L hL hLs]
  simp only [nf_ev_finEmbed]

/-- The element of `B̂` that is `z` at `p` and `0` elsewhere. -/
private noncomputable def nf_lift0 {a b : ℤ} (p : Nat.Primes) (z : QuatAlg ℚ_[p] a b) : BHat a b :=
  show QuatAlg FinAdele a b from
  ⟨RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p z.re,
    RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p z.imI,
    RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p z.imJ,
    RestrictedProduct.single (fun q : Nat.Primes ↦ PadicInt.subring q) p z.imK⟩

private theorem nf_ev_lift0_self {a b : ℤ} (p : Nat.Primes) (z : QuatAlg ℚ_[p] a b) :
    nf_ev p (nf_lift0 p z) = z := by
  ext <;> simp [nf_lift0, baseChange]

private theorem nf_ev_lift0_ne {a b : ℤ} (p q : Nat.Primes) (hq : q ≠ p) (z : QuatAlg ℚ_[p] a b) :
    nf_ev q (nf_lift0 p z) = 0 := by
  ext <;> simp [nf_lift0, baseChange, RestrictedProduct.single_eq_of_ne _ _ hq]

/-- `(L_x)_q = x_q O_q`: `w ∈ (L_x)_q` iff `(x⁻¹)_q w ∈ O_q`. -/
private theorem nf_local_idele {a b : ℤ} (O : QOrder a b) (x : (BHat a b)ˣ) (q : Nat.Primes)
    (w : QuatAlg ℚ_[q] a b) :
    w ∈ localLattice q (finiteIdeleLattice O x) ↔
      nf_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b) * w ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) := by
  obtain ⟨hfg, hsp, hc⟩ := finiteIdeleLattice_props O x
  have h1 : w ∈ localLattice q (finiteIdeleLattice O x) ↔
      nf_lift0 q w ∈ latticeCompletion (finiteIdeleLattice O x) := by
    rw [nf_mem_iff_local _ hfg hsp]
    constructor
    · intro hw q'
      by_cases hq : q' = q
      · subst hq; rw [nf_ev_lift0_self]; exact hw
      · rw [nf_ev_lift0_ne _ _ hq]; exact Submodule.zero_mem _
    · intro h
      have := h q
      rwa [nf_ev_lift0_self] at this
  have h2 : nf_lift0 q w ∈ latticeCompletion (finiteIdeleLattice O x) ↔
      ((x⁻¹ : (BHat a b)ˣ) : BHat a b) * nf_lift0 q w ∈
        latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    rw [← SetLike.mem_coe, hc]
    constructor
    · rintro ⟨v, hv, hve⟩
      have hve' : (x : BHat a b) * v = nf_lift0 q w := hve
      rw [← hve', Units.inv_mul_cancel_left]
      exact hv
    · intro h
      exact ⟨_, h, show (x : BHat a b) * (_ * _) = _ from Units.mul_inv_cancel_left _ _⟩
  rw [h1, h2, nf_mem_iff_local _ O.fg O.span_eq_top]
  constructor
  · intro h
    have := h q
    rwa [nf_ev_mul, nf_ev_lift0_self] at this
  · intro h q'
    rw [nf_ev_mul]
    by_cases hq : q' = q
    · subst hq; rw [nf_ev_lift0_self]; exact h
    · rw [nf_ev_lift0_ne _ _ hq, mul_zero]; exact Submodule.zero_mem _

private theorem nf_ev_one {a b : ℤ} (q : Nat.Primes) : nf_ev q (1 : BHat a b) = 1 :=
  map_one (nf_ev q)

private theorem nf_ev_add {a b : ℤ} (q : Nat.Primes) (x y : BHat a b) :
    nf_ev q (x + y : BHat a b) = nf_ev q x + nf_ev q y :=
  map_add (nf_ev q) x y

private theorem nf_ext {a b : ℤ} {x y : BHat a b} (h : ∀ q : Nat.Primes, nf_ev q x = nf_ev q y) : x = y := by
  have hx : ∀ q : Nat.Primes, (nf_ev (a := a) (b := b) q x).re = (nf_ev (a := a) (b := b) q y).re ∧
      (nf_ev (a := a) (b := b) q x).imI = (nf_ev (a := a) (b := b) q y).imI ∧
      (nf_ev (a := a) (b := b) q x).imJ = (nf_ev (a := a) (b := b) q y).imJ ∧
      (nf_ev (a := a) (b := b) q x).imK = (nf_ev (a := a) (b := b) q y).imK := fun q => by rw [h q]; simp
  show (show QuatAlg FinAdele a b from x) = (show QuatAlg FinAdele a b from y)
  ext
  · exact (hx _).1
  · exact (hx _).2.1
  · exact (hx _).2.2.1
  · exact (hx _).2.2.2

/-- The element of `B̂` that is `z_p` at `p ∈ S` and `1` elsewhere. -/
private noncomputable def nf_liftS {a b : ℤ} (S : Finset Nat.Primes) (z : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b) :
    BHat a b :=
  1 + ∑ p ∈ S, nf_lift0 p (z p - 1)

private theorem nf_ev_liftS {a b : ℤ} (S : Finset Nat.Primes) (z : ∀ p : Nat.Primes, QuatAlg ℚ_[p] a b)
    (q : Nat.Primes) : nf_ev q (nf_liftS S z) = if q ∈ S then z q else 1 := by
  have hsum : nf_ev q (∑ p ∈ S, nf_lift0 p (z p - 1) : BHat a b) = ∑ p ∈ S, nf_ev q (nf_lift0 p (z p - 1)) :=
    map_sum (nf_ev q) (fun p => nf_lift0 p (z p - 1)) S
  rw [nf_liftS, nf_ev_add, nf_ev_one, hsum]
  split_ifs with hq
  · rw [Finset.sum_eq_single q (fun p _ hpq => nf_ev_lift0_ne p q (Ne.symm hpq) _) (fun h => absurd hq h),
      nf_ev_lift0_self, add_sub_cancel]
  · rw [Finset.sum_eq_zero (fun p hp => nf_ev_lift0_ne p q (by rintro rfl; exact hq hp) _), add_zero]

/-- The unit of `B̂^×` that is `z_p` at `p ∈ S` and `1` elsewhere. -/
private noncomputable def nf_liftSUnit {a b : ℤ} (S : Finset Nat.Primes) (z : ∀ p : Nat.Primes, (QuatAlg ℚ_[p] a b)ˣ) :
    (BHat a b)ˣ where
  val := nf_liftS S (fun p => z p)
  inv := nf_liftS S (fun p => ((z p)⁻¹ : (QuatAlg ℚ_[p] a b)ˣ))
  val_inv := nf_ext fun q => by
    rw [nf_ev_mul, nf_ev_one, nf_ev_liftS, nf_ev_liftS]
    split_ifs
    · exact Units.mul_inv _
    · exact one_mul 1
  inv_val := nf_ext fun q => by
    rw [nf_ev_mul, nf_ev_one, nf_ev_liftS, nf_ev_liftS]
    split_ifs
    · exact Units.inv_mul _
    · exact one_mul 1

/-- The local component `x_q ∈ B_q^×` of `x ∈ B̂^×`. -/
private noncomputable def nf_evU {a b : ℤ} (q : Nat.Primes) (x : (BHat a b)ˣ) : (QuatAlg ℚ_[q] a b)ˣ where
  val := nf_ev q (x : BHat a b)
  inv := nf_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b)
  val_inv := by rw [← nf_ev_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, nf_ev_one]
  inv_val := by rw [← nf_ev_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, nf_ev_one]

private theorem nf_one_mem_local {a b : ℤ} (O : QOrder a b) (q : Nat.Primes) :
    (1 : QuatAlg ℚ_[q] a b) ∈ localLattice q (Subalgebra.toSubmodule O.toSubalgebra) :=
  Submodule.subset_span ⟨1, O.toSubalgebra.one_mem, map_one _⟩

/-- An element `N ∈ 𝔸_f` with `n² = N² u` (`u ∈ Ẑ^×`) is `n` times a unit of `Ẑ`. -/
private theorem nf_sqrt_unit (n : ℕ) (hn : 0 < n) (N : FinAdele) (u : Zhatˣ)
    (h : ((n ^ 2 : ℕ) : FinAdele) = N ^ 2 * ((u : Zhat) : FinAdele)) :
    ∃ w : Zhatˣ, N = (n : FinAdele) * ((w : Zhat) : FinAdele) := by
  set c : FinAdele := N * algebraMap ℚ FinAdele ((n : ℚ)⁻¹) with hc
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hNc : N = (n : FinAdele) * c := by
    rw [hc, ← map_natCast (algebraMap ℚ FinAdele), mul_left_comm, ← map_mul, mul_inv_cancel₀ hn0, map_one,
      mul_one]
  have hloc : ∀ p : Nat.Primes, ∃ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) = c p := by
    intro p
    set E : FinAdele →+* ℚ_[p] := RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p with hE
    obtain ⟨v, hv⟩ := (zhat_units_explicit ((u : Zhat) : FinAdele)).mp ⟨u, rfl⟩ p
    have hp := congrArg E h
    rw [map_mul, map_pow, map_natCast] at hp
    have hEN : E N = N p := rfl
    have hEu : E ((u : Zhat) : FinAdele) = ((u : Zhat) : FinAdele) p := rfl
    rw [hEN, hEu, ← hv] at hp
    have hvn : ‖((v : ℤ_[p]) : ℚ_[p])‖ = 1 := PadicInt.isUnit_iff.mp v.isUnit
    have hnorm : ‖N p‖ ^ 2 = ‖((n : ℕ) : ℚ_[p])‖ ^ 2 := by
      have := congrArg norm hp
      rw [norm_mul, norm_pow, hvn, mul_one, Nat.cast_pow, norm_pow] at this
      exact this.symm
    have hnorm' : ‖N p‖ = ‖((n : ℕ) : ℚ_[p])‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnorm
    have hnp : ((n : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hcp : c p = N p * ((n : ℕ) : ℚ_[p])⁻¹ := by
      show E c = _
      rw [hc, map_mul, hEN]
      congr 1
      show E (algebraMap ℚ FinAdele ((n : ℚ)⁻¹)) = _
      rw [← RingHom.comp_apply, eq_ratCast]
      simp
    have hc1 : ‖c p‖ = 1 := by
      rw [hcp, norm_mul, norm_inv, hnorm', mul_inv_cancel₀ (norm_ne_zero_iff.mpr hnp)]
    let t : ℤ_[p] := ⟨c p, hc1.le⟩
    have ht : IsUnit t := PadicInt.isUnit_iff.mpr hc1
    exact ⟨ht.unit, rfl⟩
  obtain ⟨w, hw⟩ := (zhat_units_explicit c).mpr hloc
  exact ⟨w, by rw [hw, hNc]⟩

/-- (c): every locally principal sublattice `J ⊆ L_x` of index `n²` is `L_{xy}` for some `y ∈ Ô_n`. -/
private theorem nf_neighbour {a b : ℤ} (O : QOrder a b) (n : ℕ) (hn : 0 < n) (x : (BHat a b)ˣ)
    (J : Submodule ℤ (QuatAlg ℚ a b)) (hJ : J ≤ finiteIdeleLattice O x)
    (hloc : ∀ p : Nat.Primes, ∃ β : (QuatAlg ℚ_[p] a b)ˣ,
        localLattice p J = (localLattice p (Subalgebra.toSubmodule O.toSubalgebra)).map
          (LinearMap.mulLeft ℤ_[p] (β : QuatAlg ℚ_[p] a b)))
    (hidx : J.toAddSubgroup.relIndex (finiteIdeleLattice O x).toAddSubgroup = n ^ 2) :
    ∃ y ∈ normNSet O n, J = finiteIdeleLattice O (x * y) := by
  classical
  choose β hβ using hloc
  obtain ⟨hfgx, hspx, -⟩ := finiteIdeleLattice_props O x
  have hfgJ : J.FG := fg_of_le_fg hfgx hJ
  have hn2 : ((n ^ 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (pow_pos hn 2).ne'
  have hspJ : Submodule.span ℚ (J : Set (QuatAlg ℚ a b)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hspx]
    refine Submodule.span_le.mpr fun z hz => ?_
    have hmem : (n ^ 2) • z ∈ J := by
      have := AddSubgroup.nsmul_relIndex_mem J.toAddSubgroup (K := (finiteIdeleLattice O x).toAddSubgroup) hz
      rwa [hidx] at this
    have hz' : z = ((n ^ 2 : ℕ) : ℚ)⁻¹ • ((n ^ 2) • z) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn2, one_smul]
    rw [hz']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  set S : Finset Nat.Primes := n.primeFactors.subtype Nat.Prime with hS
  have hmemS : ∀ q : Nat.Primes, q ∈ S ↔ (q : ℕ) ∣ n := by
    intro q
    have h1 : q ∈ S ↔ (q : ℕ) ∈ n.primeFactors := Finset.mem_subtype
    rw [h1, Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨q.2, h, hn.ne'⟩⟩
  set y : (BHat a b)ˣ := nf_liftSUnit S (fun p => (nf_evU p x)⁻¹ * β p) with hy
  have hF1 : ∀ q, nf_ev q (y : BHat a b) =
      if q ∈ S then nf_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b) * (β q : QuatAlg ℚ_[q] a b) else 1 := by
    intro q
    exact nf_ev_liftS S _ q
  have hF2 : ∀ q, nf_ev q ((y⁻¹ : (BHat a b)ˣ) : BHat a b) =
      if q ∈ S then ((β q)⁻¹ : (QuatAlg ℚ_[q] a b)ˣ) * nf_ev q (x : BHat a b) else 1 := by
    intro q
    exact (nf_ev_liftS S _ q).trans (by simp only [mul_inv_rev, inv_inv]; rfl)
  have hxx : ∀ q : Nat.Primes, nf_ev q (x : BHat a b) * nf_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b) = 1 :=
    fun q => (nf_evU q x).mul_inv
  have hloc_eq : ∀ q : Nat.Primes, localLattice q J = localLattice q (finiteIdeleLattice O (x * y)) := by
    intro q
    ext w
    rw [nf_local_idele O (x * y) q w, mul_inv_rev, Units.val_mul, nf_ev_mul, hF2]
    split_ifs with hq
    · rw [hβ q, Submodule.mem_map]
      have hsimp : ((β q)⁻¹ : (QuatAlg ℚ_[q] a b)ˣ) * nf_ev q (x : BHat a b) *
          nf_ev q ((x⁻¹ : (BHat a b)ˣ) : BHat a b) * w = (((β q)⁻¹ : (QuatAlg ℚ_[q] a b)ˣ) : QuatAlg ℚ_[q] a b) * w := by
        rw [mul_assoc (((β q)⁻¹ : (QuatAlg ℚ_[q] a b)ˣ) : QuatAlg ℚ_[q] a b), hxx, mul_one]
      rw [hsimp]
      constructor
      · rintro ⟨o, ho, rfl⟩
        rw [LinearMap.mulLeft_apply, ← mul_assoc, Units.inv_mul, one_mul]
        exact ho
      · intro h
        exact ⟨_, h, by rw [LinearMap.mulLeft_apply, ← mul_assoc, Units.mul_inv, one_mul]⟩
    · rw [one_mul, ← nf_local_idele O x q w]
      have hndvd : ¬ (q : ℕ) ∣ J.toAddSubgroup.relIndex (finiteIdeleLattice O x).toAddSubgroup := by
        rw [hidx]
        exact fun h => hq ((hmemS q).mpr (q.2.dvd_of_dvd_pow h))
      rw [(localLattice_basic q (finiteIdeleLattice O x) hfgx hspx).2.2.1 J hfgJ hspJ hJ hndvd]
  obtain ⟨hfgxy, hspxy, -⟩ := finiteIdeleLattice_props O (x * y)
  have hJeq : J = finiteIdeleLattice O (x * y) := by
    ext z
    rw [nf_mem_lattice_iff J hfgJ hspJ, nf_mem_lattice_iff _ hfgxy hspxy]
    exact forall_congr' fun q => by rw [hloc_eq q]
  have hyO : (y : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
    rw [nf_mem_iff_local _ O.fg O.span_eq_top]
    intro q
    rw [hF1]
    split_ifs with hq
    · have hβJ : (β q : QuatAlg ℚ_[q] a b) ∈ localLattice q J := by
        rw [hβ q]
        exact ⟨1, nf_one_mem_local O q, by rw [LinearMap.mulLeft_apply, mul_one]⟩
      have hmono : localLattice q J ≤ localLattice q (finiteIdeleLattice O x) :=
        Submodule.span_mono (Set.image_mono hJ)
      exact (nf_local_idele O x q _).mp (hmono hβJ)
    · exact nf_one_mem_local O q
  obtain ⟨u, hu⟩ := nf_index O x y hyO
  rw [← hJeq, hidx] at hu
  obtain ⟨w, hw⟩ := nf_sqrt_unit n hn _ u hu
  exact ⟨y, ⟨hyO, w, hw⟩, hJeq⟩

end NeighbourIndex

/-- Every order, `n ≥ 1`, `x ∈ B̂^×`: (a) for `y ∈ Ô_n`, `L_{xy} ⊆ L_x` with `[L_x : L_{xy}] = n²`; (b) `L_{xy} = L_{xy'}`
iff `yÔ^× = y'Ô^×` (`y, y' ∈ Ô_n`); (c) every right `O`-lattice `J ⊆ L_x` that is locally principal (`J_p = β_p O_p`,
`β_p ∈ B_p^×`, for every prime `p`) with `[L_x : J] = n²` is `L_{xy}` for some `y ∈ Ô_n`; (d) if `L_z = γ L_{x'}`
(`z, x' ∈ B̂^×`, `γ ∈ B^×`), then `f(z) = ρ_k^s(γ) f(x')` for every `f ∈ M_k(O; s)`. -/
@[tf_id "III.brandt.thm:hecke-neighbour-form"]
theorem hecke_neighbour_form {K : Type*} [Field K] [CharZero K] {a b : ℤ} (O : QOrder a b) (s : Splitting K a b)
    (k n : ℕ) (hn : 0 < n) (x : (BHat a b)ˣ) :
    (∀ y ∈ normNSet O n, finiteIdeleLattice O (x * y) ≤ finiteIdeleLattice O x ∧
      (finiteIdeleLattice O (x * y)).toAddSubgroup.relIndex (finiteIdeleLattice O x).toAddSubgroup = n ^ 2) ∧
    (∀ y ∈ normNSet O n, ∀ y' ∈ normNSet O n,
      finiteIdeleLattice O (x * y) = finiteIdeleLattice O (x * y') ↔
        ((y : (BHat a b)ˣ) : (BHat a b)ˣ ⧸ orderCompletionUnits O) = (y' : (BHat a b)ˣ)) ∧
    (∀ J : Submodule ℤ (QuatAlg ℚ a b), J ≤ finiteIdeleLattice O x →
      (∀ y z : QuatAlg ℚ a b, y ∈ J → z ∈ O.toSubalgebra → y * z ∈ J) →
      (∀ p : Nat.Primes, ∃ β : (QuatAlg ℚ_[p] a b)ˣ,
        localLattice p J = (localLattice p (Subalgebra.toSubmodule O.toSubalgebra)).map
          (LinearMap.mulLeft ℤ_[p] (β : QuatAlg ℚ_[p] a b))) →
      J.toAddSubgroup.relIndex (finiteIdeleLattice O x).toAddSubgroup = n ^ 2 →
      ∃ y ∈ normNSet O n, J = finiteIdeleLattice O (x * y)) ∧
    (∀ f ∈ quatForms O s k, ∀ (z x' : (BHat a b)ˣ) (γ : (QuatAlg ℚ a b)ˣ),
      finiteIdeleLattice O z = (finiteIdeleLattice O x').map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ a b)) →
        f z = splitRep s k (γ : QuatAlg ℚ a b) (f x')) := by
  refine ⟨fun y hy => ⟨?_, ?_⟩, fun y _ y' _ => ?_, ?_, fun f hf z x' γ hz => ?_⟩
  · rintro w ⟨v, hv, hw⟩
    refine ⟨(y : BHat a b) * v, mul_mem_orderCompletion O hy.1 hv, ?_⟩
    rw [hw, Units.val_mul, mul_assoc]
  · exact nf_index_eq O n hn x y hy
  · rw [nf_lattice_eq_iff, QuotientGroup.eq, QuotientGroup.eq, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · intro J hJ _ hloc hidx
    exact nf_neighbour O n hn x J hJ hloc hidx
  · rw [nf_lattice_map, nf_lattice_eq_iff] at hz
    obtain ⟨u, hu⟩ : ∃ u ∈ orderCompletionUnits O, z = Units.map (finEmbed a b).toMonoidHom γ * x' * u :=
      ⟨_, QuotientGroup.eq.mp hz.symm, by rw [mul_inv_cancel_left]⟩
    obtain ⟨hu, rfl⟩ := hu
    exact hf γ x' u hu

/-- The Brandt matrix `B(n)_{cc'} := #{yÔ^× ⊆ Ô_n : [x_c y] = c'} ∈ ℕ` for `c, c' ∈ X(O)` (representatives `x_c = c.out`). -/
@[tf_id "III.brandt.def:brandt-matrix"]
noncomputable def brandtMatrix {a b : ℤ} (O : QOrder a b) (n : ℕ) : Matrix (classSet O) (classSet O) ℕ :=
  fun c c' => Nat.card {q : (BHat a b)ˣ ⧸ orderCompletionUnits O //
    ∃ y ∈ normNSet O n, (y : (BHat a b)ˣ ⧸ orderCompletionUnits O) = q ∧ classOf O (Quotient.out c * y) = c'}

/-! ### Proof helpers for `brandt_weighted_symmetry` (private copies of helpers of Hecke.lean and Pairing.lean, which
`lfile` cannot see from here; a later cleanup can de-duplicate). -/

private theorem bw_nrd_mul {a b : ℤ} (x y : BHat a b) :
    nrd (show QuatAlg FinAdele a b from x * y) =
      nrd (show QuatAlg FinAdele a b from x) * nrd (show QuatAlg FinAdele a b from y) :=
  (nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).2.1 x y

private theorem bw_zhat_unit_inv_mul (w : Zhatˣ) :
    (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) * ((w : Zhat) : FinAdele) = 1 := by
  have := congrArg (fun z : Zhat => (z : FinAdele)) w.inv_mul
  simpa only [Subring.coe_mul, Subring.coe_one] using this

private theorem bw_nsmul_inv_mem {a b : ℤ} (O : QOrder a b) (n : ℕ) {y : (BHat a b)ˣ} (hy : y ∈ normNSet O n) :
    (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) := by
  obtain ⟨hyO, w, hw⟩ := hy
  obtain ⟨S, hS, hSO⟩ := star_mem_completion O hyO
  have hyS : (y : BHat a b) * S = algebraMap FinAdele (BHat a b) (nrd (show QuatAlg FinAdele a b from (y : BHat a b))) := by
    show (show QuatAlg FinAdele a b from (y : BHat a b)) * (show QuatAlg FinAdele a b from S) = _
    rw [hS]
    exact ((nrd_trd_basic.{0, 0} (R := FinAdele) (a := a) (b := b)).1 _).1
  have key : (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) = (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S := by
    have h1 : (y : BHat a b) * ((((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S) = algebraMap FinAdele (BHat a b) (n : FinAdele) := by
      rw [mul_smul_comm, hyS, hw, Algebra.smul_def, ← map_mul]
      congr 1
      rw [mul_left_comm, bw_zhat_unit_inv_mul, mul_one]
    calc (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b)
        = ((y⁻¹ : (BHat a b)ˣ) : BHat a b) * algebraMap FinAdele (BHat a b) (n : FinAdele) := by
          rw [Algebra.smul_def, Algebra.commutes]
      _ = (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) • S := by
          rw [← h1, ← mul_assoc, Units.inv_mul, one_mul]
  rw [key]
  exact smul_mem_latticeCompletion _ ((w⁻¹ : Zhatˣ) : Zhat).2 hSO

/-- `P y⁻¹ ∈ Ô_n` for `y ∈ Ô_n`, where `P` is the scalar `n` (so `P y⁻¹ = ȳ · n/nrd(y)`). -/
private theorem bw_n_inv_mem {a b : ℤ} (O : QOrder a b) (n : ℕ) {P y : (BHat a b)ˣ}
    (hP : (P : BHat a b) = algebraMap FinAdele (BHat a b) (n : FinAdele)) (hy : y ∈ normNSet O n) :
    P * y⁻¹ ∈ normNSet O n := by
  have hval : ((P * y⁻¹ : (BHat a b)ˣ) : BHat a b) = (n : FinAdele) • ((y⁻¹ : (BHat a b)ˣ) : BHat a b) := by
    rw [Units.val_mul, hP, ← Algebra.smul_def]
  refine ⟨by rw [hval]; exact bw_nsmul_inv_mem O n hy, ?_⟩
  obtain ⟨-, w, hw⟩ := hy
  refine ⟨w⁻¹, ?_⟩
  have h1 : nrd (show QuatAlg FinAdele a b from (y : BHat a b)) *
      nrd (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)) = 1 := by
    rw [← bw_nrd_mul, Units.mul_inv]
    show nrd (1 : QuatAlg FinAdele a b) = 1
    simp [nrd]
  rw [hw] at h1
  have hw1 := bw_zhat_unit_inv_mul w
  rw [hval]
  show nrd ((n : FinAdele) • (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b))) = _
  rw [nrd_smul_aux]
  linear_combination (-((n : FinAdele) ^ 2 * nrd (show QuatAlg FinAdele a b from ((y⁻¹ : (BHat a b)ˣ) : BHat a b)))) * hw1 +
    ((n : FinAdele) * (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele)) * h1

/-! ### Proof helpers for `brandt_eq_hecke` (copies of the norm-weight helpers of Pairing.lean, invisible to `lfile`
here), the characterisation `y ∈ Ô_n ⟺ y ∈ Ô ∧ ν(y) = 1/n`, and the fiber count `|Γ_{x_{c'}}| B(n)_{cc'} = #S_{cc'}(n)`. -/

/-- For a unit `y` of `B̂` and `n ≥ 1`: `nrd(y) ∈ nẐ^×` iff `ν(y) = 1/n`. -/
private theorem be_nu_iff {a b : ℤ} (n : ℕ) (hn : 0 < n) (y : (BHat a b)ˣ) :
    (∃ w : Zhatˣ, nrd (show QuatAlg FinAdele a b from (y : BHat a b)) = (n : FinAdele) * ((w : Zhat) : FinAdele)) ↔
      normWeight y = ((n : ℕ) : ℚ)⁻¹ := by
  obtain ⟨c, hc⟩ := nrd_unit_exists y
  have hn0 : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnR : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · rintro ⟨w, hw⟩
    have hsplit : MulEquiv.prodUnits.symm (1, c) =
        ratIdele (Units.mk0 ((n : ℕ) : ℚ) hn0) * ideleInfFin (((n : ℕ) : ℝ)⁻¹) w := by
      apply Units.ext
      rw [Units.val_mul, ideleInfFin_val (inv_ne_zero hnR), ratIdele_val]
      rw [show ((MulEquiv.prodUnits.symm (1, c) : Adeleˣ) : Adele) = (1, (c : FinAdele)) from rfl]
      refine Prod.ext ?_ ?_
      · show (1 : ℝ) = (algebraMap ℚ Adele ((n : ℕ) : ℚ)).1 * ((n : ℕ) : ℝ)⁻¹
        rw [map_natCast, Prod.fst_natCast, mul_inv_cancel₀ hnR]
      · show (c : FinAdele) = (algebraMap ℚ Adele ((n : ℕ) : ℚ)).2 * ((w : Zhat) : FinAdele)
        rw [hc, hw, map_natCast, Prod.snd_natCast]
    apply Rat.cast_injective (α := ℝ)
    rw [normWeight_eq_ideleNorm _ _ hc, hsplit, map_mul, product_formula, one_mul,
      ideleNorm_ideleInfFin (inv_ne_zero hnR), abs_inv, Nat.abs_cast, Rat.cast_inv, Rat.cast_natCast]
  · intro hν
    obtain ⟨q, r, u, hr, hx⟩ := exists_ratIdele_mul_ideleInfFin (MulEquiv.prodUnits.symm (1, c))
    have hv := congrArg (fun z : Idele => (z : Adele)) hx
    simp only [Units.val_mul, ratIdele_val, ideleInfFin_val hr.ne'] at hv
    rw [show ((MulEquiv.prodUnits.symm (1, c) : Adeleˣ) : Adele) = (1, (c : FinAdele)) from rfl] at hv
    have hv1 : (1 : ℝ) = (q : ℝ) * r := by
      have := congrArg Prod.fst hv
      simpa using this
    have hv2 : (c : FinAdele) = algebraMap ℚ FinAdele (q : ℚ) * ((u : Zhat) : FinAdele) := by
      have := congrArg Prod.snd hv
      simpa using this
    have hnorm : ((normWeight y : ℚ) : ℝ) = r := by
      rw [normWeight_eq_ideleNorm _ _ hc, hx, map_mul, product_formula, one_mul, ideleNorm_ideleInfFin hr.ne',
        abs_of_pos hr]
    rw [hν, Rat.cast_inv, Rat.cast_natCast] at hnorm
    have hq : (q : ℚ) = (n : ℚ) := by
      have h1 : ((q : ℚ) : ℝ) = ((n : ℕ) : ℝ) := by
        rw [← hnorm] at hv1
        field_simp at hv1
        linarith
      exact_mod_cast h1
    refine ⟨u, ?_⟩
    rw [← hc, hv2, hq, map_natCast]

/-- `|Γ_{x_{c'}}| B(n)_{cc'} = #S_{cc'}(n)` with `S_{cc'}(n) = {γ ∈ B^× : x_c⁻¹ ι(γ) x_{c'} ∈ Ô_n}` (`x_c = c.out`). -/
private theorem be_fiber_count {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) (n : ℕ) (hn : 0 < n)
    (c c' : classSet O) :
    Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c')) * brandtMatrix O n c c' =
      Nat.card ({γ : (QuatAlg ℚ a b)ˣ |
        (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n} :
          Set (QuatAlg ℚ a b)ˣ) := by
  classical
  have hNb := normNSet_basic O n hn
  have hfin := hNb.2.2.2.1
  have hNright : ∀ y ∈ normNSet O n, ∀ u ∈ orderCompletionUnits O, y * u ∈ normNSet O n := by
    intro y hy u hu
    have := hNb.1 y hy 1 (one_mem _) u hu
    rwa [one_mul] at this
  have hstab : ∀ (x : (BHat a b)ˣ) (δ : (QuatAlg ℚ a b)ˣ), δ ∈ classStabilizer (orderCompletionUnits O) x ↔
      x⁻¹ * Units.map (finEmbed a b).toMonoidHom δ * x ∈ orderCompletionUnits O := by
    intro x δ
    rw [classStabilizer, Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, h⟩
      rw [← h]
      convert hu using 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · intro h
      refine ⟨_, h, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hcls : ∀ (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ), u ∈ orderCompletionUnits O →
      classOf O (Units.map (finEmbed a b).toMonoidHom γ * x * u) = classOf O x := by
    intro γ x u hu
    refine DoubleCoset.eq.mpr ⟨(Units.map (finEmbed a b).toMonoidHom γ)⁻¹, ?_, u⁻¹, inv_mem hu, by group⟩
    exact inv_mem ⟨γ, rfl⟩
  have hr : ∀ c : classSet O, classOf O (Quotient.out c) = c := fun c => DoubleCoset.out_eq' c
  have : Finite (classStabilizer (orderCompletionUnits O) (Quotient.out c')) :=
    ((stabilizer_units O (Quotient.out c')).2.2 ha hb).1
  let Φ : (QuatAlg ℚ a b)ˣ → (BHat a b)ˣ ⧸ orderCompletionUnits O := fun γ =>
    QuotientGroup.mk ((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c')
  let g : (BHat a b)ˣ ⧸ orderCompletionUnits O → classSet O :=
    fun q => classOf O (Quotient.out c * Quotient.out q)
  have hfib : ∀ γ γ' : (QuatAlg ℚ a b)ˣ, Φ γ = Φ γ' ↔
      γ⁻¹ * γ' ∈ classStabilizer (orderCompletionUnits O) (Quotient.out c') := by
    intro γ γ'
    show (QuotientGroup.mk _ : (BHat a b)ˣ ⧸ orderCompletionUnits O) = QuotientGroup.mk _ ↔ _
    rw [QuotientGroup.eq, hstab, map_mul, map_inv]
    constructor <;> intro h <;> convert h using 1 <;> group
  have hmemS : ∀ γ : (QuatAlg ℚ a b)ˣ,
      (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n ↔
      Φ γ ∈ hfin.toFinset := by
    intro γ
    rw [Set.Finite.mem_toFinset]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨y, hy, hyq⟩
      rw [QuotientGroup.eq] at hyq
      have := hNright y hy _ hyq
      rwa [mul_inv_cancel_left] at this
  have hSfin : ({γ : (QuatAlg ℚ a b)ˣ |
      (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n} :
        Set (QuatAlg ℚ a b)ˣ).Finite := by
    have ht : ∀ q, {γ | Φ γ = q}.Finite := by
      intro q
      rcases Set.eq_empty_or_nonempty {γ | Φ γ = q} with h | ⟨γ₀, hγ₀⟩
      · rw [h]
        exact Set.finite_empty
      · refine (Set.finite_range (fun δ : classStabilizer (orderCompletionUnits O) (Quotient.out c') =>
          γ₀ * (δ : (QuatAlg ℚ a b)ˣ))).subset ?_
        intro γ hγ
        have hγ₀' : Φ γ₀ = q := hγ₀
        have hγ' : Φ γ = q := hγ
        refine ⟨⟨γ₀⁻¹ * γ, (hfib γ₀ γ).mp (hγ₀'.trans hγ'.symm)⟩, ?_⟩
        simp only [mul_inv_cancel_left]
    refine (Set.Finite.biUnion hfin.toFinset.finite_toSet fun q _ => ht q).subset ?_
    intro γ hγ
    exact Set.mem_biUnion (Finset.mem_coe.mpr ((hmemS γ).mp hγ)) rfl
  have hmaps : ∀ γ ∈ hSfin.toFinset, Φ γ ∈ hfin.toFinset.filter (fun q => g q = c') := by
    intro γ hγ
    rw [Set.Finite.mem_toFinset] at hγ
    rw [Finset.mem_filter]
    refine ⟨(hmemS γ).mp hγ, ?_⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O)
      ((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c')
    show classOf O (Quotient.out c * Quotient.out (Φ γ)) = c'
    rw [show Quotient.out (Φ γ) = _ from hu,
      show Quotient.out c * ((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' *
          (u : (BHat a b)ˣ)) =
        Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' * (u : (BHat a b)ˣ) by group,
      hcls γ _ u u.2, hr c']
  have hcard : ∀ q ∈ hfin.toFinset.filter (fun q => g q = c'),
      (hSfin.toFinset.filter (fun γ => Φ γ = q)).card =
        Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c')) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have hcl : classOf O (Quotient.out c') = classOf O (Quotient.out c * Quotient.out q) :=
      (hr c').trans hq.2.symm
    obtain ⟨hh, ⟨γ₀, rfl⟩, kk, hkk, hrel⟩ := DoubleCoset.eq.mp hcl
    have hγ₀ : Φ γ₀ = q := by
      have h1 : (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ₀ * Quotient.out c' =
          Quotient.out q * kk⁻¹ := by
        have h2 : Units.map (finEmbed a b).toMonoidHom γ₀ * Quotient.out c' =
            Quotient.out c * Quotient.out q * kk⁻¹ := eq_mul_inv_of_mul_eq hrel.symm
        rw [mul_assoc, h2]
        group
      show QuotientGroup.mk ((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ₀ * Quotient.out c') = q
      rw [h1, QuotientGroup.mk_mul_of_mem _ (inv_mem hkk), QuotientGroup.out_eq']
    have hto : ∀ δ : classStabilizer (orderCompletionUnits O) (Quotient.out c'),
        γ₀ * (δ : (QuatAlg ℚ a b)ˣ) ∈ hSfin.toFinset.filter (fun γ => Φ γ = q) := by
      intro δ
      have hΦ : Φ (γ₀ * δ) = q :=
        ((hfib γ₀ (γ₀ * δ)).mpr (by rw [inv_mul_cancel_left]; exact δ.2)).symm.trans hγ₀
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      refine ⟨(hmemS _).mpr ?_, hΦ⟩
      rw [hΦ]
      exact hq.1
    have hinv : ∀ γ ∈ hSfin.toFinset.filter (fun γ => Φ γ = q),
        γ₀⁻¹ * γ ∈ classStabilizer (orderCompletionUnits O) (Quotient.out c') := by
      intro γ hγ
      exact (hfib γ₀ γ).mp (hγ₀.trans (Finset.mem_filter.mp hγ).2.symm)
    rw [← Nat.card_eq_finsetCard]
    exact (Nat.card_congr ⟨fun δ => ⟨γ₀ * (δ : (QuatAlg ℚ a b)ˣ), hto δ⟩,
      fun γ => ⟨γ₀⁻¹ * (γ : (QuatAlg ℚ a b)ˣ), hinv γ γ.2⟩,
      fun δ => Subtype.ext (inv_mul_cancel_left γ₀ (δ : (QuatAlg ℚ a b)ˣ)),
      fun γ => Subtype.ext (mul_inv_cancel_left γ₀ (γ : (QuatAlg ℚ a b)ˣ))⟩).symm
  have hgy : ∀ y : (BHat a b)ˣ, g (y : (BHat a b)ˣ ⧸ orderCompletionUnits O) = classOf O (Quotient.out c * y) := by
    intro y
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits O) y
    show classOf O (Quotient.out c * Quotient.out (y : (BHat a b)ˣ ⧸ orderCompletionUnits O)) = _
    rw [hu, ← mul_assoc]
    exact DoubleCoset.eq.mpr ⟨1, one_mem _, (u : (BHat a b)ˣ)⁻¹, inv_mem u.2, by group⟩
  have hB : brandtMatrix O n c c' = (hfin.toFinset.filter (fun q => g q = c')).card := by
    rw [brandtMatrix, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨y, hy, rfl, hc⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [hgy, hc]⟩
    · rintro ⟨⟨y, hy, rfl⟩, hc⟩
      exact ⟨y, hy, rfl, by rw [← hgy, hc]⟩
  rw [hB, Nat.card_eq_card_finite_toFinset hSfin, Finset.card_eq_sum_card_fiberwise hmaps,
    Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Exit.** For `a, b < 0`, every order and `n ≥ 1`: (a) `(T_n f)(x_c) = Σ_{c'} B(n)_{cc'} f(x_{c'})` for every
`f ∈ M_2(O; s)`; (b) `|Γ_{x_{c'}}| B(n)_{cc'} = #{γ ∈ B^× : γ L_{c'} ⊆ L_c, nrd γ = n N(L_c)/N(L_{c'})}` with
`N(L_x) = ν(x)⁻¹`; (c) `B(n)_{cc'}` does not depend on the representative of `c`. -/
@[tf_id "III.brandt.thm:brandt-eq-hecke"]
theorem brandt_eq_hecke {K : Type*} [Field K] [CharZero K] {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b)
    (s : Splitting K a b) (n : ℕ) (hn : 0 < n) :
    (∀ f ∈ quatForms O s 2, ∀ c : classSet O,
      heckeOperator O n f (Quotient.out c) = ∑ᶠ c' : classSet O, (brandtMatrix O n c c' : K) • f (Quotient.out c')) ∧
    (∀ c c' : classSet O,
      Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c')) * brandtMatrix O n c c' =
        Nat.card {γ : (QuatAlg ℚ a b)ˣ //
          (finiteIdeleLattice O (Quotient.out c')).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ a b)) ≤
              finiteIdeleLattice O (Quotient.out c) ∧
            nrd (γ : QuatAlg ℚ a b) = n * normWeight (Quotient.out c') / normWeight (Quotient.out c)}) ∧
    (∀ (c c' : classSet O) (x : (BHat a b)ˣ), classOf O x = c →
      brandtMatrix O n c c' = Nat.card {q : (BHat a b)ˣ ⧸ orderCompletionUnits O //
        ∃ y ∈ normNSet O n, (y : (BHat a b)ˣ ⧸ orderCompletionUnits O) = q ∧ classOf O (x * y) = c'}) := by
  classical
  have hNb := normNSet_basic O n hn
  obtain ⟨hνpos, hνmul, hνunit, hνι⟩ := normWeight_transform O
  have hr : ∀ c : classSet O, classOf O (Quotient.out c) = c := fun c => DoubleCoset.out_eq' c
  have hcls : ∀ (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ), u ∈ orderCompletionUnits O →
      classOf O (Units.map (finEmbed a b).toMonoidHom γ * x * u) = classOf O x := by
    intro γ x u hu
    refine DoubleCoset.eq.mpr ⟨(Units.map (finEmbed a b).toMonoidHom γ)⁻¹, ?_, u⁻¹, inv_mem hu, by group⟩
    exact inv_mem ⟨γ, rfl⟩
  have hleft : ∀ y ∈ normNSet O n, ∀ v ∈ orderCompletionUnits O, v * y ∈ normNSet O n := by
    intro y hy v hv
    have := hNb.1 y hy v hv 1 (one_mem _)
    rwa [mul_one] at this
  refine ⟨fun f hf c => ?_, fun c c' => ?_, fun c c' x hx => ?_⟩
  · -- (a): the weight-2 action is trivial, and `|Γ_{c'}|⁻¹ #S_{cc'}(n) = B(n)_{cc'}`
    have hρ2 : ∀ (γ : QuatAlg ℚ a b) (v : symPowerModule K (2 - 2)), splitRep s 2 γ v = v := by
      intro γ v
      apply Subtype.ext
      show MvPolynomial.aeval (linSubst (s γ)) (v : MvPolynomial (Fin 2) K) = v
      have hv : (v : MvPolynomial (Fin 2) K) = MvPolynomial.C ((v : MvPolynomial (Fin 2) K).coeff 0) := by
        by_cases h0 : (v : MvPolynomial (Fin 2) K) = 0
        · rw [h0]
          simp
        · exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
            (((MvPolynomial.mem_homogeneousSubmodule _ _).mp v.2).totalDegree h0)
      rw [hv, MvPolynomial.aeval_C]
      rfl
    obtain ⟨hS, hMF⟩ := hecke_matrix_formula ha hb O s 2 n hn Quotient.out hr
    rw [hMF f hf c]
    refine finsum_congr fun c' => ?_
    have : Finite (classStabilizer (orderCompletionUnits O) (Quotient.out c')) :=
      ((stabilizer_units O _).2.2 ha hb).1
    have hne : (Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c')) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hsum : (∑ᶠ (γ : (QuatAlg ℚ a b)ˣ)
        (_ : (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n),
          splitRep s 2 (γ : QuatAlg ℚ a b) (f (Quotient.out c'))) =
        ∑ γ ∈ (hS c c').1.toFinset, f (Quotient.out c') := by
      rw [← finsum_mem_eq_finite_toFinset_sum _ (hS c c').1]
      exact finsum_congr fun γ => finsum_congr fun _ => hρ2 _ _
    rw [hsum, Finset.sum_const, ← Nat.card_eq_card_finite_toFinset (hS c c').1,
      ← be_fiber_count ha hb O n hn c c', ← Nat.cast_smul_eq_nsmul K, smul_smul, Nat.cast_mul, ← mul_assoc,
      inv_mul_cancel₀ hne, one_mul]
  · -- (b): `S_{cc'}(n)` is the set of `γ` with `γ L_{c'} ⊆ L_c` and `nrd γ = n ν(x_{c'})/ν(x_c)`
    rw [be_fiber_count ha hb O n hn c c']
    refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)
    have hν1 : normWeight (1 : (BHat a b)ˣ) = 1 := hνunit 1 (one_mem _)
    have hνinv : ∀ x : (BHat a b)ˣ, normWeight x⁻¹ = (normWeight x)⁻¹ := fun x =>
      eq_inv_of_mul_eq_one_left (by rw [← hνmul, inv_mul_cancel, hν1])
    have hνy : normWeight ((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c') =
        (normWeight (Quotient.out c))⁻¹ * (nrd (γ : QuatAlg ℚ a b))⁻¹ * normWeight (Quotient.out c') := by
      rw [mul_assoc, hνmul, show Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' =
        Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' * 1 by rw [mul_one],
        hνι ha hb γ _ 1 (one_mem _), hνinv]
      ring
    have hγ0 : nrd (γ : QuatAlg ℚ a b) ≠ 0 := by
      intro h0
      have h1 : nrd (γ : QuatAlg ℚ a b) * nrd ((γ⁻¹ : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1 := by
        rw [← GL2TF.Quat.nrd_mul', Units.mul_inv]
        simp [nrd]
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hνc := hνpos (Quotient.out c)
    have hνc' := hνpos (Quotient.out c')
    have hnq : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hnrd : (normWeight (Quotient.out c))⁻¹ * (nrd (γ : QuatAlg ℚ a b))⁻¹ * normWeight (Quotient.out c') =
        ((n : ℕ) : ℚ)⁻¹ ↔
        nrd (γ : QuatAlg ℚ a b) = n * normWeight (Quotient.out c') / normWeight (Quotient.out c) := by
      constructor
      · intro h
        field_simp at h
        field_simp
        linarith
      · intro h
        rw [h]
        field_simp
    have hlat : ((((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' :
          (BHat a b)ˣ)) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) ↔
        (finiteIdeleLattice O (Quotient.out c')).map (LinearMap.mulLeft ℤ (γ : QuatAlg ℚ a b)) ≤
          finiteIdeleLattice O (Quotient.out c) := by
      have hyv : ((((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' :
          (BHat a b)ˣ)) : BHat a b) =
          (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b) * (finEmbed a b (γ : QuatAlg ℚ a b) *
            ((Quotient.out c' : (BHat a b)ˣ) : BHat a b)) := by
        rw [Units.val_mul, Units.val_mul, Units.coe_map, mul_assoc]
        rfl
      constructor
      · intro hyO
        rintro _ ⟨z, ⟨w, hw, hz⟩, rfl⟩
        refine ⟨_ * w, mul_mem_orderCompletion O hyO hw, ?_⟩
        rw [hyv, LinearMap.mulLeft_apply, map_mul, hz, ← mul_assoc, ← mul_assoc, Units.mul_inv_cancel_left,
          mul_assoc]
      · intro h
        have hprop := (finiteIdeleLattice_props O (Quotient.out c)).2.2
        have hprop' := (finiteIdeleLattice_props O (Quotient.out c')).2.2
        have hmem : ((Quotient.out c' : (BHat a b)ˣ) : BHat a b) ∈
            latticeCompletion (finiteIdeleLattice O (Quotient.out c')) := by
          open scoped Pointwise in
          have h1 : ((Quotient.out c' : (BHat a b)ˣ) : BHat a b) • (1 : BHat a b) ∈
              ((Quotient.out c' : (BHat a b)ˣ) : BHat a b) •
                (latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) : Set (BHat a b)) :=
            Set.smul_mem_smul_set (one_mem_orderCompletion O)
          rw [smul_eq_mul, mul_one, ← hprop'] at h1
          exact h1
        have hclaim : ∀ w ∈ latticeCompletion (finiteIdeleLattice O (Quotient.out c')),
            finEmbed a b (γ : QuatAlg ℚ a b) * w ∈ latticeCompletion (finiteIdeleLattice O (Quotient.out c)) := by
          intro w hw
          rw [latticeCompletion] at hw
          induction hw using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨z, hz, rfl⟩ := hx
            exact Submodule.subset_span ⟨(γ : QuatAlg ℚ a b) * z, h ⟨z, hz, rfl⟩, map_mul _ _ _⟩
          | zero =>
            rw [mul_zero]
            exact Submodule.zero_mem _
          | add x z _ _ hx hz =>
            rw [mul_add]
            exact Submodule.add_mem _ hx hz
          | smul t x _ hx =>
            show finEmbed a b (γ : QuatAlg ℚ a b) * ((t : FinAdele) • x) ∈ _
            rw [mul_smul_comm]
            exact Submodule.smul_mem _ t hx
        have h2 := hclaim _ hmem
        rw [← SetLike.mem_coe, hprop] at h2
        obtain ⟨w, hw, hwe⟩ := Set.mem_smul_set.mp h2
        rw [hyv, ← hwe, smul_eq_mul, Units.inv_mul_cancel_left]
        exact hw
    show (_ ∈ normNSet O n) ↔ _
    rw [show ((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n) ↔
        (((((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' :
          (BHat a b)ˣ)) : BHat a b) ∈ latticeCompletion (Subalgebra.toSubmodule O.toSubalgebra) ∧
          ∃ w : Zhatˣ, nrd (show QuatAlg FinAdele a b from
            ((((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' :
              (BHat a b)ˣ)) : BHat a b)) = (n : FinAdele) * ((w : Zhat) : FinAdele)) from Iff.rfl,
      be_nu_iff n hn, hνy, hnrd, hlat]
  · -- (c): left translation by `u ∈ Ô^×` on `Ô_n/Ô^×`
    obtain ⟨hh, ⟨γ₀, rfl⟩, u, hu, hxe⟩ := DoubleCoset.eq.mp ((hr c).trans hx.symm)
    rw [brandtMatrix]
    have hto : ∀ q : (BHat a b)ˣ ⧸ orderCompletionUnits O,
        (∃ y ∈ normNSet O n, (y : (BHat a b)ˣ ⧸ orderCompletionUnits O) = q ∧ classOf O (Quotient.out c * y) = c') →
        ∃ y ∈ normNSet O n, (y : (BHat a b)ˣ ⧸ orderCompletionUnits O) = u⁻¹ • q ∧ classOf O (x * y) = c' := by
      rintro q ⟨y, hy, rfl, hcy⟩
      refine ⟨u⁻¹ * y, hleft y hy _ (inv_mem hu), by rw [MulAction.Quotient.smul_mk, smul_eq_mul], ?_⟩
      rw [hxe, show Units.map (finEmbed a b).toMonoidHom γ₀ * Quotient.out c * u * (u⁻¹ * y) =
        Units.map (finEmbed a b).toMonoidHom γ₀ * (Quotient.out c * y) * 1 by group, hcls _ _ 1 (one_mem _), hcy]
    have hfrom : ∀ q : (BHat a b)ˣ ⧸ orderCompletionUnits O,
        (∃ y ∈ normNSet O n, (y : (BHat a b)ˣ ⧸ orderCompletionUnits O) = q ∧ classOf O (x * y) = c') →
        ∃ y ∈ normNSet O n, (y : (BHat a b)ˣ ⧸ orderCompletionUnits O) = u • q ∧
          classOf O (Quotient.out c * y) = c' := by
      rintro q ⟨y, hy, rfl, hcy⟩
      refine ⟨u * y, hleft y hy _ hu, by rw [MulAction.Quotient.smul_mk, smul_eq_mul], ?_⟩
      rw [← hcy, hxe, show Units.map (finEmbed a b).toMonoidHom γ₀ * Quotient.out c * u * y =
        Units.map (finEmbed a b).toMonoidHom γ₀ * (Quotient.out c * (u * y)) * 1 by group, hcls _ _ 1 (one_mem _)]
    exact Nat.card_congr ⟨fun q => ⟨u⁻¹ • q.1, hto q.1 q.2⟩, fun q => ⟨u • q.1, hfrom q.1 q.2⟩,
      fun q => Subtype.ext (smul_inv_smul u q.1), fun q => Subtype.ext (inv_smul_smul u q.1)⟩

/-- Eichler data, `n ≥ 1` prime to `DM`: the row sums of `B(n)` are `Σ_{c'} B(n)_{cc'} = σ₁(n)`. -/
@[tf_id "III.brandt.thm:brandt-row-sums"]
theorem brandt_row_sums {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b) (hD : RamifiedExactly a b D)
    (φ : LevelStructure O₀.1 M) (n : ℕ) (hn : 0 < n) (hnDM : Nat.Coprime n (D * M)) :
    ∀ c : classSet (eichlerOrder φ),
      ∑ᶠ c' : classSet (eichlerOrder φ), brandtMatrix (eichlerOrder φ) n c c' = ArithmeticFunction.sigma 1 n := by
  classical
  intro c
  have hfin := (normNSet_basic (eichlerOrder φ) n hn).2.2.2.1
  have hcls : ∀ x u : (BHat a b)ˣ, u ∈ orderCompletionUnits (eichlerOrder φ) → classOf (eichlerOrder φ) (x * u) = classOf (eichlerOrder φ) x := by
    intro x u hu
    exact DoubleCoset.eq.mpr ⟨1, one_mem _, u⁻¹, inv_mem hu, by group⟩
  let g : (BHat a b)ˣ ⧸ orderCompletionUnits (eichlerOrder φ) → classSet (eichlerOrder φ) :=
    fun q => classOf (eichlerOrder φ) (Quotient.out c * Quotient.out q)
  have hgy : ∀ y : (BHat a b)ˣ, g (y : (BHat a b)ˣ ⧸ orderCompletionUnits (eichlerOrder φ)) = classOf (eichlerOrder φ) (Quotient.out c * y) := by
    intro y
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (orderCompletionUnits (eichlerOrder φ)) y
    show classOf (eichlerOrder φ) (Quotient.out c * Quotient.out (y : (BHat a b)ˣ ⧸ orderCompletionUnits (eichlerOrder φ))) = _
    rw [hu, ← mul_assoc, hcls _ _ u.2]
  have hB : ∀ c', brandtMatrix (eichlerOrder φ) n c c' = (hfin.toFinset.filter (fun q => g q = c')).card := by
    intro c'
    rw [brandtMatrix, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun q => ?_)
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨y, hy, rfl, hc⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [hgy, hc]⟩
    · rintro ⟨⟨y, hy, rfl⟩, hc⟩
      exact ⟨y, hy, rfl, by rw [← hgy, hc]⟩
  rw [finsum_congr hB, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset.image g) ?_]
  · rw [← Finset.card_eq_sum_card_fiberwise (fun q hq => Finset.mem_coe.mpr (Finset.mem_image_of_mem g hq)),
      ← Nat.card_eq_card_finite_toFinset hfin]
    exact hecke_coset_count O₀ hD φ n hn hnDM
  · intro c' hc'
    rw [Function.mem_support, Ne, Finset.card_eq_zero] at hc'
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hc'
    rw [Finset.mem_filter] at hq
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨q, hq.1, hq.2⟩)

/-- For `a, b < 0`, every order and `n ≥ 1`: `|Γ_{x_{c'}}| B(n)_{cc'} = |Γ_{x_c}| B(n)_{c'c}`. -/
@[tf_id "III.brandt.thm:brandt-weighted-symmetry"]
theorem brandt_weighted_symmetry {a b : ℤ} (ha : a < 0) (hb : b < 0) (O : QOrder a b) (n : ℕ) (hn : 0 < n) :
    ∀ c c' : classSet O,
      Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c')) * brandtMatrix O n c c' =
        Nat.card (classStabilizer (orderCompletionUnits O) (Quotient.out c)) * brandtMatrix O n c' c := by
  classical
  intro c c'
  -- `|Γ_{x_{c'}}| B(n)_{cc'} = #S_{cc'}(n)`
  have key := be_fiber_count ha hb O n hn
  -- the involution `γ ↦ n γ⁻¹` exchanges `S_{cc'}(n)` and `S_{c'c}(n)`
  have hn' : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set ν : (QuatAlg ℚ a b)ˣ := Units.map (algebraMap ℚ (QuatAlg ℚ a b)).toMonoidHom (Units.mk0 ((n : ℕ) : ℚ) hn')
    with hν
  have hνval : ((ν : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = ((n : ℕ) : QuatAlg ℚ a b) := by
    simp [hν]
  have hνc : ∀ γ : (QuatAlg ℚ a b)ˣ, ν * γ = γ * ν := by
    intro γ
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hνval]
    exact Nat.cast_comm n (γ : QuatAlg ℚ a b)
  set P : (BHat a b)ˣ := Units.map (finEmbed a b).toMonoidHom ν with hPdef
  have hPval : (P : BHat a b) = algebraMap FinAdele (BHat a b) (n : FinAdele) := by
    rw [hPdef, Units.coe_map]
    show finEmbed a b (ν : QuatAlg ℚ a b) = _
    rw [hνval, map_natCast, map_natCast]
  have hPc : ∀ x : (BHat a b)ˣ, P * x = x * P := by
    intro x
    ext
    rw [Units.val_mul, Units.val_mul, hPval]
    exact Algebra.commutes (n : FinAdele) (x : BHat a b)
  have hmap : ∀ c c' : classSet O, ∀ γ : (QuatAlg ℚ a b)ˣ,
      (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n →
      (Quotient.out c')⁻¹ * Units.map (finEmbed a b).toMonoidHom (ν * γ⁻¹) * Quotient.out c ∈ normNSet O n := by
    intro c c' γ hγ
    have h := bw_n_inv_mem O n hPval hγ
    convert h using 1
    rw [map_mul, map_inv, ← hPdef, mul_assoc, hPc, ← mul_assoc, ← mul_assoc, ← hPc, mul_assoc P]
    group
  have hinvol : ∀ γ : (QuatAlg ℚ a b)ˣ, ν * (ν * γ⁻¹)⁻¹ = γ := by
    intro γ
    rw [mul_inv_rev, inv_inv, ← mul_assoc, hνc, mul_assoc, mul_inv_cancel, mul_one]
  have hsymm : Nat.card ({γ : (QuatAlg ℚ a b)ˣ |
        (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c' ∈ normNSet O n} :
          Set (QuatAlg ℚ a b)ˣ) =
      Nat.card ({γ : (QuatAlg ℚ a b)ˣ |
        (Quotient.out c')⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c ∈ normNSet O n} :
          Set (QuatAlg ℚ a b)ˣ) :=
    Nat.card_congr ⟨fun γ => ⟨ν * (γ : (QuatAlg ℚ a b)ˣ)⁻¹, hmap c c' γ γ.2⟩,
      fun γ => ⟨ν * (γ : (QuatAlg ℚ a b)ˣ)⁻¹, hmap c' c γ γ.2⟩,
      fun γ => Subtype.ext (hinvol γ), fun γ => Subtype.ext (hinvol γ)⟩
  rw [key c c', key c' c, hsymm]

/-- Eichler data: `B(m)B(n) = B(mn)` for coprime `m, n ≥ 1`; `B(p)B(p^r) = B(p^{r+1}) + p B(p^{r−1})` for a prime
`p ∤ DM` and `r ≥ 1`; the `B(n)` with `n` prime to `DM` commute; and
`tr B(n) = Σ_c |Γ_{x_c}|⁻¹ #{γ ∈ O_{x_c} : nrd γ = n}` for `n ≥ 1`. -/
@[tf_id "III.brandt.cor:brandt-relations"]
theorem brandt_relations {a b : ℤ} {D M : ℕ} [NeZero M] (O₀ : MaxOrder a b) (hD : RamifiedExactly a b D)
    (φ : LevelStructure O₀.1 M) :
    (∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n → ∀ c c' : classSet (eichlerOrder φ),
      ∑ᶠ c'' : classSet (eichlerOrder φ), brandtMatrix (eichlerOrder φ) m c c'' * brandtMatrix (eichlerOrder φ) n c'' c' =
        brandtMatrix (eichlerOrder φ) (m * n) c c') ∧
    (∀ p r : ℕ, p.Prime → ¬ p ∣ D * M → 1 ≤ r → ∀ c c' : classSet (eichlerOrder φ),
      ∑ᶠ c'' : classSet (eichlerOrder φ),
          brandtMatrix (eichlerOrder φ) p c c'' * brandtMatrix (eichlerOrder φ) (p ^ r) c'' c' =
        brandtMatrix (eichlerOrder φ) (p ^ (r + 1)) c c' + p * brandtMatrix (eichlerOrder φ) (p ^ (r - 1)) c c') ∧
    (∀ m n : ℕ, Nat.Coprime m (D * M) → Nat.Coprime n (D * M) → ∀ c c' : classSet (eichlerOrder φ),
      ∑ᶠ c'' : classSet (eichlerOrder φ), brandtMatrix (eichlerOrder φ) m c c'' * brandtMatrix (eichlerOrder φ) n c'' c' =
        ∑ᶠ c'' : classSet (eichlerOrder φ), brandtMatrix (eichlerOrder φ) n c c'' * brandtMatrix (eichlerOrder φ) m c'' c') ∧
    (∀ n : ℕ, 0 < n →
      ∑ᶠ c : classSet (eichlerOrder φ), (brandtMatrix (eichlerOrder φ) n c c : ℚ) =
        ∑ᶠ c : classSet (eichlerOrder φ),
          (Nat.card (classStabilizer (orderCompletionUnits (eichlerOrder φ)) (Quotient.out c)) : ℚ)⁻¹ *
            (Nat.card {γ : QuatAlg ℚ a b //
              finEmbed a b γ ∈
                  (fun y : BHat a b ↦ ((Quotient.out c : (BHat a b)ˣ) : BHat a b) * y *
                    (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
                    (latticeCompletion (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) : Set (BHat a b)) ∧
                nrd γ = n} : ℚ)) := by
  classical
  have ha : a < 0 := hD.1
  have hb : b < 0 := hD.2.1
  have : Finite (classSet (eichlerOrder φ)) := classSet_finite ha hb (eichlerOrder φ)
  letI := Fintype.ofFinite (classSet (eichlerOrder φ))
  have hr : ∀ c : classSet (eichlerOrder φ), classOf (eichlerOrder φ) (Quotient.out c) = c :=
    fun c => DoubleCoset.out_eq' c
  have hcls : ∀ (γ : (QuatAlg ℚ a b)ˣ) (x u : (BHat a b)ˣ), u ∈ orderCompletionUnits (eichlerOrder φ) →
      classOf (eichlerOrder φ) (Units.map (finEmbed a b).toMonoidHom γ * x * u) = classOf (eichlerOrder φ) x := by
    intro γ x u hu
    refine DoubleCoset.eq.mpr ⟨(Units.map (finEmbed a b).toMonoidHom γ)⁻¹, ?_, u⁻¹, inv_mem hu, by group⟩
    exact inv_mem ⟨γ, rfl⟩
  -- `B(0) = 0`, since `Ô_0 = ∅`
  have hempty0 : ∀ y : (BHat a b)ˣ, y ∉ normNSet (eichlerOrder φ) 0 := by
    rintro y ⟨-, u, hu⟩
    rw [Nat.cast_zero, zero_mul] at hu
    have h1 := nrd_units_mul_inv y
    rw [hu, zero_mul] at h1
    have h2 := congrArg (fun z : FinAdele => z ⟨2, Nat.prime_two⟩) h1
    simp only [RestrictedProduct.one_apply, RestrictedProduct.zero_apply] at h2
    exact zero_ne_one h2
  have hB0 : ∀ c c' : classSet (eichlerOrder φ), brandtMatrix (eichlerOrder φ) 0 c c' = 0 := by
    intro c c'
    rw [brandtMatrix, Nat.card_eq_zero]
    left
    exact ⟨fun ⟨q, y, hy, _⟩ => hempty0 y hy⟩
  -- a splitting over `K = ℚ̄` and the weight-2 forms `1_{[x] = d}`
  obtain ⟨s₀, hs₀⟩ := IsAlgClosed.exists_pow_nat_eq ((a : ℤ) : AlgebraicClosure ℚ) (by norm_num : 0 < 2)
  set s : Splitting (AlgebraicClosure ℚ) a b := standardSplitting (AlgebraicClosure ℚ) a b s₀ hs₀ with hs
  set e1 : symPowerModule (AlgebraicClosure ℚ) (2 - 2) :=
    ⟨1, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_one _ _)⟩ with he1def
  have he1 : e1 ≠ 0 := by
    intro h
    have h' := congrArg Subtype.val h
    exact one_ne_zero h'
  have hinj : ∀ t t' : AlgebraicClosure ℚ, t • e1 = t' • e1 → t = t' := fun t t' h => smul_left_injective _ he1 h
  have hρ2 : ∀ (γ : QuatAlg ℚ a b) (v : symPowerModule (AlgebraicClosure ℚ) (2 - 2)), splitRep s 2 γ v = v := by
    intro γ v
    apply Subtype.ext
    show MvPolynomial.aeval (linSubst (s γ)) (v : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)) = v
    have hv : (v : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)) =
        MvPolynomial.C ((v : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)).coeff 0) := by
      by_cases h0 : (v : MvPolynomial (Fin 2) (AlgebraicClosure ℚ)) = 0
      · rw [h0]
        simp
      · exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
          (((MvPolynomial.mem_homogeneousSubmodule _ _).mp v.2).totalDegree h0)
    rw [hv, MvPolynomial.aeval_C]
    rfl
  let F : classSet (eichlerOrder φ) → (BHat a b)ˣ → symPowerModule (AlgebraicClosure ℚ) (2 - 2) :=
    fun d x => if classOf (eichlerOrder φ) x = d then e1 else 0
  have hFform : ∀ d, F d ∈ quatForms (eichlerOrder φ) s 2 := by
    intro d γ x u hu
    show F d (Units.map (finEmbed a b).toMonoidHom γ * x * u) = splitRep s 2 (γ : QuatAlg ℚ a b) (F d x)
    rw [hρ2]
    simp only [F, hcls γ x u hu]
  have hmod := GL2TF.HeckeModule.heckeAct_module (AlgebraicClosure ℚ) (R₀ := ℤ) (Units.map (finEmbed a b).toMonoidHom)
    (orderCompletionUnits (eichlerOrder φ)) (fun γ => splitRep s 2 (γ : QuatAlg ℚ a b))
    (by
      show splitRep s 2 ((1 : (QuatAlg ℚ a b)ˣ) : QuatAlg ℚ a b) = 1
      rw [Units.val_one, splitRep, map_one, (symPower_basic (AlgebraicClosure ℚ) (2 - 2)).2.2.2.1])
    (fun γ r v => map_zsmul _ r v)
  have hTW : ∀ j : ℕ, 0 < j → ∀ g ∈ quatForms (eichlerOrder φ) s 2,
      heckeOperator (eichlerOrder φ) j g ∈ quatForms (eichlerOrder φ) s 2 :=
    fun j hj g hg => hmod.1 ⟨_, (normNSet_basic (eichlerOrder φ) j hj).2.2.2.2 ℤ⟩ g hg
  have hTF : ∀ j : ℕ, 0 < j → ∀ g ∈ quatForms (eichlerOrder φ) s 2, ∀ c,
      heckeOperator (eichlerOrder φ) j g (Quotient.out c) =
        ∑ c' : classSet (eichlerOrder φ), (brandtMatrix (eichlerOrder φ) j c c' : AlgebraicClosure ℚ) • g (Quotient.out c') := by
    intro j hj g hg c
    rw [(brandt_eq_hecke ha hb (eichlerOrder φ) s j hj).1 g hg c, finsum_eq_sum_of_fintype]
  have hTFd : ∀ j : ℕ, 0 < j → ∀ c d, heckeOperator (eichlerOrder φ) j (F d) (Quotient.out c) =
      (brandtMatrix (eichlerOrder φ) j c d : AlgebraicClosure ℚ) • e1 := by
    intro j hj c d
    rw [hTF j hj _ (hFform d) c]
    simp only [F, hr, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq' Finset.univ d]
    simp
  have hTTF : ∀ i j : ℕ, 0 < i → 0 < j → ∀ c d,
      heckeOperator (eichlerOrder φ) i (heckeOperator (eichlerOrder φ) j (F d)) (Quotient.out c) =
        ((∑ c'' : classSet (eichlerOrder φ), brandtMatrix (eichlerOrder φ) i c c'' *
          brandtMatrix (eichlerOrder φ) j c'' d : ℕ) : AlgebraicClosure ℚ) • e1 := by
    intro i j hi hj c d
    rw [hTF i hi _ (hTW j hj _ (hFform d)) c]
    calc ∑ c'' : classSet (eichlerOrder φ), (brandtMatrix (eichlerOrder φ) i c c'' : AlgebraicClosure ℚ) •
          heckeOperator (eichlerOrder φ) j (F d) (Quotient.out c'')
        = ∑ c'' : classSet (eichlerOrder φ), ((brandtMatrix (eichlerOrder φ) i c c'' : AlgebraicClosure ℚ) *
            (brandtMatrix (eichlerOrder φ) j c'' d : AlgebraicClosure ℚ)) • e1 :=
          Finset.sum_congr rfl fun c'' _ => by rw [hTFd j hj c'' d, smul_smul]
      _ = _ := by
          rw [← Finset.sum_smul]
          push_cast
          rfl
  refine ⟨fun m n hm hn hmn c c' => ?_, fun p r hp hpDM hr1 c c' => ?_, fun m n hm hn c c' => ?_, ?_⟩
  · have h := congrFun ((hecke_multiplicative (eichlerOrder φ) s 2 m n hm hn hmn).2 (F c') (hFform c')).1
      (Quotient.out c)
    rw [hTTF m n hm hn c c', hTFd (m * n) (Nat.mul_pos hm hn) c c'] at h
    rw [finsum_eq_sum_of_fintype]
    exact_mod_cast hinj _ _ h
  · have h := congrFun (hecke_recursion O₀ hD φ s 2 le_rfl p hp hpDM r hr1 (F c') (hFform c')) (Quotient.out c)
    rw [Pi.add_apply, Pi.smul_apply, hTTF p (p ^ r) hp.pos (pow_pos hp.pos r) c c',
      hTFd (p ^ (r + 1)) (pow_pos hp.pos _) c c', hTFd (p ^ (r - 1)) (pow_pos hp.pos _) c c', smul_smul,
      ← add_smul] at h
    rw [finsum_eq_sum_of_fintype]
    have h' := hinj _ _ h
    norm_num at h'
    exact_mod_cast h'
  · rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [hB0]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [hB0]
    have h := congrFun (hecke_commutative O₀ hD φ s 2 m n hm hn (F c') (hFform c')) (Quotient.out c)
    rw [hTTF m n hm0 hn0 c c', hTTF n m hn0 hm0 c c'] at h
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    exact_mod_cast hinj _ _ h
  · intro n hn
    refine finsum_congr fun c => ?_
    have : Finite (classStabilizer (orderCompletionUnits (eichlerOrder φ)) (Quotient.out c)) :=
      ((stabilizer_units _ _).2.2 ha hb).1
    have hne : (Nat.card (classStabilizer (orderCompletionUnits (eichlerOrder φ)) (Quotient.out c)) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hfc := be_fiber_count ha hb (eichlerOrder φ) n hn c c
    have hnq : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hval : ∀ γ : (QuatAlg ℚ a b)ˣ,
        (((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c : (BHat a b)ˣ) : BHat a b) =
          (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b) * finEmbed a b (γ : QuatAlg ℚ a b) *
            ((Quotient.out c : (BHat a b)ˣ) : BHat a b) := by
      intro γ
      rw [Units.val_mul, Units.val_mul, Units.coe_map]
      rfl
    have hnrdc : ∀ γ : (QuatAlg ℚ a b)ˣ, nrd (show QuatAlg FinAdele a b from
        (((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c : (BHat a b)ˣ) : BHat a b)) =
          algebraMap ℚ FinAdele (nrd (γ : QuatAlg ℚ a b)) := by
      intro γ
      rw [hval, bw_nrd_mul, bw_nrd_mul]
      have h1 := nrd_units_mul_inv (Quotient.out c)
      have h2 : nrd (show QuatAlg FinAdele a b from finEmbed a b (γ : QuatAlg ℚ a b)) =
          algebraMap ℚ FinAdele (nrd (γ : QuatAlg ℚ a b)) :=
        ((nrd_trd_basic (R := ℚ) (a := a) (b := b)).2.2.2 FinAdele (algebraMap ℚ FinAdele) γ).1
      rw [h2]
      linear_combination (algebraMap ℚ FinAdele (nrd (γ : QuatAlg ℚ a b))) * h1
    have hn1 : (n : FinAdele) * algebraMap ℚ FinAdele ((n : ℚ)⁻¹) = 1 := by
      rw [← map_natCast (algebraMap ℚ FinAdele), ← map_mul, mul_inv_cancel₀ hnq, map_one]
    have hfwd : ∀ γ : (QuatAlg ℚ a b)ˣ,
        (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c ∈ normNSet (eichlerOrder φ) n →
        nrd (γ : QuatAlg ℚ a b) = n := by
      intro γ hγ
      obtain ⟨-, w, hw⟩ := hγ
      rw [hnrdc] at hw
      have hγne : (γ : QuatAlg ℚ a b) ≠ 0 := Units.ne_zero γ
      have hd := (nrd_definite ha hb).1 (γ : QuatAlg ℚ a b)
      have hpos : 0 < nrd (γ : QuatAlg ℚ a b) :=
        lt_of_le_of_ne (le_trans (by positivity) hd.1) (Ne.symm (mt hd.2.mp hγne))
      set q : ℚ := nrd (γ : QuatAlg ℚ a b) / n with hq
      have hqpos : 0 < q := div_pos hpos (Nat.cast_pos.mpr hn)
      have hqw : algebraMap ℚ FinAdele q = ((w : Zhat) : FinAdele) := by
        rw [hq, div_eq_mul_inv, map_mul, hw]
        linear_combination ((w : Zhat) : FinAdele) * hn1
      have hqiw : algebraMap ℚ FinAdele q⁻¹ = (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) := by
        have h1 : algebraMap ℚ FinAdele q⁻¹ * algebraMap ℚ FinAdele q = 1 := by
          rw [← map_mul, inv_mul_cancel₀ hqpos.ne', map_one]
        have h2 := bw_zhat_unit_inv_mul w
        rw [hqw] at h1
        linear_combination (-(algebraMap ℚ FinAdele q⁻¹)) * h2 + (((w⁻¹ : Zhatˣ) : Zhat) : FinAdele) * h1
      obtain ⟨k, hk⟩ := rat_isInt_of_mem_zhat q (by rw [hqw]; exact (w : Zhat).2)
      obtain ⟨k', hk'⟩ := rat_isInt_of_mem_zhat q⁻¹ (by rw [hqiw]; exact ((w⁻¹ : Zhatˣ) : Zhat).2)
      have hkk : k * k' = 1 := by
        have h3 : ((k * k' : ℤ) : ℚ) = 1 := by
          push_cast
          rw [← hk, ← hk', mul_inv_cancel₀ hqpos.ne']
        exact_mod_cast h3
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hkk with h4 | h4
      · have hq1 : q = 1 := by rw [hk, h4]; norm_num
        rw [hq] at hq1
        exact (div_eq_one_iff_eq hnq).mp hq1
      · exfalso
        rw [hk, h4] at hqpos
        norm_num at hqpos
    have hmk : ∀ γ' : QuatAlg ℚ a b, nrd γ' = n → ∃ U' : (QuatAlg ℚ a b)ˣ, (U' : QuatAlg ℚ a b) = γ' := by
      intro γ' hγ'
      have h1 := ((nrd_trd_basic.{0, 0} (R := ℚ) (a := a) (b := b)).1 γ').1
      have h2 := ((nrd_trd_basic.{0, 0} (R := ℚ) (a := a) (b := b)).1 γ').2.1
      rw [hγ'] at h1 h2
      refine ⟨⟨γ', ((n : ℕ) : ℚ)⁻¹ • star γ', ?_, ?_⟩, rfl⟩
      · rw [mul_smul_comm, h1, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hnq, map_one]
      · rw [smul_mul_assoc, h2, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hnq, map_one]
    have hfwd1 : ∀ γ : (QuatAlg ℚ a b)ˣ,
        (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c ∈ normNSet (eichlerOrder φ) n →
        finEmbed a b (γ : QuatAlg ℚ a b) ∈ (fun y : BHat a b ↦ ((Quotient.out c : (BHat a b)ˣ) : BHat a b) * y *
          (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
            (latticeCompletion (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) : Set (BHat a b)) := by
      intro γ hγ
      refine ⟨_, hγ.1, ?_⟩
      show ((Quotient.out c : (BHat a b)ˣ) : BHat a b) *
          (((Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c : (BHat a b)ˣ) : BHat a b) *
          (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b) = _
      rw [hval]
      simp only [mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left]
    have hbwd : ∀ (γ' : QuatAlg ℚ a b) (h : finEmbed a b γ' ∈
        (fun y : BHat a b ↦ ((Quotient.out c : (BHat a b)ˣ) : BHat a b) * y *
          (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
            (latticeCompletion (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) : Set (BHat a b)) ∧
        nrd γ' = n),
        (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom (Classical.choose (hmk γ' h.2)) * Quotient.out c ∈
          normNSet (eichlerOrder φ) n := by
      intro γ' h
      have hU := Classical.choose_spec (hmk γ' h.2)
      refine ⟨?_, 1, ?_⟩
      · rw [hval, hU]
        obtain ⟨y, hy, hye⟩ := h.1
        rw [← hye]
        simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left]
        exact hy
      · rw [hnrdc, hU, h.2]
        simp
    have hcard : Nat.card ({γ : (QuatAlg ℚ a b)ˣ |
        (Quotient.out c)⁻¹ * Units.map (finEmbed a b).toMonoidHom γ * Quotient.out c ∈ normNSet (eichlerOrder φ) n} :
          Set (QuatAlg ℚ a b)ˣ) =
        Nat.card {γ : QuatAlg ℚ a b //
          finEmbed a b γ ∈ (fun y : BHat a b ↦ ((Quotient.out c : (BHat a b)ˣ) : BHat a b) * y *
            (((Quotient.out c)⁻¹ : (BHat a b)ˣ) : BHat a b)) ''
              (latticeCompletion (Subalgebra.toSubmodule (eichlerOrder φ).toSubalgebra) : Set (BHat a b)) ∧
          nrd γ = n} :=
      Nat.card_congr ⟨fun γ => ⟨(γ.1 : QuatAlg ℚ a b), hfwd1 γ.1 γ.2, hfwd γ.1 γ.2⟩,
        fun γ' => ⟨Classical.choose (hmk γ'.1 γ'.2.2), hbwd γ'.1 γ'.2⟩,
        fun γ => Subtype.ext (Units.ext (Classical.choose_spec (hmk (γ.1 : QuatAlg ℚ a b) (hfwd γ.1 γ.2)))),
        fun γ' => Subtype.ext (Classical.choose_spec (hmk γ'.1 γ'.2.2))⟩
    rw [← hcard, ← hfc, Nat.cast_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GL2TF.Quat
