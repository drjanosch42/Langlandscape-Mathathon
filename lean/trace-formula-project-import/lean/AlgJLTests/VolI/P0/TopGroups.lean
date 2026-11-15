import AlgJL.VolI.P0.TopGroups

/-!
# Tests for `GL2TF.VolI.P0.TopGroups`

Non-vacuity examples (PLAN.md §2.3) at `ℚ_[p]`.
-/

open GL2TF

namespace GL2TFTests

/-- `K_{ℚ_p}` is a subgroup containing `1`. -/
theorem one_mem_maxCompact_padic (p : ℕ) [Fact p.Prime] : (1 : GL (Fin 2) ℚ_[p]) ∈ 𝐊[ℚ_[p]] :=
  Subgroup.one_mem _

/-! ### M3 U6: adelic `GL₂` -/

/-- The components of `g ∈ G(𝔸)` are the maps induced by the coordinate ring homomorphisms; `g_p = (g_f)_p`. -/
theorem adelic_components_eq (p : Nat.Primes) (g : GL (Fin 2) Adele) :
    compInf = gl2Map (RingHom.fst ℝ FinAdele) ∧ compFin = gl2Map (RingHom.snd ℝ FinAdele) ∧
      compFinPlace p = gl2Map (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p) ∧
      compPlace p g = compFinPlace p (compFin g) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The image of `γ ∈ GL₂(ℚ)` lies in `G(ℚ)`. -/
theorem gl2Map_mem_gl2RatAdelic (γ : GL (Fin 2) ℚ) : gl2Map (algebraMap ℚ Adele) γ ∈ gl2RatAdelic :=
  ⟨γ, rfl⟩

/-- Membership in `K_f` and `K` is componentwise. -/
theorem mem_maxCompactFin_adelic (k : GL (Fin 2) FinAdele) (g : GL (Fin 2) Adele) :
    (k ∈ maxCompactFin ↔ ∀ p : Nat.Primes, compFinPlace p k ∈ 𝐊[ℚ_[p]]) ∧
      (g ∈ maxCompactAdelic ↔ compInf g ∈ maxCompactReal ∧ ∀ p : Nat.Primes, compPlace p g ∈ 𝐊[ℚ_[p]]) := by
  simp [maxCompactFin, maxCompactAdelic, Subgroup.mem_iInf]

/-- `a(r) ∈ A_G^+` for `r > 0`. -/
theorem centralElt_mem_splitComponent (r : ℝˣ) (hr : 0 < (r : ℝ)) : centralElt r ∈ splitComponent :=
  ⟨r, hr, rfl⟩

/-- `n(x)` lies in the mirabolic subgroup. -/
theorem upperRightHom_mem_mirabolic {R : Type*} [CommRing R] (x : R) :
    Matrix.GeneralLinearGroup.upperRightHom x ∈ mirabolic R := by
  simp [mirabolic]

/-- Elements of `GL₂(Ẑ)` whose reduction mod `N` is upper triangular (resp. mirabolic, resp. trivial) give elements of
`K_0(N)` (resp. `K_1(N)`, resp. `K_f(N)`). -/
theorem gl2Zhat_mem_congruence (N : ℕ) (g : GL (Fin 2) Zhat) :
    (gl2ZhatRed N g ∈ GL2TF.borel _ → gl2Zhat g ∈ congruenceK0 N) ∧
      (gl2ZhatRed N g ∈ mirabolic _ → gl2Zhat g ∈ congruenceK1 N) ∧
      (gl2ZhatRed N g = 1 → gl2Zhat g ∈ congruenceKf N) :=
  ⟨fun h ↦ ⟨g, h, rfl⟩, fun h ↦ ⟨g, h, rfl⟩, fun h ↦ ⟨g, h, rfl⟩⟩

/-- `g ↦ (g_p)_p` has components `g_p`. -/
theorem gl2FinToResProd_apply (g : GL (Fin 2) FinAdele) (p : Nat.Primes) :
    gl2FinToResProd g p = compFinPlace p g :=
  rfl

/-- `diag(t₁, t₂) ∈ T(𝔸)^1` for norm-one `t₁, t₂`; `G(𝔸)^1` is the kernel of `g ↦ |det g|_𝔸`. -/
theorem torusNormOne_normOneGroup (t₁ t₂ : Idele) (h₁ : t₁ ∈ ideleNormOne) (h₂ : t₂ ∈ ideleNormOne) :
    diagElt t₁ t₂ ∈ torusNormOne ∧ normOneGroup = (ideleNorm.comp Matrix.GeneralLinearGroup.det).ker :=
  ⟨⟨(t₁, t₂), ⟨h₁, h₂⟩, rfl⟩, rfl⟩

/-- m5: `K_0(2) ≠ K_f`: the Weyl element `(0 1; 1 0)` lies in `K_f` but not in `K_0(2)`. -/
theorem congruenceK0_two_ne_maxCompactFin : congruenceK0 2 ≠ maxCompactFin := by
  intro h
  set w : GL (Fin 2) ℚ := ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  set k := gl2Map (algebraMap ℚ FinAdele) w
  have hval : (k : Matrix (Fin 2) (Fin 2) FinAdele) = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [k, w, gl2Map, Matrix.GeneralLinearGroup.map]
  have hinv : ((k⁻¹ : GL (Fin 2) FinAdele) : Matrix (Fin 2) (Fin 2) FinAdele) = !![0, 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [k, w, gl2Map, Matrix.GeneralLinearGroup.map]
  have hk : k ∈ maxCompactFin := by
    rw [mem_maxCompactFin_iff', hval, hinv]
    intro i j; fin_cases i <;> fin_cases j <;> simp [Zhat.zero_mem, Zhat.one_mem]
  rw [← h, (congruence_explicit 2 (by norm_num)).1, hval] at hk
  obtain ⟨-, z, hz, h1⟩ := hk
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h1
  have hp : Nat.Prime 2 := Nat.prime_two
  set p2 : Nat.Primes := ⟨2, hp⟩
  have h2 := congrArg (fun x : FinAdele ↦ x p2) h1
  simp only [RestrictedProduct.one_apply, RestrictedProduct.mul_apply] at h2
  have hz2 : ‖z p2‖ ≤ 1 := (mem_zhat.mp hz) p2
  have hn := congrArg norm h2
  rw [norm_one, norm_mul] at hn
  have h2n : ‖((2 : ℕ) : FinAdele) p2‖ = 1 / 2 := by
    have : ((2 : ℕ) : FinAdele) p2 = ((2 : ℕ) : ℚ_[(p2 : ℕ)]) :=
      map_natCast (RestrictedProduct.evalRingHom (fun p : Nat.Primes ↦ ℚ_[p]) p2 :
        FinAdele →+* ℚ_[(p2 : ℕ)]) 2
    rw [this, Padic.norm_p]
    norm_num [p2]
  rw [h2n] at hn
  linarith

/-- Unfolding of `matPair`, and `glProdEquiv` inverts `glPair` on `GL₂(ℝ) × GL₂(𝔸_f)`. -/
theorem matPair_glPair_glProdEquiv (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 2) FinAdele)
    (a : GL (Fin 2) ℝ) (b : GL (Fin 2) FinAdele) :
    matPair A B = Matrix.of (fun i j ↦ (A i j, B i j)) ∧
      ((glPair a b : GL (Fin 2) (ℝ × FinAdele)) : Matrix (Fin 2) (Fin 2) (ℝ × FinAdele)) = matPair a b ∧
      glProdEquiv (glPair a b) = (a, b) :=
  ⟨rfl, rfl, (glProdEquiv (R := ℝ) (S := FinAdele)).apply_symm_apply (a, b)⟩

end GL2TFTests
