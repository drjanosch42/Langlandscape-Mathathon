/-
Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Januszewski, Abhijit A J
-/
import Langlandscape.Graph.Weighted

/-!
# Bipartite collapse — S03-L2

Lemma bip (`lem:s03-bip`) for a finite connected bipartite multigraph `G`, over any commutative
ring `R`:

* (a) `H₁(G, R) = ker ∂ ⊆ R[E]⁰` (`bip_ker_le_deg0`), `∂` maps `R[E]⁰` onto
  `R[V₀]⁰ × R[V₁]⁰` (`bip_surj_deg0`), the exact sequence
  `0 → H₁(G, R) → R[E]⁰ → R[V₀]⁰ × R[V₁]⁰ → 0` (`bip_exact`), and over `ℤ` the rank
  `rk H₁ = |E| − |V₀| − |V₁| + 1` (`bip_rank`);
* (b) for every abelian group `A`, the kernel of `∂^∨ : (f₀, f₁) ↦ s₁^* f₁ − s₀^* f₀` is the
  diagonal of constants (`bip_ker_dual`);
* (c) the connecting map (snake-lemma recipe, `collapseDelta`) for the short exact
  sequence of chain complexes `0 → K_• → C_•(G) → C_•(G^{(2)}) → 0` of the two-vertex collapse
  `collapse2 G` (S03-L1) is `∂` restricted to `H₁(G^{(2)}, R) = R[E]⁰`
  (`H1_collapse2`, `collapseBoundary_eq`, `ker_collapseBoundary`, `bip_collapse_connecting`), and `H₁(G, R) → H₁(G^{(2)}, R) → K₀` is exact
  (`bip_collapse_exact`).

Tex labels: `lem:s03-bip`.

Status: formalized (Mathlib + stage-02 `Graph.boundary` + S03-L1 `deg0`, `collapse2`).
Never `open Graph` (clash with `_root_.Graph`).
-/

namespace Langlandscape.Graph

open Finsupp

/-- The degree (augmentation) `R[S] → R`, the sum of all coefficients; `deg0 S R` is its kernel. -/
noncomputable def degMap (S : Type*) (R : Type*) [CommRing R] : (S →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R fun _ : S => (1 : R)

section Degree

variable {S : Type*} {R : Type*} [CommRing R]

/-- Membership in `R[S]⁰` (`lem:s03-bip`, `s03-bip`). -/
theorem mem_deg0_iff (x : S →₀ R) : x ∈ deg0 S R ↔ degMap S R x = 0 := by
  show x ∈ LinearMap.ker (degMap S R) ↔ _
  exact LinearMap.mem_ker

/-- Degree of a basis vector (`lem:s03-bip`, `s03-bip`). -/
theorem degMap_single (s : S) (r : R) : degMap S R (Finsupp.single s r) = r := by
  simp [degMap, Finsupp.linearCombination_single]

end Degree

variable (G : BipMultigraph) (R : Type*) [CommRing R]

/-- The vertex part `K₀ = R[V₀]⁰ × R[V₁]⁰` of the kernel of the collapse map. -/
noncomputable def deg0Prod : Submodule R ((G.V0 →₀ R) × (G.V1 →₀ R)) :=
  (deg0 G.V0 R).prod (deg0 G.V1 R)

variable {G R}

/-- The augmentation is the sum of the two degrees (`lem:s03-bip`, `s03-bip`). -/
theorem aug_apply (z : (G.V0 →₀ R) × (G.V1 →₀ R)) :
    aug G R z = degMap G.V0 R z.1 + degMap G.V1 R z.2 := by
  simp only [aug, degMap, LinearMap.coprod_apply]

/-- The type-0 component of `∂ y` has degree `−deg y` (`lem:s03-bip`, `s03-bip`). -/
theorem degMap_boundary_fst (y : G.E →₀ R) :
    degMap G.V0 R (boundary G R y).1 = -degMap G.E R y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Prod.fst_add, hf, hg, neg_add]
  | single e r => simp [boundary_single, degMap_single]

/-- The type-1 component of `∂ y` has degree `deg y` (`lem:s03-bip`, `s03-bip`). -/
theorem degMap_boundary_snd (y : G.E →₀ R) :
    degMap G.V1 R (boundary G R y).2 = degMap G.E R y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Prod.snd_add, hf, hg]
  | single e r => simp [boundary_single, degMap_single]

/-- Membership in `H₁(G, R) = ker ∂` (`lem:s03-bip`, `s03-bip`). -/
theorem mem_H1_iff (y : G.E →₀ R) : y ∈ H1 G R ↔ boundary G R y = 0 := by
  show y ∈ LinearMap.ker (boundary G R) ↔ _
  exact LinearMap.mem_ker

/-- `∂` maps `R[E]⁰` into `R[V₀]⁰ × R[V₁]⁰` (`lem:s03-bip`(a), `s03-bip`). -/
theorem boundary_mem_deg0Prod {y : G.E →₀ R} (hy : y ∈ deg0 G.E R) :
    boundary G R y ∈ deg0Prod G R := by
  rw [mem_deg0_iff] at hy
  show boundary G R y ∈ (deg0 G.V0 R).prod (deg0 G.V1 R)
  rw [Submodule.mem_prod, mem_deg0_iff, mem_deg0_iff, degMap_boundary_fst, degMap_boundary_snd, hy,
    neg_zero]
  exact ⟨rfl, rfl⟩

/-- `lem:s03-bip`(a), first claim (`s03-bip`): `H₁(G, R) = ker ∂ ⊆ R[E]⁰`, over any commutative
ring (no connectivity needed). -/
theorem bip_ker_le_deg0 : H1 G R ≤ deg0 G.E R := by
  intro y hy
  rw [mem_H1_iff] at hy
  rw [mem_deg0_iff, ← degMap_boundary_snd y, hy, Prod.snd_zero, map_zero]

/-- `lem:s03-bip`(a), surjectivity (`s03-bip`): for connected `G`, over any commutative ring,
`∂(R[E]⁰) = R[V₀]⁰ × R[V₁]⁰`. Input: stage 02's `range_boundary_of_connected`. -/
theorem bip_surj_deg0 [Finite G.V0] [Finite G.V1] (hc : G.Connected) :
    (deg0 G.E R).map (boundary G R) = deg0Prod G R := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact boundary_mem_deg0Prod hy
  · intro z hz
    have hz' : z ∈ (deg0 G.V0 R).prod (deg0 G.V1 R) := hz
    rw [Submodule.mem_prod, mem_deg0_iff, mem_deg0_iff] at hz'
    have hker : z ∈ LinearMap.ker (aug G R) := by
      rw [LinearMap.mem_ker, aug_apply, hz'.1, hz'.2, add_zero]
    rw [← range_boundary_of_connected (R := R) hc] at hker
    obtain ⟨y, rfl⟩ := hker
    have hy : y ∈ deg0 G.E R := by
      rw [mem_deg0_iff, ← degMap_boundary_snd y]
      exact hz'.2
    show boundary G R y ∈ (deg0 G.E R).map (boundary G R)
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩

variable (G R)

/-- The inclusion `H₁(G, R) → R[E]⁰` (`lem:s03-bip`(a)). -/
noncomputable def H1toDeg0 : H1 G R →ₗ[R] deg0 G.E R :=
  Submodule.inclusion bip_ker_le_deg0

/-- The restriction `∂ : R[E]⁰ → R[V₀]⁰ × R[V₁]⁰` (`lem:s03-bip`(a)). -/
noncomputable def boundaryDeg0 : deg0 G.E R →ₗ[R] deg0Prod G R :=
  ((boundary G R).domRestrict (deg0 G.E R)).codRestrict (deg0Prod G R) fun y =>
    boundary_mem_deg0Prod y.2

variable {G R}

/-- `lem:s03-bip`(a), exact sequence (`s03-bip`): for connected `G`, over any commutative ring,
`0 → H₁(G, R) → R[E]⁰ → R[V₀]⁰ × R[V₁]⁰ → 0` is exact. -/
theorem bip_exact [Finite G.V0] [Finite G.V1] (hc : G.Connected) :
    Function.Injective (H1toDeg0 G R) ∧ Function.Exact (H1toDeg0 G R) (boundaryDeg0 G R) ∧
      Function.Surjective (boundaryDeg0 G R) := by
  refine ⟨Submodule.inclusion_injective _, ?_, ?_⟩
  · intro y
    constructor
    · intro h
      have h' : boundary G R (y : G.E →₀ R) = 0 := congrArg Subtype.val h
      exact ⟨⟨(y : G.E →₀ R), (mem_H1_iff _).mpr h'⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact (mem_H1_iff _).mp x.2
  · intro z
    have hz : (z : (G.V0 →₀ R) × (G.V1 →₀ R)) ∈ (deg0 G.E R).map (boundary G R) := by
      rw [bip_surj_deg0 hc]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := hz
    exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

/-- `lem:s03-bip`(a), rank over a domain (`s03-bip`): `rk_R H₁ = |E| − |V₀| − |V₁| + 1`, from
stage 02's `finrank_H1_of_connected`. -/
theorem bip_rank_of_isDomain [IsDomain R] [Finite G.V0] [Finite G.V1] [Finite G.E]
    (hc : G.Connected) :
    (Module.finrank R (H1 G R) : ℤ) = Nat.card G.E - Nat.card G.V0 - Nat.card G.V1 + 1 := by
  have h := finrank_H1_of_connected (R := R) hc
  omega

/-- `lem:s03-bip`(a), rank over `ℤ` (`s03-bip`): `rk H₁(G, ℤ) = |E| − |V₀| − |V₁| + 1`. -/
theorem bip_rank [Finite G.V0] [Finite G.V1] [Finite G.E] (hc : G.Connected) :
    (Module.finrank ℤ (H1 G ℤ) : ℤ) = Nat.card G.E - Nat.card G.V0 - Nat.card G.V1 + 1 :=
  bip_rank_of_isDomain hc

/-! ### (b) the dual map -/

variable (G) in
/-- The dual of `∂`: `∂^∨ (f₀, f₁) = s₁^* f₁ − s₀^* f₀`, i.e. `e ↦ f₁ (s₁ e) − f₀ (s₀ e)`
(`lem:s03-bip`(b)). -/
def boundaryDual (A : Type*) [AddCommGroup A] : (G.V0 → A) × (G.V1 → A) →+ (G.E → A) where
  toFun f := fun e => f.2 (G.s1 e) - f.1 (G.s0 e)
  map_zero' := by
    funext e
    simp
  map_add' f g := by
    funext e
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    abel

/-- Value of `∂^∨` at an edge (`lem:s03-bip`(b), `s03-bip`). -/
theorem boundaryDual_apply {A : Type*} [AddCommGroup A] (f : (G.V0 → A) × (G.V1 → A)) (e : G.E) :
    boundaryDual G A f e = f.2 (G.s1 e) - f.1 (G.s0 e) :=
  rfl

/-- `lem:s03-bip`(b) (`s03-bip`): for connected `G` and every abelian group `A`, the kernel of
`∂^∨ : A^{V₀} × A^{V₁} → A^E` is the diagonal `{(c·𝟏, c·𝟏) : c ∈ A}`. -/
theorem bip_ker_dual (A : Type*) [AddCommGroup A] (hc : G.Connected)
    (f : (G.V0 → A) × (G.V1 → A)) :
    boundaryDual G A f = 0 ↔ ∃ c : A, f = (fun _ => c, fun _ => c) := by
  constructor
  · intro h
    have he : ∀ e, f.1 (G.s0 e) = f.2 (G.s1 e) := fun e => by
      have h1 : f.2 (G.s1 e) - f.1 (G.s0 e) = 0 := by
        rw [← boundaryDual_apply, h, Pi.zero_apply]
      exact (sub_eq_zero.mp h1).symm
    have hadj : ∀ u v : G.V0 ⊕ G.V1, G.toSimpleGraph.Adj u v →
        Sum.elim f.1 f.2 u = Sum.elim f.1 f.2 v := by
      intro u v huv
      obtain ⟨_, ⟨e, rfl, rfl⟩ | ⟨e, rfl, rfl⟩⟩ := huv
      · exact he e
      · exact (he e).symm
    have hreach : ∀ u v : G.V0 ⊕ G.V1, G.toSimpleGraph.Reachable u v →
        Sum.elim f.1 f.2 u = Sum.elim f.1 f.2 v := by
      intro u v huv
      rw [SimpleGraph.reachable_iff_reflTransGen] at huv
      induction huv with
      | refl => rfl
      | tail _ ha ih => exact ih.trans (hadj _ _ ha)
    have hc' : G.toSimpleGraph.Connected := hc
    obtain ⟨u0⟩ := hc'.nonempty
    refine ⟨Sum.elim f.1 f.2 u0, Prod.ext (funext fun x => ?_) (funext fun y => ?_)⟩
    · exact hreach (Sum.inl x) u0 (hc'.preconnected _ _)
    · exact hreach (Sum.inr y) u0 (hc'.preconnected _ _)
  · rintro ⟨c, rfl⟩
    funext e
    simp [boundaryDual_apply]

/-! ### (c) the two-vertex collapse and its connecting map -/

/-- The boundary of the collapse `G^{(2)}` is `y ↦ deg y · ([1] − [0])` (`lem:s03-bip`(c),
`s03-bip`). -/
theorem boundary_collapse2_apply (y : G.E →₀ R) :
    WGraph.boundary (collapse2 G) R y =
      Finsupp.single true (degMap G.E R y) - Finsupp.single false (degMap G.E R y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, hf, hg, Finsupp.single_add]
    abel
  | single e r =>
    rw [WGraph.boundary_single, degMap_single]

/-- `lem:s03-bip`(c) (`s03-bip`): `H₁(G^{(2)}, R) = ker (R[E] → R²) = R[E]⁰`. -/
theorem H1_collapse2 :
    LinearMap.ker (WGraph.boundary (collapse2 G) R) = deg0 G.E R := by
  ext y
  rw [LinearMap.mem_ker, boundary_collapse2_apply, mem_deg0_iff]
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h true
    simpa [Finsupp.single_apply] using h1
  · intro h
    simp [h]

variable (G R)

/-- The boundary of the collapse `G^{(2)}` on `R[E]`, with explicit types:
`y ↦ deg y · ([1] − [0]) ∈ R[{0, 1}] = R[Bool]`; equal to `WGraph.boundary (collapse2 G) R`
(`collapseBoundary_eq`) (`lem:s03-bip`(c)). -/
noncomputable def collapseBoundary : (G.E →₀ R) →ₗ[R] (Bool →₀ R) :=
  ((Finsupp.lsingle true : R →ₗ[R] (Bool →₀ R)) - Finsupp.lsingle false) ∘ₗ degMap G.E R

/-- The collapse on vertices `C₀(G) = R[V₀] × R[V₁] → C₀(G^{(2)}) = R[Bool]`,
`(a, b) ↦ deg a · [0] + deg b · [1]` (`lem:s03-bip`(c)). -/
noncomputable def collapseVert : (G.V0 →₀ R) × (G.V1 →₀ R) →ₗ[R] (Bool →₀ R) :=
  ((Finsupp.lsingle false : R →ₗ[R] (Bool →₀ R)) ∘ₗ degMap G.V0 R).coprod
    ((Finsupp.lsingle true : R →ₗ[R] (Bool →₀ R)) ∘ₗ degMap G.V1 R)

variable {G R}

/-- Value of the collapse boundary (`lem:s03-bip`(c), `s03-bip`). -/
theorem collapseBoundary_apply (y : G.E →₀ R) :
    collapseBoundary G R y =
      Finsupp.single true (degMap G.E R y) - Finsupp.single false (degMap G.E R y) := by
  simp only [collapseBoundary, LinearMap.comp_apply, LinearMap.sub_apply, Finsupp.lsingle_apply]

/-- `collapseBoundary` is the boundary of the weighted graph `collapse2 G` (S03-L1)
(`lem:s03-bip`(c), `s03-bip`). -/
theorem collapseBoundary_eq (y : G.E →₀ R) :
    WGraph.boundary (collapse2 G) R y = collapseBoundary G R y :=
  (boundary_collapse2_apply y).trans (collapseBoundary_apply y).symm

/-- `ker collapseBoundary = R[E]⁰` (`lem:s03-bip`(c), `s03-bip`). -/
theorem ker_collapseBoundary : LinearMap.ker (collapseBoundary G R) = deg0 G.E R := by
  ext y
  rw [LinearMap.mem_ker, collapseBoundary_apply, mem_deg0_iff]
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h true
    simpa [Finsupp.single_apply] using h1
  · intro h
    simp [h]

/-- Value of the vertex collapse (`lem:s03-bip`(c), `s03-bip`). -/
theorem collapseVert_apply (z : (G.V0 →₀ R) × (G.V1 →₀ R)) :
    collapseVert G R z =
      Finsupp.single false (degMap G.V0 R z.1) + Finsupp.single true (degMap G.V1 R z.2) := by
  simp only [collapseVert, LinearMap.coprod_apply, LinearMap.comp_apply, Finsupp.lsingle_apply]

/-- Top row `0 → C₁(G) → C₁(G^{(2)})` (the identity of `R[E]`) is exact, with `K₁ = 0` modelled
by `⊥` (`lem:s03-bip`(c), `s03-bip`). -/
theorem collapse_exact_top :
    Function.Exact (⊥ : Submodule R (G.E →₀ R)).subtype
      (LinearMap.id : (G.E →₀ R) →ₗ[R] (G.E →₀ R)) := by
  intro y
  rw [LinearMap.id_apply]
  constructor
  · intro h
    refine ⟨0, ?_⟩
    rw [map_zero, h]
  · rintro ⟨x, rfl⟩
    rw [Submodule.subtype_apply]
    exact (Submodule.mem_bot R).mp x.2

/-- Bottom row `K₀ → C₀(G) → C₀(G^{(2)})` is exact (`lem:s03-bip`(c), `s03-bip`). -/
theorem collapse_exact_bot : Function.Exact (deg0Prod G R).subtype (collapseVert G R) := by
  intro z
  rw [collapseVert_apply]
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h false
    have h1 := DFunLike.congr_fun h true
    simp at h0 h1
    have hz : z ∈ deg0Prod G R := by
      show z ∈ (deg0 G.V0 R).prod (deg0 G.V1 R)
      rw [Submodule.mem_prod, mem_deg0_iff, mem_deg0_iff]
      exact ⟨h0, h1⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    have hx : (x : (G.V0 →₀ R) × (G.V1 →₀ R)) ∈ (deg0 G.V0 R).prod (deg0 G.V1 R) := x.2
    rw [Submodule.mem_prod, mem_deg0_iff, mem_deg0_iff] at hx
    simp [Submodule.subtype_apply, hx.1, hx.2]

/-- Left square of the collapse diagram commutes (`lem:s03-bip`(c), `s03-bip`). -/
theorem collapse_comm_left :
    (deg0Prod G R).subtype ∘ₗ (0 : (⊥ : Submodule R (G.E →₀ R)) →ₗ[R] deg0Prod G R) =
      boundary G R ∘ₗ (⊥ : Submodule R (G.E →₀ R)).subtype := by
  refine LinearMap.ext fun x => ?_
  have hx : (x : G.E →₀ R) = 0 := (Submodule.mem_bot R).mp x.2
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.zero_apply, map_zero,
    Submodule.subtype_apply, hx, map_zero]

/-- Right square of the collapse diagram commutes: `π₀ ∘ ∂_G = ∂_{G^{(2)}} ∘ π₁`
(`lem:s03-bip`(c), `s03-bip`). -/
theorem collapse_comm_right :
    collapseVert G R ∘ₗ boundary G R =
      collapseBoundary G R ∘ₗ (LinearMap.id : (G.E →₀ R) →ₗ[R] (G.E →₀ R)) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_apply, collapseVert_apply,
    degMap_boundary_fst, degMap_boundary_snd, collapseBoundary_apply, Finsupp.single_neg]
  abel

/-- Exactness at `K₃ = H₁(G^{(2)}, R)` (`lem:s03-bip`(c), `s03-bip`). -/
theorem collapse_exact_ker :
    Function.Exact (LinearMap.ker (collapseBoundary G R)).subtype (collapseBoundary G R) :=
  LinearMap.exact_subtype_ker_map _

/-- Exactness at `C₁ = K₀` (`K₁ = 0`, so the cokernel of `K₁ → K₀` is `K₀`)
(`lem:s03-bip`(c), `s03-bip`). -/
theorem collapse_exact_coker :
    Function.Exact (0 : (⊥ : Submodule R (G.E →₀ R)) →ₗ[R] deg0Prod G R)
      (LinearMap.id : deg0Prod G R →ₗ[R] deg0Prod G R) := by
  intro z
  rw [LinearMap.id_apply]
  constructor
  · intro h
    refine ⟨0, ?_⟩
    rw [LinearMap.zero_apply, h]
  · rintro ⟨x, rfl⟩
    rw [LinearMap.zero_apply]

/-- The edge collapse (the identity of `R[E]`) is surjective (`lem:s03-bip`(c), `s03-bip`). -/
theorem collapseEdge_surjective :
    Function.Surjective (LinearMap.id : (G.E →₀ R) →ₗ[R] (G.E →₀ R)) :=
  fun y => ⟨y, LinearMap.id_apply y⟩

variable (G R)

/-- Every `y ∈ H₁(G^{(2)}, R)` has `∂_G y ∈ K₀` (`lem:s03-bip`(c), `s03-bip`). -/
theorem boundary_mem_deg0Prod_of_ker (y : LinearMap.ker (collapseBoundary G R)) :
    boundary G R (y : G.E →₀ R) ∈ deg0Prod G R := by
  have hy : (y : G.E →₀ R) ∈ deg0 G.E R := by
    rw [← ker_collapseBoundary]
    exact y.2
  exact boundary_mem_deg0Prod hy

/-- The connecting map `δ : H₁(G^{(2)}, R) = ker collapseBoundary → H₀(K) = K₀ = R[V₀]⁰ × R[V₁]⁰`
of the long exact homology sequence of `0 → K_• → C_•(G) → C_•(G^{(2)}) → 0`, built by the
snake-lemma recipe: lift `y` along the identity `C₁(G) → C₁(G^{(2)})` (the lift is `y`), apply
`∂_G`, and pull back along the injection `K₀ → C₀(G)` (`collapse_exact_bot`); `K₁ = 0`, so no
quotient is taken (`lem:s03-bip`(c)). -/
noncomputable def collapseDelta :
    LinearMap.ker (collapseBoundary G R) →ₗ[R] deg0Prod G R :=
  LinearMap.codRestrict (deg0Prod G R)
    ((boundary G R).domRestrict (LinearMap.ker (collapseBoundary G R)))
    fun c => boundary_mem_deg0Prod_of_ker G R c

/-- The map `H₁(G, R) → H₁(G^{(2)}, R)` induced by the collapse (the identity on chains)
(`lem:s03-bip`(c)). -/
noncomputable def H1toCollapse : H1 G R →ₗ[R] LinearMap.ker (collapseBoundary G R) :=
  Submodule.inclusion (bip_ker_le_deg0.trans_eq ker_collapseBoundary.symm)

variable {G R}

/-- `lem:s03-bip`(c) (`s03-bip`): the connecting map of the collapse `G → G^{(2)}` is
`∂|_{R[E]⁰}`: `δ y = ∂_G y` for `y ∈ H₁(G^{(2)}, R) = R[E]⁰` (any commutative ring, no
connectivity needed). -/
theorem bip_collapse_connecting (y : LinearMap.ker (collapseBoundary G R)) :
    ((collapseDelta G R y : deg0Prod G R) : (G.V0 →₀ R) × (G.V1 →₀ R)) =
      boundary G R (y : G.E →₀ R) := by
  rfl

/-- `lem:s03-bip`(c), snake-lemma characterisation (`s03-bip`): if `y' ∈ C₁(G)` lifts
`y ∈ H₁(G^{(2)}, R)` and `z ∈ K₀` maps to `∂_G y'` in `C₀(G)`, then `δ y = z`. -/
theorem bip_collapse_connecting_unique (y : LinearMap.ker (collapseBoundary G R))
    (y' : G.E →₀ R) (hy' : y' = (y : G.E →₀ R)) (z : deg0Prod G R)
    (hz : (deg0Prod G R).subtype z = boundary G R y') : collapseDelta G R y = z := by
  apply Subtype.ext
  rw [bip_collapse_connecting, ← hy', ← hz, Submodule.subtype_apply]

/-- `lem:s03-bip`(c), exactness at `H₁(G^{(2)}, R)` (`s03-bip`): `H₁(G, R) → H₁(G^{(2)}, R)
→ K₀` is exact, and the first map is injective (`H₁(K) = 0`). -/
theorem bip_collapse_exact :
    Function.Injective (H1toCollapse G R) ∧
      Function.Exact (H1toCollapse G R) (collapseDelta G R) := by
  refine ⟨Submodule.inclusion_injective _, ?_⟩
  intro y
  constructor
  · intro h
    have h' : boundary G R (y : G.E →₀ R) = 0 := by
      rw [← bip_collapse_connecting y, h, Submodule.coe_zero]
    exact ⟨⟨(y : G.E →₀ R), (mem_H1_iff _).mpr h'⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    rw [bip_collapse_connecting, Submodule.coe_zero]
    exact (mem_H1_iff _).mp x.2

/-- `lem:s03-bip`(c), surjectivity of `δ` (`s03-bip`): for connected `G`,
`δ : H₁(G^{(2)}, R) → K₀` is onto, so the long exact sequence is
`0 → H₁(G, R) → R[E]⁰ → R[V₀]⁰ × R[V₁]⁰ → 0`, the sequence of (a). -/
theorem bip_collapse_surjective [Finite G.V0] [Finite G.V1] (hc : G.Connected) :
    Function.Surjective (collapseDelta G R) := by
  intro z
  have hz : (z : (G.V0 →₀ R) × (G.V1 →₀ R)) ∈ (deg0 G.E R).map (boundary G R) := by
    rw [bip_surj_deg0 hc]
    exact z.2
  obtain ⟨y, hy, hyz⟩ := hz
  have hy' : y ∈ LinearMap.ker (collapseBoundary G R) := by
    rw [ker_collapseBoundary]
    exact hy
  refine ⟨⟨y, hy'⟩, ?_⟩
  apply Subtype.ext
  rw [bip_collapse_connecting]
  exact hyz

end Langlandscape.Graph
