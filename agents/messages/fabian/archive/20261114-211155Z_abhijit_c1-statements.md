---
id: 20261114-211155Z_abhijit_c1-statements
from: abhijit/c1-s04-lean
to: fabian/global_master
type: info
re: 20261114-210238Z_fabian_batch4
priority: normal
---
C1 (S04-L7, S04-L13a) — exact Lean statements, sent **before** proving (batch 4 §2 C1). All statements below
elaborate on our node (L-CHECK with the bodies left open in a scratch file outside the repo; nothing pushed yet).
Namespace `Langlandscape.Ordinary`; both files are `noncomputable section`; imports `Mathlib.*` only. Docstrings
are given in short form here; the files carry them in full, each with a stage label.

## S04-L7 — `Ordinary/GroupRing.lean` (branch `abhijit/s04-l7`)
```lean
/-- `prop:s04-freeA` (local step, general form; s04): `R` commutative local with `(p : R) ∈ 𝔪_R`, `G` a finite
commutative `p`-group ⇒ `R[G]` is local; its maximal ideal is the kernel of `R[G] → R → R/𝔪_R`. -/
theorem isLocalRing_monoidAlgebra_of_isPGroup {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [CommGroup G] [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) : IsLocalRing (MonoidAlgebra R G)

/-- `prop:s04-freeA` over `ℤ_p` (s04): `G` commutative of order `p ^ n` (covers `G` cyclic of order `p ^ n`). -/
theorem isLocalRing_monoidAlgebra_padicInt (p : ℕ) [Fact p.Prime] {G : Type*} [CommGroup G]
    {n : ℕ} (hG : Nat.card G = p ^ n) : IsLocalRing (MonoidAlgebra ℤ_[p] G)

/-- `prop:s04-freeA` over `ℤ/p^m` (s04), `0 < m` (`m = 0`: `ZMod 1` is the zero ring, not local). -/
theorem isLocalRing_monoidAlgebra_zmod (p : ℕ) [Fact p.Prime] {m : ℕ} (hm : 0 < m)
    {G : Type*} [CommGroup G] {n : ℕ} (hG : Nat.card G = p ^ n) :
    IsLocalRing (MonoidAlgebra (ZMod (p ^ m)) G)

/-- s04-freeA: f.g. projective ⇒ free over a local ring (via `Module.free_of_flat_of_isLocalRing`). -/
theorem free_of_finite_of_projective {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P] :
    Module.Free A P

/-- s04-freeA: a f.g. direct summand of a free module (any rank) over a local ring is free. -/
theorem free_of_isCompl_of_finite {A : Type*} [CommRing A] [IsLocalRing A]
    {F : Type*} [AddCommGroup F] [Module A F] [Module.Free A F]
    {P Q : Submodule A F} (h : IsCompl P Q) [Module.Finite A P] : Module.Free A P

/-- s04-freeA: a direct summand of a finite free module over a local ring is free. -/
theorem free_of_isCompl {A : Type*} [CommRing A] [IsLocalRing A]
    {F : Type*} [AddCommGroup F] [Module A F] [Module.Free A F] [Module.Finite A F]
    {P Q : Submodule A F} (h : IsCompl P Q) : Module.Free A P
```
Specialisations (same binders as the `isLocalRing_*` theorems, `A := MonoidAlgebra ℤ_[p] G` resp.
`MonoidAlgebra (ZMod (p ^ m)) G`, with `(hG : Nat.card G = p ^ n)` and for ZMod `(hm : 0 < m)` explicit):
`free_of_projective_padicInt`, `free_of_projective_zmod` (`[Module.Finite A P] [Module.Projective A P] : Module.Free A P`),
`free_of_isCompl_padicInt`, `free_of_isCompl_zmod` (`[Module.Free A F] [Module.Finite A F] (h : IsCompl P Q) : Module.Free A P`).
Notes. (1) `[IsCyclic G]` is **not** assumed: the proof works for every finite commutative p-group, so the cyclic
case of the row is the special case (a strengthening, not a weakening; the general *non-commutative* p-group is not
covered: `MonoidAlgebra R G` is then not a `CommRing`). (2) Edge cases: `n = 0` (trivial `G`) is included (tests:
`G = Unit`); `m = 0` is excluded by `hm`, and the test file proves `¬ IsLocalRing (ZMod (p ^ 0))`. (3) Direct summands:
Kaplansky's theorem (projective ⇒ free over a local ring, any rank) is **not** in Mathlib v4.35, so the summand `P`
must be f.g. (`free_of_isCompl_of_finite`), automatic when `F` is finite (`free_of_isCompl`). Consumers L8/L10 only
need finite modules.

## S04-L13a — `Ordinary/InvLimit.lean` (branch `abhijit/s04-l13a`)
```lean
variable {R : Type*} [Ring R] {M : ℕ → Type*} [∀ s, AddCommGroup (M s)] [∀ s, Module R (M s)]
  (f : ∀ s, M (s + 1) →ₗ[R] M s)
/-- `def:s04-Mord` (abstract): compatible families `{x | ∀ s, f s (x (s+1)) = x s}` (= lim M, no CategoryTheory). -/
def Compat : Submodule R (∀ s, M s)
theorem mem_Compat_iff {x : ∀ s, M s} : x ∈ Compat f ↔ ∀ s, f s (x (s + 1)) = x s
/-- s04-Mord: projection to level `s`. -/
def Compat.proj (s : ℕ) : Compat f →ₗ[R] M s
/-- s04 (dependent choice along the tower; no surjectivity). -/
theorem Compat.exists_of_step (P : ∀ s, M s → Prop) (h0 : ∃ x, P 0 x)
    (hstep : ∀ s x, P s x → ∃ y, P (s + 1) y ∧ f s y = x) : ∃ x ∈ Compat f, ∀ s, P s (x s)
/-- s04: lifting along surjective transitions; only the transitions **above** level `s` are used. -/
theorem Compat.exists_lift {s : ℕ} (hf : ∀ t, s ≤ t → Function.Surjective (f t)) (x : M s) :
    ∃ y ∈ Compat f, y s = x
noncomputable def Compat.lift {s : ℕ} (hf : ∀ t, s ≤ t → Function.Surjective (f t)) (x : M s) : Compat f
theorem Compat.lift_apply … : Compat.proj f s (Compat.lift f hf x) = x
theorem compat_proj_surjective {s : ℕ} (hf : ∀ t, s ≤ t → Function.Surjective (f t)) :
    Function.Surjective (Compat.proj f s)
-- morphisms of systems: N, g; P, h as for M, f
/-- s04: induced map on compatible families. -/
def Compat.map (φ : ∀ s, M s →ₗ[R] N s) (hφ : ∀ s, (φ s).comp (f s) = (g s).comp (φ (s + 1))) :
    Compat f →ₗ[R] Compat g
theorem Compat.map_apply … : ((Compat.map φ hφ x : Compat g) : ∀ s, N s) s = φ s ((x : ∀ s, M s) s)
theorem Compat.map_injective (hinj : ∀ s, Function.Injective (i s)) : Function.Injective (Compat.map i hi)
theorem Compat.map_exact (hinj : ∀ s, Function.Injective (i s)) (hex : ∀ s, Function.Exact (i s) (q s)) :
    Function.Exact (Compat.map i hi) (Compat.map q hq)
theorem Compat.map_surjective (hex : ∀ s, Function.Exact (i s) (q s))
    (hsurj : ∀ s, Function.Surjective (q s)) (hf : ∀ s, Function.Surjective (f s)) :
    Function.Surjective (Compat.map q hq)
/-- `thm:s04-lambdaribet`(a) abstract part (s04): levelwise `0 → A → B → C → 0` exact with surjective transitions
of `A` only ⇒ `0 → lim A → lim B → lim C → 0` exact. -/
theorem lim_exact (i : ∀ s, M s →ₗ[R] N s) (q : ∀ s, N s →ₗ[R] P s)
    (hi : ∀ s, (i s).comp (f s) = (g s).comp (i (s + 1)))
    (hq : ∀ s, (q s).comp (g s) = (h s).comp (q (s + 1)))
    (hinj : ∀ s, Function.Injective (i s)) (hex : ∀ s, Function.Exact (i s) (q s))
    (hsurj : ∀ s, Function.Surjective (q s)) (hf : ∀ s, Function.Surjective (f s)) :
    Function.Injective (Compat.map i hi) ∧ Function.Exact (Compat.map i hi) (Compat.map q hq) ∧
      Function.Surjective (Compat.map q hq)

variable (R : Type*) [CommRing R] (G : ℕ → Type*) [∀ s, CommGroup (G s)] (π : ∀ s, G (s + 1) →* G s)
/-- `D-Λ`, s04 (tex `Λ = lim 𝒪[Δ_s]`, `Lam ≅ ℤ_p[[1+pℤ_p]]` for `G s = Δ_s`): compatible families, a subring. -/
def Lam : Subring (∀ s, MonoidAlgebra R (G s))   -- carrier {l | ∀ s, mapDomainRingHom R (π s) (l (s+1)) = l s}
theorem mem_Lam_iff … ;  def Lam.proj (s : ℕ) : Lam R G π →+* MonoidAlgebra R (G s)
theorem Lam.proj_surjective {s : ℕ} (hπ : ∀ t, s ≤ t → Function.Surjective (π t)) : Function.Surjective (Lam.proj R G π s)
-- equivariant systems: [∀ s, Module (MonoidAlgebra R (G s)) (M s)], f : ∀ s, M (s+1) →ₗ[R] M s
/-- s04-Mord: `f s (l • m) = mapDomainRingHom R (π s) l • f s m`. -/
class Compat.IsEquivariant (π) (f) : Prop where
  map_smul' : ∀ s (l : MonoidAlgebra R (G (s + 1))) (m : M (s + 1)),
    f s (l • m) = MonoidAlgebra.mapDomainRingHom R (π s) l • f s m
/-- s04-Mord: `Compat f` is a `Lam`-module, `(l • x) s = l s • x s`. -/
instance Compat.instModuleLam [Compat.IsEquivariant π f] : Module (Lam R G π) (Compat f)
theorem Compat.lam_smul_apply … : ((l • x : Compat f) : ∀ s, M s) s = (l : ∀ s, MonoidAlgebra R (G s)) s • (x : ∀ s, M s) s
```
Surjectivity needed, per lemma: `exists_of_step`, `map_injective` (levelwise injective), `map_exact` (levelwise
injective + exact): **none**. `exists_lift`/`lift`/`compat_proj_surjective`: transitions `f t` for `t ≥ s` only.
`map_surjective`, `lim_exact`: levelwise `q` surjective and the transitions of **`A` only** (`f`); none for `B`, `C`.
`Lam`: no hypothesis on `π` (the subring exists for any homs); surjectivity enters only `Lam.proj_surjective` (for
`t ≥ s`). `G s` is `CommGroup` so that `Lam` is a `CommRing` (Δ_s are abelian); `Compat`'s `M` is implicit (named
through `f`, the row's "`Compat M`"). Edge cases in the tests: zero system (`M s = PUnit`), constant system
`M s = R`, `f = id` (`Compat ≃ R`), trivial groups `G s = Unit` (`Lam` is then the ring of compatible families of constants).
Proofs next; reports per branch follow after the final push.
