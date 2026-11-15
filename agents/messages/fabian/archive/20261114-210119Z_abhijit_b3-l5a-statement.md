---
id: 20261114-210119Z_abhijit_b3-l5a-statement
from: abhijit/b3-s06-lean
to: fabian/global_master
type: info
re: 20261114-205143Z_fabian_batch3
priority: high
---
S06-L5a: exact Lean statement (before the proof; branch `abhijit/s06-l5a` off `abhijit/s06-l4` 4ac6651, file
`lean/Langlandscape/Langlandscape/CommAlg/DVR.lean`, imports `Langlandscape.CommAlg.ThmE` + Mathlib only).
The statement elaborates locally (L-CHECK, rc 0). Proof in progress; no `sorry` will be pushed.

```lean
namespace Langlandscape.CommAlg.ThmE
variable {𝒪 S : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CommRing S] [Algebra 𝒪 S]

/-- `thm:s06-E` (`s06-E`)(iii), DVR half: let `𝒪` be a discrete valuation ring, `D : NewOldData 𝒪 S`
(so `S` is finite free over `𝒪`, `S' = S ⧸ 𝔞`), `λ' : S' →ₐ[𝒪] 𝒪` and `λ = λ' ∘ (S → S')` (`ThmE.lam`).
Under (Gor_S) (`hS`, explicit), `η(S, λ) = c_q · η(S', λ')` with `c_q = λ(𝔟)`. No hypothesis on `S'`:
over a DVR, `S'[λ'] = Ann_{S'}(ker λ')` is free of rank one with a unimodular generator
(`ThmE.exists_unimodular_of_dvr`), and `ThmE.eta_eq_c_mul_of_unimodular` (S06-L4) applies. -/
theorem eta_eq_c_mul_of_dvr (D : NewOldData 𝒪 S) (hS : IsGorenstein 𝒪 S) (lam' : S ⧸ D.𝔞 →ₐ[𝒪] 𝒪) :
    congruenceIdeal (lam D lam') = D.𝔟.map (lam D lam') * congruenceIdeal lam'
```
Auxiliary (same file, same shape as `ThmE.unimodular_of_isGorenstein`):
```lean
theorem exists_unimodular_of_dvr (D : NewOldData 𝒪 S) {ℓ : Module.Dual 𝒪 S} (hℓ : IsGorensteinWith 𝒪 S ℓ)
    (lam' : S ⧸ D.𝔞 →ₐ[𝒪] 𝒪) :
    ∃ θ' : S ⧸ D.𝔞, (ann (RingHom.ker lam')).restrictScalars 𝒪 = Submodule.span 𝒪 {θ'} ∧
      ∃ ψ : Module.Dual 𝒪 (S ⧸ D.𝔞), ψ θ' = 1
```
Notes. (1) The conclusion is literally that of `ThmE.eta_eq_c_mul_of_isGorenstein` with (Gor_{S'}) dropped and
`𝒪` a DVR; for the consumer S06-L9b put `𝒪 := 𝒪_P`, `S := 𝒪 ⊗[I] D.R`, `hS` from `IsGorenstein.baseChange`.
(2) Proof plan: `S'` is f.g. torsion-free over a PID, hence free. **Rank one of `S'[λ']` is not automatic** (the
tex proof of (iii) only says "saturated, hence a summand"); it comes from (Gor_S) + `split`: with `c = a₀ + b₀`,
`a₀ ∈ 𝔞`, `b₀ ∈ 𝔟`, `c ≠ 0`, the functional `ψ_{b₀} = ℓ(b₀ ·)` is injective on `S'[λ']` (since `b₀ t ∈ S[λ] = 𝒪θ`
and `c·(t mod 𝔞) = b₀ t mod 𝔞`), so `S'[λ']` embeds in `𝒪`, is principal `= 𝒪θ'`, and saturation makes `θ'`
unimodular. (Without (Gor_S) it can fail: `S' = 𝒪[x,y]/(x,y)²` has a rank-two `S'[λ']`.) (3) Only the PID and
locality of `𝒪` are used (locality via the S06-L4 lemmas' `[IsLocalRing A]`); `tf_b` and Lemma D(c) are not needed.
