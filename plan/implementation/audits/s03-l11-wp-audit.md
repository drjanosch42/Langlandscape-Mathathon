<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit and the Langlandscape team -->
# Adversarial WP audit — S03-L11 (Ihara (iii) statement layer: `tau`, `epsilon`, `Hyp.IharaH0`)

- Auditor: adversarial Fable WP audit (OVERVIEW §5.3). Read-only; **no Lean build was run** (no `.olean` for these
  modules exists in the WP worktree, so LCHK remains the compile gate).
- Code: `lean/Langlandscape/Langlandscape/{Hyp/IharaH0.lean, Ribet/IharaH0.lean}`,
  `lean/Langlandscape/LanglandscapeTests/S03/IharaH0.lean` at commit `44bcd72` (worktree `Langlandscape-wt/s03-l11`),
  stacked on S03-L14 `53026f8`. L14's fix `dfd587b` (branch `impl/s03-l14`) was read for rebase compatibility.
- Spec: `stage-03.md` row S03-L11 and the `Hyp.IharaH0` row of §0.2.2; maths `thm:s03-iharaH0`(a), (C4)–(C6),
  `cor:s03-eis`, standing hypotheses of `ss:s03-ihara` (`mathematics/chapters/s03/4-ihara.tex`); `NOTES.md` (M7);
  `agents/rules/lean.md`; L14 audit m1/m2.
- Lean objects read to check the statement: `Tree.{HasFactorAt, IsQLevel, IsQAdmissible, BGConnected, alphaElt}`,
  `Quat.{IsInvariantAt, NrdSurj, localComponent, wx, XB, globalUnits}`, `Brandt.brandtModule`, `Ribet.CoeffData`,
  `GL2TF.Quat.normWeight` + `normWeight_transform`, `Hyp.SA` and the A18 note in `Tree/Admissible.lean`.

**Verdict: PASS WITH REMARKS** — 0 critical, 1 major (M1, additive), 8 minor.
The hypothesis is faithful to `thm:s03-iharaH0`(a); I found no counterexample and no unsatisfiable premise set.

---

## 1. Is `Hyp.IharaH0` faithful? Counterexample search

### 1.1 Premises against the tex, one by one

| tex (standing hyp. of `ss:s03-ihara` + thm (a)) | Lean premise | verdict |
|---|---|---|
| `p ≥ 5`, `p ≠ q`, `p ∤ D` | `5 ≤ p`, `p ≠ q`, argument `hp` | exact |
| `U` `q`-admissible | `Tree.IsQAdmissible` (`U ≤ Ô^×`, finite index, factor `GL₂(ℤ_q)` at `q`, `NrdSurj`) | exact up to A18 (m3) |
| `U = U_p × U^{(p)}` | `∃ K, HasFactorAt d p hp K U` | exact (see below) |
| (iii) of `prop:s02-BG` | `Tree.BGConnected d q hq U hU` | exact |
| `V` f.g. over `ℤ_p` | `Module.Finite ℤ_[p] V` | exact |
| `U_p`-action | `∀ u, u_p = 1 → ρ u = 1` | exact: for a group hom this is "`ρ` factors through the image of `U` in `GL₂(ℚ_p)`"; this is L14 audit m2, resolved as a premise |
| continuous | `∀ n, ∃ W` open, `U ∩ W` trivial on `V/p^n` | exact (`Aut(V/p^n)` is finite); mathematically redundant, see m4 |
| `−1 ∈ U ⇒ −1` acts trivially | `∀ u, ↑u = -1 → ρ u = 1` | exact; redundant, see m4 |

`HasFactorAt d p hp K U` allows any `K ≤ GL₂(ℚ_p)` and any `V` invariant at `p`. Together with `U ≤ Ô^×` nothing is lost
or gained: replace `V` by `V ∩ Ô^×` (still invariant) and `K` by `K ∩ GL₂(ℤ_p)`; a subgroup of
`Ô^× = GL₂(ℤ_p) × Ô^{(p)×}` containing the `p`-factor is a product. So the premise is the tex's `U = U_p × U^{(p)}`.

Conclusion: `EpsWellDefined ∧ Surjective ε ∧ ker ε = range alphaV`. This is clause (a) without the identification with
`H_0(Γ_U, V)`, as the registry row says. No premise is stronger than the tex's, so the hypothesis is not weaker than the
theorem; none is missing, so it is not stronger either.

### 1.2 Conventions that could have made the Prop false (all checked, all right)

- **`normWeight` direction.** `normWeight x = ∏_ℓ ℓ^{−v_ℓ(nrd x_ℓ)} = ‖Nrd x‖ = r^{−1}` for `Nrd x = r t`. Hence
  `tau x = det ι_p(x_p) · r^{−1} = t_p ∈ ℤ_p^×`, which is (C5). With the opposite convention `tau` would be `r² t_p`,
  clause 2 of `EpsWellDefined` would fail, and the hypothesis would be **false**. It is not.
- **Brandt convention.** `brandtModule`: `f(γxu) = ρ(u)^{−1} f(x)`. With `τ(γxu) = τ(x) det u_p` the summand
  `[τ(x)] f(x)` is class-invariant in `V_{U^1_p}`. Matches (a1).
- **Compatibility with L14's `alphaV`** (general `Quotient.out` representatives, factor `ρ(c.out)`):
  `[τ(x)] ρ(u) g(xu) = [τ(xu)] g(xu)`, and `[qτ(x)] ρ(u) g(xuα^{−1}) = [τ(xuα^{−1})] g(xuα^{−1})` because
  `Nrd α^{−1} = q^{−1}` at `q` gives `τ(xα^{−1}) = q τ(x)`. So (a2) goes through with the Lean maps; the factor `q` sits
  on the `f₁`-summand, as in the tex.
- **Weights.** `wx = |Γ_x| / |Γ_x ∩ {±1}|` (C2). For `U ≤ Ô^×` of finite index `|Γ_x|` divides 24, so `p ≥ 5` makes
  `(w_x : ℤ_p)` a unit, and `Ring.inverse` is the true inverse.
- **Coinvariants.** `U1p = ker(det ι_p(·_p))|_U`. Its image in `U_p` is `U_p ∩ SL₂`, and `ρ` factors through `U_p`, so
  `Coinv = V_{U^1_p}`. `U1p` is normal in `U` (a kernel), so `ρ(u)` descends.
- **`Γ_U`.** Stage 02 defines `Γ_U` with `Nrd = 1` (`s02/1-tree.tex:113`), so no central `q` acts on `V`; the cited
  `H_0(Γ_U,V) = V_{U^1_p}` is consistent. (Not part of the Lean statement anyway.)

### 1.3 Attempted counterexamples (by hand)

1. `V = ℤ_p`, `ρ = χ ∘ det(u_p)` for any character `χ : ℤ_p^× → ℤ_p^×`. `Coinv = ℤ_p`. Twisting `f ↦ χ(τ)·f` identifies
   `Brandt(U,V)` with `ℤ_p^{X_B(U)}`, turns `alphaV` into `(−tr₀, χ(q)^{−1} tr₁)` and `ε` into
   `Σ w^{−1}h₀ + χ(q) Σ w^{−1}h₁`. Rescaling the second coordinate by `χ(q)` gives the trivial-coefficient complex,
   whose cokernel is `ℤ_p` via the weighted sum when `BG(U,q)` is connected. Holds. (It holds even for discontinuous `χ`.)
2. `−1 ∈ U` acting as `−1`: both Brandt modules vanish and `2V ⊆ coinvKer`, so `Coinv = 0`; the statement is `0 → 0`.
   Holds without the `−1` premise.
3. `V = 0`, `V` torsion with trivial action, trivial `ρ` on `ℤ_p`: reduce to `H_0` of a connected graph. Hold.
4. Rank check, `U = Ô^×`, `V = Sym^{k−2}`, `k > 2`: the cokernel is torsion, consistent with
   `rk Brandt(U') ≥ 2 rk Brandt(U)`.

### 1.4 Vacuity

The premises are jointly satisfiable: `U = Ô^×`, trivial `ρ` (`hloc`, `hcont` with `W = ⊤`, `hneg` are trivial;
`IsQAdmissible` from `Hyp.RamNrdSurj`; factor at `p` is discharged in the test). So the hypothesis is not vacuous, and
since the conclusion is a theorem of the tex, it is not known to be inconsistent. No Lean instance with non-trivial `ρ`
is exhibited by this WP (m1).

## 2. Is `Ribet.epsilon` the tex ε? Junk values

`epsilonAt x (f₀,f₁) = Ring.inverse(w_x) • (mkQ(ρ(detSec τ(x)) f₀(x)) + mkQ(ρ(detSec(q τ(x))) f₁(x)))`, summed by `finsum`
over `X_B(U)` with representatives `Quotient.out`. This is the displayed formula of (a).

| fallback | when it fires | effect on `Hyp.IharaH0` |
|---|---|---|
| `Ring.inverse` of a non-unit `= 0` | never under the premises (`p ≥ 5`); excluded by `EpsWellDefined` clause 1 | none |
| `detSec t = 1` when no `u ∈ U` has `det u_p = t` | never under `NrdSurj` (take `u` with `Nrd u = (t at p, 1 elsewhere)`; factorisation is not even needed); excluded by clauses 2, 3 | none |
| `finsum` over infinite support `= 0` | never: `X_B(U)` is finite for `U` of finite index in `Ô^×` | would make "onto" false, not trivially true |

None of the fallbacks can make the hypothesis trivially true: each junk branch makes a conjunct of the *conclusion*
false. `detSec` is a `Classical.choose`; the value of `ε` does not depend on the choice (two choices differ by `U1p`),
and nothing in the statement depends on which one is taken.

## 3. `EpsWellDefined`

It is a conjunct of the **conclusion**, not a premise, so it cannot smuggle anything into the antecedent. Its four clauses
are exactly step (a1): units, existence of `u_{τ(x)}` and `u_{qτ(x)}`, class-independence of the summand. All four are
true under the premises (§1.2). It does not mention `alphaV` or the kernel. Policy remark: these clauses are elementary
and *proved outright* in the tex, yet they sit inside an unproved hypothesis (m5).

## 4. Exported shape

Usable as it stands for clause (a): consumers take `h : Hyp.IharaH0 d q hq U hU p hp V c` and the premises. Compatible
with S04-L15a (`heckeTV` on the same `brandtModule U R V ρ`). Rebase onto L14 `dfd587b` is name-compatible
(`CoeffData`, `CoeffData.triv`, `alphaV` unchanged; `CoeffData.ofLocal`, `CoeffData.triv_ρ` are new there).
Gaps: M1, m6, m7.

## 5. Docstrings and labels

Both theorems in `Ribet/IharaH0.lean` and the three test theorems have a preceding docstring with `s03-iharaH0`; every
public `def`/`abbrev` is documented; no `sorry`/`axiom`. Remarks: m2, m8.

---

## Findings

| id | sev | finding | required fix |
|---|---|---|---|
| **M1** | **major** (shape, additive) | (C6)'s operator `[t]` has no Lean object. `epsilonAt` inlines `mkQ ∘ ρ(detSec t)`; there is no endomorphism of `Coinv`. Clause (b) (`ε ∘ T_g = deg(UgU) · [ℓ^m] ∘ ε`, S04-L15a optional item), `cor:s03-eis` and the `ℤ_p[ℤ_p^×]`-structure of stage 04 all need `[t] : Coinv →ₗ Coinv`. Without it each consumer invents its own, and the exported shape forks. | In `Ribet/IharaH0.lean` add `coinvMap c p hp (u : U) : Coinv →ₗ[R] Coinv` (`Submodule.mapQ`, stability from normality of `U1p`: `ρ(u)(ρ(h)w − w) = ρ(uhu⁻¹)ρ(u)w − ρ(u)w`), `diamond c p hp (t : ℚ_[p]) := coinvMap (detSec … t)`, and the bridge `mkQ (ρ u v) = coinvMap u (mkQ v)`. Keep `epsilonAt`'s definition (no change to `Hyp.IharaH0`); optionally restate `epsilonAt_apply` through `diamond`. |
| m1 | minor | The shape test uses only `CoeffData.triv`, and passes `hloc`, `hcont`, `hneg`, `hadm` as hypotheses instead of discharging them ("no defeq of `triv`'s `ρ` with `1` is used"). So no test shows that the premises can be met, and the "`U_p`-action" premise is never exercised against a non-trivial `ρ`. L14 `dfd587b` now provides `CoeffData.triv_ρ` and `CoeffData.ofLocal`. | After rebasing on `dfd587b`: (i) discharge `hloc`, `hcont` (`W = ⊤`), `hneg` in the trivial test via `CoeffData.triv_ρ`, and take `hadm` from `isQAdmissible_Ohat hram`; (ii) add a test with `CoeffData.ofLocal … ρp` whose `hloc` is proved from `ofLocal_ρ_apply`. |
| m2 | minor (process) | Module docstring says "Registered in `HYPOTHESES.md`", but the commit touches no registry (correct: registries are the stage master's), and the modules are not in the root import files. | Stage master adds the §0.2.2 row to `HYPOTHESES.md` and the imports at the int2 merge; the row should say "not instantiable in stage 03; premises satisfiable at `Ô^×`, trivial `ρ`". |
| m3 | minor | A18: `IsQLevel` is "finite index in `Ô^×`", weaker than "compact open", so `Hyp.IharaH0` is formally stronger than the tex theorem for non-open `U`. `Hyp.SA` carries a faithfulness note (Nikolov–Segal); `Hyp.IharaH0` has none. I see no failure (the proof uses `U` only through `U^1`, finite indices, and `Hyp.SA`), but it is unrecorded. | Add a "Faithfulness (A18)" paragraph to the `Hyp/IharaH0.lean` header pointing to `Tree/Admissible.lean`, or add the premise `IsOpen (U : Set _)` (weakens the hypothesis; costs an openness lemma per level). The note is enough. |
| m4 | minor | Two premises are mathematically redundant. Continuity: `ρ` factors through a finite-index subgroup of `GL₂(ℤ_p)` and `Aut(V/p^n)` is finite, so the kernel has finite index, hence is open (Serre). `−1`: see §1.3(2). Both are harmless (they only weaken the hypothesis) and faithful to the tex. But `hcont` costs downstream: the only openness lemma in the tree is `Ohat_isOpen`; for `V_k` one needs openness of the principal congruence kernel at `p`. | Keep both (fidelity). Record the redundancy in the translation notes, and note for stage 04 that discharging `hcont` for `V_k` needs "`ker(Ô^× → GL₂(ℤ/p^n))` is open". |
| m5 | minor | `EpsWellDefined` and surjectivity are *proved outright* in the tex ((a1), (a3)); only `ker ε ⊆ im α` is cited. Putting all of (a) into the hypothesis enlarges the unproved surface. Acceptable for a statement-layer WP. | Docstring: say which conjuncts are elementary and which is the cited part. Follow-up (not this WP): prove clauses 2–4 of `EpsWellDefined` and reduce the hypothesis to `ker ε ≤ range alphaV`. |
| m6 | minor (shape) | `tau : B̂^× → ℚ_[p]` is a bare function. (C5)'s rules (`τ(γxu) = τ(x) det u_p`, `τ(xα) = q^{−1}τ(x)`, `τ(xg) = ℓ^{−m}τ(x)`) and `τ(x) ∈ ℤ_p^×` are not stated, though the docstring claims "`∈ ℤ_p^×`". Clause (b) needs them. | Add `tau_mul : tau (x*y) = tau x * tau y` (from `map_mul` and `normWeight_transform`), or define `tau` as a `MonoidHom` now (changing the type later is breaking; lemmas are not). Fix the docstring ("valued in `ℚ_[p]`; a unit of `ℤ_p`, not proved here"). |
| m7 | minor (shape) | No packaged consequence "`coker alphaV ≃ₗ Coinv`" and no `eis_support_of_IharaH0` (optional in the row; cannot be stated before `heckeTV`). | Optional: `Ribet.cokerEquivOfIharaH0` from the three conjuncts. Leave `cor:s03-eis` to stage 04 and say so in the header. |
| m8 | minor | Stale status: the `def` docstring and the registry row say "Source: tex sketch", the module header says "*proved modulo cited*" (which is the tex status `\stpmc`). The header also cites (C1)–(C6) where the row says (C4)–(C6) (harmless). | Align the `def` docstring and the §0.2.2 row with `\stpmc`. |

Compile risks (read, not built): `epsilon_apply` (`rw` with two `finsum_eq_sum_of_fintype` then `LinearMap.sum_apply`)
and `epsilonAt_apply := rfl` are plausible but unverified; `def coinvKer`/`def evalV` are not marked `noncomputable`
(L14's fix had to add it to neighbouring defs). If LCHK is red there, mark them `noncomputable`.

**Counts:** critical 0, major 1 (M1), minor 8 (m1–m8).
