# Audit: S04-L6 strand D, round 0

Scope checked: `strand-D.patch` against `brief.md`, `stage-excerpt.tex`, `check.txt`; API use against the stage-1
sources (`Local/GL2Levels.lean`, `Local/UpCosets.lean`) and the frozen Mathlib (all six imports exist; every stage-1
and Mathlib name used was located with a compatible signature). Lean was not run by the auditor.
`HL` = `lean/Langlandscape/Langlandscape/Local/HidaLocal.lean`, line numbers are file lines (patch line - 6).

## Defects

No critical and no major defects found.

- **A0.1** — minor — `HL:358-369` (`kppQuotEquiv`). The equivalence is a bare `Equiv` (`≃`), built by `.toEquiv` from
  a `MulEquiv`; the stage tex uses the group isomorphism `K'_s/K_{s+1} ≅ ker(Δ_{s+1} → Δ_s)` (torsor statement). The
  brief writes `≃`, so this is within the letter, but multiplicativity is only recoverable indirectly via
  `dModHom`/`ker_dModHom`/`range_dModHom`. Fix: add a `map_mul` companion lemma, or provide the `≃*` version (with the
  normality instance of `(K1 p (s+1)).subgroupOf (Kpp p s)`, which follows from `ker_dModHom`).
- **A0.2** — minor — `HL:372-375` (`kppQuotEquiv_mk`). Proved by `rfl` through `quotientEquivOfEq ∘
  quotientKerEquivRange ∘ subgroupCongr` and two coercions; this depends on the definitional unfolding of three Mathlib
  definitions and is brittle under any Mathlib change. Fix: prove it by `simp`/`rw` with the corresponding `_mk`/`_apply`
  lemmas, or state it via `dModHom_apply`.
- **A0.3** — minor — `HL:357` (docstring of `kppQuotEquiv`). The sentence "For `s ≥ 1` this kernel is also
  `ker((1 + pℤ_p)/(1 + p^{s+1}) → (1 + pℤ_p)/(1 + p^s))`" is an unproved mathematical claim that is neither
  formalized nor referenced. Fix: delete it or mark it as a remark with a reference.
- **A0.4** — minor — `HL:71-95` and `HL:236-267`. `exists_varpi_inv_mul_mem_Kpp` repeats the proof of stage-1
  `exists_varpi_inv_mul` almost verbatim instead of factoring a shared entry-level lemma; the general helpers `entZ`,
  `coe_entZ`, `entZ_mul` (with the proof `hgh` as an implicit `{…}` binder, `HL:250-253`),
  `toZModPow_eq_zero_iff_norm`, `toZModPow_eq_one_iff_norm` are not specific to Hida's lemma but live in this file under
  `s04-hida` labels. Fix: make `hgh` explicit (or drop it by taking the product membership from `mul_mem`), and note
  in the module docstring that these helpers are candidates for `GL2Levels.lean`.

## Non-defects noted (not counted)

- The extra explicit `(hs : 1 ≤ s)` on `Kpp_mul_varpi_mul_Kpp`, `exists_varpi_conj`, `relIndex_Kpp`, `kppQuotEquiv` is
  permitted by the brief, matches the stage tex (`s ≥ 1`) and is necessary (at `s = 0`: `K1 p 0 = GL2Zl p`,
  `Kpp p 0 = K0 p 1`, index `p + 1`, and (b) fails for the Weyl element).
- `instance fact_prime_five` in the test file is a global instance of a proved fact inside the test namespace, same
  pattern as existing `LanglandscapeTests/S04/ControlAbstract.lean`; not a hypothesis instance.
- Caveat on evidence: `check.txt` is headed "strand label D, round 0" but the embedded result block names ref
  `s04-l6-a-3` / "round 3". The auditor cannot confirm that the PASS refers to exactly this patch; the verdict below
  takes the check at face value (BUILD rc=0, CHECK_WP 0 FAIL, nonstandard axioms 0). A source-level read found no
  step that should fail.

## Mathematics check (summary)

- (a)/(b) core: `k ϖ = ϖ_j · !![a - jc, β; pc, d]` with `b = pβ + jd`; `p^s ∣ pc`, `p^{s+1} ∣ pc`, `p^s ∣ d - 1` — correct;
  agrees with the stage-tex proof (lower row `(pc, cj+d)` after absorbing `!![1,j;0,1]` into `u`).
- (b): `u ϖ_j = (u · unipUpper j) ϖ`, then the core lemma — correct.
- Index: representatives `!![1,0;p^s x,1]`, `x < p`; injectivity and surjectivity (needs `a` a unit, hence `s ≥ 1`) correct.
- Quotient: `d mod p^{s+1}` is multiplicative on `Kpp` since `c ≡ 0 mod p^{s+1}`; kernel `K1 p (s+1)`; image
  `ker(ZMod.unitsMap)` via `diag(1, t)` — correct.
- Tests are non-vacuous (`diag(1,6) ∈ Kpp 5 1 \ K1 5 2`, index instance, (a), (b), non-trivial image under the equivalence).

## Rubric

- correctness: **4** — every statement and proof step checks against the stage tex; no wrong or imprecise statement found.
- completeness: **2** — all five outputs plus the test file present; no `sorry`/`axiom`/`native_decide`; docstring rule and SPDX headers satisfied.
- interface fidelity: **2** — names, namespace, binders and statement shapes as in the brief; the only additions are the explicitly allowed `hs : 1 ≤ s` arguments; quotient form stated in the docstring as required.
- maintainability: **1** — readable and well documented, but `rfl` through composed equivalences, duplicated stage-1 proof, and general helpers parked in this file (A0.2, A0.4).

Q = 9

Counts: critical 0, major 0, minor 4.

VERDICT: PASS
W = 3*0 + 2*0 + 4 = 4
