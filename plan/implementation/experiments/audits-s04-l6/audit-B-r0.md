# Audit S04-L6, strand B, round 0

Scope checked: `strand-B.patch` (two new files, both inside the allowed paths), against `brief.md`,
`stage-excerpt.tex`, `check.txt` (BUILD rc=0, CHECK_WP 0 FAIL, axioms 4/4 standard), the stage-1 sources
`Local/GL2Levels.lean`, `Local/UpCosets.lean`, and the frozen Mathlib (all six Mathlib imports exist).
No `sorry`/`admit`/`axiom`/`native_decide`, no heartbeat options, SPDX headers present, every theorem/lemma has
a docstring carrying `s04-hida`. The matrix computations of (a) and (b) were re-derived by hand and agree with
the stage tex (lower row `(pc, cj+d)`, `i ≡ (aj+b)/(cj+d)`). The explicit `hs : 1 ≤ s` on `exists_varpi_conj`
and `relIndex_Kpp` is necessary (both fail at `s = 0`) and is permitted by the brief (§2).

No critical and no major defects found.

## Defects

Line numbers are patch line numbers (`strand-B.patch`); file = `Langlandscape/Local/HidaLocal.lean` unless noted.

- **A0.1** — minor — `strand-B.patch:342-345` (`KppQuotEquiv`).
  Problem: the equivalence is delivered as a bare `Equiv` (`.toEquiv` discards the structure), although it is
  built from the group homomorphism `kerHom` and the stage tex uses the group isomorphism
  `Kpp s / K1(s+1) ≅ ker(Δ_{s+1} → Δ_s)` (torsor statement in the proof of (c)). No `Normal` instance for
  `(K1 p (s+1)).subgroupOf (Kpp p s)` is provided, so a downstream user has to redo the construction to get `≃*`.
  The brief literally asks for `≃`, so this is not an interface deviation.
  Fix: add `instance`/lemma `Normal` (via `ker_kerHom ▸ MonoidHom.normal_ker`) and a `≃*` version
  (or at least a lemma `KppQuotEquiv hs (mk k) = kerHom p s k`); there is currently no computation lemma at all.

- **A0.2** — minor — `strand-B.patch:304, 342` (`kerHom_surjective`, `KppQuotEquiv`).
  Problem: the hypothesis `hs : 1 ≤ s` is superfluous for these two declarations (at `s = 0` the statement
  `Iw / K1 p 1 ≃ (ZMod p)ˣ = ker(Δ_1 → Δ_0)` holds; `d0` is a unit because its image `u` is a unit, not because
  `s ≥ 1`). The docstring does not say the hypothesis is only there to match the standing `s ≥ 1` of the tex.
  Fix: derive `IsUnit d0` from `u` being a unit and drop `hs`, or state in the docstring that `hs` is conventional.

- **A0.3** — minor — `strand-B.patch:338, 373` (docstrings of `KppQuotEquiv`, `relIndex_Kpp`).
  Problem: both are attributed to "`lem:s04-hida` (a)". In the stage tex the index `[K1 s : Kpp s] = p` is in
  the lemma's preamble and the quotient isomorphism is in the proof of (c); neither is part (a). The module
  docstring lists them without a part, which is correct; the declaration docstrings are misleading.
  Fix: cite "`lem:s04-hida`, preamble" resp. "proof of (c)".

- **A0.4** — minor — `strand-B.patch:195, 200, 205, 223, 266, 282`.
  Problem: generic public helper names in `Langlandscape.Local`: `toZModPow_eq_zero_iff`,
  `toZModPow_eq_one_iff` (pure `PadicInt` facts, not namespaced under `PadicInt` and not level-specific),
  `dEntry`, `dHom`, `kerHom`, `unitsRed`. Collision-prone for later work packages in the same namespace and
  uninformative out of context.
  Fix: make the helpers `private` or rename (`Kpp.dEntry`, `KppDHom`, `KppKerHom`, `PadicInt.toZModPow_eq_zero_iff`).

- **A0.5** — minor — `strand-B.patch:271-278, 287-295, 331-336`
  (`unitsRed_dHom`, `kerHom_eq_one_iff`, `kerHom_surjective`).
  Problem: the proofs rely on `change`/`exact` through the definitional unfolding of `MonoidHom.toHomUnits`,
  `MonoidHom.codRestrict` and `ZMod.unitsMap` (e.g. `exact h'` after two `congrArg`s, `change (ZMod.cast …) = …`).
  They build now but break on any change of these Mathlib definitions; no `@[simp]` unfolding lemma
  (`kerHom_apply_val`) is stated once and reused.
  Fix: state one lemma `((kerHom p s k : (ZMod _)ˣ) : ZMod _) = dHom p s k` (using `MonoidHom.coe_toHomUnits`)
  and rewrite with it.

- **A0.6** — minor — `strand-B.patch:426-448` (`LanglandscapeTests/S04/HidaLocal.lean`, the `…_five` tests).
  Problem: the `p = 5` examples take `[Fact (Nat.Prime 5)]` as an instance hypothesis that is never discharged,
  so the "instantiated at `p = 5`" tests are still conditional statements; the non-vacuity is not closed.
  Fix: discharge locally (`haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩` inside the statement/proof, no global
  instance) or state them as `example`s with the local instance.

## Rubric

- correctness: **4** — all statements and proof steps check; (a), (b) match the stage tex; build and axiom check pass; the `s ≥ 1` hypotheses are exactly where needed for the brief's statements.
- completeness: **2** — `Kpp`, `Kpp_mul_varpi_mul_Kpp`, `exists_varpi_conj`, `relIndex_Kpp`, the quotient equivalence and the requested tests are all present; no `sorry`.
- interface fidelity: **2** — names and statement shapes as in the brief; extra hypothesis is an explicit argument as prescribed; quotient form `subgroupOf` documented in the docstring.
- maintainability: **1** — readable and in the style of stage 1, but defeq-dependent `change` steps, generic public helper names, no API lemma for the equivalence, mislabelled docstrings (A0.1, A0.3–A0.5).

Q = 9

Counts: critical 0, major 0, minor 6.

W = 3*0 + 2*0 + 6 = 6

VERDICT: PASS
