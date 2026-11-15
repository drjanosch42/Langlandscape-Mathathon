# Audit S04-L6, strand B, round 1 (delta audit)

Scope checked: `strand-B.patch` (two new files, both inside the allowed paths, no other file touched) against
`brief.md`, `stage-excerpt.tex`, `check.txt` (PASS: BUILD rc=0, CHECK_WP S04-L6 0 FAIL, AXIOMS 4/4 nonstandard=0),
`prior-findings.md`, the stage-1 sources `Local/GL2Levels.lean`, `Local/UpCosets.lean`, and the frozen Mathlib
(all six Mathlib imports exist; `ZMod.unitsMap_val`, `MonoidHom.coe_toHomUnits`, `PadicInt.cast_toZModPow` exist
with the shapes used). No `sorry`/`admit`/`axiom`/`native_decide`, no heartbeat option, SPDX headers present,
every theorem/lemma/def/instance (incl. `private` and tests) has a docstring carrying `s04-hida`.
Matrix identities of (a) and (b) re-derived by hand against `varpi = !![p, j; 0, 1]`, `varpiDiag = diag(p, 1)`:
(a) `ϖ_j · !![a - jc, β; pc, d] = k · ϖ`; (b) `ϖ_i · !![a - ic, β; pc, cj + d] = u · ϖ_j`, lower row
`(pc, cj+d)`, `i ≡ (aj+b)/(cj+d)` — as in the stage tex. `hs : 1 ≤ s` on `exists_varpi_conj` and `relIndex_Kpp`
is necessary (both false at `s = 0`) and explicit, as the brief permits.

## Prior findings

- **A0.1 — RESOLVED.** `instance normal_K1_succ_subgroupOf_Kpp` (via `ker_kerHom`, patch 381-386),
  `KppQuotMulEquiv : … ≃* …` (406-411) and computation lemmas `KppQuotEquiv_mk`, `KppQuotMulEquiv_mk` (400-417)
  added. The brief's `≃` form is kept.
- **A0.2 — RESOLVED** (by the second alternative of the required fix). `hs` is kept on `kerHom_surjective` /
  `KppQuotEquiv`, and both docstrings (322-324, 392-393) now state that it is the standing `s ≥ 1` of the tex.
- **A0.3 — RESOLVED.** `relIndex_Kpp` now cites "`lem:s04-hida`, preamble" (425), `KppQuotEquiv` and its
  companions cite "proof of (c)" (388, 400, 406, 413, 419). (A new slip in the module docstring: A1.1.)
- **A0.4 — RESOLVED.** `dEntry`, `dHom`, `unitsRed`, `kerHom` and their lemmas moved to namespace
  `Langlandscape.Local.Kpp`; the two `toZModPow_*` facts are `private` (203-211).
- **A0.5 — RESOLVED.** `Kpp.kerHom_apply_val` (300-302) and `Kpp.unitsRed_apply_val` (278-282) are stated once
  and used by `rw`; `unitsRed_dHom`, `kerHom_eq_one_iff`, `kerHom_surjective` no longer `change` through
  `toHomUnits`/`codRestrict`/`unitsMap`. The remaining definitional dependence is confined to the one-line
  `rfl` of `kerHom_apply_val`, the idiomatic place for it.
- **A0.6 — RESOLVED.** The `p = 5` tests are now unconditional: `Fact (Nat.Prime 5)` is proved
  (`s04_test_fact_prime_five`, 476-477) and made a `local instance` (479), no global instance.

No prior finding OPEN or REGRESSED.

## Defects (new diff)

Line numbers are patch line numbers (`strand-B.patch`); file = `Langlandscape/Local/HidaLocal.lean`.
No critical and no major defects found.

- **A1.1** — minor — `strand-B.patch:29-34` (module docstring).
  Problem: "This [the quotient `KppQuotEquiv`] and the index are in the preamble resp. the proof of (c)" pairs
  the items in the wrong order: the index `[K1 s : Kpp s] = p` is in the preamble, the quotient isomorphism in
  the proof of (c) (the declaration docstrings at 388 and 425 have it right).
  Fix: "The index is in the preamble, the quotient isomorphism in the proof of (c) of `lem:s04-hida`."

- **A1.2** — minor — `strand-B.patch:394-398, 408-411` (`KppQuotEquiv`, `KppQuotMulEquiv`).
  Problem: the same map is constructed twice by two parallel chains (`Subgroup.quotientEquivOfEq … .toEquiv`
  vs. `QuotientGroup.quotientMulEquivOfEq …`), and no lemma states that they agree
  (`(KppQuotMulEquiv hs).toEquiv = KppQuotEquiv hs` or `⇑(KppQuotMulEquiv hs) = ⇑(KppQuotEquiv hs)`); a user
  can relate them only pointwise through the two `_mk` lemmas after a quotient induction.
  Fix: define `KppQuotEquiv hs := (KppQuotMulEquiv hs).toEquiv` (statement shape unchanged), or add the
  coercion lemma.

- **A1.3** — minor — `strand-B.patch:287` (`Kpp.unitsRed_dHom`).
  Problem: `obtain ⟨a, b, c, d, hM, hu, hc, hd⟩` binds `hu`, `hc` which are never used (unused-variable linter
  noise); elsewhere the file correctly uses `-` for such components (e.g. 240-241, 266).
  Fix: `obtain ⟨a, b, c, d, hM, -, -, hd⟩`.

## Rubric

- correctness: **4** — all statements and proof steps check; (a), (b) agree with the stage tex; index and quotient statements are correct for `s ≥ 1`; build and axiom check pass.
- completeness: **2** — `Kpp`, `Kpp_mul_varpi_mul_Kpp`, `exists_varpi_conj`, `relIndex_Kpp`, the quotient equivalence (now also `≃*`, normality, `_mk` lemmas) and unconditional `p = 5` tests are present; no `sorry`.
- interface fidelity: **2** — names and statement shapes as in the brief; the extra `1 ≤ s` is an explicit argument; quotient form `subgroupOf` and the `Δ_s = (ZMod (p^s))ˣ` choice documented in the docstring.
- maintainability: **2** — helpers namespaced/private, API lemmas in place of `change` steps, labels on every declaration; only cosmetic residue (A1.1–A1.3).

Q = 10

Counts: critical 0, major 0, minor 3.

W = 3*0 + 2*0 + 3 = 3

VERDICT: PASS
