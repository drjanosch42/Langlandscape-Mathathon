<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Lean audit: discharge of `Hyp.RamNrdSurj` (scratch files, commit 35b31cc9)

- Date: 2026-11-15. Auditor: independent Lean audit (Fable), read-only, **no build** (no Lean on this node).
- Target: commit `35b31cc9` on `origin/abhijit/ramnrdsurj-discharge` (parent = merge-base with main = `4be17e33`).
  The commit adds only `lean/Langlandscape/Scratch{A,B,C,Main}.lean` (1273 lines); no library source is touched.
- Main statement: `ramNrdSurj_proved (d : DefiniteData) : RamNrdSurj d` (`ScratchMain.lean:636`).
- Hypothesis: `Langlandscape.Hyp.RamNrdSurj` (`lean/Langlandscape/Langlandscape/Hyp/RamNrdSurj.lean:35`).
- Mathematical reference: `mathematics/chapters/s01/1-classsets.tex`, `lem:s01-nrd` (the `ℓ ∣ D` part).
- Method: `git show` of the four files, textual diff of ScratchMain against ScratchA–C, grep of every library and
  Mathlib name against the sources (frozen Mathlib `/home/janosch/data/mathlib4_v4350`, toolchain core sources
  v4.35.0, the GL2TF import), reading of the whole proof, an independent Python check of the finite mod-8 statement.

## Verdict: PASS WITH REMARKS

The statement is exactly the registered hypothesis, the file contains no escape hatch, and the mathematics is
correct. I found no step that looks wrong. **Not verified by me: that the file compiles.** The build and the
`#print axioms` output are taken from the commit message (another node, a working copy `Langlandscape_copy`, direct
`lake env lean`). An acceptance build through `tools/lfile.sh` on TITAN/CONCEPTD against main is still required
(finding B1). Nothing here is fit for main as it stands (scratch files; findings B2, N1–N8).

## 1. Build (role item 1)

Not run. Reported in the commit message: `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false
../../ScratchMain.lean`, exit 0; `#print axioms ramNrdSurj_proved` = `[propext, Classical.choice, Quot.sound]`.
Warnings were not reported; expected ones are listed in N5.

## 2. Soundness (question (b))

Grep over all four files for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `opaque`,
`extern`, `set_option`, `macro`, `syntax`, `notation`, `elab`, `instance`, `attribute`, `universe`, `variable`,
`local`, `def`, `abbrev`, `structure`:

- none of them occurs, except `set_option autoImplicit false` (line 4 of ScratchMain, line 3 of A–C; harmless and
  already a project-wide `leanOption`) and `#print axioms` (last line of each file);
- the files contain **only `theorem` declarations** (15 in ScratchMain), no definitions, no instances, no notation,
  no `variable`;
- one `decide` (`zmod8_cover`, `ScratchMain.lean:415`), a kernel `decide`, not `native_decide`;
- no unusual Unicode (character census of ScratchMain: only standard mathematical symbols and Greek letters).

## 3. Faithfulness (question (a))

**The theorem proves exactly `Langlandscape.Hyp.RamNrdSurj d` for every `d : Langlandscape.Quat.DefiniteData`.**

- Statement (`ScratchMain.lean:636`): `theorem ramNrdSurj_proved (d : DefiniteData) : RamNrdSurj d`, in the root
  namespace, after `open Langlandscape.Quat Langlandscape.Hyp` (line 631). No `variable`, no instance argument, no
  extra hypothesis, no universe parameter.
- The type is the constant applied to `d`, not a restatement, so only two names have to resolve correctly:
  - `RamNrdSurj`: the only declaration of this name in our project, the import and Mathlib is
    `Langlandscape.Hyp.RamNrdSurj` (`Hyp/RamNrdSurj.lean:35`). The scratch files declare no `RamNrdSurj`.
  - `DefiniteData`: only `Langlandscape.Quat.DefiniteData` (`Quat/Basic.lean:56`).
- ScratchMain imports only `Langlandscape.Hyp.RamNrdSurj` and `AlgJL.VolIII.P2.LocalStructure` (not ScratchA–C), so
  no other file can inject declarations.
- Namespaces: `ScratchA` (6–64), `ScratchBFile` (66–403) containing `ScratchB` (76–401), `ScratchCFile` (405–627).
  The `open`s inside them end with the namespaces. None of the declared names
  (`ramNrdSurj_of_core`, `norm_lt_one_of_toZMod_eq_zero`, `isUnit_of_toZMod_ne_zero`, `two_isUnit`,
  `exists_sq_sub_mul_sq_zmod`, `bin_odd`, `aux_plane`, `exists_nrd_eq_odd`, `zmod8_cover`, `zmod8_ne_zero_four`,
  `div_sq_eq`, `exists_nrd_eq_two`, `ramNrdSurj_proved`) shadows a library name.
- The intermediate statement `ScratchA.ramNrdSurj_of_core` (line 14) also concludes with the constant `RamNrdSurj d`;
  its hypothesis `hcore` is the hypothesis without the `localEmbed … ∈ d.Ohat` clause, written with the same names
  (`QuatAlg` = `Langlandscape.Quat.QuatAlg`, an `abbrev` of `GL2TF.Quat.QuatAlg`; `GL2TF.Quat.nrd` fully qualified).
- Library names used and where they resolve (all unmodified library declarations, none redefined):
  `localEmbed` (`Quat/LocalEmbed.lean:98`), `localEmbed_mem_orderCompletionUnits_iff` (`Quat/LocalEmbed.lean:169`),
  `DefiniteData.Ohat` (`Quat/Basic.lean:88`), `DefiniteData.ha/hb/hD` (`Quat/Basic.lean:74,77,66`),
  `GL2TF.Quat.nrd` (`AlgJL/Common/QuaternionNorm.lean:41`), `GL2TF.Quat.isUnit_iff_isUnit_nrd` (`:87`),
  `GL2TF.Quat.localLattice` (`AlgJL/VolIII/P2/LocalStructure.lean:37`), `GL2TF.Quat.division_maximalOrder`
  (`:1090`), `GL2TF.Quat.hilbertSymbol` (`AlgJL/Common/QuaternionHilbert.lean:37`), `GL2TF.Quat.RamifiedExactly`
  (`AlgJL/VolIII/P2/Ramification.lean:23`).

**The concatenation.** ScratchMain is a verbatim concatenation:

| ScratchMain lines | source | diff |
|---|---|---|
| 11–62 | `ScratchA.lean` 7–58 | identical |
| 71–401 | `ScratchB.lean` 7–337 | identical |
| 410–626 | `ScratchC.lean` 7–223 | identical |
| 629–651 | new: `open`, `ramNrdSurj_proved`, `#print axioms` | — |

The only changes are the wrapping namespaces and the merged import/`set_option` header.

**Modified copies of library declarations in ScratchMain: none.** ScratchMain contains no copy of any declaration
of `lean/Langlandscape/Langlandscape/**` or of the import. The duplication is of two other kinds:

1. ScratchA–C are duplicated wholesale inside ScratchMain (table above); three of the four files are redundant.
2. Re-proofs of facts the library already has (to be replaced by the library versions on integration):
   - `ScratchMain.lean:30–31` (`hone`, inline `have`) re-proves `nrd 1 = 1`: library
     `Langlandscape/Brandt/RightTranslate.lean:306` (`nrd_one_local`), import private
     `AlgJL/Common/QuaternionNorm.lean:61`.
   - `ScratchMain.lean:32–36` (`hnrd_mul`, inline `have`) re-proves multiplicativity of `nrd`: import
     `AlgJL/Common/QuaternionNorm.lean:67` (`nrd_trd_basic`, component `.2.1`; private `nrd_mul'` at `:57`), library
     `Langlandscape/Brandt/RightTranslate.lean:302` (`nrd_mul_local`).
   - `ScratchMain.lean:80` (`norm_lt_one_of_toZMod_eq_zero`) overlaps the import's private
     `toZMod_eq_zero_iff` (`AlgJL/Common/QuaternionHilbert.lean:388`); private there, so not reusable.
   - The Hensel square-root steps (`ScratchMain.lean:238–264`, `268–294`, `574–596`) overlap the import's private
     `padic_sq_of_hensel` (`QuaternionHilbert.lean:233`); private there, so not reusable.

## 4. Mathematics and proof structure (question (c))

The argument is correct. It proves more than needed: for every prime `ℓ` and all nonzero `a, b`, every unit of `ℤ_ℓ`
is a reduced norm from `B_ℓ` (true for every quaternion algebra over `ℚ_ℓ`); ramification enters only in step A.

**A. Reduction (`ramNrdSurj_of_core`, 14–62).** For `ℓ ∣ D`, `division_maximalOrder d.hD ℓ hℓD` (third component,
applied to `d.O`) gives `localLattice ℓ 𝒪 = {y | nrd y ∈ ℤ_ℓ}`. If `nrd x = w ∈ ℤ_ℓ^×` then
`nrd x⁻¹ = w⁻¹ ∈ ℤ_ℓ`, so `x, x⁻¹ ∈ 𝒪_ℓ`, and `localEmbed_mem_orderCompletionUnits_iff d.O.1 x` gives
`localEmbed ℓ x ∈ Ô^×` (`d.Ohat` is an `abbrev` for `orderCompletionUnits d.O.1`). The types match the library
statements literally.

**B. Odd `p` (`exists_nrd_eq_odd`, 357–399).** Among `-a, -b, ab` one has even `p`-adic valuation (if `v(a)`, `v(b)`
are both odd, `v(ab)` is even). On the corresponding plane `nrd = X² + dY²` with `d = p^{2m} d₀`, `d₀` a unit
(`aux_plane`, 300–354). `bin_odd` (210–294): `x² − c y² = w` is solvable in `ℤ_p` for units `c, w`: mod `p` by the
counting argument (`exists_sq_sub_mul_sq_zmod`, 114–205: `(p+1)/2` squares, the sets `S` and `w + cS` meet), with
`(α, β) ≠ (0,0)` because `w ≠ 0`; then Hensel in `x` if `α ≠ 0` (derivative `2α̃`, a unit) or in `y` if `α = 0`
(derivative `2cβ̃`, a unit). Rescaling `Y = y / p^m` gives the norm. Correct.

**C. `p = 2` (`exists_nrd_eq_two`, 457–626).** Write `a = 2^{2e_I} A`, `b = 2^{2e_J} B`, `ab = 2^{2e_K} D` with
`A, B, D` each an odd number or twice an odd number, hence not `0` or `4` mod 8 (`zmod8_ne_zero_four`). The finite
statement `zmod8_cover` (412–415): for `A, B, D ∉ {0, 4}` and `W` a unit mod 8 there are `x₁, x₂, x₃` with
`1 − A x₁² − B x₂² + D x₃² = W`. **I checked this independently by brute force (Python): true for all 864
admissible `(A, B, D, W)`**; note that it does not use `D = AB`. Then `F = X² − c` with
`c = A x₁² + B x₂² − D x₃² + w` has `F(1) ≡ 0 mod 8`, so `‖F(1)‖ ≤ 2⁻³ < 2⁻² = ‖F'(1)‖²`, and Hensel gives
`z² = c`. The quaternion `(z, x₁/2^{e_I}, x₂/2^{e_J}, x₃/2^{e_K})` has norm `w`. Correct. The hypothesis `hdiv`
(Hilbert symbol `= −1`) is unused.

**D. Combination (636–649).** `d.ha`, `d.hb` give `a, b ≠ 0`; case split on `ℓ = 2`; the element is a unit by
`isUnit_iff_isUnit_nrd` because its norm is a unit of `ℚ_ℓ`. Correct.

**Name check.** Every lemma name used was looked up in the sources. All exist with a signature compatible with the
use, among them: `hensels_lemma` (`Mathlib/NumberTheory/Padics/Hensel.lean:460`), `PadicInt.mem_subring_iff`,
`PadicInt.Coe.ringHom`, `PadicInt.isUnit_iff`, `PadicInt.norm_units`, `PadicInt.norm_lt_one_iff_dvd`,
`PadicInt.ker_toZMod`, `PadicInt.maximalIdeal_eq_span_p`, `PadicInt.toZModPow`, `PadicInt.ker_toZModPow`,
`PadicInt.norm_le_pow_iff_mem_span_pow`, `PadicInt.norm_p`, `PadicInt.coe_add/coe_mul/coe_pow/coe_intCast`,
`padicValInt_dvd`, `padicValInt_dvd_iff`, `padicValInt_dvd_iff_of_ne_one`, `padicValInt.mul`,
`ZMod.intCast_zmod_eq_zero_iff_dvd`, `ZMod.natCast_eq_zero_iff`, `ZMod.natCast_zmod_val`, `ZMod.ringChar_zmod_n`,
`ZMod.card`, `Ring.eq_self_iff_eq_zero_of_char_ne_two`, `sq_eq_sq_iff_eq_or_eq_neg`,
`Finset.card_eq_sum_card_image`, `Finset.card_pair` (alias, `Finset/Card.lean:143`), `Finset.card_union_of_disjoint`
(alias, `:595`), `Finset.notMem_erase`, `Finset.eq_empty_iff_forall_notMem`, `Polynomial.derivative_C_mul_X_sq`,
`Units.val_neg`, `Int.prime_two`, `Int.mul_ediv_cancel'`, `Int.mul_dvd_mul_iff_left`, `ite_eq_left` / `ite_eq_right`
(core `Init/Core.lean:1179,1188`; these names exist only in recent toolchains, which fits a file written against
v4.35.0). **No missing name found.**

**Spots I could not settle without a build** (none looks wrong; listed so the acceptance build is read with them in
mind):

- `zmod8_cover` by `decide` (415): kernel evaluation over `(ZMod 8)^4 × (ZMod 8)^3` including the instance
  `Decidable (IsUnit W)` (through `Fintype (ZMod 8)ˣ`). Mathematically true; may be slow or sensitive to
  `maxRecDepth`. Record the elaboration time of this declaration.
- `hEq'` (559–560) and the application of `zmod8_cover` to `PadicInt.toZModPow 3 …` rely on `ZMod (2^3)` and
  `ZMod 8` being definitionally equal (they are; unification has to see it).
- Line 644: `(d.hD.2.2.2 2).mpr hℓ` after `subst h2`: the `Fact (Nat.Prime 2)` instance is the local one, the
  statement of `exists_nrd_eq_two` uses the global one; proof-irrelevant, fine.
- Terminal `simp`/`push_cast`/`linear_combination` calls (e.g. 31, 35, 228, 242, 273, 363, 586, 623–626) cannot
  be checked by reading.

## 5. Replacing the hypothesis at the consumers (question (d))

Yes. Every consumer takes the hypothesis as an explicit argument `(hram : Hyp.RamNrdSurj d)` for an arbitrary `d`:
`Quat.exists_Ohat_nrd_eq`, `nrdSurj_Ohat`, `nrdSurj_U0`, `nrdSurj_U1`, `nrdSurj_Utower`
(`Quat/LevelNrd.lean:149,217,222,231,240`), `Tree.isQAdmissible_Ohat/U0/U1/Utower`
(`Tree/Admissible.lean:143,148,154,160`), and the tests (`LanglandscapeTests/S02/LevelNrd.lean:27,31`,
`S02/Admissible.lean:55,62`, `S03/IharaH0.lean:53,65,77`). Since the theorem has no hypothesis beyond `d`, the term
`ramNrdSurj_proved d` can be supplied at each call site with the signatures unchanged.

- No import cycle: the proof needs only `Hyp/RamNrdSurj.lean` and `AlgJL.VolIII.P2.LocalStructure`; it does not
  depend on `Quat/LevelNrd.lean` or `Tree/Admissible.lean`.
- Two ways: (i) keep the signatures and add `_uncond` twins in a file importing the consumers and the new module
  (the pattern used for `Hyp.PadicOrdDecomp`, `Ordinary/TowerUncond.lean`); (ii) drop the argument, which changes
  signatures and every downstream call. (i) is what "signatures unchanged" asks for.
- Registry updates (stage master only): `HYPOTHESES.md` row `Langlandscape.Hyp.RamNrdSurj d` to *discharged*, the
  status lines in `Hyp/RamNrdSurj.lean`, `Quat/LevelNrd.lean:26`, `Tree/Admissible.lean:48–59`, and an entry for the
  new theorem in `Audit/PrintAxioms.lean` (the hypothesis is at line 173).

## 6. Findings

### Blocking (before the hypothesis counts as discharged on main)

- **B1. No acceptance build.** The only build evidence is the commit message: another node, a copy of the tree,
  direct `lake env lean`. That is outside the wrappers (`agents/rules/lean.md`: never call `lake` directly) and it
  is not shown that the copy's library equals main `4be17e33`. Required: build of the integrated module through
  `tools/lfile.sh` / `tools/lbuild.sh` on TITAN/CONCEPTD, with `#print axioms` of the main theorem and the full
  warning list.
- **B2. The scratch files must not be merged as they are.** They sit in `lean/Langlandscape/` outside every
  `lean_lib` root, so no library build checks them, and they violate the file rules (N1–N4). ScratchA–C are
  redundant with ScratchMain.

### Non-blocking (integration work)

- **N1. Placement and names.** One library module, e.g. `Langlandscape/Quat/RamNrdSurj.lean`, namespace
  `Langlandscape.Quat`; drop the namespaces `ScratchA`, `ScratchBFile`, `ScratchB`, `ScratchCFile`; rename
  `ramNrdSurj_proved` (root namespace now) to e.g. `Langlandscape.Quat.ramNrdSurj`. The general statements
  (`exists_nrd_eq_odd`, `exists_nrd_eq_two`) are about `GL2TF.Quat.nrd` over `ℚ_p` and are reusable. "One topic
  per file" may suggest splitting the local norm surjectivity from the reduction.
- **N2. Header.** The five-line copyright header is missing in all four files.
- **N3. Docstring rule.** No docstring carries a label `s<NN>-…` (here `s01-nrd`); `exists_nrd_eq_two` (457) has no
  docstring at all; the main theorem's docstring does not reference `lem:s01-nrd`.
- **N4. Imports.** Only two imports; `hensels_lemma`, `PadicInt.toZModPow`, the `ZMod` and `Finset` lemmas and the
  tactics arrive transitively (through `AlgJL.Common.QuaternionHilbert` etc.). The merge gate asks for minimised
  and explicit imports: add the needed `Mathlib.*` imports explicitly (at least
  `Mathlib.NumberTheory.Padics.Hensel`, `Mathlib.NumberTheory.Padics.RingHoms`), then minimise by a root build.
  `AlgJL.VolIII.P2.LocalStructure` is needed for `division_maximalOrder`.
- **N5. Expected warnings.** `set_option autoImplicit false` is redundant with the lakefile (drop). Unused argument
  `hdiv` in `exists_nrd_eq_two` (458): drop it and the term `((d.hD.2.2.2 2).mpr hℓ)` at 644. Deprecated in this
  toolchain: `if_pos` / `if_neg` (128, 135, 161, 164; use `ite_eq_left` / `ite_eq_right`), `push_neg` (179, 199;
  Mathlib prints "`push_neg` has been deprecated", use `push Not`). Non-terminal `simp` (35, 586
  `simp [hFdef] <;> norm_num`). `#print axioms` at the end (move to `Audit/PrintAxioms.lean`). Unneeded
  `classical` in several proofs.
- **N6. Duplicated material.** Replace the inline `hone` / `hnrd_mul` (30–36) by the library lemmas (section 3,
  item 2). The two branches `ℓ = 2` / `ℓ ≠ 2` of the main theorem end with the same three lines (645–646,
  648–649): factor out "an element whose norm is a unit of `ℤ_ℓ` is a unit of `B_ℓ`".
- **N7. `decide` cost.** See section 4; if `zmod8_cover` is slow, state it with `W % 2 = 1`-style conditions or
  split by cases. Not a soundness matter.
- **N8. The statement proved is stronger than registered.** `exists_nrd_eq_odd` / `exists_nrd_eq_two` hold at every
  prime, ramified or not. Worth saying in the module docstring and in `lem:s01-nrd`; status of the lemma's
  `ℓ ∣ D` ingredient becomes *formalized* once B1 is done.
- **N9. Commit message.** The `#print axioms` lines are duplicated (cosmetic).

## 7. Summary table

| Question | Answer |
|---|---|
| (a) exactly `Hyp.RamNrdSurj d`, no redefinition / shadowing | yes; only theorems are declared, names resolve uniquely to the library |
| (b) no `sorry`/axiom/`native_decide`/… | yes (grep); one kernel `decide` |
| (c) mathematics and structure | correct; all lemma names exist; compile status not verified here |
| (d) usable at the consumers with unchanged signatures | yes, supply `ramNrdSurj_proved d` (or `_uncond` twins) |
