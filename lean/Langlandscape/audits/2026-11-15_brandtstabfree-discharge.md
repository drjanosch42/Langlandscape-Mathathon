# Audit: discharge of `Hyp.BrandtStabFree` (static, read-only) — 2026-11-15

Worktree `/home/janosch/dev/Langlandscape-wt/bsf`, branch `impl/brandtstab-discharge`, HEAD c70ef3a9
(commits ee379dca, c70ef3a9 over 7c6b2ebe). Nothing was built or run; all findings are from reading the source.
Paths below are relative to `lean/Langlandscape/`.

## Verdict: PASS (static), conditional on the TITAN build and its `#print axioms` output

No critical or major finding. Kernel acceptance and the axiom list can only be confirmed by the build.

## 1. Statement and assembly
- `Langlandscape/Hyp/BrandtStabFreeDischarge.lean:48` — `brandtStabFree_holds (d : DefiniteData) (ℓ : ℕ) : BrandtStabFree d ℓ`,
  in namespace `Langlandscape.Hyp`, importing the unchanged definition (`Hyp/BrandtStabFree.lean:44`; the diff to that
  file is a module-docstring status line only). No weakening.
- No redefinition or shadowing of `BrandtStabFree`, `wx`, `XB`, `brandtMatrix`, `Gam`, `pmOne`, `normNSet`, `Ohat`,
  `classOf`, `globalUnits`, `GL2Zl`, `localComponent` in the new namespaces. New definitions are only: `uOf`, `nbrSet`,
  `nbrSmul`, `nbrAction` (Orbit); `Zgam`, `Zgam.toB` (twice: Principal and LocalPi); `intMat`, `redMat`, `redVec`,
  `toZModMatAlgHom`, `conjUnit`, `zgamEval` (LocalPi); private `pb`, `bas`, `rt`, `crd0`, `crd1`, `N`, `conj` (Principal).
  None of them occurs in the headline statement. No `notation`, `macro`, `syntax`, `elab`, no instances, no attributes
  other than one `@[simp]` (`LocalPi.lean:627`). `nbrAction` is used through a local `letI`, not as a global instance.
- Hypothesis discharge in the assembly (`BrandtStabFreeDischarge.lean:49-56`):
  `core` of `Orbit.brandtStabFree_of_core` (Orbit.lean:178) <- `Core.stabFree_core` (Core.lean:154);
  its `hlocal` <- `LocalPi.local_pi` (LocalPi.lean:715); its `hprin` <- `Principal.principality d.ha d.hb`
  (Principal.lean:635). `principality` has no remaining hypothesis beyond `a < 0`, `b < 0` (theorems `d.ha`, `d.hb`,
  from the structure field `hD : RamifiedExactly`, `Quat/Basic.lean:72-75`). Nothing remains assumed.
  The binder shapes of `core`/`hlocal`/`hprin` agree with the conclusions of the theorems supplied (argument order
  `hpm`/`hγxy` is permuted by the explicit lambdas in the assembly).

## 2. Vacuity
- `Orbit.nbrSet` (Orbit.lean:67) is verbatim the subtype in the import's `brandtMatrix`
  (`trace-formula-project-import/lean/AlgJL/VolIII/Brandt/Brandt.lean:623-625`); `card_nbrSet` (Orbit.lean:74) is
  `brandtMatrix d.O.1 ℓ c c' = Nat.card (nbrSet d ℓ c c')` by `rfl`. The tie to the import's entry is definitional and
  genuine (the kernel will reject it if not).
- The action is the real one: `γ • q = [x⁻¹ ι(γ) x · out q]`, with `one_smul`/`mul_smul` proved. Stabiliser = `Γ_x ∩ {±1}`
  is proved in both directions (Orbit.lean:211-269); orbit size = `Nat.card Γ_x / Nat.card (Γ_x ⊓ pmOne)` = `wx` by
  Lagrange with finiteness of `Γ_x` from the import (`stabilizer_units`, `unitGroup_eq_nrd_one_finite`), so the natural
  division in `wx` is exact and not exploited. Finiteness of `nbrSet` is from `normNSet_basic`.
- The only `exfalso` (Orbit.lean:235) is the mathematically intended contradiction with `c ≠ c'`; the `absurd`s in
  `LocalPi.step_i` (LocalPi.lean:106-107) are the `γ = ±1` cases. No unreachable premise, no hypothesis of the form
  `False`, no theorem whose premises are contradictory by construction. `local_pi` produces an actual witness
  (`t`, `p`, `π = p(γ)` as a unit with explicit inverse `star π / ℓ`).

## 3. ℓ prime, ℓ ∤ D, D prime
- `ℓ.Prime` is turned into `Fact ℓ.Prime` (Discharge:50) and used in Orbit (`hℓ.pos`), Core, LocalPi.
- `¬ ℓ ∣ d.D` is used only through `localComponent d ℓ hℓD` / `d.iota ℓ hℓD` / `mem_localLattice_iff_iota`
  (Core.lean:160-183, LocalPi.lean:180-256, 715ff). Places `q ≠ ℓ` are treated uniformly via `localLattice` (no splitting
  needed there), Core.lean:194-332. Correct.
- `d.D.Prime` is unused: bound as `_hD` (Orbit.lean:184) and passed through unused (Discharge:56). Confirmed.

## 4. Axioms and tricks
- Whole-word grep over the six new files for `axiom`, `sorry`, `admit`, `native_decide`, `decide`, `implemented_by`,
  `extern`, `unsafe`, `opaque`, `skipKernelTC`, `macro`, `elab`, `syntax`, `notation`, `instance`, `attribute`, `partial`,
  `csimp`, `ofReduceBool`: no hit. Only `set_option autoImplicit false`.
- Upstream: the import contains two `sorry`s, `AlgJL/VolIII/P2/Instances.lean:1832` (`eichler_mass_instances_small`) and
  `AlgJL/VolIII/Brandt/BrandtInstances.lean:794` (`hecke_d11_weight4`). Neither name is referenced anywhere else in the
  import or in Langlandscape, and neither is among the import lemmas used here (`stabilizer_units`, `unit_cases`,
  `unitGroup_val_props`, `unitGroup_eq_nrd_one_finite`, `normNSet_basic`, `localLattice_basic`, `star_mem_order`,
  `isUnit_iff_isUnit_nrd`, `nrd_trd_basic`, `mul_star_eq_nrd`, `mem_orderCompletionUnits_iff_local`,
  `zhat_units_explicit`, `localProj_mem_localLattice`, `one_mem_orderCompletion`). The transitive cone was not traced by
  hand; `Audit/PrintAxioms.lean` has five new `#print axioms` lines for exactly this — check that the build prints only
  `propext`, `Classical.choice`, `Quot.sound`.

## 5. Conventions
- Headers, module docstrings, provenance notes present in all six files; no `import Mathlib`.
- Every theorem/lemma has a docstring containing an `s03-` label (scripted check).
- minor: `Principal.lean:118` `private def crd1` has no docstring.
- minor: definitions without an `s03-` label in the docstring (theorems are fine): `Orbit.lean:50, 140`;
  `LocalPi.lean:44, 63, 267, 277, 286, 561, 619, 661`; `Principal.lean:36, 56, 77, 88, 104, 117, 151, 366`.
- minor: `Zgam`, `Zgam.aeval_of_sq`, `Zgam.toB` are duplicated verbatim (`Principal.lean:36-64`, `LocalPi.lean:44-71`);
  `nrd_localProj'` is duplicated (`Core.lean:147`, `LocalPi.lean:169`). The assembly relies on the two `Zgam.toB` being
  defeq by unfolding (Discharge:55). Sound, but this is the most likely place for an elaboration failure in the build;
  LocalPi could import Principal instead.
- minor: `HYPOTHESES.md` says "integrated and audited" in advance of this audit and of the build.

## Not verified
- That the files compile (no build run, by instruction). Tactic-level correctness of the ~2400 lines was read for
  structure and plausibility, not re-derived line by line; the kernel is the check for that.
- The actual axiom list (needs the build's `#print axioms` output).

## Addendum (after TITAN bsf-acc-1)

TITAN bsf-acc-1 on c70ef3a9 is green: lbuild Langlandscape + LanglandscapeTests rc 0; `#print axioms` on the five new
declarations lists only `propext`, `Classical.choice`, `Quot.sound`; sorry count 0. The verdict is therefore an
unconditional **PASS** (no critical or major findings; minor findings only).
