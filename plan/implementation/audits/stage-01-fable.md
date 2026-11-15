# Stage 01 implementation plan — Fable audit

Auditor: Fable (alone, no subagents), 2026-11-14. Audited at `wip-plan` f972d7e: `OVERVIEW.md`, `stage-01.md`,
`EXPERIMENT_PROTOCOL.md`, `audits/stage-01-{muse,resolution}.md`, `tools/muse_audit.sh`, against
`plan/staged/stage-01-quaternion-foundations.tex`, `plan/scouting/{SUMMARY,Stacks}.md`, `agents/rules/*`, and the import
(`lean/trace-formula-project-import/`: lakefile, manifest, `tools/*`, the state of its `.lake/`).
**No build, no `lake` command and no write outside this file was made.** Status words: *verified* = read in the Lake
v4.35.0 sources (`~/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/lake/Lake/`) or in the files named;
*computed* = by a read-only script this session; *judgement* = my assessment, not checked by running anything.

## Verdict: GO WITH REQUIRED FIXES

The plan is thorough and its central Lean decision (P: path dependency on the built import through `.lake/GL2TF`,
hand-made manifest, never build GL2TF) is **sound according to the Lake sources**. It is not ready to execute as
written: 3 critical fixes (all in the Lean setup), 14 major, 12 minor. None needs a redesign; all are edits to the
three plan files. Counts: **critical 3 / major 14 / minor 12**.

## A. What I verified about the Lean setup (so the fixer need not re-derive)

1. *verified* `Load/Workspace.lean:61–69`: with a manifest present Lake calls `materializeDeps` and never writes the
   manifest (`writeManifest` is only reached from `updateAndMaterialize`). **But if the manifest file does not exist,
   Lake silently runs a full update** (line 69): fetches, and for our layout it would run git inside
   `.lake/packages/<pkg>`, i.e. through the symlinks inside the frozen farm. A malformed manifest only throws (safe).
2. *verified* `Load/Resolve.lean:585–627`: every dependency, direct or transitive, is looked up by name in the root
   manifest; a missing one is an error. `validateManifest` does not warn for path/path.
   `Load/Materialize.lean:266–292`: a `path` entry with `copy:false` is used in place, `resolvePath?` = realpath, so
   the symlink `.lake/GL2TF` resolves to the main checkout's import. Required JSON keys of a path entry
   (`Load/Manifest.lean:129–139`): `name`, `type`, `inherited`, `dir`; `scope`, `configFile`, `manifestFile`, `copy`
   default. The entry of OVERVIEW §3.3 is well-formed.
3. *verified* `Load/Config.lean:83`: config oleans of `lakefile.lean` packages go to `<root ws>/.lake/config/<idx>`,
   not into the dependency (the import's own `.lake/config/{1,5}` confirms).
4. *verified* `Build/Package.lean:87–95`: a dependency's build cache is fetched only if its build dir is missing and
   (`preferReleaseBuild` or scope ∈ {`leanprover`, `leanprover-community`}). GL2TF has scope `""` and a build dir, so
   no fetch. **Keep `"scope": ""` in the path entry.**
5. *verified* `Build/Common.lean:213–255`, `Build/Module.lean:1066–1100`: up-to-date = saved `depHash` equals the
   recomputed input hash; then the log is replayed and nothing is written, provided the `.hash` files exist.
   *computed*: the import build has 112 `.olean`, 112 `.ilean`, 112 `.c`, each with its `.hash` (344 hash files incl.
   module-system artefacts). So an up-to-date check from our project writes nothing into the import.
6. *verified* (import trace `AlgJL/VolIII/Brandt/Brandt.trace`): the input trace mixes the Lean version, the source
   content hash (the absolute path is only a caption; the traces carry the old path
   `/home/janosch/dev/trace_formula_gl2/algebraic_jl/lean/…`), the options `-DautoImplicit=false
   -DrelaxedAutoImplicit=false`, `Module.name` and **`Package.id?: (some GL2TF)`** (`Config/Package.lean:160`,
   `origName`). Consequences: under P the package identity is unchanged, so the oleans should replay (*judgement*:
   I expect outcome P, not P′; X1 decides). Under V the package is `Langlandscape`, so nothing can be reused from
   the import (as the plan assumes). Copying a `.lake/build` between worktrees of the same project is trace-valid.
7. *computed* import closure of `AlgJL.VolIII.{P2,Brandt}.*` + `AlgJL.Hyp.EichlerMass`: **37 AlgJL modules + 2
   `Definitions.*` (AnthropicFLT) + 2 `FLT.*` (ImperialFLT: `FLT.NumberField.Padics.RestrictedProduct`,
   `FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic`), 25.1k lines**. OVERVIEW §3.1(7) says 34 + 2, 20.8k lines,
   and has no ImperialFLT. All import names used by the L-WPs lie in this closure except `jl_formula_identity`
   (`AlgJL.VolIII.P1.JLFormula`, used only by Q5 and the tex's L0 facade list).
8. *verified* the import's `lbuild.sh` takes `lean.lock` exclusively and no slot; `lfile.sh` takes `lean.lock`
   shared, then a slot, then waits for memory, then runs `check_frozen.sh --file`. `check_frozen.sh` scans the
   project's `.lean` files (pruning `.lake`) for imports whose first component is in `DEP_ROOTS`.
9. *verified* on this node: `unshare -rmn true` works (unprivileged user + mount + net namespaces); `bwrap` is not
   installed; disk 182 GB free on `/mnt/c`, 79 GB RAM available.

## B. Required fixes

### Critical

**C1. Fail-closed pin guard before every `lake` call (OVERVIEW §3.4, §3.5; protocol §7.2/§7.3).**
Reason: A.1. A missing `lake-manifest.json` (deleted by an `--auto` opencode job, a worktree made from a pre-X1
commit, a bad merge) turns the next `lfile`/`lbuild`/`check_frozen` into a `lake update` that fetches and writes
through the farm symlinks. This is the only irreversible damage the plan can cause, and the post-flight
`find -newer` only reports it afterwards. Apply:
- OVERVIEW §3.4, new first bullet: "`tools/pins.sha256` (committed by S01-X1) holds the sha256 of `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain`. `deps_load.sh` (sourced by every wrapper) runs
  `sha256sum -c --quiet tools/pins.sha256` and checks that `.lake/package-overrides.json` is absent, **before any
  `lake` invocation**; on failure exit 99 without calling Lake."
- OVERVIEW §3.3: the manifest is **generated**, not hand-edited: a committed `tools/make_manifest.py` loads the
  import's manifest, sets `"name": "Langlandscape"`, appends the path entry (keys exactly as in §3.3, `"scope": ""`,
  `"copy": false`, `"inherited": false`), and dumps it; X1 records the diff against the import's file.
- Protocol §7.2/§7.3: in the loop, the `git status --porcelain` check (and the pin check) runs **before** `lfile.sh`,
  not after the iteration; `stop reason=frozen` then happens without any Lean process having started.
- OVERVIEW §3.4 `check_frozen.sh`: add `fetching|materializing` to the log pattern that makes the dry check fail.

**C2. Restructure S01-X1: minimal smoke first, sandboxed first contact, lock change separate, run before the stage
clock starts (OVERVIEW §3.5, stage-01 §1/§2/§9).**
Reason: X1 as written bundles (i) the P/V decision, (ii) nine wrapper copies and (iii) a new lock model into one
40-minute "mechanical" Sonnet WP at the head of the critical path. A wrapper bug then looks like a P failure and
sends the stage to V (+45 min and ≈ 25 min per worktree) for nothing. Replace X1 by:
- **S01-X1a (smoke, decides P/P′/V).** Wrapper copies with the *minimal* diff only: `lean="$repo"`, target
  allowlist, the `path` exception in `link_deps.sh`, `GL2TF_IMPORT`, `DEP_ROOTS`, the pin guard of C1. The lock
  model stays the import's (exclusive `lean.lock`). Do not copy `prune_stale_build.sh`/`stale_build.py` (not needed
  in stage 1; a prune tool next to `.lake/GL2TF` is an avoidable hazard). Steps, in this order:
  0. pre-flight as in §3.5 step 0, plus sha256 of the import's three frozen files and `git status --porcelain` of
     the import; `unshare -rmn true` must succeed.
  1. skeleton + generated manifest + `Smoke.lean` (as in §3.5 step 1) with **all** stage-01 libs declared
     (`LanglandscapeVendorStacks` with a not-yet-existing `srcDir` included, so that this is exercised).
  2. `tools/link_deps.sh && tools/link_deps.sh --verify`.
  3. **Sandboxed first contact**: run the dry check and the first build once inside a namespace where the farm,
     the Mathlib tree and the import are read-only and there is no network, e.g.
     `unshare -rmn sh -c 'for d in /home/janosch/data <main checkout>/lean/trace-formula-project-import; do mount
     --bind "$d" "$d" && mount -o remount,ro,bind "$d"; done; exec lake build --no-build +Mathlib.Init
     +AlgJL.VolIII.Brandt.Pairing +AlgJL.Hyp.EichlerMass'` (inside the wrapper's systemd scope, `unshare` innermost),
     then the same with `lake build +Langlandscape.Smoke`. Any attempted write or fetch then fails with an error
     instead of damaging a frozen tree. Expected: "All targets up-to-date", then exactly one module built.
     (This is the one place where X1 calls `lake` directly; it is part of the wrapper's `--smoke` mode, not a
     manual command.)
  4.–6. §3.5 steps 3–6 through the normal wrappers (unsandboxed), with the checks as written.
  7. Second worktree: `link_deps`, dry check, **and the seeding test of M1** (copy `.lake/build`, then
     `lbuild.sh +Langlandscape.Smoke` must report the module as replayed, zero modules compiled).
  Decision rule as in §3.5. Model: **opus** (cost is negligible against "a wrong conclusion costs the whole stage").
- **S01-X1b (lock model + `SLOTS` allowlist).** Only after Fabian approves OVERVIEW §8 Q2. Acceptance: (a) two
  worktrees run `lbuild.sh +Langlandscape.Smoke` concurrently and both finish; (b) the deadlock test of C3; (c) an
  import `lbuild` (simulated by holding `lean.lock` exclusively with `flock`) blocks both. Until X1b is merged, the
  stage runs with the exclusive lock and batched gates (stage-01 R4).
- **Timing**: X1a (and X4 on TITAN) run **before** stage 1 starts, as the last step of P4/P5. They need no other
  input, they gate every Lean WP, and Fabian's approvals (§8 Q1–Q3) are needed anyway. stage-01 §8/§9 then start at
  t = 0 with L1, L3a; the critical path shortens by 40 min.

**C3. Lock order (OVERVIEW §3.4 lock model; protocol §1.5).**
Reason: the new model has two resources (a node slot, the per-checkout lock) and no stated order. `lfile.sh`
(import order: `lean.lock` → slot → …) would hold a slot while waiting for the checkout lock; `lbuild.sh` could hold
the checkout lock while waiting for a slot. Two `lfile`s plus one `lbuild` in one checkout (a worker's background
build plus its own check plus an opencode job's check — exactly the "pipeline" of §4) then deadlock with both node
slots taken, for up to `LOCK_WAIT` = 7200 s, stopping all Lean work on the node. Apply to §3.4: "Acquisition order
in **both** scripts: (1) `exp.lock` if an experiment check, (2) `lean.lock` shared, (3) the per-checkout lock
(`lbuild`: exclusive, `lfile`: shared), (4) a node slot, (5) the memory wait. No script waits for (3) while holding
(4). The slot is taken with a blocking retry loop only after (3) is held." Add the deadlock test to X1b: start
`lbuild` and two `lfile`s in one checkout while the second slot is held by a dummy `flock`; all must finish.

### Major

**M1. Seeding `.lake/build` in fresh worktrees is needed under P too, and must not use hard links (stage-01 §9;
OVERVIEW §2/§4; protocol §2.1).** `lfile.sh` needs all project imports of the file built. `new_wp.sh` creates a
fresh worktree per WP, so by L10 a worker would first rebuild L1, L3a–d, L6–L8a, L9 (≈ 120 min of Lean process time
by the plan's own estimates) before its first check. The plan mentions seeding only for V and as an unexplained
"S01-X1 mechanism". Apply: (a) `new_wp.sh` copies `.lake/build` of the `impl` worktree (where the merge gates built
everything) with `cp -a` under that checkout's lock held shared; A.6 says Lake accepts it; X1a step 7 proves it.
(b) Replace `cp -al` in stage-01 §9 by `cp -a` (`--reflink=auto`): with hard links, a rebuild in one worktree
rewrites the shared inode and corrupts the other worktree's build while its `.hash` files still claim the old
content. (c) If step 7 fails, fall back to one long-lived worktree per worker lane (`git switch -c` after each
merge; `.lake/build` survives). State which of (a)/(c) is in force in `DECISION-PV.md`.

**M2. V layout and provenance are wrong (OVERVIEW §3.1(7), §3.2, §3.3; stage-01 X1).** By A.7: add
`LanglandscapeVendorImperial` (`srcDir="Vendor/ImperialFLT"`, `globs=["FLT.+"]`,
`leanOptions={ maxSynthPendingDepth = 3 }`) and `Vendor/ImperialFLT/LICENSE`; correct the numbers to 37 + 2 + 2
modules, 25.1k lines; add `AlgJLTests.*` files to the closure if a test uses the import's Hurwitz instances. For the
third-party files, **copy the import's `Vendor/MANIFEST.tsv` rows verbatim** (true upstream URL, rev and
`sha256_upstream`; `modified = yes` for the two AnthropicFLT files, which the import changed) and add
"via lean/trace-formula-project-import @<commit>" in the note column; do not write `sha256_upstream = sha256_local`
with the import as "upstream" for them. Copy `Vendor/AnthropicFLT/{LICENSE,NOTICE}` verbatim.

**M3. P's guards are incomplete (OVERVIEW §3.4; an `agents/rules` change for the global master).** (a) `DEP_ROOTS`
must also contain `AlgJLTests`: the first-component match does not cover it, and `LanglandscapeTests` may import the
import's test instances; a stale one would be built *into the import* by our Lake process. (b) P depends on the
import's sources not changing while stage work runs, but `frozen.md` freezes only its lakefile, toolchain and
manifest. Add to OVERVIEW §8 as a request: "`lean/trace-formula-project-import/lean/**` is read-only during
implementation; any change goes through the global master, who rebuilds with the import's `lbuild.sh` before any
stage build resumes."

**M4. Missing DAG edges (stage-01 §1, §4, §8, §9; protocol E5).**
- L7's `normMap_bijective_padic` uses L5a(c); L7 does not depend on L5a, and L5a is an experiment strand (E2).
- L11's `Up_comm_Tl` uses `Up`, defined in L10; L11 does not depend on L10 (they are scheduled in parallel).
- L13's `Hyp.JLClassical` uses `U0` (L3c) and `Tl` (L11); L13 depends only on L1, L7.
Apply: (i) new **S01-L17 "corollaries"** (core, routine, sonnet, 40 min, build 8), deps L5a, L7, L8b, L10, L11:
`normMap_bijective_padic`, `Up_comm_Tl`, and the adjoint corollaries of M6; remove the first two from L7 and L11.
(ii) L13 deps become L1, L7, L3c, L11. (iii) L14 deps add L17. (iv) Recompute waves and the critical path:
`L1 → L6 → L7 → L8a → {L8b, L10, L11} → {L13, L17} → L14 → L15 → L16`; with the plan's numbers and X1 moved out
(C2) this is 40+45+60+50+60+40+30+50+45 = 420 min, i.e. unchanged in length but **L13 now has zero slack**, which
invalidates the E5 slack statement in §8 and "E5 needs L1 and L7" in protocol §2.1 (see M12).

**M5. `relIndex_K1_succ` is false as stated (stage-01 L9; brief of E1).** `(K1 p (s+1)).relIndex (K1 p s) = p^2`
has no hypothesis on `s`; at `s = 0` (`K1 p 0 = GL2Zl`) the index is `p² − 1`. Add `(hs : 1 ≤ s)`. (The Muse
resolution F8 checked the `relIndex` orientation but not `s = 0`.) This matters twice: both E1 strands get the
false signature as "exact", and the audit template scores a changed signature as critical.

**M6. Lean coverage is silently narrower than the tex (stage-01 §0, §4, §10).** Nothing in the plan says so, and
§10 claims the Lean counterparts of `if:s01-*` are the declarations of L1, L5a–c, L6, L7, L8a/b, L10, L11. Not
covered by any L-WP:
- `lem:s01-nrd` (`Nrd U = Ẑ^×`, part of `if:s01-classset`);
- Hecke operators with coefficients (tex "L3: double-coset operators with monoid action"; `brandtModule` gets no
  Hecke action; `def:s01-pairingV`, `V_k`);
- `prop:s01-adjoint`(b) "in particular" and `if:s01-hecke`: `T_ℓ^* = S_ℓ^{-1}T_ℓ`, `⟨d⟩^* = ⟨d⟩^{-1}`,
  `Π_ℓ^* = Π_ℓ^{-1}`, `T_ℓ` self-adjoint at `U_0(M)` (the plan has it only at `Ô^×`, in the *ext* WP L12);
- `lem:s01-Up`(c) trace half and (d) (`U_p^* = ⟨p⟩_M U'_p`; the global `U'_p` is never defined);
- `prop:s01-relations`(a), (b), (d); `def:s01-T`;
- the tex's L4 dictionary (linear equivalence over `ℚ_p`, all `k`, level `Ô(M)^×`): plan L12 is `k = 2`, `Ô^×` only;
- L5c proves freeness for `Utower` only, the tex for any `U = U^{(p)} × U_1(p^s)_p`.
Apply: (i) add to stage-01 §0 a **coverage table** "tex label → WP / Lean declaration / status (core, ext, deferred
to stage NN, not planned)" with exactly the items above marked; correct the §10 "Exports" sentence accordingly.
(ii) Put the cheap ones into L17 (they are one-line consequences of L8b and L11): `Tl_adjoint`, `diamond_adjoint`,
`PiEll_adjoint`, `Tl_selfAdjoint_U0` (`ℓ ∤ DM`, level `U0 d M`). (iii) `lem:s01-nrd`: either a small WP
(`nrd_U1_eq_top`, via `localEmbedGL (diag u 1)`; routine, sonnet, 30 min, deps L3c, L3d) or "deferred to stage 02"
in the table — the stage-02 planner must then confirm that Prop quot does not need it formally. (iv) The stage
02–06 plans must be checked against the table for consumers of a "deferred" item (in particular `U'_p`/`U_p^*` in
stage 04 and Hecke-with-coefficients in stages 04–06).

**M7. L13 statements (stage-01 L13, Q5; brief of E5).** (a) `Eis k` and `eisT ℓ` are undefined, so the "exact
shape" is not exact; define them in the block (`k = 2`: `Eis := ℂ`, `eisT ℓ := (ℓ+1) • id`). (b) With an arbitrary
`S : GL2CuspData`, `Hyp.JLClassical d M 2 S` only says "S is a Hecke-module complement of the constants"; some `S`
always satisfies it, so it carries **no** GL₂ content. That is acceptable only if it is said: docstring and
HYPOTHESES.md row must read "schematic interface; the GL₂ side is abstract data because Mathlib v4.35.0 has no
Hecke operators on `S_k(Γ_0(N))`; the hypothesis is JL only when `S` is instantiated by the true space, which
cannot be checked in Lean here", and no later theorem may be advertised as "under classical JL" without that
caveat. (c) `Hyp.LambdaJL` keeps only the surjection and drops the tex's `T^{ord,D-new} ≅ T_B^{ord}`; add the
kernel statement as a second field/conjunct with an abstract `D`-new quotient, or record the omission in the
coverage table. (d) Difficulty is not "mechanical": the shapes are design decisions. Keep sonnet, but fix the
shapes in the plan (by the Opus fixer) so that the WP itself is mechanical.

**M8. The M-track acceptance check fails for a section WP on its own branch (stage-01 §3 common acceptance 2).**
Sections reference each other's labels (M3 cites `lem:s01-Up`(d) from M4; M2 cites `lem:s01-stab` from M1; M5 cites
`def:s01-NUp`), so `grep -c undefined main.log = 0` cannot hold before all six are merged; agents would add dummy
labels and break check 3 at merge. Apply: M0 creates in each section file the **statement skeletons with all tex
labels** (environments and labels copied from the stage tex, bodies `TODO`), so every label exists from M0 on;
section WPs fill bodies and may not add or remove a tex label (new labels only from the list in §3). M0's
acceptance adds "every label of the stage tex is defined exactly once".

**M9. C6 compares the wrong level (stage-01 §1 table and C6).** `S_s = X_B(U_1(5^s))` for `D = 3`, `M = 1`
corresponds to level `3·5^s`: **15 for `s = 1`**, 75 for `s = 2`. The table says "Γ_1(25)∩Γ_0(3) (and s = 2)" and
the block uses `mfinit([75,2,χ])` for both `ℂ[S_1]` and `ℂ[S_2]`. Fix: `s = 1`: `mfinit([15,2,χ])`, `χ` mod 5 even;
`s = 2`: `mfinit([75,2,χ])`, `χ` of conductor dividing 25; add the dimension checks `2 = 1 + Σ_χ dim` and
`50 = 1 + Σ_χ dim`. As written, the assertion would fail and trigger R1 ("not a test to be adjusted"), stopping
L10/M4 on a false alarm.

**M10. The R1 numeric check runs last, and the C track is falsely serialized behind Lean (stage-01 §9).** C has no
dependency on Lean, yet C1 starts at 480 min and C6 — the numerical half of the plan's highest risk, whose failure
"stops the U_p-dependent WPs" — ends at 850 min, hours after L9, L10 and M4 were written, merged and audited. This
is only an artefact of three worker slots. Apply: schedule `C0 → C1 → C2 → C5 → C6` (≈ 235 min) from t = 0 so
that C6 finishes before L10 starts (≈ 250–295). With three workers this is impossible without displacing Lean,
so Q1 (track sub-coordinators for M and C/T, each ≤ 3 workers) becomes a **required decision** rather than an open
question; RAM allows it (≈ 9 agents × 2 GB + 2 × 8 GB Lean + opencode ≈ 40 GB of 79 GB). If Q1 is denied: C chain
on W3 from t = 0, M track after it, and say so in §9.

**M11. L11 is overloaded and sits on the critical path (stage-01 L11).** "routine · sonnet · 60" covers `Tl`, `Sl`,
`Ul`, `diamond`, `PiEll` + `PiEll_indep`, `rightTranslate`, two commutation theorems. `PiEll` needs the local
structure at ramified primes (normality of `𝒪_ℓ^×` in `B_ℓ^×`, a `localEmbed` at `ℓ ∣ D`, which L3d builds only
through `ι_ℓ` at split primes) — *judgement*: hard. Split: **L11a** (`Tl Sl Ul diamond`, `heckeT_comm_of_disjoint`;
routine, sonnet, 45) and **L11b** (`PiEll`, `PiEll_indep`, `rightTranslate`, `heckeT_comm_rightTranslate`; hard,
opus, 60; deps L8a, L3d), in parallel. State in L3d whether `localEmbed ℓ` is defined for all `ℓ` (it must be, for
L11b).

**M12. Protocol: the decision metric and the merge rule let the experiment touch the critical path
(protocol §3, §4.1, §4.4, §1.5; stage-01 §8/§9).** (a) `wall = t_pass − t_impl_start` includes the time a strand
waits for the single experiment Claude slot (audit queue), for the stage master to react, and for Lean slots; this
differs systematically between reference and challenger. Decide on **`active = impl_min + audit_min + fix_min`**
(the lead's definition: implementation + Opus audit + fixes), report `wall` and `queue_min` beside it. (b) "First
passing strand is merged" makes the Opus audit and its fix rounds part of the production path of all eight
reference WPs, and none of that time is in stage-01 §9 (L13: zero slack after M4; L9 feeds L10). Add to §4.4: "A
reference strand is **mergeable at mechanical acceptance** (the OVERVIEW §2 gate), like any `impl/` WP; downstream
WPs start then. Its audit and fix rounds continue on the `exp/` branch for timing and are merged as a follow-up."
(c) Give the eight reference audits a place in §9 (≈ 8 × 10–20 min of the experiment slot).

**M13. Protocol: isolation and logging holes (protocol §5, §7, §10; stage-01 X3/X5).**
- `events.tsv` is a tracked file on every strand branch; wrappers running in strand worktrees would append to
  their own copy, pollute `strand-<X>.patch` and trip the "change outside the WP's files" check. Fix: exactly one
  file, addressed by absolute path in the `impl` worktree, appended under `flock`, committed only by the stage
  master; strand worktrees never write it.
- Strands can read each other: sibling worktree paths are predictable and all `exp/*` branches are in the shared
  repository (`git show exp/s01-l9-opus:…`), and a merged-first reference is visible in `wip-implementation`. Add to
  both fixed preambles "read nothing outside your worktree except the frozen import, Mathlib and the brief inputs;
  no `git` command other than `add`/`commit`", and a post-hoc check by the stage master (grep the opencode JSON tool
  events / the agent transcript for sibling paths and `git (show|log|branch|worktree|checkout)`); a hit marks the
  strand `contaminated` and removes it from the decision.
- E6 cannot run as specified: X3 fetches with `gh api`, the opencode prompt forbids network commands. Fix: X5 (or
  the stage master) fetches the 8 blobs and `LICENSE` once at rev `c496df0d…` into `.exp/inputs/` (raw accept
  header, not base64 pasted by a model) and records their git blob shas; both E6 strands start from these files.

**M14. Protocol: the experiment does not answer the question that matters most for stages 02–06 (protocol §1.3).**
Stages 02–06 are dominated by hard and routine Lean. The only hard-Lean cell is muse vs opus (E1); given P1's Muse
data its likely outcome is "Opus keeps the class", which says nothing about **Sonnet vs Opus on hard Lean**, the
assignment with the largest cost and wall effect. Apply: (a) make E1 a three-strand cell on L9 (opus reference,
**sonnet** and muse challengers; Mathlib-only, exact statement, 90 min of slack through L10; the sonnet strand uses
the experiment Claude slot at 85–145, which is otherwise idle). (b) Drop **E7** (M0: 20 min skeleton; it forced M0
behind X5 to t = 110, which delays the whole math track as soon as Q1 is granted; M0 returns to t = 0). (c) E5 on
L13 is no longer off the critical path (M4); keep it only with the M12(b) rule. (d) State in §9 of the protocol
that every one-comparison verdict is a prior to be revised from `runs/sNN.md`, not a decision.

### Minor

- **m1.** Protocol §3 cost weights tie muse = mistral = haiku = 1, but the binding order is muse < haiku < mistral.
  Use weights 1 / 2 / 3 (or break cost ties by that order) so that "cheaper wins" is defined for E6.
- **m2.** S01-X2 (`check_wp.sh` is the acceptance check of every L-WP): assign sonnet, not mistral. Make the
  sorry check robust: fail on `declaration uses 'sorry'` in the build log in addition to the source grep; drop the
  ill-defined "docstring names a label" test or define it as "every `theorem` in the file list has a docstring
  containing `s01-`". Acceptance: planted `sorry`, `admit`, `axiom`, `native_decide` each return 1.
- **m3.** S01-X3 integrity: compare `git hash-object <file>` with the blob sha of the GitHub tree at the pinned rev
  (the sha256 of what was just downloaded proves nothing); record both in `MANIFEST.tsv`/`PROVENANCE.md`.
- **m4.** Licensing text for `Vendor/AxiomStacks/`: `LICENSE` = upstream file at the pinned rev, verbatim;
  **no NOTICE file** (upstream has none; do not invent one in their name); `ATTRIBUTION.md` with the row from
  `scouting/Stacks.md` §1 ("no per-file header upstream; Copyright AxiomMath …; authors per formalization.yaml …")
  and the sentence "statements follow the Stacks Project (GFDL); only Lean code and tag numbers are copied".
  X3 checks the 8 files' docstrings for verbatim Stacks prose and records the result in `PROVENANCE.md`.
- **m5.** Protocol §6: for E6 do not commit the loser patch (it would duplicate Apache-licensed files under `plan/`
  away from their LICENSE); record the file list and shas instead.
- **m6.** L2: `maxSynthPendingDepth = 3` is a library option of the vendored lib only and `lfile.sh` passes only
  top-level options; allow `set_option maxSynthPendingDepth 3 in` at use sites in the L2 brief (R5).
- **m7.** OVERVIEW §3.4/§4 wording "≤ 2 Lean processes node-wide": one `lbuild` runs up to 2 `lean` children in one
  8G scope, so two builds are up to 4 processes and 16 GB. Say "≤ 2 Lean jobs (scopes)". Within the RAM rule.
- **m8.** OVERVIEW §3.1(6): replace "should be up to date; not verified" by the facts of A.5/A.6.
- **m9.** Stage-01 §9: the merge gates on the critical path (≈ 8 × 3–6 min) are not in the 420 min; add them, or
  batch gates and say that downstream WPs start from the WP branch before the gate.
- **m10.** S01-X5 also writes `tools/exp_event.sh` and `tools/exp_prepare_audit.sh` (patch, excerpt, check output,
  `shuf` label), so that each transition is one command for the stage master; ≈ 130 events by hand is a
  coordinator bottleneck.
- **m11.** S01-X4: state its precondition "TITAN's import is built and its `deps.local.conf` exists" and that
  `SLOTS=3` needs the X1b allowlist change.
- **m12.** L5c: add "(tex: any `U^{(p)}`; here `Utower` only)" to the block, per M6.

## C. Recommendations (not required)

1. **L6 → L7 looks like false serialization.** `brandtPairing`, `normMap` and `normMap_bijective` need only `wx`
   (L1), with `c.out`; if L7 needs `wx_translate`, move that lemma to L1. Then L7 starts at L1's end, the head
   chain shortens by 45 min, and `L1 → L3b → L3d → L10/L11` becomes co-critical; run L3b before L9 on W2 (L9 has
   slack). Estimated core path ≈ 375 min instead of 420.
2. Fable windows: `global_master.md` says Fable runs with no other subagent of the same coordinator. If the two
   audits (L15, M7) are launched by a separate audit coordinator of the global master, the stage master's workers
   need not idle (≈ 200 worker-min saved). See item F4.
3. Add a second routine-Lean Muse strand (L3a: Mathlib-only, 45 min, slack) so that the cell most used in stages
   02–06 has n = 2; it costs no Claude slot except the audit.
4. Send merge-gate builds to TITAN when both local slots are busy (295–355 has three Lean WPs, gates and
   experiment checks competing for two slots while TITAN's three are idle).
5. `Tl_eq_heckeOperator` (L12) through the Cartan decomposition is *judgement* more than 60 min; keep it ext.
6. Keep `Smoke.lean` and re-run X1a steps 3–6 after every `main` merge that touches `lean/` (cheap regression test
   of the frozen setup).

## D. Check-by-check summary

1. **Mathematical faithfulness**: the M and C tracks cover the stage tex completely and keep its corrections (F1,
   F3, F4, F6, F15; `N_{U_p}`, lower row, factor 2, `Δ_s`). Numbers checked by hand: `h(D)` list for primes ≤ 53,
   `|S_s| = 2·25^{s−1}`, `|X(U_1(5))| = 1` for `D = 2`, `1/4 + 1/6`, `T_2` eigenvalues `3, −2` — all correct. Lean:
   statements that are planned match the tex except M5, M7; the coverage is narrower than the tex without saying so
   (M6); C6 has a level error (M9).
2. **Lean structure under `frozen.md`**: P resolves offline and builds nothing in the import, per the Lake sources
   (A.1–A.6). Required: C1–C3, M1–M3. V is a valid fallback after M2.
3. **WALL**: DAG has three missing edges (M4) and one probable false edge (rec. 1); the critical-path length is
   right for the plan's numbers but ignores gates (m9), seeding (M1) and reference audits (M12); the real
   bottleneck is the three-worker limit (M10). Model assignments are sensible (no Haiku on conceptual work) except
   X1 (→ opus), X2 (→ sonnet), L11 split (M11).
4. **Experiment protocol**: well isolated at the git level, blinded audits, caps and stop rules are fine; required:
   M12–M14, m1, m5, m10. With n = 1 per cell it yields priors, not decisions; the protocol says so.
5. **Licensing**: Apache-2.0 obligations for Stacks are met by the plan with m3–m5; V needs M2. The repository
   itself has no top-level LICENSE yet (F5).
6. **Resources**: thresholds match `resources.md` (X1 is stricter: 50 GB / 24 GB); caps 8G/6G with
   `MemorySwapMax=0` are inherited unchanged; worst case with Q1 ≈ 40 GB of 79 GB. Disk is at 95 % (182 GB free):
   fine under P (tens of MB per worktree), ≈ 3 GB under V with 12 worktrees.

## E. Items for Fabian

- **F1.** Approve P (OVERVIEW §8 Q1), and the request of M3(b): the import's Lean sources are read-only during
  implementation.
- **F2.** Approve the lock change and `SLOTS=3` on TITAN (§8 Q2) — now a separate WP X1b with its own tests (C2, C3);
  the stage can start without it.
- **F3.** Decide Q1 (sub-coordinators for the M and C/T tracks). Recommended: yes; it is what moves the R1 check
  ahead of the work it can invalidate and takes ≈ 14 h to ≈ 9 h (M10).
- **F4.** Clarify "Fable runs alone": per coordinator (plan's reading, two idle windows) or may an audit
  coordinator of the global master run Fable in parallel with the stage's workers (rec. 2)?
- **F5.** Before the repository goes public: choose its top-level LICENSE and add a top-level NOTICE /
  third-party list pointing to `lean/trace-formula-project-import/lean/Vendor/` (Anthropic FLT, Imperial FLT) and
  `lean/Langlandscape/Vendor/AxiomStacks/`. Nothing in the plan creates these.
- **F6.** Q5 / M7: accept that `Hyp.JLClassical` and `Hyp.LambdaJL` are schematic interfaces with an abstract GL₂
  side (no GL₂ content in Lean), or ask for the trace-form statement through `jl_formula_identity` instead.
- **F7.** Q4 (`ι_ℓ` as the import's `Classical.choose` term) — no objection from this audit. Q2 (ext WPs
  "continuing") — no objection, provided the coverage table of M6 says so.
- **F8.** The HACS snapshot is still missing (`code/hacs/` empty); H0/H1 stay optional.
- **F9.** Update `agents/rules/lean.md` (§8 Q3) before stage 1 starts, not at its end: workers read the rule file.
