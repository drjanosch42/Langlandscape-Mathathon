# Stage-03 re-plan notes (drafter, Opus, 2026-11-14)
## What changed and why
- Coarse 29 WPs / 9.3 h critical path → **33 WPs, critical path ≈ 141 min, stage wall 2.4 h (1.8–3.3 h)**. This follows
  the stage-1 calibration (brief F) and the remote-only Lean regime with stacked drafts and integration rounds (brief C).
- **Stacks Frontier vendoring dropped** (old X2 + go/no-go + soft edges). It would need a lakefile glob, i.e. a pin
  regeneration, and the code is AI-written and unreviewed. Mathlib suffices (`Module.Dual ℤ X ⧸ range`,
  `index_eq_natAbs_det`). This removes Muse F3/F10 and coarse risk 1.
- **Lemma bip is stated on stage 02's `Graph.BipMultigraph`** and no longer on a separate `WGraph` bridge. `phiComb` is
  defined for any `(w, X ≤ E →₀ ℤ)`, so the two-vertex, DR and general cases share one definition.
- Coarse L5 split into L5 (pure arithmetic, wave 1) and L6 (Mazur instantiation). The `|Γ|`→`w` mass conversion is the
  explicit lemma `Ribet.sum_inv_wx_Ohat` (F12). Coarse L6 split into L7 (abstract) and L8 (instantiation at `Ô^×`).
  The `U₀(M)` instantiation became ext, because stage 1 has no row-sum lemma at our levels.
- Models follow brief A. The opencode routes (muse, mistral) are gone. Every row names its model plus a fix budget.
  Promoted (Muse F7): M3 to hard/opus, L11 to conceptual/opus with an adversarial Fable WP audit.
- New WPs: X2 (axiom scratch file, lesson D2), M6 (literature), M7 (second reader for the exponent chain), L12/M8
  (parallel Fable audits), L13 (audit fixes). There is now an early gate (gate-1) and a from-scratch final gate.
- E8 is placed on **S03-M2** (`prop:s03-phieis` + `prop:s03-LRdef`). It is pure proof writing with a known route, and
  step (1) has never had a second reader, which gives a real correctness test. Its size is about that of E8 at stage 1.
  It is off the critical path, and L7/L8 carry step (1) as `Hyp.BrandtStabFree`. M4 was rejected (conceptual,
  convention confound), M5 too (literature-time confound), and M3 too (depends on stage-02 coefficient conventions).
- Remote-eligible: M1, M3, M4, M5, M6, M7. M9 is excluded because it edits existing files. The stage is launchable
  without Abhijit.
## Assumptions about stage 02 (bound to labels and declared outputs, not WP ids)
- `Graph.BipMultigraph` with `∂ = (−s₀*, s₁*)`, `Graph.H1`, a decidable connectivity predicate and a rank formula
  (`Graph/{Bipartite,H1}.lean`); `Tree.BG U q`, `s0`, `s1`, `Tree.BGConnected` (`if:s02-quot`); Hecke commutation of
  `s_j` (`prop:s02-quot`(c)); `partialHom`/`XindefV` (`if:s02-coh`); `tree/{quotient,twoterm}.py`.
- Optional: a stage-02 lemma `BGConnected` from `Hyp.SA ∧ Hyp.HS ∧ Hyp.BTtree`. Without it, L9 states only the
  `BGConnected` version.
- Stage 02 (or else S03-X1) generalises the hard-coded `'s01-'` docstring test of `tools/check_wp.sh` to `s0[1-6]-`.
- Entry = stage-02 Lean final gate green. If the names drift, L1/L2/L9/L11 rebind in their first fix round.
## Assumptions about the new OVERVIEW
- The section names are taken from the brief (§4.3 TITAN, §4.4 calibration, §5/§5.2 models and strands, §6.1 remote,
  §9 lessons). Parallel Fable (master log 18:22) holds, so L12 ∥ M8. Strand branches are generalised to `exp/s03-*`.
  The sub-coordinator structure follows F3.
## Open questions for Fabian
1. Do you confirm dropping the Stacks `CycleRank`/`DiscriminantGroup` vendoring?
2. E8 on S03-M2 with Fable single-shot: may a winning Fable strand become the merged section?
3. Is the `U₀(M)` Eisenstein instantiation wanted now, or is level 1 enough?
4. Should the Mathlib-only graph WPs start early during stage 02, competing for TITAN slots?
5. Abhijit: should A-S03M (M1, M3–M5) go out as one package or per WP, and should M6 go there by default?
