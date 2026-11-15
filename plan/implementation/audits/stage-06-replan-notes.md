# Stage 06 re-plan notes (drafter, Opus, 2026-11-14)

## What changed and why
- Structure §0–§7 per `briefs/replan-s02-06.md`; WP table gains `model (+fix)`, `remote`, `early`, `TITAN round`; times are
  wall/active, calibrated per brief F (stage-1 factor ≈ 0.25). Wall: 1.7 h (A, early lane merged first) / 2.3 h (B, cold start), was 9 h.
- Models per brief A: muse/mistral removed (L2, L6, L7, L14, M1, M4 now sonnet + budgeted opus fix); hard Lean/LaTeX opus +
  planned fix; audits Fable in parallel (L12 ∥ M9); M6 opus (remote) or Fable (local).
- NEW early lane (X0, jobs `s06-eint<k>`, CommAlg gate `s06-egate-1`): the CommAlg layer is Mathlib-only and GL2TF-free, enforced by a grep
  gate; 13 Lean WPs marked `early`.
- `if:s06-lemD` shape frozen in §0: same file, same declaration names as stage-05.md, and `NewOldData` fields written out
  (Mathlib v4.35 names: `Module.IsTorsionFree`, `Submodule.colon` with a `Set` argument; verified in the frozen Mathlib).
  L3 stays one WP (no file split, so stage-05 imports are unchanged); (a) is sent in the first round.
- Splits: L5 → L5a (DVR) + L5b (Lemma G, needs only L1); L8 → L8a (Setting + Hyp) + L8b (Galois); L10 → L10a (CommAlg toy,
  early) + L10b (Hyp non-vacuity).
- New WPs: X0 (early kickoff), X2 (axiom scratch, lesson D2), X3 (closure), M11 (literature), L15 (audit fixes), L16 (final gate).
- L13 (Gorenstein + Lemma S base change) is now required: (Gor_R′) comes over Λ via `Hyp.HsiehGor` + `Hyp.LambdaJL` and must be base-changed to `I`
  (tex says so); the coarse plan skipped this step.
- Lessons D1–D6 written in as steps: early full gate (L11), X2, docstring check in the round, rebase after fixes, outbox,
  no fix hints in strand relays.
- Carried over: `check_wp.sh` hard-codes `s01-` in its docstring check (X0 generalises it unless an earlier stage already did);
  0 new linter warnings; HACS still absent, so H1 stays gated.
- Conditional strand E1′ (opus vs sonnet) on L5a, triggered only by an undecided/confounded S02 E1.
- Remote table: M1–M8, M11 (M6 preferred remote); not M9, M10, strands, L/C/T/X.

## Assumptions
- Stage 04 provides `Langlandscape.Hyp.HsiehGor` in `Hyp/HsiehGor.lean`, ideally stated via `CommAlg.IsGorenstein`; if it is not, L8a adds a bridge lemma.
- Cross-stage inputs are named by label/file/declaration only (Smith-form helper "if merged", stage-1 `brandt.py`/`symn.py`).
- Concurrency as in stage 1 (stage master + M and C/T sub-coordinators; 8-subagent limit; Fable may run in parallel).
- Early-lane TITAN jobs run at priority 3 and never pre-empt the active stage; stacked drafts start against §0 signatures.
- KO, Hs, Wi95 and Dia89 PDFs are in `literature/`, which an Abhijit run would need copied over (scout Q2).

## Open questions for Fabian
- Q1 Early lane: approve it, and who merges its gated branch into `wip-implementation` while another stage is active?
- Q2 M6 executor: Abhijit (independent account) or local Fable, or both?
- Q3 L13 required (prove base change) vs an extra `Hyp` stating (Gor_R′) directly over `I`?
- Q4 Code WPs C1–C4 remote (scout candidate A-C06) although brief E excludes code?
- Q5 Strand trigger rule, including "not triggered if L5a already ran early".
