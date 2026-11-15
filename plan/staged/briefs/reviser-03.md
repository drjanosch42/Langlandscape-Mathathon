<!-- model: Sonnet (high effort) -->
You are the REVISER for STAGE 03 of the Langlandscape staged plan (Jacquet–Langlands). Worktree: /home/janosch/dev/Langlandscape-wt/plan (branch wip-plan). Commit there; NEVER push. Other agents work in parallel in the same worktree: write ONLY plan/staged/stage-03-*.tex, plan/staged/bib/stage-03.bib, plan/staged/missing/stage-03.md and plan/staged/audits/stage-03-resolution.md. Commit with `git add <those files> && git commit -m "plan: revise stage 03 after Muse audit"` (end the message with `Co-Authored-By: Claude <your model name> <noreply@anthropic.com>` (e.g. Claude Sonnet 5.5)); if you hit index.lock, wait and retry; never `git add -A`. Never edit plan/seed/.

Input: the Muse Spark Open audit plan/staged/audits/stage-03-muse.md of the stage file plan/staged/stage-03-*.tex (context: plan/staged/SPLIT.md, the seed plan/seed/towards_simplicial_jl.tex, and the literature at /home/janosch/dev/Langlandscape/literature/, which you can read with pdftotext). Muse audits are known to contain false claims, so CHECK EACH FINDING INDEPENDENTLY: re-derive the mathematics and open the cited PDF where a reference is questioned.

Write plan/staged/audits/stage-03-resolution.md: a table/list with one entry per finding (F-id, short title, verdict CONFIRMED / PARTIALLY CONFIRMED / REJECTED, reason (1–4 sentences, concrete), and what changed (file section/label) or "no change"). End it with counts: total, confirmed, partially, rejected, and a one-line overall judgement of the audit's usefulness. Apply only confirmed (or confirmed parts of) findings to the stage file. Do not otherwise restructure it, and keep the interface statements unless a confirmed finding forces a change; any interface change must be listed under "Interface deviations" in the stage file.

Compile check in a PRIVATE copy: `T=$(mktemp -d); rsync -a plan/staged/ $T/; cd $T && latexmk -pdf -interaction=nonstopmode main.tex` (ignore errors originating in other stages' files). No build products get committed.

Report (≤ 8 lines): commit sha, counts (total / confirmed / partial / rejected), the most significant confirmed change, and any finding you could not decide.

Seam items to preserve (already applied by the drafter): factor-2 hypothesis (C3), amended if:s02-indef import, Ihara (iii) exponent +1 with full-density hypothesis.
