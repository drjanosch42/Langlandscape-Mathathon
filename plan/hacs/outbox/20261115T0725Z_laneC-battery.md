<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->
# Lane C closure battery (the one full run), impl/hacs-laneC @ 08481d69
Script /home/janosch/data/hacs-run/laneC/final_run.sh via heavy.sh (label laneC-final1); logs /home/janosch/data/hacs-run/laneC/final1/.
- Fresh build /home/janosch/data/hacs-build/laneC/final1 (CUDA off, RelWithDebInfo, -j12): 237 s (configure 07:09:23Z). `hacs 0.2.1 (commit unknown; contract [C] 1.28.0, [E] 1.25.3, [U] 0.8.1)`. sha256 19ab4d0670f25e5c14d290f363b3fd86c9eebc636e5dcffec181029bf59def9d.
- `--list`: 303 names = upstream 294 in order + 4 Lane B JL + 5 Lane C JL (JLQuatCore, JLBrandtSym, JLLevel, JLTreeW2, JLIharaK).
- `--all`, 4 shards: SHARDED_ALL passed=253/253 failed=0, union = roster (253, 0 duplicated), wall 551.9 s, verdict OK.
- GOLDEN_STRICT=1 GoldenRegressionValidation: tier A 12154 checked / 0 failing; tier B 6231 / 0 mismatching; PASS (33 s).
- Total 824 s. Not run (as Lane B): digests, LABEL_CENSUS, --all-full, device lane.
Coverage: HJ-8 / HJ-8-def stay outside the binary (option (a)); at closure `git diff 08481d69..HEAD` on code/hacs/cmake/jl, code/hacs/src/hacs/Registry/JL/*.{cpp,h} and the nine linked quat sources must be empty.
