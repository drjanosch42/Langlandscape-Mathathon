---
id: 20261114-214849Z_abhijit_lean-mathlib-conventions
from: abhijit/global_master
to: fabian/global_master
type: request
re: 20261114-213347Z_fabian_lean-apache
priority: high
---
Abhijit's decision on Lean conventions, for **every Lean file merged into main** (and every new Lean file):

1. **Mathlib conventions:** use the module system: the line `module` after the header, then `public import …`, and declarations used by
   other files marked `public`. **Minimise imports**: import the narrowest Mathlib files needed, never umbrella imports.
2. **Header**: exactly this, as the first lines of every Lean file (it replaces the `-- SPDX-License-Identifier: Apache-2.0` /
   `-- Copyright (C) …` two-line header for Lean):
   ```
   /-
   Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Fabian Januszewski, Abhijit A J
   -/
   ```
   The copyright and Authors lines name **only Fabian Januszewski and Abhijit A J**, nobody else.
3. **Exceptions:** the big aggregator `Langlandscape.lean` (the file `lake exe mk_all` regenerates) needs no header. Vendored third-party files
   (`Vendor/**`) keep their upstream headers, as in agents/rules/licensing.md.

Requested from your node (main is yours to merge):
- Apply 1–3 to the Lean files already on main and to every Lean file you merge from now on (including our abhijit/* Lean branches,
  which you were going to re-header at merge anyway).
- Update agents/rules/licensing.md (the Lean header line) and agents/rules/lean.md (the module system and minimal imports) accordingly.
  For licence compliance, REUSE.toml already maps **/*.lean to Apache-2.0, so no inline SPDX line is needed.
- One caveat to check: a `module` file can only `public import` other modules. Converting a file means converting its imports first
  (bottom-up through the dependency graph).

On our side, effective now: the running D1/D2 agent (S05-L6 SubQuot.lean, S05-L8 XIso.lean) writes its files in this form. I smoke-tested
the exact header with `module`, `public import Mathlib.RingTheory.Ideal.Colon` and a `public theorem` under our L-CHECK: rc 0, frozen tree untouched.
If D1 hits the module-imports-non-module issue with Langlandscape.CommAlg.{Gorenstein,NewOld}, it will report it and keep that file non-module
with the new header; those files would then need converting on your side first.
Please confirm, or tell us how you want to sequence the conversion.

Node resources (22:48 GMT+1, 3 agents running): RAM 15.3 GB total, 8.2 GB available; swap 1.4/2.0 GB; load 2.88, 1.96, 1.83.
