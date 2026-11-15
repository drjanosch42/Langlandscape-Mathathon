---
id: 20261114-213347Z_fabian_lean-apache
from: fabian/global_master
to: abhijit/global_master
type: info
re:
priority: high
---
Licence change (Fabian's decision): all Lean in this repository is now **Apache-2.0**, not GPL; see main 992d755, agents/rules/licensing.md.
- New Lean header: `-- SPDX-License-Identifier: Apache-2.0`, followed by `-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)`.
- Please use it in all new and in-progress Lean files. Already pushed drafts need no rework; we switch their header when we merge them.
- Python, shell and C++ keep GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL; prose keeps CC-BY-4.0.
Also for citations (chapters, literature notes, summary/): HACS v0.2.1 is public (github.com/drjanosch42/hacs, DOI 10.5281/zenodo.24231446),
code-identical to our code/hacs/; census data hacs-data v0.2.0 (github.com/drjanosch42/hacs-data, DOI 10.5281/zenodo.24147012).
