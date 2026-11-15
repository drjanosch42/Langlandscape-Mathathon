# Rule: licensing (all agents, all directories)

Decision (Fabian, 2026-11-14). The repository goes public **with its full history**. Overview: `LICENSE`; path mapping:
`REUSE.toml`; third-party list: `THIRD-PARTY-NOTICES.md`; texts: `LICENSES/`.

- **Prose** (LaTeX, Markdown, other documents, result records): `CC-BY-4.0`.
- **Lean** (all our `.lean` files and the Lean projects `lean/Langlandscape/`, `lean/trace-formula-project-import/lean/`, its `tools/`): `Apache-2.0`
  (Fabian, 2026-11-14, for consistency with HACS's `lean/` and Mathlib; replaces the earlier GPL assignment for Lean).
- **Other code** (Python, C++/CUDA, shell, CAS scripts): `GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL`.
- **Every new file** gets an SPDX header and the copyright line, in the file's comment syntax, at the top
  (after a shebang / Lean `module` line if one is required to come first):
  - Lean: the Mathlib-style block header in `agents/rules/lean.md` ("Copyright (c) 2026 Fabian Januszewski, Abhijit A J. All rights reserved. /
    Released under Apache 2.0 license as described in the file LICENSE. / Authors: Fabian Januszewski, Abhijit A J"); no SPDX line and
    no copyright line below it (REUSE.toml maps `**/*.lean` to Apache-2.0)
  - Python / shell: `# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL`
  - C++ / CUDA: `// SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL`
  - LaTeX: `% SPDX-License-Identifier: CC-BY-4.0`
  - Markdown: `<!-- SPDX-License-Identifier: CC-BY-4.0 -->`
  - followed by (same comment syntax): `Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)`
  Existing files without a header are covered by `REUSE.toml`; adding headers to them is optional, never required.
- **Vendored and imported third-party files keep their upstream form and headers**: never add, change or remove headers
  in `lean/trace-formula-project-import/lean/Vendor/**` or `lean/Langlandscape/Vendor/**`. A new vendored file needs a
  MANIFEST/ATTRIBUTION row and an entry in `THIRD-PARTY-NOTICES.md` and `REUSE.toml` (global master).
- **Never change `code/hacs/` licensing** (`LICENSE`, `LICENSE.GPL`, `NOTICE`, `COPYRIGHT.md`, `LICENSES/`,
  `REUSE.toml`, headers). New files inside `code/hacs/` follow HACS's own scheme (`code/hacs/REUSE.toml`).
- Do not copy third-party text or code (papers in `literature/`, other repositories) into the tree; cite instead.
  Code under other licences enters only via the vendoring procedure above.
- **Acknowledgments** appear only in this exact wording (snippets: `mathematics/acknowledgments.tex`,
  `talk/slides/acknowledgments.tex`; `README.md`):
  "We gratefully acknowledge support from an NVIDIA Academic Grant Program award to Fabian Januszewski (CUDA-GNFS
  project), which provided two NVIDIA RTX PRO 6000 Max-Q Workstation Edition GPUs used for the HACS computations, and
  from the Deutsche Forschungsgemeinschaft (DFG, German Research Foundation) – SFB-TRR 358/1 2023 – 491392403."
- Changes to `LICENSE`, `LICENSES/`, `REUSE.toml`, `THIRD-PARTY-NOTICES.md` and this file: global master only.
