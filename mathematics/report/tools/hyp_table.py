#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Rebuild the hypothesis status table of mathematics/report/hypotheses.tex from the registry.

Usage (from the repository root):
    python3 mathematics/report/tools/hyp_table.py \
        lean/Langlandscape/HYPOTHESES.md > mathematics/report/generated/hyp-table.tex

The registry lean/Langlandscape/HYPOTHESES.md is a Markdown table with the columns
    Lean name | file | statement label | source | used by | instances | discharge plan | status
The *kind* of a hypothesis (literature / out of scope / infrastructure / condition) and the *stage* that
introduced it are editorial classifications of the report and are not recorded in the registry; they live
in KIND and STAGE below.  A registry row whose short name is missing from KIND is emitted with kind
"unclassified" and reported on stderr, so that a new stage-5/6 hypothesis cannot be dropped silently.
"""
from __future__ import annotations

import re
import sys

# Editorial classification (see hypotheses.tex, section "Kinds").
KIND = {
    "EichlerMass": "lit",
    "JLClassical": "oos",
    "LambdaJL": "oos",
    "SA": "lit",
    "HS": "lit",
    "BTtree": "lit",
    "SerreCoh": "lit",
    "SerreFree": "lit",
    "RamNrdSurj": "dis",
    "IharaH0": "infra",
    "EllipticCount": "lit",
    "BrandtStabFree": "dis",
    "PadicOrdDecomp": "dis",
    "MordLambdaFree": "infra",
    "HidaControl": "lit",
    "HsiehCR": "cond",
    "InvLimExact": "infra",
    # stage 6 (S06-X2)
    "HsiehGor": "lit", "HsiehGorFull": "lit", "FreeRankTwo": "infra", "HidaControlGL2": "lit",
    "KimOta": "lit", "KimOtaRT": "lit", "OldDecomp": "infra", "TamSpec": "infra", "ResidualBurnside": "dis",
}
STAGE = {
    "EichlerMass": "S01", "JLClassical": "S01", "LambdaJL": "S01",
    "SA": "S02", "HS": "S02", "BTtree": "S02", "SerreCoh": "S02", "SerreFree": "S02", "RamNrdSurj": "S02",
    "IharaH0": "S03", "EllipticCount": "S03", "BrandtStabFree": "S03",
    "PadicOrdDecomp": "S04", "MordLambdaFree": "S04", "HidaControl": "S04", "HsiehCR": "S04", "InvLimExact": "S04",
    "HsiehGor": "S06", "HsiehGorFull": "S06", "FreeRankTwo": "S06", "HidaControlGL2": "S06", "KimOta": "S06",
    "KimOtaRT": "S06", "OldDecomp": "S06", "TamSpec": "S06", "ResidualBurnside": "S06",
}
# Stage-5 rows (X.char, X.gal, X.iso) are registered but still "planned" in the report (section
# "Projected hypotheses"); they are not in this stage-4 table.  Move them into KIND/STAGE when the report is refreshed for stage 5.
SKIP = {"char", "gal", "iso"}
KIND_MACRO = {
    "lit": r"\kindlit", "oos": r"\kindoos", "infra": r"\kindinfra", "cond": r"\kindcond",
    "dis": r"\kinddis", "unclassified": r"\textbf{??}",
}


def tex_escape(s: str) -> str:
    """Escape a registry cell for a \\texttt / text context (keeps it ASCII-safe for pdflatex)."""
    s = s.replace("\\", r"\textbackslash{}")
    for a, b in (("_", r"\_"), ("&", r"\&"), ("%", r"\%"), ("#", r"\#"), ("{", r"\{"), ("}", r"\}")):
        s = s.replace(a, b)
    return s


def short_name(cell: str) -> str:
    m = re.search(r"`([^`]*)`", cell)
    full = m.group(1) if m else cell
    full = full.split()[0]                      # drop the arguments, e.g. `SA d q hq`
    return full.split(".")[-1]


def status_of(cell: str) -> str:
    c = cell.lower()
    if "discharged" in c:
        return "discharged"
    if "alias" in c:
        return "alias"
    if "schematic" in c:
        return "open (schematic)"
    return "open"


def rows(md: str):
    for line in md.splitlines():
        if not line.startswith("| `"):
            continue
        # split on "|" outside backtick code spans (a cell may contain `a|_b`)
        cells = [c.strip() for c in re.split(r"\|(?=(?:[^`]*`[^`]*`)*[^`]*$)", line.strip().strip("|"))]
        if len(cells) < 8:
            print(f"warning: short row skipped: {line[:60]}", file=sys.stderr)
            continue
        yield cells


def main(path: str) -> int:
    with open(path, encoding="utf-8") as fh:
        md = fh.read()
    out = []
    seen = set()
    for cells in rows(md):
        name = short_name(cells[0])
        st = status_of(cells[7])
        if st == "alias":
            continue                             # Hyp.EichlerMass alias: not a new hypothesis
        if name in seen or name in SKIP:
            continue
        seen.add(name)
        kind = KIND.get(name, "unclassified")
        if kind == "unclassified":
            print(f"warning: {name} has no KIND entry", file=sys.stderr)
        inst = "yes" if re.search(r"(proved|Tests?\.)", cells[5]) and not cells[5].startswith("none") else "none"
        if st == "discharged":
            inst = "yes"                         # a closed proof is an instance (table caption)
        ns = "GL2TF.Hyp" if cells[0].startswith("`GL2TF") else "Hyp"
        out.append(
            f"\\texttt{{{ns}.{tex_escape(name)}}} & {STAGE.get(name, '?')} & {KIND_MACRO[kind]} & "
            f"{inst} & {tex_escape(st)} \\\\"
        )
    sys.stdout.write("% SPDX-License-Identifier: CC-BY-4.0\n"
                     "% Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)\n")
    sys.stdout.write("% Generated by mathematics/report/tools/hyp_table.py from lean/Langlandscape/HYPOTHESES.md;"
                     " do not edit by hand.\n")
    sys.stdout.write("\n".join(out) + "\n")
    print(f"{len(out)} hypotheses", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "lean/Langlandscape/HYPOTHESES.md"))
