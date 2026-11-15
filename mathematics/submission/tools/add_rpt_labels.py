# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Insert an explicit \\label{rpt:<chapter label>} directly after the header of every quoted block
(\\begin{quoted}{kind}{number}{page}{label}{title}{file}) in the given .tex files, unless it is already there.
The flattener redirects \\ref{<chapter label>} to \\ref{rpt:<chapter label>} when it finds such a label.

Usage: python3 -I mathematics/submission/tools/add_rpt_labels.py FILE.tex [...]
"""
import sys


def groups(text, i, n):
    out = []
    for _ in range(n):
        while text[i] in " \t\n":
            i += 1
        assert text[i] == "{", text[i:i + 30]
        depth, j = 0, i
        while True:
            c = text[j]
            if c == "\\":
                j += 2
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        out.append(text[i + 1:j])
        i = j + 1
    return out, i


def main():
    for path in sys.argv[1:]:
        text = open(path, encoding="utf-8").read()
        res, i, n = [], 0, 0
        key = "\\begin{quoted}"
        while True:
            k = text.find(key, i)
            if k < 0:
                res.append(text[i:])
                break
            g, end = groups(text, k + len(key), 6)
            lab = "\\label{rpt:%s}" % g[3]
            res.append(text[i:end])
            if not text[end:end + len(lab) + 2].lstrip().startswith(lab):
                res.append(lab)
                n += 1
            i = end
        open(path, "w", encoding="utf-8").write("".join(res))
        print(path, n, "labels added")


if __name__ == "__main__":
    main()
