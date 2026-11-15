# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Copy result statements verbatim from mathematics/chapters/ into the final report.

Usage (from mathematics/final-report/):
    python3 -I tools/extract_statements.py /path/to/main.aux

main.aux is the aux file of a build of mathematics/main.tex (not committed; build artefact).
The statement bodies are copied unchanged, except that
  * \\label{...} is removed (the label is printed in the header instead),
  * \\ref{X}, \\eqref{X}, \\sfref{X} are replaced by the number of X in main.pdf
    (labels sec:stage-0N become "Stage 0N"; an unknown label is printed as \\texttt{X}).
Output: generated/statements-s0N.tex and generated/results-table.tex.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent          # mathematics/final-report
MATH = HERE.parent                                      # mathematics
CH = MATH / "chapters"

ENVS = r"theorem|proposition|corollary|conjecture|lemma|hypothesis|definition"
NAMES = {"theorem": "Theorem", "proposition": "Proposition", "corollary": "Corollary",
         "conjecture": "Conjecture", "lemma": "Lemma", "hypothesis": "Hypothesis", "definition": "Definition"}

# headline statements copied in full, per stage (order = order in the report)
SELECT = {
    "s01": ["thm:s01-mass", "thm:s01-JLclassical", "thm:s01-lambdaJL"],
    "s02": ["thm:s02-SA", "prop:s02-BG", "prop:s02-quot", "prop:s02-harm"],
    "s03": ["prop:s03-mazur", "prop:s03-phieis", "thm:s03-ribet", "cor:s03-ihara", "thm:s03-iharaH0",
            "conj:s03-iharaGL2"],
    "s04": ["lem:s04-ekills", "thm:s04-control", "thm:s04-lambdaribet", "thm:s04-Gor", "prop:s04-etaprinciple"],
    "s05": ["hyp:s05-X", "prop:s05-sign", "prop:s05-Xiso", "prop:s05-subquot", "prop:s05-Xlambda", "conj:s05-O2"],
    "s06": ["hyp:s06-H", "thm:s06-E", "prop:s06-galois", "thm:s06-defect", "cor:s06-allweights", "prop:s06-levM",
            "prop:s06-betti", "conj:s06-several"],
}
TABLE_ENVS = ("theorem", "proposition", "corollary", "conjecture")
STATUS_RE = re.compile(r"\\(st[a-z]+|provisional|leanplanned)\b")
# In several chapters (e.g. stage 02, s04/hsieh.tex, s04/vk.tex) the status is printed in the paragraph right
# after \end{theorem} etc.  That paragraph is captured verbatim when it starts with \noindent (or
# \begin{sloppypar}\noindent) and contains a status marker; it ends at the first blank line, \begin{proof},
# \end{sloppypar}, the next environment or a sectioning command.
TRAIL_STOP = re.compile(r"\n[ \t]*\n|\\begin\{proof\}|\\end\{sloppypar\}|\\begin\{(?:remark|lemma|theorem|proposition|"
                        r"corollary|conjecture|definition|hypothesis|interface|example)\}|\\(?:sub)*section\*?\{|\\paragraph\{")


def trailing_status(s, j):
    """Status paragraph following an environment that ends at s[j]; '' if there is none."""
    t = s[j:].lstrip()
    if t.startswith("\\begin{sloppypar}\\noindent"):
        t = t[len("\\begin{sloppypar}"):]
    elif not t.startswith("\\noindent"):
        return ""
    st = TRAIL_STOP.search(t)
    t = (t[:st.start()] if st else t).strip()
    return t if STATUS_RE.search(t) else ""


def read_aux(path):
    labels = {}
    for line in Path(path).read_text().splitlines():
        m = re.match(r"\\newlabel\{([^}]*)\}\{\{(.*?)\}\{(\d+)\}", line)
        if m:
            labels[m.group(1)] = (m.group(2), m.group(3))
    return labels


def parse_balanced(s, i, open_c, close_c):
    """s[i] == open_c; return index after the matching close_c."""
    depth = 0
    j = i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == open_c:
            depth += 1
        elif c == close_c:
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    raise ValueError("unbalanced")


def environments():
    out = []
    for f in sorted(CH.glob("s0*/*.tex")):
        stage = f.parent.name
        s = f.read_text()
        for m in re.finditer(r"\\begin\{(" + ENVS + r")\}", s):
            env = m.group(1)
            j = m.end()
            title = ""
            if j < len(s) and s[j] == "[":
                k = parse_balanced(s, j, "[", "]")
                title = s[j + 1:k - 1]
                j = k
            end = s.find("\\end{" + env + "}", j)
            body = s[j:end]
            trail = trailing_status(s, end + len("\\end{" + env + "}")) if env in TABLE_ENVS else ""
            lab = re.search(r"\\label\{([^}]*)\}", body[:400])
            out.append(dict(stage=stage, env=env, title=title, body=body, trail=trail,
                            label=lab.group(1) if lab else None, file=str(f.relative_to(MATH))))
    return out


def fmt_marks(text):
    marks = []
    for mk in STATUS_RE.findall(text):
        if mk not in marks and mk not in ("status",):
            marks.append(mk)
    marks_tex = ", ".join("\\" + mk + "{}" for mk in marks if mk != "provisional")
    if "provisional" in marks:
        marks_tex += (", " if marks_tex else "") + "\\textsf{\\small[provisional note]}"
    return marks_tex


def fix_refs(text, labels):
    text = re.sub(r"\\label\{[^}]*\}", "", text)

    def rep(m):
        cmd, lab = m.group(1), m.group(2)
        mm = re.match(r"sec:stage-0(\d)$", lab)
        if mm:
            return "Stage~0" + mm.group(1)
        if lab in labels and labels[lab][0]:
            num = labels[lab][0]
            return "(" + num + ")" if cmd == "eqref" else num
        return "\\texttt{" + lab.replace("_", "\\_") + "}"
    return re.sub(r"\\(ref|eqref|sfref)\{([^}]*)\}", rep, text)


def main():
    labels = read_aux(sys.argv[1])
    envs = environments()
    by_label = {e["label"]: e for e in envs if e["label"]}
    gen = HERE / "generated"
    gen.mkdir(exist_ok=True)
    hdr = ("% SPDX-License-Identifier: CC-BY-4.0\n"
           "% Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)\n"
           "% GENERATED by tools/extract_statements.py from mathematics/chapters/ -- do not edit by hand.\n")
    for stage, labs in SELECT.items():
        chunks = [hdr]
        for lab in labs:
            e = by_label[lab]
            num, page = labels.get(lab, ("?", "?"))
            title = fix_refs(e["title"], labels)
            body = fix_refs(e["body"], labels).strip("\n")
            if e["trail"]:
                body += ("\n\\par\\smallskip\\noindent{\\scriptsize\\itshape [Status paragraph following the statement "
                         "in the chapter:]}\\par\n" + fix_refs(e["trail"], labels))
            chunks.append(
                "\\begin{quoted}{%s}{%s}{%s}{%s}{%s}{%s}\n%s\n\\end{quoted}\n" % (
                    NAMES[e["env"]], num, page, lab.replace("_", "\\_"), title,
                    e["file"].replace("_", "\\_"), body))
        (gen / ("statements-%s.tex" % stage)).write_text("\n".join(chunks))
    # results table
    cap = ("\\caption{Every theorem, proposition, corollary and conjecture of \\texttt{mathematics/main.pdf} (number, page), "
           "with the status markers that occur inside its statement and, marked ``after the statement'', those of a status "
           "paragraph printed directly after it in the chapter (generated; \\texttt{\\textbackslash lean} refs = number "
           "of Lean cross-references in the statement). Mixed markers refer to different clauses; the statement in main.pdf "
           "is authoritative. A ``--'' means that no marker was found in either place, not that the result is proved. "
           "Rows are in the numerical order of main.pdf within each stage.}\\label{tab:allresults}\\\\")
    rows = [hdr, "\\begin{longtable}{@{}>{\\raggedright}p{0.13\\textwidth} >{\\raggedright}p{0.25\\textwidth} >{\\raggedright}p{0.30\\textwidth} >{\\raggedright\\arraybackslash}p{0.25\\textwidth}@{}}", cap,
            "\\toprule no.\\ (p.) & label & title & status markers\\\\\\midrule\\endfirsthead",
            "\\toprule no.\\ (p.) & label & title & status markers\\\\\\midrule\\endhead"]
    def numkey(e):
        num = labels.get(e["label"], ("", ""))[0]
        return (e["stage"], [int(x) for x in re.findall(r"\d+", num)])
    cur = None
    for e in sorted((e for e in envs if e["env"] in TABLE_ENVS and e["label"]), key=numkey):
        if e["stage"] != cur:
            cur = e["stage"]
            rows.append("\\multicolumn{4}{@{}l}{\\textbf{Stage %s}}\\\\" % cur[1:])
        num, page = labels.get(e["label"], ("?", "?"))
        marks_tex = fmt_marks(e["body"])
        nlean = len(re.findall(r"\\lean\{", e["body"]))
        if nlean:
            marks_tex += "; %d \\texttt{\\textbackslash lean} refs" % nlean
        if e["trail"]:
            marks_tex += ("; " if marks_tex else "") + "after the statement: " + fmt_marks(e["trail"])
        rows.append("%s %s (p.~%s) & \\texttt{\\footnotesize %s} & %s & %s\\\\" % (
            NAMES[e["env"]][:4] + ".", num, page, e["label"].replace("_", "\\_"),
            fix_refs(e["title"], labels), marks_tex or "--"))
    rows.append("\\bottomrule\\end{longtable}")
    (gen / "results-table.tex").write_text("\n".join(rows) + "\n")


if __name__ == "__main__":
    main()
