#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Flatten a modular LaTeX report into ONE self-contained .tex file (Mathathon submission rules).

  flatten.py MAIN.tex [-o report.tex] [options]      flatten, self-test, build PDF, run checks
  flatten.py --check report.tex [--repo DIR]         only run the rule checks on an existing flat file

What it does: inlines \\input/\\include/\\subfile/\\IfFileExists/\\InputIfFileExists, the primitive
\\@@input and \\usepackage of local .sty files; strips comments (keeps the SPDX line); replaces
biblatex/biber by an inlined \\begin{thebibliography} built from the .bib entries actually cited;
errors on \\includepdf (or substitutes a LaTeX source with --hyp-appendix / --pdf-substitute) and on
\\includegraphics (unless --allow-images); lists every figure/tikzpicture with its description status.
See README.md in this directory.  Python >= 3.8, standard library only (+ pdflatex for the self-test).
"""
import argparse, os, re, shutil, subprocess, sys, tempfile, unicodedata
from pathlib import Path

# ----------------------------------------------------------------------------- configuration
IDENT_WORDS = ["Fabian", "Januszewski", "Abhijit", "TITAN", "CONCEPTD", "drjanosch", "janosch",
               "gmail", "Paderborn", "Wuppertal", "Fabian's", "Abhijit's", "Jayanthan", "Aryampilly"]
IDENT_REGEXES = [r"[\w.+-]+@[\w-]+\.[\w.-]+", r"github\.com/"]  # e-mail addresses, GitHub URLs

SECTION_PATTERNS = [  # (number, name, regex on the lower-cased heading text)
    (1, "Abstract", r"^__abstract__$"),
    (2, "Introduction and motivation", r"introduc|motivation"),
    (3, "Setup and definitions", r"set-?up|definitions|preliminar|notation|conventions"),
    (4, "Our question / the integral Hecke-equivariant map", r"question|hecke-equivariant|equivariant map"),
    (5, "Why the Bruhat-Tits-tree route", r"bruhat|tree"),
    (6, "Proof outline", r"outline|stage by stage|stage-by-stage|proof strategy|the proof"),
    (7, "Main results (with status)", r"main results|results"),
    (8, "Lean section", r"lean"),
    (9, "Computations", r"computation"),
    (10, "Work during the event vs prior work", r"40|during the|prior work|event"),
    (11, "AI use", r"\bai\b|artificial|ai-assisted|ai use|use of ai"),
    (12, "Sources and acknowledgements", r"sources|acknowledg"),
    (13, "Limitations and next steps", r"limitation|next steps|open items|open problems"),
]

PROBLEM_TEXT = (
    "The Jacquet\u2013Langlands correspondence, established by Herv\u00e9 Jacquet and Robert Langlands in 1970, "
    "is a foundational result in number theory and representation theory. It links automorphic "
    "representations of GL(2) with those of the multiplicative group of a quaternion algebra, matching "
    "representations that share the same local data and L-functions. As one of the earliest proven cases of "
    "Langlands functoriality, it became an essential tool in modern arithmetic, including work leading to the "
    "proof of Fermat's Last Theorem.")

PDF_PRESETS = {  # pdf basename -> (tex body, extra preamble, bib)  (paths relative to the search roots)
    "standalone-hypotheses.pdf": ("report/hypotheses.tex", "report/hyp-preamble.tex", "report/hypotheses.bib"),
}

KEEP_LOCAL = False

class FlattenError(Exception):
    pass

def warn(msg):
    print("WARNING: " + msg, file=sys.stderr)

# ----------------------------------------------------------------------------- low-level text helpers
def read_group(text, pos, open_ch="{", close_ch="}"):
    """text[pos] must be open_ch; return (content, index after the matching close). Honours \\{ and \\}."""
    if pos >= len(text) or text[pos] != open_ch:
        raise FlattenError("expected %r at %d near %r" % (open_ch, pos, text[pos:pos + 40]))
    depth, i = 0, pos
    while i < len(text):
        c = text[i]
        if c == "\\":
            i += 2
            continue
        if c == open_ch:
            depth += 1
        elif c == close_ch:
            depth -= 1
            if depth == 0:
                return text[pos + 1:i], i + 1
        i += 1
    raise FlattenError("unbalanced braces near %r" % text[pos:pos + 60])

def skip_ws(text, i):
    while i < len(text) and text[i] in " \t\r\n":
        i += 1
    return i

VERB_ENVS = ("verbatim", "Verbatim", "lstlisting", "minted", "alltt")

def strip_comments(text, keep_header=False):
    """Remove % comments (not \\%, not inside verbatim / \\verb); comment-only lines disappear,
    trailing comments become a bare % (keeps TeX's end-of-line behaviour)."""
    out, header, in_verb, in_comment_env = [], [], None, False
    started = False
    for line in text.split("\n"):
        if in_comment_env:
            if re.match(r"\s*\\end\{comment\}", line):
                in_comment_env = False
            continue
        if in_verb:
            out.append(line)
            if re.search(r"\\end\{%s\}" % in_verb, line):
                in_verb = None
            continue
        if re.match(r"\s*\\begin\{comment\}", line):
            in_comment_env = True
            continue
        m = re.search(r"\\begin\{(%s)\*?\}" % "|".join(VERB_ENVS), line)
        i, cut = 0, None
        while i < len(line):
            c = line[i]
            if c == "\\":
                if line.startswith("verb", i + 1) and i + 5 < len(line):
                    j = i + 5
                    if line[j] == "*":
                        j += 1
                    if j < len(line) and not line[j].isalpha():
                        k = line.find(line[j], j + 1)
                        i = (k + 1) if k >= 0 else len(line)
                        continue
                i += 2
                continue
            if c == "%":
                cut = i
                break
            i += 1
        if m and (cut is None or m.start() < cut):
            in_verb = m.group(1)
            out.append(line)
            continue
        if cut is None:
            out.append(line.rstrip())
            started = True
            continue
        code, comment = line[:cut], line[cut:]
        if code.strip() == "":
            if keep_header and not started and re.search(r"SPDX-License|Copyright", comment):
                header.append(comment.rstrip())
            continue
        out.append(code.rstrip() + "%")
        started = True
    text2 = "\n".join(out)
    text2 = re.sub(r"\n{3,}", "\n\n", text2)
    return text2, header

# ----------------------------------------------------------------------------- the expander
class Flattener:
    def __init__(self, main, extra_roots=(), allow_images=False, subst=None, verbose=False):
        self.main = Path(main).resolve()
        self.maindir = self.main.parent
        roots = [self.maindir] + [Path(r).resolve() for r in extra_roots]
        p = self.maindir.parent
        while True:
            roots.append(p)
            if (p / ".git").exists() or p == p.parent:
                break
            p = p.parent
        seen, self.roots = set(), []
        for r in roots:
            if r not in seen:
                seen.add(r); self.roots.append(r)
        self.allow_images = allow_images
        self.subst = subst or {}            # pdf basename -> (body, preamble, bib)
        self.verbose = verbose
        self.bibfiles = []                  # resolved .bib paths in order
        self.used_files = []
        self.pending_preamble = []          # preamble snippets to inject before \begin{document}
        self.subst_used = []
        self.errors = []

    # -- file resolution (TeX would use the cwd; we also try the including file's dir and all ancestors)
    def resolve(self, name, curdir, exts=("", ".tex")):
        name = name.strip().strip('"')
        cands = [curdir] + self.roots
        for d in cands:
            for e in exts:
                p = (Path(d) / (name + e)) if not name.endswith(e) or e == "" else None
                if p is None:
                    continue
                p = p.resolve() if p.exists() else p
                if p.is_file():
                    return p
        return None

    def load(self, path, keep_header=False):
        raw = Path(path).read_text(encoding="utf-8")
        self.used_files.append(str(path))
        return strip_comments(raw, keep_header)

    # -- main recursion
    CMD = re.compile(
        r"\\(?P<cmd>@@input|input|include|subfile|IfFileExists|InputIfFileExists|addbibresource|bibliography"
        r"|usepackage|RequirePackage|includepdf|includegraphics|documentclass)(?![A-Za-z@])")

    def expand(self, text, curdir, depth=0, stack=()):
        if depth > 30:
            raise FlattenError("include depth > 30 (cycle?) at " + " -> ".join(stack))
        out, i = [], 0
        while True:
            m = self.CMD.search(text, i)
            if not m:
                out.append(text[i:])
                break
            cmd, start = m.group("cmd"), m.start()
            j = m.end()
            # ------ commands that take a brace argument (possibly after optional [..])
            if cmd in ("input", "@@input"):
                k = skip_ws(text, j) if cmd == "@@input" or text[j:j + 1] in " \t\n" else j
                if k < len(text) and text[k] == "{":
                    arg, end = read_group(text, k)
                else:  # primitive: \input name<space>
                    mm = re.match(r"([^\s{}\\]+)\s?", text[k:])
                    if not mm:
                        out.append(text[i:j]); i = j; continue
                    arg, end = mm.group(1), k + mm.end()
                out.append(text[i:start])
                out.append(self.inline_file(arg, curdir, depth, stack, text, start, end, primitive=(cmd == "@@input")))
                i = end; continue
            if cmd in ("include", "subfile"):
                k = skip_ws(text, j)
                arg, end = read_group(text, k)
                out.append(text[i:start])
                out.append(self.inline_file(arg, curdir, depth, stack, text, start, end))
                i = end; continue
            if cmd in ("IfFileExists", "InputIfFileExists"):
                k = skip_ws(text, j)
                arg, k = read_group(text, k)
                tru, k = read_group(text, skip_ws(text, k))
                fal, end = read_group(text, skip_ws(text, k))
                p = self.resolve(arg, curdir, exts=("",) if "." in Path(arg).name else ("", ".tex"))
                out.append(text[i:start])
                if p is not None:
                    pre = ""
                    if cmd == "InputIfFileExists":
                        pre = self.inline_file(arg, curdir, depth, stack, text, start, end)
                    out.append(pre + self.expand(tru, curdir, depth + 1, stack))
                else:
                    out.append(self.expand(fal, curdir, depth + 1, stack))
                i = end; continue
            if cmd == "addbibresource":
                k = skip_ws(text, j)
                if text[k:k + 1] == "[":
                    _, k = read_group(text, k, "[", "]")
                arg, end = read_group(text, k)
                p = self.resolve(arg, curdir, exts=("",))
                if p is None:
                    self.errors.append("bib resource not found: %s (from %s)" % (arg, curdir))
                elif p not in self.bibfiles:
                    self.bibfiles.append(p)
                out.append(text[i:start]); i = end; continue
            if cmd == "bibliography":
                k = skip_ws(text, j)
                arg, end = read_group(text, k)
                for n in arg.split(","):
                    p = self.resolve(n.strip(), curdir, exts=(".bib", ""))
                    if p is None:
                        self.errors.append("bib file not found: %s" % n)
                    elif p not in self.bibfiles:
                        self.bibfiles.append(p)
                out.append(text[i:start] + "\\printbibliography"); i = end; continue
            if cmd in ("usepackage", "RequirePackage"):
                k = j
                opts = ""
                kk = skip_ws(text, k)
                if text[kk:kk + 1] == "[":
                    opts, kk = read_group(text, kk, "[", "]")
                if text[kk:kk + 1] != "{":
                    out.append(text[i:j]); i = j; continue
                arg, end = read_group(text, kk)
                names = [n.strip() for n in arg.split(",") if n.strip()]
                keep, inl = [], []
                for n in names:
                    if n in ("biblatex", "pdfpages"):
                        continue          # replaced by thebibliography / forbidden
                    p = self.resolve(n, curdir, exts=(".sty",)) if (curdir / (n + ".sty")).exists() or any((r / (n + ".sty")).exists() for r in self.roots) else None
                    (inl if p else keep).append((n, p))
                out.append(text[i:start])
                if keep:
                    out.append("\\usepackage%s{%s}" % ("[%s]" % opts if opts else "", ",".join(n for n, _ in keep)))
                for n, p in inl:
                    body, _ = self.load(p)
                    body = re.sub(r"\\(ProvidesPackage|NeedsTeXFormat)\s*(\{[^}]*\})?(\[[^\]]*\])?", "", body)
                    out.append("\\makeatletter\n%s\n\\makeatother" % self.expand(body, p.parent, depth + 1, stack + (str(p),)))
                i = end; continue
            if cmd == "includepdf":
                k = skip_ws(text, j)
                if text[k:k + 1] == "[":
                    _, k = read_group(text, k, "[", "]")
                arg, end = read_group(text, skip_ws(text, k))
                base = Path(arg).name
                if base in self.subst:
                    body, pre, bib = self.subst[base]
                    out.append(text[i:start])
                    self.subst_used.append(base)
                    if pre:
                        pp = self.resolve(pre, curdir)
                        if not pp: raise FlattenError("substitute preamble not found: " + pre)
                        ptext, _ = self.load(pp)
                        self.pending_preamble.append(self.expand(ptext, pp.parent, depth + 1, stack + (str(pp),)))
                    if bib:
                        bp = self.resolve(bib, curdir, exts=("",))
                        if bp and bp not in self.bibfiles:
                            self.bibfiles.append(bp)
                    out.append("\\input{%s}" % body)       # re-scanned on the next loop pass
                    text = text[:end] if False else text   # (no-op, keeps flow explicit)
                    # splice the \input into the stream and re-expand it here
                    sub = self.expand("\\input{%s}" % body, curdir, depth + 1, stack)
                    out[-1] = sub
                    i = end; continue
                self.errors.append("\\includepdf{%s}: pdfpages is forbidden (use --hyp-appendix or --pdf-substitute %s=TEXFILE)" % (arg, base))
                out.append(text[i:end]); i = end; continue
            if cmd == "includegraphics":
                k = skip_ws(text, j)
                if text[k:k + 1] == "[":
                    _, k = read_group(text, k, "[", "]")
                arg, end = read_group(text, skip_ws(text, k))
                if not self.allow_images:
                    self.errors.append("\\includegraphics{%s}: images are not allowed (describe the figure in words; --allow-images to override)" % arg)
                else:
                    warn("\\includegraphics{%s} kept (--allow-images); the output is NOT self-contained" % arg)
                out.append(text[i:end]); i = end; continue
            if cmd == "documentclass":
                if depth > 0:
                    raise FlattenError("\\documentclass inside an included file (%s)" % (stack[-1] if stack else "?"))
                out.append(text[i:j]); i = j; continue
        return "".join(out)

    def inline_file(self, arg, curdir, depth, stack, text, start, end, primitive=False):
        p = self.resolve(arg, curdir)
        if p is None:
            raise FlattenError("file not found: \\input{%s} (in %s; searched %s)" % (arg, curdir, ", ".join(map(str, self.roots[:4]))))
        if str(p) in stack:
            raise FlattenError("include cycle: " + " -> ".join(stack + (str(p),)))
        body, _ = self.load(p)
        if re.search(r"\\documentclass|\\begin\{document\}", body):
            raise FlattenError("%s is a standalone document (\\documentclass/\\begin{document}); cannot inline" % p)
        if self.verbose:
            print("  " * depth + "inline %s" % p, file=sys.stderr)
        body = self.expand(body, p.parent, depth + 1, stack + (str(p),))
        ls = text.rfind("\n", 0, start) + 1
        le = text.find("\n", end)
        le = len(text) if le < 0 else le
        alone = text[ls:start].strip() == "" and text[end:le].strip() == ""
        body = body.strip("\n")
        if alone:
            return body
        # inline inside an argument/macro: no blank lines (\par) and, for the primitive, doubled #
        body = re.sub(r"\n\s*\n", "\n", body).strip()
        if primitive:
            body = body.replace("#", "##")
        return body

    def run(self):
        text, header = self.load(self.main, keep_header=True)
        self.header = header
        flat = self.expand(text, self.maindir, 0, (str(self.main),))
        if self.pending_preamble:
            inj = "\n".join(self.pending_preamble)
            if "\\begin{document}" not in flat:
                raise FlattenError("no \\begin{document} in the main file")
            flat = flat.replace("\\begin{document}", inj + "\n\\begin{document}", 1)
        return flat


# ----------------------------------------------------------------------------- external references
REF_RE = re.compile(r"\\(?P<cmd>ref|eqref|cref|Cref|autoref|vref|pageref)\*?\s*\{(?P<labs>[^}]*)\}")
HREF_RE = re.compile(r"\\hyperref\s*\[(?P<lab>[^\]]*)\]\s*\{")
KIND_BY_PREFIX = {"thm": "Theorem", "prop": "Proposition", "lem": "Lemma", "cor": "Corollary", "def": "Definition",
                  "rem": "Remark", "hyp": "Hypothesis", "ex": "Example", "conj": "Conjecture", "if": "Interface",
                  "tc": "Test case", "sec": "Section", "ss": "Section", "sub": "Section", "eq": "Equation",
                  "tab": "Table", "fig": "Figure", "ch": "Chapter", "stage": "Section"}
KIND_BY_ANCHOR = {"theorem": "Theorem", "section": "Section", "subsection": "Section", "subsubsection": "Section",
                  "chapter": "Chapter", "equation": "Equation", "table": "Table", "figure": "Figure",
                  "Item": "Item", "enumi": "Item", "page": "Page"}
PRE_WORD = re.compile(r"(Thm|Theorem|Prop|Proposition|Cor|Corollary|Lem|Lemma|Rem|Remark|Hyp|Hypothesis|Def|Definition|"
                      r"Ex|Example|Sect?|Section|Stage|Conj|Conjecture|Eq|Equation|Chapter|Ch|Table|Fig|Figure|Interface)s?\.?(~|\s)\s*$")

def parse_aux(path):
    """label -> (number, anchor-type) from \\newlabel entries of main.aux"""
    labs = {}
    for m in re.finditer(r"\\newlabel\{([^}]+)\}\{\{([^{}]*)\}\{([^{}]*)\}", Path(path).read_text(encoding="utf-8", errors="replace")):
        rest = Path(path).read_text(encoding="utf-8", errors="replace")[m.end():m.end() + 300]
        anc = re.search(r"\}\{([A-Za-z]+)[.\w-]*\}", rest)
        labs[m.group(1)] = (m.group(2), anc.group(1) if anc else "")
    return labs

ABBR = {"Theorem": "Thm", "Proposition": "Prop", "Corollary": "Cor", "Lemma": "Lem", "Remark": "Rem", "Hypothesis": "Hyp",
        "Definition": "Def", "Section": "Sec", "Equation": "Eq", "Example": "Ex", "Conjecture": "Conj", "Interface": "Interface",
        "Chapter": "Ch", "Table": "Table", "Figure": "Fig", "Test case": "Test", "Item": "Item", "Page": "p."}

def pointer(label, num, anchor, cmd):
    """The one pointer format: '[chapters, Thm~21.5]' (numbers of main.pdf); equations '(chapters, Eq~(2.1))'."""
    pre = label.split(":")[0].lower() if ":" in label else ""
    kind = KIND_BY_PREFIX.get(pre) or KIND_BY_ANCHOR.get(anchor, "")
    if cmd == "pageref":
        kind = "Page"
    if cmd == "eqref":
        kind, num = "Equation", "(%s)" % num
    return "chapters, %s%s" % (ABBR.get(kind, kind) + "~" if kind else "", num)

def externalize_refs(flat, aux):
    """\\ref-family commands whose label L is not \\label'ed in `flat`:
    (1) the report defines rpt:L -> `\\cmd{rpt:L} [chapters, Thm~21.5]`;
    (2) else L in main.aux -> `[chapters, Thm~21.5]` only (a preceding 'Thm.~' is dropped), listed as external-only;
    (3) else unresolved. \\hyperref[L]{t} -> t. returns (flat, n_rpt, external_only{label:pointer}, unresolved)"""
    defined = set(re.findall(r"\\label\{([^}]*)\}", flat))
    unresolved, ext_only, nrpt = [], {}, [0]
    def one(lab, cmd):
        lab = lab.strip()
        if lab in defined or lab.startswith("#"):
            return None
        ptr = pointer(lab, *aux[lab], cmd) if lab in aux else None
        if "rpt:" + lab in defined:
            nrpt[0] += 1
            return "\\%s{rpt:%s}%s" % (cmd, lab, " [%s]" % ptr if ptr else "")
        if ptr:
            ext_only[lab] = ptr
            return "[%s]" % ptr
        unresolved.append(lab)
        return None
    out, i = [], 0
    pat = re.compile(REF_RE.pattern + "|" + HREF_RE.pattern)
    while True:
        m = pat.search(flat, i)
        if not m:
            out.append(flat[i:]); break
        if m.group("cmd"):
            labs = m.group("labs").split(",")
            reps = [one(l, m.group("cmd")) for l in labs]
            chunk = flat[i:m.start()]
            if all(r is None for r in reps):
                out.append(chunk + m.group(0))
            else:
                if reps[0] is not None and reps[0].startswith("[chapters"):
                    chunk = re.sub(PRE_WORD.pattern, "", chunk)   # 'Thm.~' + '[chapters, Thm~21.5]' -> '[chapters, Thm~21.5]'
                out.append(chunk + ", ".join(r if r is not None else "\\%s{%s}" % (m.group("cmd"), l.strip()) for r, l in zip(reps, labs)))
            i = m.end()
        else:  # \hyperref[lab]{text} -> text for labels not defined in the report
            txt, end = read_group(flat, m.end() - 1)
            lab = m.group("lab").strip()
            out.append(flat[i:m.start()])
            if lab not in defined and ("rpt:" + lab in defined or lab in aux):
                out.append(txt)
                if "rpt:" + lab not in defined:
                    ext_only[lab] = pointer(lab, *aux[lab], "ref")
            else:
                if lab not in defined: unresolved.append(lab)
                out.append(flat[m.start():end])
            i = end
    return "".join(out), nrpt[0], ext_only, sorted(set(unresolved))

def find_aux(roots):
    for r in roots:
        for c in (r / "main.aux", r / "mathematics" / "main.aux"):
            if c.is_file():
                return c
    return None

# ----------------------------------------------------------------------------- bibliography
def parse_bib(text):
    entries, strings = {}, {"jan": "January", "feb": "February", "mar": "March", "apr": "April", "may": "May",
                            "jun": "June", "jul": "July", "aug": "August", "sep": "September", "oct": "October",
                            "nov": "November", "dec": "December"}
    i = 0
    while True:
        i = text.find("@", i)
        if i < 0:
            break
        m = re.match(r"@\s*([A-Za-z]+)\s*([{(])", text[i:])
        if not m:
            i += 1; continue
        typ = m.group(1).lower()
        op = m.group(2)
        cl = "}" if op == "{" else ")"
        try:
            body, end = read_group(text, i + m.end() - 1, op, cl)
        except FlattenError:
            break
        i = end
        if typ in ("comment", "preamble"):
            continue
        if typ == "string":
            mm = re.match(r"\s*([^=\s]+)\s*=\s*(.*)", body, re.S)
            if mm:
                strings[mm.group(1).lower()] = parse_value(mm.group(2), strings)
            continue
        mm = re.match(r"\s*([^,\s]+)\s*,(.*)", body, re.S)
        if not mm:
            continue
        key, rest = mm.group(1), mm.group(2)
        fields, k = {}, 0
        while k < len(rest):
            fm = re.compile(r"\s*,?\s*([A-Za-z_][\w-]*)\s*=\s*").match(rest, k)
            if not fm:
                break
            k = fm.end()
            val, k = parse_value_at(rest, k, strings)
            fields[fm.group(1).lower()] = val
        entries[key] = (typ, fields)
    return entries

def parse_value_at(s, k, strings):
    parts = []
    while True:
        k = skip_ws(s, k)
        if k >= len(s):
            break
        c = s[k]
        if c == "{":
            v, k = read_group(s, k); parts.append(v)
        elif c == '"':
            j, depth = k + 1, 0
            while j < len(s) and not (s[j] == '"' and depth == 0):
                if s[j] == "{": depth += 1
                elif s[j] == "}": depth -= 1
                elif s[j] == "\\": j += 1
                j += 1
            parts.append(s[k + 1:j]); k = j + 1
        else:
            mm = re.compile(r"[^\s,#}]+").match(s, k)
            if not mm:
                break
            tok = mm.group(0)
            parts.append(strings.get(tok.lower(), tok) if not tok.isdigit() else tok)
            k = mm.end()
        k2 = skip_ws(s, k)
        if k2 < len(s) and s[k2] == "#":
            k = k2 + 1
            continue
        break
    return re.sub(r"\s+", " ", "".join(parts)).strip(), k

def parse_value(s, strings):
    return parse_value_at(s, 0, strings)[0]

def split_names(s):
    out, depth, cur, i = [], 0, "", 0
    toks = re.split(r"(\{|\})", s)
    flat = ""
    for t in toks:
        flat += t
    parts, buf, depth = [], "", 0
    i = 0
    while i < len(s):
        c = s[i]
        if c == "{": depth += 1
        elif c == "}": depth -= 1
        if depth == 0 and re.match(r"\s+and\s+", s[i:]) and True:
            mm = re.match(r"\s+and\s+", s[i:])
            parts.append(buf); buf = ""; i += mm.end(); continue
        buf += c; i += 1
    parts.append(buf)
    return [p.strip() for p in parts if p.strip()]

def person(n):
    """return (display 'First Last', surname)"""
    n = n.strip()
    if n.startswith("{") and n.endswith("}") and read_group(n, 0)[1] == len(n):
        return n[1:-1], n[1:-1]            # corporate name
    depth, commas = 0, []
    for i, c in enumerate(n):
        if c == "{": depth += 1
        elif c == "}": depth -= 1
        elif c == "," and depth == 0: commas.append(i)
    if commas:
        last = n[:commas[0]].strip()
        first = n[commas[-1] + 1:].strip()
        jr = n[commas[0] + 1:commas[-1]].strip() if len(commas) > 1 else ""
        return " ".join(x for x in (first, last, jr) if x), last
    words = n.split()
    if len(words) == 1:
        return n, n
    # von parts: lower-case words stay with the surname
    i = len(words) - 1
    while i > 1 and words[i - 1][:1].islower():
        i -= 1
    return n, " ".join(words[i:])

def ascii_letters(s):
    s = re.sub(r"\\[`'^\"~=.uvHcdbk]\s*\{?([A-Za-z])\}?", r"\1", s)
    s = re.sub(r"\\(ss|o|O|ae|AE|oe|OE|l|L|aa|AA)\b", lambda m: {"ss": "s", "o": "o", "O": "O", "ae": "a", "AE": "A", "oe": "o", "OE": "O", "l": "l", "L": "L", "aa": "a", "AA": "A"}[m.group(1)], s)
    s = unicodedata.normalize("NFKD", s)
    return re.sub(r"[^A-Za-z]", "", s)

def make_labels(keys, entries):
    labels, used = {}, {}
    for k in keys:
        typ, f = entries[k]
        names = split_names(f.get("author") or f.get("editor") or "")
        sur = [ascii_letters(person(n)[1]) for n in names]
        if not sur:
            base = ascii_letters(f.get("title", k))[:3] or k[:3]
        elif len(sur) == 1:
            base = sur[0][:3]
        elif len(sur) <= 4:
            base = "".join(s[:1] for s in sur)
        else:
            base = "".join(s[:1] for s in sur[:3]) + "+"
        y = re.search(r"\d{4}", f.get("year", f.get("date", "")) or "")
        yy = y.group(0)[2:] if y else ""
        lab = (base[:1].upper() + base[1:]) + yy
        labels[k] = lab
        used.setdefault(lab, []).append(k)
    for lab, ks in used.items():
        if len(ks) > 1:
            for n, k in enumerate(sorted(ks)):
                labels[k] = lab + chr(ord("a") + n)
    return labels

def clean_url(v):
    return v.replace("\\_", "_").replace("\\%", "%").replace("\\&", "&").replace("\\#", "#").strip()

def format_entry(key, entries):
    typ, f = entries[key]
    if "crossref" in f and f["crossref"] in entries:
        pf = entries[f["crossref"]][1]
        for kk, vv in pf.items():
            if kk == "title":
                f.setdefault("booktitle", vv)
            else:
                f.setdefault(kk, vv)
    g = lambda *ks: next((f[k] for k in ks if f.get(k)), "")
    names = split_names(f.get("author", ""))
    people = [person(n)[0] for n in names]
    if not people and f.get("editor"):
        people = [person(n)[0] for n in split_names(f["editor"])]
        people[-1] += " (ed.)" if len(people) == 1 else " (eds.)"
    if len(people) > 2:
        auth = ", ".join(people[:-1]) + ", and " + people[-1]
    else:
        auth = " and ".join(people)
    title = g("title")
    sub = g("subtitle")
    if sub:
        title += ": " + sub
    year = g("year")
    if not year and g("date"):
        year = g("date")[:4]
    parts = []
    if auth:
        parts.append(auth)
    pages = g("pages").replace("---", "--")
    if typ == "article":
        if title: parts.append(title)
        j = g("journal", "journaltitle")
        s = "\\emph{%s}" % j if j else ""
        if g("volume"): s += " \\textbf{%s}" % g("volume")
        if year: s += " (%s)" % year
        if g("number"): s += ", no.~%s" % g("number")
        if pages: s += ", pp.~%s" % pages if "-" in pages else ", p.~%s" % pages
        if g("eid"): s += ", %s" % g("eid")
        parts.append(s.strip())
    elif typ in ("incollection", "inproceedings", "inbook", "conference"):
        if title: parts.append(title)
        s = "In: \\emph{%s}" % g("booktitle") if g("booktitle") else ""
        ed = split_names(g("editor")) if g("editor") and f.get("author") else []
        if ed:
            s += ", ed.~" + " and ".join(person(n)[0] for n in ed)
        if g("series"): s += ", " + g("series") + (" %s" % g("number", "volume") if g("number", "volume") else "")
        if g("publisher"): s += ", " + g("publisher")
        if g("address", "location"): s += ", " + g("address", "location")
        if year: s += ", " + year
        if pages: s += ", pp.~%s" % pages
        parts.append(s.strip(", "))
    else:  # book, thesis, report, misc, online, unpublished, ...
        if title:
            parts.append("\\emph{%s}" % title if typ in ("book", "mvbook", "collection", "proceedings", "phdthesis", "mastersthesis", "thesis") else title)
        s = []
        if typ in ("phdthesis", "mastersthesis", "thesis") and g("school", "institution"): s.append(g("school", "institution"))
        if typ in ("techreport", "report"):
            s.append(g("type") or "Technical report")
            if g("institution"): s.append(g("institution"))
        if g("edition"): s.append("%s ed." % g("edition") if g("edition").isdigit() else g("edition"))
        if g("series"): s.append(g("series") + (" %s" % g("number", "volume") if g("number", "volume") else ""))
        if g("publisher"): s.append(g("publisher"))
        if g("howpublished"): s.append(g("howpublished"))
        if g("address", "location"): s.append(g("address", "location"))
        if year and year not in g("howpublished"): s.append(year)   # no repeated year when howpublished has it
        if s: parts.append(", ".join(s))
    note = g("note")
    if not KEEP_LOCAL:   # internal pointers such as "local: literature/x.pdf; verified Sec. 3" are dropped
        note = re.sub(r"local:\s*\S+\.pdf;?\s*", "", note).strip()
    if note: parts.append(note)
    txt = ". ".join(p.rstrip(".") for p in parts if p) + "."
    if g("doi"):
        d = clean_url(g("doi")).replace("https://doi.org/", "")
        txt += " \\url{https://doi.org/%s}" % d
    elif g("url"):
        txt += " \\url{%s}" % clean_url(g("url"))
    if g("eprint") and not g("doi"):
        txt += " arXiv:%s" % clean_url(g("eprint")) if (g("eprinttype", "archiveprefix") or "arxiv").lower() == "arxiv" else " %s" % g("eprint")
    return txt

CITE_RE = re.compile(
    r"\\(?P<cmd>[Pp]arencite|[Tt]extcite|[Aa]utocite|footcitetext|footcite|citep|citet|cite|Cite|fullcite|footfullcite|smartcite|nocite)"
    r"(?P<star>\*?)(?P<opts>(?:\s*\[[^\]]*\]){0,2})\s*\{(?P<keys>[^}]*)\}")

def convert_cites(flat):
    keys = []
    def sub(m):
        cmd = m.group("cmd")
        ks = [k.strip() for k in m.group("keys").split(",") if k.strip()]
        real = [k for k in ks if not k.startswith("#")]
        if "*" in real:
            raise FlattenError("\\nocite{*} is not supported")
        for k in real:
            if k not in keys:
                keys.append(k)
        opts = re.findall(r"\[([^\]]*)\]", m.group("opts"))
        note = " ".join(o.strip() for o in opts if o.strip())
        o = "[%s]" % note if note else ""
        if cmd == "nocite":
            return "\\nocite{%s}" % m.group("keys")
        c = "\\cite%s{%s}" % (o, m.group("keys"))
        if cmd in ("footcite", "footcitetext"):
            return "\\footnote{%s}" % c
        return c
    return CITE_RE.sub(sub, flat), keys

def build_bibliography(keys, bibfiles):
    entries = {}
    for bf in bibfiles:
        for k, v in parse_bib(Path(bf).read_text(encoding="utf-8", errors="replace")).items():
            if k in entries and entries[k] != v:
                warn("duplicate bib key %s (kept the first; also in %s)" % (k, bf))
            entries.setdefault(k, v)
    missing = [k for k in keys if k not in entries]
    have = [k for k in keys if k in entries]
    labels = make_labels(have, entries)
    order = sorted(have, key=lambda k: (labels[k].lower(), k))
    width = max((labels[k] for k in order), key=len, default="99")
    lines = ["\\begin{thebibliography}{%s}" % width]
    for k in order:
        lines.append("\\bibitem[%s]{%s} %s" % (labels[k], k, format_entry(k, entries)))
    lines.append("\\end{thebibliography}")
    return "\n".join(lines), missing, len(entries)

# ----------------------------------------------------------------------------- figure report
def figure_report(flat):
    rows = []
    for m in re.finditer(r"\\begin\{(figure\*?)\}(.*?)\\end\{\1\}", flat, re.S):
        body = m.group(2)
        cap = re.search(r"\\caption\s*(\[[^\]]*\])?\s*\{", body)
        words = 0
        if cap:
            c, _ = read_group(body, cap.end() - 1)
            words = len(re.findall(r"[A-Za-z]{2,}", re.sub(r"\\[A-Za-z]+|\$[^$]*\$", " ", c)))
        lab = re.search(r"\\label\{([^}]*)\}", body)
        line = flat.count("\n", 0, m.start()) + 1
        rows.append(("figure", line, lab.group(1) if lab else "-", bool(cap), words, "tikz" if "tikzpicture" in body else "other"))
    spans = [(m.start(), m.end()) for m in re.finditer(r"\\begin\{(figure\*?)\}(.*?)\\end\{\1\}", flat, re.S)]
    for m in re.finditer(r"\\begin\{(tikzpicture|tikzcd)\}", flat):
        if not any(a <= m.start() < b for a, b in spans):
            rows.append(("bare " + m.group(1), flat.count("\n", 0, m.start()) + 1, "-", False, 0, "tikz"))
    return rows

# ----------------------------------------------------------------------------- checks
def title_span(flat):
    starts = [m.start() for m in re.finditer(r"\\(title|author|address|curraddr|email|thanks)\b", flat)]
    mt = re.search(r"\\maketitle", flat)
    if not mt:
        return None
    s = min(starts) if starts else mt.start()
    if s > mt.start():
        s = mt.start()
    return (s, mt.end())

def norm_letters(s):
    s = re.sub(r"\\mathrm\{([^}]*)\}", r"\1", s)
    s = re.sub(r"\\(GL|SL|PGL)\b", r"\1", s)
    s = re.sub(r"\\[`'^\"~=.]\s*\{?([A-Za-z])\}?", r"\1", s)   # accents
    s = re.sub(r"\\[a-zA-Z]+\*?", " ", s)
    s = unicodedata.normalize("NFKD", s)
    return re.sub(r"[^A-Za-z0-9]", "", s).lower()

def lineno(text, pos):
    return text.count("\n", 0, pos) + 1

def run_checks(flat, ident_words, draft=False, log_info=None, repo=None, pdf=None):
    """returns list of (id, requirement, status, detail); status in PASS/FAIL/WARN/SKIP"""
    R = []
    add = lambda i, req, st, d="": R.append((i, req, st, d))
    # A1 forbidden commands
    bad = re.compile(r"\\(input|include|subfile|includeonly|addbibresource|bibliography|bibliographystyle|printbibliography|includepdf|includegraphics|import|subimport)(?![A-Za-z@])|\\usepackage(\[[^\]]*\])?\{[^}]*(pdfpages|biblatex|graphicx)[^}]*\}")
    hits = [(lineno(flat, m.start()), m.group(0)) for m in bad.finditer(flat)]
    add("A1", "no \\input/\\include/\\addbibresource/\\bibliography/\\includepdf/\\includegraphics/biblatex/pdfpages",
        "FAIL" if hits else "PASS", "; ".join("L%d %s" % h for h in hits[:6]))
    # A13 own-work bibliography entries carry no author names (title, version, year, DOI only)
    mb = re.search(r"\\begin\{thebibliography\}.*?\\end\{thebibliography\}", flat, re.S)
    bibtxt = mb.group(0) if mb else ""
    bibhits = sorted({w for w in ("Januszewski", "Jayanthan", "Aryampilly", "Abhijit", "Fabian", "drjanosch") if w in bibtxt})
    add("A13", "no team-member names in any bibliography entry (own prior work cited by title/version/year/DOI only)",
        "FAIL" if bibhits else "PASS", ", ".join(bibhits))
    # A2 bibliography inline
    has_bib = "\\begin{thebibliography}" in flat
    nocite = len(re.findall(r"\\(cite|parencite|textcite)\b", flat))
    add("A2", "bibliography inlined as \\begin{thebibliography}", "PASS" if has_bib else ("FAIL" if nocite else "WARN"),
        "" if has_bib else "no thebibliography")
    # A3 single doc
    nd = len(re.findall(r"\\documentclass", flat))
    add("A3", "exactly one \\documentclass / one \\begin{document}", "PASS" if nd == 1 and flat.count("\\begin{document}") == 1 else "FAIL", "")
    # A4 figures
    figs = figure_report(flat)
    badf = [f for f in figs if f[0] == "figure" and f[4] < 12]
    bare = [f for f in figs if f[0] != "figure"]
    add("A4", "every figure/tikzpicture has a textual description (caption >= 12 words)",
        "FAIL" if badf else ("WARN" if bare else "PASS"),
        "%d figure env(s); no/short caption: %s; bare tikz (check adjacent prose): %s" % (
            len([f for f in figs if f[0] == "figure"]), [f[1] for f in badf], [f[1] for f in bare]))
    # A5 title block
    ts = title_span(flat)
    if ts is None:
        add("A5", "title block present (\\maketitle)", "FAIL", "no \\maketitle")
        tb = ""
    else:
        tb = flat[ts[0]:ts[1]]
        # expand a hash macro used in the title block (e.g. \PublicCommitHash defined in the preamble)
        for mname in set(re.findall(r"\\([A-Za-z]*CommitHash)\b", tb)):
            md = re.search(r"\\newcommand\{\\" + mname + r"\}\{([^{}]*)\}", flat)
            if md:
                tb = tb.replace("\\" + mname, md.group(1))
        problems = []
        if not (re.search(r"Abhijit", tb) and re.search(r"Januszewski", tb)):
            problems.append("both author names")
        if not re.search(r"https?://\S+|\\url\{|\\href\{", tb):
            problems.append("repository link")
        if not re.search(r"\b[0-9a-f]{40}\b", tb):
            problems.append("FULL 40-hex commit hash")
        if re.search(r"TODO|PLACEHOLDER|\\TODOFACT", tb, re.I):
            problems.append("placeholders still in title block")
        if not re.search(r"affiliation|university|universit|institut|department|\\address", tb, re.I):
            problems.append("affiliations")
        add("A5", "title block: names, affiliations, repository link, full 40-hex commit hash",
            ("FAIL" if not draft else "WARN") if problems else "PASS", "missing/open: " + ", ".join(problems) if problems else "")
    # A6 identifying info outside the title block
    rest = flat if ts is None else flat[:ts[0]] + flat[ts[1]:]
    offs = []
    for w in ident_words:
        for m in re.finditer(re.escape(w), rest, re.I):
            offs.append((lineno(rest, m.start()), w))
    for rx in IDENT_REGEXES:
        for m in re.finditer(rx, rest, re.I):
            offs.append((lineno(rest, m.start()), m.group(0)))
    offs = sorted(set(offs))
    add("A6", "no identifying info outside the title block (names, nodes, GitHub users, e-mails)",
        "FAIL" if offs else "PASS", "%d hit(s): %s" % (len(offs), "; ".join("L%d %r" % o for o in offs[:10])) if offs else "")
    # A7 required sections
    heads = [("__abstract__", 0)] if re.search(r"\\begin\{abstract\}", flat) else []
    for m in re.finditer(r"\\(?:chapter|section)\*?\s*(?:\[[^\]]*\])?\s*\{", flat):
        try:
            t, _ = read_group(flat, m.end() - 1)
        except FlattenError:
            continue
        heads.append((re.sub(r"\\texorpdfstring\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}\{[^{}]*\}", r"\1", t).lower(), m.start()))
    missing, seq = [], []
    for num, name, rx in SECTION_PATTERNS:
        hit = next(((t, p) for t, p in heads if re.search(rx, t)), None)
        if not hit:
            missing.append("%d %s" % (num, name))
        else:
            seq.append((num, hit[1]))
    order_ok = all(seq[i][1] <= seq[i + 1][1] for i in range(len(seq) - 1))
    add("A7", "required sections 1-13 present (by heading keyword)", "FAIL" if missing else ("PASS" if order_ok else "WARN"),
        ("missing: " + "; ".join(missing)) if missing else ("" if order_ok else "all present but out of order"))
    # A8 scope statement
    sc = all(re.search(p, flat, re.I) for p in (r"\bdefinite\b", r"number field", r"inner form"))
    add("A8", "scope statement (definite quaternion algebras, over Q only, JL for all inner forms/number fields)",
        "PASS" if sc else "FAIL", "" if sc else "need 'definite', 'number field', 'inner form'")
    # A9 claim statuses
    st = {k: len(re.findall(v, flat)) for k, v in (("proved", r"\\stproved|\[proved"), ("pmc", r"\\stpmc|proved modulo"), ("cited", r"\\stcited|\[cited"),
                                                     ("formal", r"\\stformal|Lean-verified"), ("computed", r"\\stcomp|\[computed"), ("open", r"\\stopen|\\stconj|conjectural"))}
    miss = [k for k in ("proved", "cited", "formal", "computed") if not st[k]]
    add("A9", "claim-status markers present (proved/cited/Lean-verified/computed ...); per-claim completeness is MANUAL",
        "FAIL" if miss else "PASS", "counts %s" % st)
    # A10 problem text verbatim
    nf = norm_letters(flat)
    full = norm_letters(PROBLEM_TEXT)
    sents = re.split(r"(?<=[.])\s+(?=[A-Z])", PROBLEM_TEXT)
    unmatched = [s[:50] for s in sents if norm_letters(s) not in nf]
    dois = [d for d in ("10.1007/BFb0058988", "10.1007/978-3-319-27666-3_8") if norm_letters(d) not in nf]
    add("A10", "problem text quoted verbatim + both references (JL LNM 114 doi, Bergeron Ch. 8 doi)",
        "PASS" if full in nf and not dois else "FAIL",
        ("sentences not found: %s; " % unmatched if unmatched else "") + ("dois missing: %s" % dois if dois else ""))
    # X1 unresolved \ref-family labels
    defd = set(re.findall(r"\\label\{([^}]*)\}", flat))
    used = set()
    for m in REF_RE.finditer(flat):
        used.update(l.strip() for l in m.group("labs").split(","))
    for m in HREF_RE.finditer(flat):
        used.add(m.group("lab").strip())
    unres = sorted(l for l in used if l not in defd and not l.startswith("#"))
    add("X1", "no unresolved external references (every \\ref/\\eqref/\\cref/\\hyperref label is defined in the file)",
        "FAIL" if unres else "PASS", "%d: %s" % (len(unres), ", ".join(unres[:8])) if unres else "")
    # A12 external-only pointers
    ptrs = []
    for m in re.finditer(r"\[chapters, [^\]]*\]", flat):
        if not re.search(r"\\(ref|eqref|cref|Cref|autoref|vref)\{rpt:[^}]*\}\s?$", flat[max(0, m.start() - 40):m.start()]):
            ptrs.append((lineno(flat, m.start()), m.group(0)))
    add("A12", "external-only references (pointer to main.pdf, statement not in the report): one line each",
        "WARN" if ptrs else "PASS", "%d:\n" % len(ptrs) + "\n".join("          L%d %s" % p for p in ptrs[:40]) if ptrs else "")
    # A11 placeholders
    ph = [(lineno(flat, m.start()), m.group(0)) for m in re.finditer(r"\\TODOFACT|TODO|FIXME|PLACEHOLDER|\\provisional\{|\?\?\?|XXX", flat)]
    add("A11", "no unresolved placeholders (\\TODOFACT, TODO, FIXME, \\provisional, ???)", ("WARN" if draft else "FAIL") if ph else "PASS",
        "%d: %s" % (len(ph), "; ".join("L%d %s" % h for h in ph[:6])) if ph else "")
    # B Lean
    decls = set(re.findall(r"Langlandscape\.[A-Za-z0-9_.']*[A-Za-z0-9_']", flat))
    add("B1", "Lean table: declarations listed (>= 20 distinct Langlandscape.* names; completeness vs PrintAxioms is MANUAL)",
        "PASS" if len(decls) >= 20 else "FAIL", "%d distinct names" % len(decls))
    add("B2", "Lean table has 'conditional on Hyp.' entries and a differences column",
        "PASS" if re.search(r"conditional on", flat) and re.search(r"difference", flat, re.I) else "FAIL", "")
    disc = all(re.search(p, flat, re.I) for p in (r"explicit argument", r"\bProp\b", r"sorry", r"standard axioms|propext"))
    add("B3", "hypothesis-discipline paragraph (Prop-valued, explicit arguments, sorry-free, standard axioms)", "PASS" if disc else "FAIL", "")
    # final gate: bsf-gate-1 (955/955, from scratch, Lean tree c70ef3a9, logs fa755069); previous: 950/950 at 28d2b091 (gate
    # commit dc61af50), 840/840 at 2323a252
    m_ga = re.search(r"\\newcommand\{\\GateAudited\}\{(\d+)\}", flat)
    gate = (m_ga is not None and m_ga.group(1) == "955" and re.search(r"955/955|\\GateAudited/\\GateAudited", flat)
            and re.search(r"c70ef3a9", flat) and re.search(r"fa755069", flat))
    add("B4", "final gate referenced (955/955, Lean tree c70ef3a9, logs fa755069) and the frozen-import sorry mentioned",
        "PASS" if gate and re.search(r"frozen", flat) else "FAIL", "")
    # compile
    if log_info is not None:
        ok, msg = log_info
        add("S1", "compiles from report.tex alone (pdflatex x2), no errors / undefined refs or citations / missing files",
            "PASS" if ok else "FAIL", msg)
    else:
        add("S1", "compiles from report.tex alone", "SKIP", "not built (--no-build / --check without --build)")
    if pdf and Path(pdf).exists() and shutil.which("pdftotext"):
        t = subprocess.run(["pdftotext", str(pdf), "-"], capture_output=True, text=True).stdout
        qq = len(re.findall(r"\?\?", t))
        add("S2", "no '??' (unresolved reference/citation) in the PDF text", "PASS" if qq == 0 else "FAIL", "%d occurrence(s)" % qq)
    else:
        add("S2", "no '??' in the PDF text", "SKIP", "no PDF / pdftotext")
    # repo-level checks
    if repo:
        repo = Path(repo)
        mm = repo / "mathematics/main.tex"
        if mm.exists():
            add("C1", "mathematics/main.tex includes chapter s00", "PASS" if re.search(r"s00", mm.read_text()) else "FAIL", "")
        tm = repo / "talk/main.tex"
        if tm.exists():
            try:
                fl = Flattener(tm); t = fl.run()
                main_part = re.split(r"\\appendix\b", re.sub(r"(?m)^\s*%.*$", "", t), 1)  # backup frames after \appendix are not counted
                n = len(re.findall(r"\\begin\{frame\}|\\frame\{|\\frame\s*\[", main_part[0]))
                nb = len(re.findall(r"\\begin\{frame\}", main_part[1])) if len(main_part) > 1 else 0
                add("D1", "talk has 14-21 frames before \\appendix (team decision 13:20Z; 19 frames 14:30Z; 21 frames 18:40Z)", "PASS" if 14 <= n <= 21 else "FAIL", "%d frames (talk/main.tex, flattened), %d backup frame(s) after \\appendix" % (n, nb))
            except Exception as e:  # noqa
                add("D1", "talk has 14-19 frames (team decision 13:20Z, 19 frames 14:30Z)", "WARN", "could not flatten talk: %s" % e)
    return R

def print_checks(R):
    w = max(len(r[0]) for r in R)
    for i, req, st, d in R:
        print("%-5s %-4s %s%s" % (st, i, req, ("\n          -> " + d) if d else ""))
    nf = sum(1 for r in R if r[2] == "FAIL")
    nw = sum(1 for r in R if r[2] == "WARN")
    print("\n%d FAIL, %d WARN, %d PASS, %d SKIP" % (nf, nw, sum(1 for r in R if r[2] == "PASS"), sum(1 for r in R if r[2] == "SKIP")))
    return nf

# ----------------------------------------------------------------------------- compile self-test
def compile_test(flat_path, pdf_out, tmp_parent=None):
    d = Path(tempfile.mkdtemp(prefix="flatcheck-", dir=tmp_parent))
    shutil.copy(flat_path, d / "report.tex")
    log = ""
    for n in range(3):
        r = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-file-line-error", "report.tex"], cwd=d,
                           capture_output=True, text=True, errors="replace", stdin=subprocess.DEVNULL, timeout=900)
        log = (d / "report.log").read_text(errors="replace") if (d / "report.log").exists() else r.stdout
        if n >= 1 and "Rerun to get" not in log and "undefined" not in log.lower():
            break
    probs = []
    errs = re.findall(r"^(?:\./)?report\.tex:\d+: (.*)$", log, re.M) + re.findall(r"^! (.*)$", log, re.M)
    if errs: probs.append("%d error(s): %s" % (len(errs), "; ".join(sorted(set(errs))[:4])))
    for pat, nm in ((r"Citation `[^']*' on page \d+ undefined", "undefined citations"), (r"Reference `[^']*' on page \d+ undefined", "undefined references"),
                    (r"LaTeX Warning: Label `[^']*' multiply defined", "multiply defined labels"), (r"File `[^']*' not found", "missing files"),
                    (r"There were undefined references", "undefined refs"), (r"Rerun to get cross-references right", "needs another run")):
        f = re.findall(pat, log)
        if f: probs.append("%s: %s" % (nm, "; ".join(f[:3])))
    if not (d / "report.pdf").exists():
        probs.append("no PDF produced")
    else:
        shutil.copy(d / "report.pdf", pdf_out)
        shutil.copy(d / "report.log", Path(pdf_out).with_suffix(".log"))
    return (not probs), ("; ".join(probs) if probs else "ok (%s)" % d), d

# ----------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description="Flatten a modular LaTeX report into one self-contained .tex (see module docstring).")
    ap.add_argument("main", nargs="?", help="modular main .tex (omit with --check)")
    ap.add_argument("-o", "--output", help="output .tex (default: report.tex next to this tool's parent, i.e. mathematics/submission/report.tex)")
    ap.add_argument("--check", metavar="FLAT.tex", help="only run the rule checks on an existing flat file")
    ap.add_argument("--repo", help="repository root for the repo-level checks C1/D1 (default: auto)")
    ap.add_argument("--root", action="append", default=[], help="extra directory searched for \\input files (repeatable)")
    ap.add_argument("--hyp-appendix", action="store_true", help="substitute the standalone-hypotheses.pdf \\includepdf by the TEXT of report/hypotheses.tex")
    ap.add_argument("--pdf-substitute", action="append", default=[], metavar="PDF=TEX[:PREAMBLE[:BIB]]")
    ap.add_argument("--allow-images", action="store_true")
    ap.add_argument("--no-build", action="store_true", help="skip the pdflatex self-test and PDF")
    ap.add_argument("--build", action="store_true", help="with --check: also compile")
    ap.add_argument("--draft", action="store_true", help="placeholders / title-block gaps are WARN instead of FAIL")
    ap.add_argument("--idword", action="append", default=[], help="extra identifying word (repeatable)")
    ap.add_argument("--idwords-file", help="file with one identifying word per line (replaces the default list)")
    ap.add_argument("--keep-copyright", action="store_true", help="keep the named copyright comment line (default: anonymised)")
    ap.add_argument("--keep-going", action="store_true", help="write the output even if errors were found")
    ap.add_argument("--external-aux", metavar="PATH", help="main.aux of the chapters document (default: mathematics/main.aux if present; "
                    "build: cd mathematics && latexmk -pdf main.tex). Labels not defined in the flat report but in this file become plain text 'Thm.~21.5 of the chapters'")
    ap.add_argument("--keep-bib-local", action="store_true", help="keep 'local: literature/..pdf' pointers in bib notes")
    ap.add_argument("-v", "--verbose", action="store_true")
    a = ap.parse_args()
    global KEEP_LOCAL
    KEEP_LOCAL = a.keep_bib_local
    idw = list(IDENT_WORDS)
    if a.idwords_file:
        idw = [l.strip() for l in Path(a.idwords_file).read_text().splitlines() if l.strip() and not l.startswith("#")]
    idw += a.idword
    repo = a.repo
    here = Path(__file__).resolve()
    if not repo:
        for p in here.parents:
            if (p / ".git").exists():
                repo = str(p); break

    if a.check:
        flat = Path(a.check).read_text(encoding="utf-8")
        li = None; pdf = Path(a.check).with_suffix(".pdf")
        if a.build:
            ok, msg, _ = compile_test(a.check, pdf); li = (ok, msg)
        sys.exit(1 if print_checks(run_checks(flat, idw, a.draft, li, repo, pdf)) else 0)

    if not a.main:
        ap.error("MAIN.tex required (or use --check)")
    out = Path(a.output) if a.output else here.parent.parent / "report.tex"
    subst = {}
    if a.hyp_appendix:
        subst.update(PDF_PRESETS)
    for s in a.pdf_substitute:
        k, v = s.split("=", 1); p = (v.split(":") + ["", ""])[:3]
        subst[k] = tuple(x or None for x in p)
    fl = Flattener(a.main, a.root, a.allow_images, subst, a.verbose)
    flat = fl.run()
    flat = re.sub(r"\\printbibliography(\[[^\]]*\])?", "\\\\printbibliography", flat)
    flat = re.sub(r"\\bibliographystyle\{[^}]*\}[ \t]*\n?", "", flat)   # bibtex style line: not needed once thebibliography is inlined
    # drop biblatex-only setup lines that are meaningless without biblatex
    flat = re.sub(r"^\\(DeclareFieldFormat|DeclareNameFormat|defbibheading|DeclareBibliographyDriver)\b.*\n", "", flat, flags=re.M)
    flat, keys = convert_cites(flat)
    auxp = Path(a.external_aux) if a.external_aux else find_aux(fl.roots)
    aux = parse_aux(auxp) if auxp and auxp.is_file() else {}
    if a.external_aux and not aux:
        errs0 = "--external-aux %s not found or empty" % a.external_aux
        fl.errors.append(errs0)
    elif not aux and re.search(r"\\(?:ref|eqref|cref|Cref|autoref)\{", flat):
        # without the chapters' main.aux the "[chapters, Thm N]" pointers would be dropped silently
        fl.errors.append("no main.aux found: build it first (cd mathematics && latexmk -pdf main.tex) or pass --external-aux")
    elif aux and auxp:
        chap = auxp.parent / "chapters"
        newer = [str(f) for f in chap.rglob("*.tex") if f.stat().st_mtime > auxp.stat().st_mtime] if chap.is_dir() else []
        if newer:
            fl.errors.append("stale %s: %d chapter source(s) are newer (e.g. %s); rebuild main.pdf first" % (auxp, len(newer), newer[0]))
    flat, nrpt, ext_only, unres = externalize_refs(flat, aux)
    print("flatten: %d ref(s) redirected to rpt:LABEL, %d label(s) external-only (aux: %s)%s" % (nrpt, len(ext_only), auxp, "" if aux else "  [no main.aux found; build it: cd mathematics && latexmk -pdf main.tex]"), file=sys.stderr)
    for u in unres:
        warn("unresolved reference label (in neither the report nor main.aux): %s" % u)
    bib_block, missing, nent = build_bibliography(keys, fl.bibfiles)
    if "\\printbibliography" in flat:
        flat = flat.replace("\\printbibliography", bib_block, 1)
    elif keys:
        flat = flat.replace("\\end{document}", bib_block + "\n\\end{document}", 1)
    if not re.search(r"\\usepackage(\[[^\]]*\])?\{[^}]*(hyperref|url)[^}]*\}", flat) and "\\url{" in bib_block:
        flat = flat.replace("\\begin{document}", "\\usepackage{url}\n\\begin{document}", 1)
    flat = re.sub(r"\n{3,}", "\n\n", flat)
    hdr = [h for h in fl.header if "SPDX" in h]
    hdr.append("%" + (" Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)" if a.keep_copyright
                       else " Copyright (C) 2026 the Langlandscape team"))
    hdr.append("% GENERATED by mathematics/submission/tools/flatten.py from the modular sources; do not edit by hand.")
    flat = "\n".join(hdr) + "\n" + flat.lstrip("\n")
    if not flat.endswith("\n"):
        flat += "\n"
    # report
    print("flatten: %d source file(s) inlined; %d bib file(s) (%d entries); %d distinct cited keys" % (len(fl.used_files), len(fl.bibfiles), nent, len(keys)), file=sys.stderr)
    errs = list(fl.errors)
    if missing:
        errs.append("cited keys with no .bib entry: " + ", ".join(missing))
    for typ, line, lab, cap, words, kind in figure_report(flat):
        status = ("caption of %d words" % words) if cap else "NO CAPTION"
        if typ != "figure": status = "not inside a figure environment: needs a description paragraph (manual)"
        warn("%s at flat line %d (label %s, %s): %s" % (typ, line, lab, kind, status))
    for e in errs:
        print("ERROR: " + e, file=sys.stderr)
    if errs and not a.keep_going:
        print("flatten: FAILED (%d error(s)); nothing written (use --keep-going to write anyway)" % len(errs), file=sys.stderr)
        sys.exit(2)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(flat, encoding="utf-8")
    print("flatten: wrote %s (%d lines, %d KiB)" % (out, flat.count("\n"), len(flat.encode()) // 1024), file=sys.stderr)
    li, pdf = None, out.with_suffix(".pdf")
    if not a.no_build:
        ok, msg, d = compile_test(out, pdf)
        li = (ok, msg)
        print("self-test compile: %s (%s)" % ("OK" if ok else "FAILED", msg), file=sys.stderr)
    print()
    nf = print_checks(run_checks(flat, idw, a.draft, li, repo, pdf if not a.no_build else None))
    if ext_only:
        print("\nA12 summary: %d external-only reference(s) (statement not in the report; pointer to main.pdf only)" % len(ext_only))
        for l in sorted(ext_only):
            print("  WARN external-only ref %s -> [%s]" % (l, ext_only[l]))
    sys.exit(1 if (nf or errs) else 0)

if __name__ == "__main__":
    main()
