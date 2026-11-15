#!/usr/bin/env python3
"""Generate an axiom-check Lean file for theorems/lemmas/defs in given Lean files.

Usage (run from lean/Langlandscape/):
    python3 -I tools/gen_axioms.py [--names N1,N2,...] FILE...

Output: one `import <Module>` line per declaring file (input order), a blank line, then
`#print axioms <Full.Name>` per name. With --names, each listed short name (matched by last
component or by full name) is printed; an unknown name is an error (exit 1). Without --names,
every public theorem/lemma/def is printed. Private declarations are skipped.
Python 3 standard library only.
"""
import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # lean/Langlandscape/

CMD = re.compile(r'^[ \t]*(namespace|section|end)(?:[ \t]+(\S+))?[ \t]*$', re.MULTILINE)
DECL = re.compile(
    r'^[ \t]*((?:@\[[^\]]*\][ \t\n]*)*)'
    r'((?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*)'
    r'(theorem|lemma|def)\s+([^\s(){}\[\]:|,]+)',
    re.MULTILINE,
)


def strip_comments(src):
    """Blank out nested block comments, line comments and string literals; keep newlines."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth:
            if src.startswith('/-', i):
                depth += 1
                i += 2
            elif src.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                if src[i] == '\n':
                    out.append('\n')
                i += 1
            continue
        if src.startswith('/-', i):
            depth = 1
            i += 2
        elif src.startswith('--', i):
            while i < n and src[i] != '\n':
                i += 1
        elif src[i] == '"':
            out.append('""')
            i += 1
            while i < n and src[i] != '"':
                if src[i] == '\\':
                    i += 1
                elif src[i] == '\n':
                    out.append('\n')
                i += 1
            i += 1
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)


def parse_decls(text):
    """Return list of (full_name, is_private) in order of appearance."""
    stripped = strip_comments(text)
    events = [(m.start(), 'cmd', m) for m in CMD.finditer(stripped)]
    events += [(m.start(), 'decl', m) for m in DECL.finditer(stripped)]
    events.sort(key=lambda e: e[0])
    stack = []  # entries: ('ns', name) or ('sec', None)
    decls = []
    for _, kind, m in events:
        if kind == 'cmd':
            word, arg = m.group(1), m.group(2)
            if word == 'namespace':
                stack.append(('ns', arg))
            elif word == 'section':
                stack.append(('sec', None))
            elif stack:  # end: closes the most recent namespace or section
                stack.pop()
            continue
        mods = m.group(2).split()
        name = m.group(4)
        if name.startswith('_root_.'):
            full = name[len('_root_.'):]
        else:
            prefix = '.'.join(a for k, a in stack if k == 'ns')
            full = prefix + '.' + name if prefix else name
        decls.append((full, 'private' in mods))
    return decls


def module_of(path):
    rel = os.path.relpath(os.path.abspath(path), ROOT)
    if rel.startswith('..'):
        sys.exit(f'gen_axioms: {path} is outside {ROOT}')
    mod = rel[:-len('.lean')] if rel.endswith('.lean') else rel
    if mod.startswith('Vendor/AxiomStacks/'):
        mod = mod[len('Vendor/AxiomStacks/'):]
    return mod.replace('/', '.')


def main():
    ap = argparse.ArgumentParser(description='Generate #print axioms file for Lean declarations.')
    ap.add_argument('--names', default=None, help='comma-separated short or full names to print')
    ap.add_argument('files', nargs='+', help='Lean source files')
    args = ap.parse_args()

    per_file = []  # (module, [(full_name)]) in input order
    for f in args.files:
        try:
            with open(f, encoding='utf-8') as fh:
                text = fh.read()
        except OSError as e:
            print(f'gen_axioms: cannot read {f}: {e}', file=sys.stderr)
            sys.exit(1)
        public = [full for full, priv in parse_decls(text) if not priv]
        per_file.append((f, public))

    wanted = None
    if args.names is not None:
        wanted = [s.strip() for s in args.names.split(',') if s.strip()]
        if not wanted:
            print('gen_axioms: --names given but empty', file=sys.stderr)
            sys.exit(1)

    imports, prints, seen = [], [], set()
    if wanted is None:
        for f, names in per_file:
            if names:
                imports.append(f'import {module_of(f)}')
            for full in names:
                if full not in seen:
                    seen.add(full)
                    prints.append(f'#print axioms {full}')
    else:
        found = {s: False for s in wanted}
        for f, names in per_file:
            hit = False
            for s in wanted:
                for full in names:
                    if full == s or full.split('.')[-1] == s:
                        found[s] = True
                        hit = True
                        if full not in seen:
                            seen.add(full)
                            prints.append(f'#print axioms {full}')
            if hit:
                imports.append(f'import {module_of(f)}')
        missing = [s for s, ok in found.items() if not ok]
        if missing:
            print('gen_axioms: name(s) not found: ' + ', '.join(missing), file=sys.stderr)
            sys.exit(1)

    out = imports + [''] + prints
    sys.stdout.write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
