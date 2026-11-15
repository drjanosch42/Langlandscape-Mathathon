#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-or-later
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Export AI-session logs (Claude Code, opencode) as redacted, readable Markdown.

Usage (every option except --out has a default):
  python3 redact.py --node NODE --out DIR \
      [--claude-root ~/.claude/projects] [--match Langlandscape --match Langlandscope] \
      [--opencode-db ~/.local/share/opencode/opencode.db] [--no-opencode] [--no-claude]

Output: DIR/NODE/redacted/*.md, DIR/NODE/MANIFEST.md, manifest.json, scan_report.json
Only the Python standard library is used. Raw logs are only read, never modified.

Policy:
  * conversation order; user/assistant text in full (fenced blocks > 15 lines are cut),
    tool calls = name + arguments truncated to 500 chars, tool results truncated to 300 chars;
  * model "thinking"/"reasoning" is NOT exported;
  * results of reads from literature/ or pdftotext output -> "[literature excerpt removed]";
  * e-mail addresses (except the team's institutional ones), tokens/keys/passwords, rclone
    config, phone numbers, home paths and claude.ai session URLs are masked;
  * output files are split at 5 MB.
"""
import argparse, collections, glob, json, os, re, sqlite3, datetime

ARG_MAX, RES_MAX, FENCE_MAX, FILE_MAX = 500, 300, 15, 5 * 1024 * 1024
ALLOWED_EMAIL = re.compile(r'(@(math\.)?uni-paderborn\.de$|^noreply@anthropic\.com$)', re.I)
LIT_MARK = '[literature excerpt removed]'

counts = collections.Counter()

def _sub(cat, rx, rep, text):
    def f(m):
        counts[cat] += 1
        return rep(m) if callable(rep) else rep
    return rx.sub(f, text)

def _email(m):
    if ALLOWED_EMAIL.search(m.group(0)):
        return m.group(0)
    counts['gmail' if m.group(0).lower().endswith('@gmail.com') else 'email'] += 1
    return '[email removed]'

PATTERNS = [  # (category, regex, replacement)
    ('private_key', r'-----BEGIN [A-Z ]*-----[\s\S]{0,4000}?(?:-----END [A-Z ]*-----|\Z)', '[private key removed]'),
    ('private_key', r'-----BEGIN[ A-Z]*', '[private key marker removed]'),
    ('token', r'\bsk-[A-Za-z0-9_\-]{12,}', '[token removed]'),
    ('token', r'\bgh[pousr]_[A-Za-z0-9]{20,}', '[token removed]'),
    ('token', r'\bgithub_pat_[A-Za-z0-9_]{20,}', '[token removed]'),
    ('token', r'\bAKIA[0-9A-Z]{16}\b', '[token removed]'),
    ('token', r'\bxox[abprs]-[A-Za-z0-9-]{10,}', '[token removed]'),
    ('token', r'\bAIza[0-9A-Za-z_\-]{30,}', '[token removed]'),
    ('token', r'(?i)\bBearer\s+[A-Za-z0-9._~+/=\-]{16,}', 'Bearer [token removed]'),
    ('token', r'\beyJ[A-Za-z0-9_\-]{10,}\.[A-Za-z0-9_\-]{10,}\.[A-Za-z0-9_\-]{5,}', '[token removed]'),
    ('secret_assignment', r'(?i)\b((?:client_)?secret|pass(?:word|wd)?|(?:refresh_|access_|api_?)?token|api[_-]?key)\b(\s*["\']?\s*[=:]\s*)("[^"\n]*"|\'[^\'\n]*\'|[^\s,;]+)',
        lambda m: f'{m.group(1)}{m.group(2)}[removed]'),
    ('rclone_config', r'(?im)^\s*(?:pass|token|client_secret|client_id|service_account_credentials|refresh_token)\s*=.*$', '[rclone config line removed]'),
    ('session_url', r'https://claude\.ai/code/session_[A-Za-z0-9]+', '[session url removed]'),
    ('session_url', r'bridge:session_[A-Za-z0-9]+', 'bridge:session_…'),
    ('home_path', r'/home/[A-Za-z0-9_.\-]+', '~'),
    ('home_path', r'(?<=-home-)[A-Za-z0-9_]+(?=-)', 'USER'),  # Claude project dir names
    ('home_path', r'/Users/[A-Za-z0-9_.\-]+', '~'),
    ('phone', r'(?<![\w.])\+\d{1,3}[ \-]?\(?\d{1,4}\)?(?:[ \-]?\d{2,}){2,}(?!\w)', '[phone removed]'),
    ('phone', r'\(\d{3}\)\s?\d{3}-\d{4}\b', '[phone removed]'),
    ('phone', r'(?<![\w.\-])\d{3}-\d{3}-\d{4}\b', '[phone removed]'),
    ('phone', r'(?<![\w.\-])0\d{2,4}[ /\-]\d{5,9}\b', '[phone removed]'),
]
COMPILED = [(c, re.compile(p), r) for c, p, r in PATTERNS]
EMAIL_RE = re.compile(r'[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}')

def redact(text):
    if not text:
        return text
    for cat, rx, rep in COMPILED:
        text = _sub(cat, rx, rep, text)
    return EMAIL_RE.sub(_email, text)

def cut(text, n):
    text = text if isinstance(text, str) else json.dumps(text, ensure_ascii=False)
    return text if len(text) <= n else text[:n] + f' …[+{len(text)-n} chars]'

FENCE_RE = re.compile(r'(```[^\n]*\n)(.*?)(\n```)', re.S)
def _trim_lines(m):
    lines = m.group(2).split('\n')
    if len(lines) <= FENCE_MAX:
        return m.group(0)
    counts['long_block_trimmed'] += 1
    return m.group(1) + '\n'.join(lines[:FENCE_MAX]) + f'\n[... {len(lines)-FENCE_MAX} lines removed]' + m.group(3)

def trim_fences(text):
    return FENCE_RE.sub(_trim_lines, text)

PASTE_RE = re.compile(r'(<pasted_content[^>]*>)(.*?)(</pasted_content[^>]*>)', re.S)
REMINDER_RE = re.compile(r'(<system-reminder>)(.*?)(</system-reminder>)', re.S)
def _rem(m):
    return m.group(0) if len(m.group(2)) <= 600 else m.group(1) + m.group(2)[:600] + ' …[system reminder truncated]' + m.group(3)
def trim_user(text):
    return trim_fences(REMINDER_RE.sub(_rem, PASTE_RE.sub(_trim_lines, text)))

def is_literature(call_repr, result_text):
    blob = (call_repr or '')
    return 'literature/' in blob or 'pdftotext' in blob or 'pdftotext' in (result_text or '')[:2000]

def block_text(content):
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return '\n'.join(b.get('text', '') if isinstance(b, dict) else str(b) for b in content)
    return json.dumps(content, ensure_ascii=False)

def quote_result(res):
    return '> result: ' + cut(res, RES_MAX).replace('\n', '\n> ') + '\n'

class Doc:
    def __init__(self):
        self.parts, self.models, self.t0, self.t1, self.turns = [], set(), None, None, 0
    def stamp(self, ts):
        if ts:
            self.t0 = self.t0 or ts
            self.t1 = ts
    def add(self, s):
        self.parts.append(redact(s))

def render_claude(path):
    doc, calls = Doc(), {}
    for line in open(path, encoding='utf-8', errors='replace'):
        try:
            d = json.loads(line)
        except Exception:
            continue
        t = d.get('type')
        if t not in ('user', 'assistant'):
            continue
        ts = d.get('timestamp', '')
        doc.stamp(ts)
        m = d.get('message') or {}
        content = m.get('content')
        if t == 'assistant':
            if m.get('model'):
                doc.models.add(m['model'])
            for b in content if isinstance(content, list) else []:
                if b.get('type') == 'text' and b.get('text', '').strip():
                    doc.turns += 1
                    doc.add(f"\n### Assistant · {ts}\n\n{trim_fences(b['text'])}\n")
                elif b.get('type') == 'tool_use':
                    args = json.dumps(b.get('input', {}), ensure_ascii=False)
                    calls[b.get('id')] = args
                    doc.add(f"\n**Tool call `{b.get('name')}`**: `{cut(args, ARG_MAX)}`\n")
        else:
            if isinstance(content, str):
                content = [{'type': 'text', 'text': content}]
            for b in content or []:
                if b.get('type') == 'text' and b.get('text', '').strip():
                    doc.turns += 1
                    doc.add(f"\n### User · {ts}\n\n{trim_user(b['text'])}\n")
                elif b.get('type') == 'tool_result':
                    res = block_text(b.get('content'))
                    if is_literature(calls.get(b.get('tool_use_id')), res):
                        counts['literature_results_removed'] += 1
                        res = LIT_MARK
                    doc.add(quote_result(res))
    return doc

def render_opencode(sess, msgs):
    doc = Doc()
    ms = lambda v: datetime.datetime.fromtimestamp(v / 1000, datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ') if v else None
    doc.stamp(ms(sess['time_created']))
    for mm in msgs:
        try:
            d = json.loads(mm['data'])
        except Exception:
            continue
        ts = ms(mm['time_created']) or ''
        doc.stamp(ts)
        if mm['type'] == 'user' and d.get('text', '').strip():
            doc.turns += 1
            doc.add(f"\n### User · {ts}\n\n{trim_user(d['text'])}\n")
        elif mm['type'] == 'assistant':
            mdl = (d.get('model') or {}).get('id')
            if mdl:
                doc.models.add(mdl)
            for it in d.get('content', []):
                k = it.get('type')
                if k == 'text' and it.get('text', '').strip():
                    doc.turns += 1
                    doc.add(f"\n### Assistant · {ts}\n\n{trim_fences(it['text'])}\n")
                elif k == 'tool':
                    st = it.get('state', {})
                    args = json.dumps(st.get('input', {}), ensure_ascii=False)
                    res = block_text(st.get('content', st.get('output', '')))
                    doc.add(f"\n**Tool call `{it.get('name')}`**: `{cut(args, ARG_MAX)}`\n")
                    if is_literature(args, res):
                        counts['literature_results_removed'] += 1
                        res = LIT_MARK
                    doc.add(quote_result(res))
    return doc

def write_doc(doc, outdir, stem, header, manifest, kind, sid, src_bytes):
    os.makedirs(outdir, exist_ok=True)
    head = redact(header) + '\n'
    chunks, cur, size = [], [], len(head.encode())
    for p in doc.parts:
        b = len(p.encode('utf-8'))
        if size + b > FILE_MAX - 200 and cur:
            chunks.append(cur); cur, size = [], len(head.encode())
        cur.append(p); size += b
    chunks.append(cur)
    files, total = [], 0
    for i, ch in enumerate(chunks, 1):
        name = f'{stem}.md' if len(chunks) == 1 else f'{stem}.part{i:02d}.md'
        txt = head + (f'_(part {i}/{len(chunks)})_\n' if len(chunks) > 1 else '') + ''.join(ch)
        with open(os.path.join(outdir, name), 'w', encoding='utf-8') as f:
            f.write(txt)
        files.append(name); total += len(txt.encode('utf-8'))
    manifest.append(dict(kind=kind, session=sid, file=files, models=sorted(doc.models), start=doc.t0, end=doc.t1,
                         turns=doc.turns, bytes_before=src_bytes, bytes_after=total))

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--node', default='localhost')
    ap.add_argument('--out', required=True, help='root dir; writes <out>/<node>/redacted/')
    ap.add_argument('--claude-root', default='~/.claude/projects')
    ap.add_argument('--match', action='append', help='substring of project dir / session directory (default: Langlandscape, Langlandscope)')
    ap.add_argument('--opencode-db', default='~/.local/share/opencode/opencode.db')
    ap.add_argument('--no-claude', action='store_true')
    ap.add_argument('--no-opencode', action='store_true')
    a = ap.parse_args()
    matches = a.match or ['Langlandscape', 'Langlandscope']
    base = os.path.join(os.path.expanduser(a.out), a.node)
    outdir = os.path.join(base, 'redacted')
    os.makedirs(outdir, exist_ok=True)
    manifest = []

    root = os.path.expanduser(a.claude_root)
    if not a.no_claude and os.path.isdir(root):
        seen_dirs = set()
        for pd in sorted(os.listdir(root)):
            if not any(m in pd for m in matches):
                continue
            real = os.path.realpath(os.path.join(root, pd))  # old-name symlinks -> same dir
            if real in seen_dirs:
                continue
            seen_dirs.add(real)
            for f in sorted(glob.glob(os.path.join(root, pd, '**', '*.jsonl'), recursive=True)):
                rel = os.path.relpath(f, os.path.join(root, pd)).replace(os.sep, '/')
                parts = rel.split('/')
                sid = parts[0].replace('.jsonl', '')
                stem = f'claude-{sid}' if len(parts) == 1 else f'claude-{sid}--' + '-'.join(parts[1:]).replace('.jsonl', '')
                doc = render_claude(f)
                if not doc.parts:
                    continue
                hdr = (f'# Claude Code transcript `{rel}`\n\n- project dir: `{pd}`\n'
                       f'- models: {", ".join(sorted(doc.models)) or "n/a"}\n- span: {doc.t0} → {doc.t1}\n')
                write_doc(doc, outdir, stem, hdr, manifest, 'claude-main' if len(parts) == 1 else 'claude-subagent',
                          sid, os.path.getsize(f))

    dbp = os.path.expanduser(a.opencode_db)
    if not a.no_opencode and os.path.exists(dbp):
        c = sqlite3.connect('file:' + dbp + '?mode=ro', uri=True)
        c.row_factory = sqlite3.Row
        where = ' or '.join(["directory like '%" + m.replace("'", '') + "%'" for m in matches] +
                            ["directory like '/tmp/muse-%'", "directory like '/tmp/claude-%/muse-%'", "directory like '%/opencode-test'"])
        for s in c.execute(f'select * from session_v2 where {where} order by time_created').fetchall():
            s = dict(s)
            msgs = [dict(m) for m in c.execute('select * from session_message where session_id=? order by seq', (s['id'],))]
            doc = render_opencode(s, msgs)
            if not doc.parts:
                continue
            hdr = (f'# opencode session `{s["id"]}`\n\n- title: {s["title"]}\n- directory: `{s["directory"]}`\n'
                   f'- models: {", ".join(sorted(doc.models)) or "n/a"}\n- span: {doc.t0} → {doc.t1}\n')
            write_doc(doc, outdir, f'opencode-{s["id"]}', hdr, manifest, 'opencode', s['id'], sum(len(m['data']) for m in msgs))

    json.dump(manifest, open(os.path.join(base, 'manifest.json'), 'w'), indent=1)
    with open(os.path.join(base, 'MANIFEST.md'), 'w') as f:
        f.write('| kind | session | file(s) | model(s) | start | end | turns | bytes before | bytes after |\n|---|---|---|---|---|---|---|---|---|\n')
        for m in manifest:
            f.write(f"| {m['kind']} | {m['session'][:12]} | {', '.join(m['file'])} | {', '.join(m['models'])} | {m['start']} | {m['end']} | {m['turns']} | {m['bytes_before']} | {m['bytes_after']} |\n")
    json.dump(dict(counts), open(os.path.join(base, 'scan_report.json'), 'w'), indent=1)
    print(f'{len(manifest)} sessions; masked counts: {dict(counts)}')

if __name__ == '__main__':
    main()
