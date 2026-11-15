#!/usr/bin/env python3
"""Stale-artifact tooling for lean/.lake/build (M2 ticket T-13).

  stale_build.py closure [--lean DIR]            project modules reachable from the GL2TF and GL2TFTests roots
  stale_build.py modules [--lean DIR]            the modules leanchecker must replay: the closure (GL2TF.*, GL2TFTests.*, vendored)
  stale_build.py prune [--dry-run] [--lean DIR]  delete build artifacts of modules with no source file
  stale_build.py check-replayed LOG [--lean DIR] exit 1 unless the project modules replayed in LOG are exactly the closure

Only files under <lean>/.lake/build/{lib,ir} are ever deleted; .lake/packages is never touched (CLAUDE.md rule 2).
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

ROOTS = ("AlgJL", "AlgJLTests")  # algebraic_jl fork (L-A, 2026-11-14)
DEFAULT_VENDOR_DIRS = ("Vendor/AnthropicFLT", "Vendor/ImperialFLT")
IMPORT = re.compile(r"^\s*(?:public\s+|meta\s+)*import\s+(?:(?:public|meta)\s+)*([A-Za-z_][\w.]*)", re.M)


def vendor_dirs(lean: Path) -> tuple[str, ...]:
    """srcDirs of the vendor libraries declared in lakefile.toml (those under Vendor/); the defaults if unreadable."""
    try:  # python 3.10 has no tomllib: the lakefile's srcDir lines are simple `srcDir = "..."` strings
        text = (lean / "lakefile.toml").read_text(encoding="utf-8")
    except OSError:
        text = ""
    dirs = tuple(dict.fromkeys(d for d in (m.strip("/") for m in re.findall(r'^\s*srcDir\s*=\s*"([^"]+)"', text, re.M))
                               if d.startswith("Vendor/")))
    return dirs or DEFAULT_VENDOR_DIRS


def source_of(lean: Path, mod: str) -> Path | None:
    rel = mod.replace(".", "/") + ".lean"
    for base in ("", *vendor_dirs(lean)):
        p = lean / base / rel
        if p.is_file():
            return p
    return None


def closure(lean: Path, roots=ROOTS) -> set[str]:
    seen: set[str] = set()
    todo = list(roots)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        src = source_of(lean, m)
        if src is None:  # external (Mathlib, Lean, Std, ...) or missing: not a project module
            continue
        seen.add(m)
        text = re.sub(r"/-.*?-/", "", src.read_text(encoding="utf-8", errors="replace"), flags=re.S)
        todo.extend(IMPORT.findall(text))
    return seen


def artifact_roots(lean: Path) -> list[Path]:
    b = lean / ".lake" / "build"
    lib = b / "lib" / "lean"
    return [lib if lib.is_dir() else b / "lib", b / "ir"]


def stale_artifacts(lean: Path) -> list[Path]:
    """Files under build/{lib,ir} whose module has no source file. Refuses paths that resolve outside build/."""
    build = (lean / ".lake" / "build").resolve()
    out = []
    for root in artifact_roots(lean):
        if not root.is_dir():
            continue
        for dirpath, dirnames, files in os.walk(root, followlinks=False):
            dirnames[:] = [d for d in dirnames if not os.path.islink(os.path.join(dirpath, d))]
            for f in files:
                p = Path(dirpath) / f
                real = p.resolve()
                if build not in real.parents:
                    raise SystemExit(f"stale_build: refusing {p}: resolves outside {build}")
                rel = p.relative_to(root)
                mod = ".".join((*rel.parts[:-1], rel.name.split(".")[0]))
                if source_of(lean, mod) is None:
                    out.append(p)
    return sorted(out)


def prune(lean: Path, dry: bool) -> list[Path]:
    victims = stale_artifacts(lean)
    for p in victims:
        print(("would delete " if dry else "deleting ") + str(p))
        if not dry:
            p.unlink()
    if not dry:
        for root in artifact_roots(lean):
            if root.is_dir():
                for dirpath, _, _ in os.walk(root, topdown=False):
                    if Path(dirpath) != root and not os.path.islink(dirpath) and not os.listdir(dirpath):
                        os.rmdir(dirpath)
    print(f"stale_build: {len(victims)} stale artifact(s){' (dry run)' if dry else ' removed'}")
    return victims


def check_replayed(lean: Path, log: Path) -> int:
    want = closure(lean)
    got = {l[len("replaying "):].strip() for l in log.read_text(errors="replace").splitlines() if l.startswith("replaying ")}
    got_proj = {m for m in got if source_of(lean, m) is not None}
    extra, missing = sorted(got_proj - want), sorted(want - got_proj)
    if extra or missing:
        print("stale_build: replayed project modules differ from the import closure", file=sys.stderr)
        print(f"  missing ({len(missing)}, in closure, not replayed): {', '.join(missing) or '-'}", file=sys.stderr)
        print(f"  extra ({len(extra)}, replayed, not in closure): {', '.join(extra) or '-'}", file=sys.stderr)
        return 1
    print(f"stale_build: leanchecker replayed exactly the {len(want)} project modules of the import closure")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=("closure", "modules", "prune", "check-replayed"))
    ap.add_argument("log", nargs="?")
    ap.add_argument("--lean", default=str(Path(__file__).resolve().parent.parent / "lean"))
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    lean = Path(a.lean)
    if a.cmd in ("closure", "modules"):
        print("\n".join(sorted(closure(lean))))
    elif a.cmd == "prune":
        prune(lean, a.dry_run)
    else:
        if not a.log:
            ap.error("check-replayed needs a log file")
        return check_replayed(lean, Path(a.log))
    return 0


if __name__ == "__main__":
    sys.exit(main())
