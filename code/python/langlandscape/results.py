"""Provenance helper for result files under ``code/results/``.

Every result file is JSON with top-level keys ``provenance`` and ``data``.
Fractions are serialised as ``"p/q"`` strings and sets as sorted lists.
"""

from __future__ import annotations

import datetime as _dt
import fractions
import json
import pathlib
import subprocess
import time
from typing import Any


def repo_root() -> pathlib.Path:
    """Return the git top-level directory containing this file."""
    here = pathlib.Path(__file__).resolve().parent
    out = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        cwd=here, capture_output=True, text=True, check=True,
    ).stdout.strip()
    return pathlib.Path(out)


def git_commit() -> str:
    """Return HEAD sha, suffixed with ``-dirty`` if the tree has changes; ``unknown`` on failure."""
    try:
        cwd = pathlib.Path(__file__).resolve().parent
        sha = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=cwd, capture_output=True, text=True, check=True,
        ).stdout.strip()
        status = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=cwd, capture_output=True, text=True, check=True,
        ).stdout.strip()
        return sha + ("-dirty" if status else "")
    except (subprocess.SubprocessError, OSError):
        return "unknown"


class Timer:
    """Context manager measuring wall time in ``.seconds``."""

    def __init__(self) -> None:
        self.seconds: float = 0.0
        self._start: float = 0.0

    def __enter__(self) -> "Timer":
        self._start = time.perf_counter()
        return self

    def __exit__(self, *exc: object) -> None:
        self.seconds = time.perf_counter() - self._start


def _pari_version() -> str | None:
    try:
        import cypari2
    except ImportError:
        return None
    try:
        v = cypari2.Pari().version()
        return ".".join(map(str, v)) if isinstance(v, tuple) else str(v)
    except Exception:  # pragma: no cover - defensive
        return None


def _default(obj: Any) -> Any:
    if isinstance(obj, fractions.Fraction):
        return f"{obj.numerator}/{obj.denominator}"
    if isinstance(obj, (set, frozenset)):
        return sorted(obj)
    raise TypeError(f"Object of type {type(obj).__name__} is not JSON serialisable")


def write(
    relpath: str,
    data: Any,
    *,
    script: str,
    params: dict,
    runtime_s: float,
    notes: str | None = None,
) -> pathlib.Path:
    """Write ``data`` with provenance to ``<repo_root>/code/results/<relpath>``.

    Returns the path written.
    """
    path = repo_root() / "code" / "results" / relpath
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "provenance": {
            "script": script,
            "commit": git_commit(),
            "params": params,
            "date": _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat(),
            "runtime_s": runtime_s,
            "python": __import__("platform").python_version(),
            "pari_version": _pari_version(),
            "notes": notes,
        },
        "data": data,
    }
    with path.open("w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=1, sort_keys=True, default=_default)
        fh.write("\n")
    return path


def read(relpath: str) -> dict:
    """Return the full result dict (``provenance`` and ``data``) stored at ``relpath``."""
    path = repo_root() / "code" / "results" / relpath
    with path.open(encoding="utf-8") as fh:
        return json.load(fh)
