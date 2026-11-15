# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Run HACS console scripts and parse their ``@@TAG <json>`` output lines.

Child environment (``child_env``): built from an explicit ALLOWLIST, never by copying ``os.environ``. Only ``PATH``,
``HOME``, ``LANG``, ``LC_ALL``, ``TMPDIR`` are copied from the parent; ``ENGINE_THREADS`` is set from ``threads``.
``LD_LIBRARY_PATH`` is NOT passed: the Lane A binary finds ``libcudart`` through its RUNPATH (checked with
``env -i ldd``). A caller may add names through ``env_extra``, but only names of the allowlist or of
``READ_ONLY_INPUT_HOOKS``; every write-capable name (``is_forbidden``) is refused with ``ValueError``. So no
owner-gated emitter, interlock, dump hook or arm/route hook of ``code/hacs/CLAUDE.md`` can reach the child, and
``ENGINE_DEVICE`` is unset (the CPU golden path) unless the caller passes ``ENGINE_DEVICE="cpu"`` explicitly.

Tag parsing: a line ``@@TAG<sep><json>`` (``<sep>`` = one or more spaces or tabs, ``TAG`` matching
``[A-Za-z0-9_.-]+``) contributes the decoded JSON; ``@@TAG`` with no payload or only whitespace contributes ``None``.
Any other line starting with ``@@`` and any undecodable payload is a parse error: ``HacsParseError`` when
``check=True``; recorded in ``ScriptResult.parse_errors`` (and not raised) when ``check=False``.
"""

from __future__ import annotations

import dataclasses
import datetime as _dt
import hashlib
import json
import os
import pathlib
import platform
import re
import subprocess
import tempfile
import time
from typing import Any, Iterable, Sequence

from .. import results as _results

DEFAULT_HACS = "/home/janosch/data/hacs-build/laneA/hacs"
ENV_VAR = "LANGLANDSCAPE_HACS"

# ---- environment ---------------------------------------------------------------------------------------------------

#: names copied from the parent environment when present (nothing else is).
ENV_ALLOWLIST = ("PATH", "HOME", "LANG", "LC_ALL", "TMPDIR")

#: documented read-only input hooks a caller may pass through ``env_extra`` (code/hacs/CLAUDE.md: they change no value
#: and write nothing). ``ENGINE_DEVICE`` is restricted to ``cpu``: this box has no GPU arm, the GPU is never the default.
READ_ONLY_INPUT_HOOKS = {
    "ENGINE_DEVICE": frozenset({"cpu"}),
    "HECKEZ_LOCAL_PAR": None,   # route of the HZ local step, printed in its EFFECTIVE line; no value change
}

#: every write-capable env hook found in the seed's src/ (getenv grep, 2026-11-15) plus the owner-gated interlocks.
_FORBIDDEN = frozenset({
    # owner-gated emitters / re-baselines (code/hacs/CLAUDE.md table)
    "GOLDEN_EMIT", "GOLDEN_DUMP", "GOLDEN_OUT", "CONSOLE_EMIT_EXPECTED", "CLI_MANUAL_EMIT",
    # scratch dumps for the Lean checkers (all HECKE_DUMP_* read in src/)
    "HECKE_DUMP_TAU", "HECKE_DUMP_TAU_PAIR", "HECKE_DUMP_TAU_RHO_CELLS", "HECKE_DUMP_MEREL",
    "HECKE_DUMP_SAT_CERT", "HECKE_DUMP_SAT_CERT_CELLS", "HECKE_DUMP_HZ_CERT", "HECKE_DUMP_HZ_CERT_CELLS",
    "HECKE_DUMP_EXZ2",
    # other file writers: HeckeExtRamanujanValidation.cpp:344, HeckeAtlas.cpp:1223, OrbifoldMPRulesValidation.cpp:113
    "HECKE_EXT_JSON_OUT", "HECKE_ATLAS_OUT", "ORBIFOLD_MP_DUMP",
    # interlocks
    "GOLDEN_STRICT", "HECKE_LOCALITY_PROBE", "HECKE_HIDA_HEAVY",
})
_FORBIDDEN_PREFIXES = ("HECKE_DUMP_", "GOLDEN_")
_FORBIDDEN_SUFFIXES = ("_OUT", "_DUMP", "_EMIT")


def forbidden_env() -> set[str]:
    """The explicit set of write-capable / owner-gated names (the pattern rule is ``is_forbidden``)."""
    return set(_FORBIDDEN)


def is_forbidden(name: str) -> bool:
    """True for the explicit set and for any ``GOLDEN_*``, ``HECKE_DUMP_*``, ``*_OUT``, ``*_DUMP``, ``*_EMIT``."""
    return name in _FORBIDDEN or name.startswith(_FORBIDDEN_PREFIXES) or name.endswith(_FORBIDDEN_SUFFIXES)


def child_env(threads: int = 4, env_extra: dict[str, str] | None = None, *,
              base: dict[str, str] | None = None) -> dict[str, str]:
    """The environment of a HACS child: the allowlist from ``base`` (default ``os.environ``), ``ENGINE_THREADS``,
    then ``env_extra`` (allowlisted or read-only-input names only; a write-capable name raises ``ValueError``)."""
    src = os.environ if base is None else base
    env = {k: src[k] for k in ENV_ALLOWLIST if k in src}
    env["ENGINE_THREADS"] = str(int(threads))
    for k, v in (env_extra or {}).items():
        if is_forbidden(k):
            raise ValueError(f"env_extra: {k} is a write-capable / owner-gated HACS hook and is never passed")
        if k == "ENGINE_THREADS":
            raise ValueError("env_extra: set ENGINE_THREADS through the `threads` argument")
        if k in READ_ONLY_INPUT_HOOKS:
            allowed = READ_ONLY_INPUT_HOOKS[k]
            if allowed is not None and v not in allowed:
                raise ValueError(f"env_extra: {k}={v!r} not allowed (allowed: {sorted(allowed)})")
        elif k not in ENV_ALLOWLIST:
            raise ValueError(f"env_extra: {k} is neither allowlisted nor a documented read-only input hook")
        env[k] = str(v)
    return env


def sanitized_env(threads: int = 4, base: dict[str, str] | None = None) -> dict[str, str]:
    """Backward-compatible alias of ``child_env(threads, base=base)``."""
    return child_env(threads, base=base)


# ---- errors and results --------------------------------------------------------------------------------------------

class HacsError(Exception):
    """Base class of bridge errors."""


class HacsNotFound(HacsError):
    """The HACS binary is missing or not executable."""


class HacsParseError(HacsError, ValueError):
    """A malformed ``@@`` line or an undecodable payload (raised only with ``check=True``)."""


class HacsScriptError(HacsError):
    """A HACS script exited with a nonzero return code."""

    def __init__(self, returncode: int | None, stdout: str, stderr: str, msg: str | None = None):
        self.returncode, self.stdout, self.stderr = returncode, stdout, stderr
        head = msg or f"hacs exited with {returncode}"
        super().__init__(
            f"{head}\n--- stderr (tail) ---\n{stderr[-1500:]}\n--- stdout (tail) ---\n{stdout[-1500:]}"
        )


class HacsTimeout(HacsScriptError):
    """The script hit its timeout; ``stdout`` / ``stderr`` hold the partial output (``returncode`` is None)."""

    def __init__(self, timeout: float, stdout: str, stderr: str):
        self.timeout = timeout
        super().__init__(None, stdout, stderr, msg=f"hacs timed out after {timeout} s")


@dataclasses.dataclass
class ScriptResult:
    tags: dict[str, list]
    stdout: str
    stderr: str
    returncode: int
    wall_s: float
    parse_errors: list[str] = dataclasses.field(default_factory=list)


# ---- binary --------------------------------------------------------------------------------------------------------

def find_hacs(path: str | os.PathLike | None = None) -> pathlib.Path:
    """Explicit path, else ``$LANGLANDSCAPE_HACS``, else the Lane A build; returned resolved (absolute)."""
    p = pathlib.Path(path or os.environ.get(ENV_VAR) or DEFAULT_HACS).expanduser().resolve()
    if not p.is_file() or not os.access(p, os.X_OK):
        raise HacsNotFound(f"HACS binary missing or not executable: {p}")
    return p


def hacs_version(hacs: str | os.PathLike | None = None) -> str:
    r = subprocess.run([str(find_hacs(hacs)), "--version"], capture_output=True, text=True,
                       env=child_env(1), timeout=60)
    return (r.stdout or r.stderr).strip()


_SHA_CACHE: dict[tuple[str, int, int], str] = {}


def hacs_sha256(hacs: str | os.PathLike | None = None) -> str:
    """sha256 of the binary file, cached per (path, mtime, size)."""
    exe = find_hacs(hacs)
    st = exe.stat()
    key = (str(exe), st.st_mtime_ns, st.st_size)
    if key not in _SHA_CACHE:
        h = hashlib.sha256()
        with exe.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1 << 20), b""):
                h.update(chunk)
        _SHA_CACHE[key] = h.hexdigest()
    return _SHA_CACHE[key]


# ---- parsing -------------------------------------------------------------------------------------------------------

_TAG = re.compile(r"^@@([A-Za-z0-9_.\-]+)(?:[ \t]+(.*))?$")


def parse_tags(stdout: str, errors: list[str] | None = None) -> dict[str, list]:
    """Collect the payloads of all ``@@TAG <json>`` lines, in order, per tag (empty payload -> ``None``).

    A malformed ``@@`` line or undecodable payload raises ``HacsParseError``, unless ``errors`` is a list: then a
    message ``"line <i>: <reason>: <line>"`` is appended to it and the line is skipped."""
    tags: dict[str, list] = {}
    for i, line in enumerate(stdout.splitlines(), 1):
        if not line.startswith("@@"):
            continue
        m = _TAG.match(line.rstrip("\r"))
        if not m:
            err = f"line {i}: malformed tag line: {line[:200]!r}"
        else:
            payload = (m.group(2) or "").strip()
            if not payload:
                tags.setdefault(m.group(1), []).append(None)
                continue
            try:
                value = json.loads(payload)
            except json.JSONDecodeError as e:
                err = f"line {i}: bad JSON payload of @@{m.group(1)} ({e.msg}): {line[:200]!r}"
            else:
                tags.setdefault(m.group(1), []).append(value)
                continue
        if errors is None:
            raise HacsParseError(err)
        errors.append(err)
    return tags


def _text(x: Any) -> str:
    if x is None:
        return ""
    return x.decode("utf-8", "replace") if isinstance(x, bytes) else x


def run_script(src: str, *, hacs: str | os.PathLike | None = None, threads: int = 4,
               timeout: float = 3600, check: bool = True, env_extra: dict[str, str] | None = None) -> ScriptResult:
    """Write ``src`` to a temporary ``.oc`` file (outside the repository) and run ``hacs --script`` on it.

    ``check=True``: a nonzero exit raises ``HacsScriptError``, a parse error ``HacsParseError``. ``check=False``:
    neither raises (parse errors go to ``ScriptResult.parse_errors``). A timeout always raises ``HacsTimeout``."""
    exe = find_hacs(hacs)
    env = child_env(threads, env_extra)
    with tempfile.TemporaryDirectory(prefix="hacs_bridge_") as td:
        fn = pathlib.Path(td) / "script.oc"
        fn.write_text(src, encoding="utf-8")
        t = time.perf_counter()
        try:
            r = subprocess.run([str(exe), "--script", str(fn)], capture_output=True, text=True,
                               env=env, timeout=timeout, cwd=td)
        except subprocess.TimeoutExpired as e:
            raise HacsTimeout(timeout, _text(e.stdout), _text(e.stderr)) from None
        wall = time.perf_counter() - t
    if check and r.returncode != 0:
        raise HacsScriptError(r.returncode, r.stdout, r.stderr)
    errors: list[str] = []
    tags = parse_tags(r.stdout, None if check else errors)
    return ScriptResult(tags, r.stdout, r.stderr, r.returncode, wall, errors)


def oc_matrix(p: int, rows: Iterable[Sequence[int]]) -> str:
    """Console literal ``matrix(p, [[a, b], [c, d]])`` with entries reduced mod ``p``."""
    rows = [[int(x) % p for x in r] for r in rows]
    if not rows or any(len(r) != len(rows[0]) for r in rows):
        raise ValueError("oc_matrix needs a nonempty list of equal-length rows")
    return f"matrix({int(p)}, [" + ", ".join("[" + ", ".join(map(str, r)) + "]" for r in rows) + "])"


# ---- HZ settings ---------------------------------------------------------------------------------------------------

DOCUMENTED_HZ_DEFAULT_FP = "0x8ffc29730c4f9672"   # kHZDefaultFingerprint, src/hacs/Golden/GoldenHarness.cpp:2710
DOCUMENTED_HZ_THETA_ORDER = "lex"                  # RationalSettings::theta_order default, Integral/HeckeZRational.h:142
_HZ_CACHE: dict[str, dict] = {}
_HZ_SCRIPT = ('set coefficient_ring = "Z";\nE = hecke_structure(11, 0, "anemic");\n'
              'print("@@HZFP " + json(E.settings_fingerprint));\n')


def hz_settings(hacs: str | os.PathLike | None = None) -> dict:
    """The HZ (integral Hecke structure) settings of the binary: ``{"default_fp", "hz_theta_order", "source"}``.

    ``default_fp`` is REPORTED: the ``settings_fingerprint`` of a default ``hecke_structure(11, 0, "anemic")`` record.
    The theta order has no console field; it is INFERRED: ``RationalSettings::canonical_text`` prints a theta_order
    key only when it is not ``lex``, and the fingerprint is the FNV-1a-64 of that text, so the documented default
    fingerprint means ``lex`` (any other fingerprint gives ``"unknown"``). If the run fails, the documented values are
    returned with ``source = "documented-not-reported"``. Cached per binary sha256."""
    exe = find_hacs(hacs)
    key = hacs_sha256(exe)
    if key not in _HZ_CACHE:
        try:
            r = run_script(_HZ_SCRIPT, hacs=exe, threads=1, timeout=300)
            fp = r.tags["HZFP"][0]
            if not isinstance(fp, str):
                raise HacsParseError(f"settings_fingerprint not a string: {fp!r}")
            _HZ_CACHE[key] = {
                "default_fp": fp,
                "hz_theta_order": DOCUMENTED_HZ_THETA_ORDER if fp == DOCUMENTED_HZ_DEFAULT_FP else "unknown",
                "source": "reported: hecke_structure(11,0,'anemic').settings_fingerprint; "
                          "theta order inferred from the fingerprint",
            }
        except (HacsError, KeyError, IndexError):
            _HZ_CACHE[key] = {"default_fp": DOCUMENTED_HZ_DEFAULT_FP, "hz_theta_order": DOCUMENTED_HZ_THETA_ORDER,
                              "source": "documented-not-reported"}
    return dict(_HZ_CACHE[key])


# ---- provenance ----------------------------------------------------------------------------------------------------

def _repo_root() -> pathlib.Path | None:
    try:
        return _results.repo_root().resolve()
    except (subprocess.SubprocessError, OSError):
        return None


def public_path(p: str | os.PathLike, root: pathlib.Path | None = None) -> str:
    """A path safe for public result records: relative paths unchanged; absolute paths inside the repository root
    relative to it; any other absolute path reduced to its last three components (e.g. ``hacs-build/laneA/hacs``)."""
    s = os.fspath(p)
    if not os.path.isabs(s):
        return s
    q = pathlib.Path(s).resolve()
    root = _repo_root() if root is None else root
    if root is not None:
        try:
            return q.relative_to(root).as_posix()
        except ValueError:
            pass
    return "/".join(q.parts[-3:]) if len(q.parts) > 3 else q.name


def provenance(script: str, params: dict, runtime_s: float, hacs: str | os.PathLike | None = None, *,
               notes: str | None = None, hz: bool = False) -> dict:
    """Provenance block in the ``code/results`` convention (``results.write``'s keys: script, commit, params, date,
    runtime_s, python, pari_version, notes), extended by ``dirty``, ``hacs_version``, ``hacs_sha256``, ``hacs_binary``
    (and ``hz_settings`` if ``hz``). No absolute path is recorded: ``script``, ``hacs_binary`` and absolute-path
    string values of ``params`` go through ``public_path``."""
    exe = find_hacs(hacs)
    root = _repo_root()
    commit = _results.git_commit()
    out = {
        "script": public_path(script, root),
        "commit": commit,
        "dirty": commit.endswith("-dirty"),
        "params": {k: (public_path(v, root) if isinstance(v, str) and os.path.isabs(v) else v)
                   for k, v in params.items()},
        "date": _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat(),
        "runtime_s": runtime_s,
        "python": platform.python_version(),
        "pari_version": _results._pari_version(),
        "notes": notes,
        "hacs_version": hacs_version(exe),
        "hacs_sha256": hacs_sha256(exe),
        "hacs_binary": public_path(exe, root),
    }
    if hz:
        out["hz_settings"] = hz_settings(exe)
    return out
