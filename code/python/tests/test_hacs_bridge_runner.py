# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Tests of ``langlandscape.hacs_bridge.runner`` (unit tests need no binary; integration tests skip without one)."""

import os

import pytest

from langlandscape.hacs_bridge import runner
from langlandscape.hacs_bridge import (HacsNotFound, HacsScriptError, find_hacs, forbidden_env, hacs_version,
                                       oc_matrix, provenance, run_script)


def _have_hacs():
    try:
        find_hacs()
        return True
    except HacsNotFound:
        return False


needs_hacs = pytest.mark.skipif(not _have_hacs(), reason="HACS binary not available")


# ---- unit tests ------------------------------------------------------------------------------------------------

def test_forbidden_env_contents():
    f = forbidden_env()
    for name in ("GOLDEN_EMIT", "GOLDEN_DUMP", "CONSOLE_EMIT_EXPECTED", "CLI_MANUAL_EMIT", "GOLDEN_STRICT",
                 "HECKE_LOCALITY_PROBE", "HECKE_HIDA_HEAVY", "HECKE_DUMP_TAU", "HECKE_DUMP_MEREL"):
        assert name in f


def test_is_forbidden_patterns():
    for name in forbidden_env():
        assert runner.is_forbidden(name)
    for name in ("HECKE_EXT_JSON_OUT", "ORBIFOLD_MP_DUMP", "HECKE_ATLAS_OUT", "GOLDEN_OUT", "GOLDEN_ANYTHING",
                 "HECKE_DUMP_NEW", "X_OUT", "FOO_DUMP", "BAR_EMIT", "GOLDEN_STRICT", "HECKE_LOCALITY_PROBE",
                 "HECKE_HIDA_HEAVY"):
        assert runner.is_forbidden(name), name
    for name in ("PATH", "ENGINE_THREADS", "ENGINE_DEVICE", "HECKE_ATLAS_IN", "OUTPUT", "HECKE_DESCENT_CELLS"):
        assert not runner.is_forbidden(name), name


def test_forbidden_env_covers_grep_findings():
    f = forbidden_env()
    for name in ("HECKE_EXT_JSON_OUT", "ORBIFOLD_MP_DUMP", "HECKE_ATLAS_OUT", "GOLDEN_OUT", "HECKE_DUMP_TAU_PAIR",
                 "HECKE_DUMP_SAT_CERT_CELLS", "HECKE_DUMP_HZ_CERT_CELLS", "HECKE_DUMP_TAU_RHO_CELLS", "HECKE_DUMP_EXZ2"):
        assert name in f


def test_env_sanitising():
    base = {"PATH": "/bin", "HOME": "/h", "LANG": "C.UTF-8", "GOLDEN_EMIT": "1", "HECKE_DUMP_ANYTHING": "/x",
            "HECKE_DUMP_TAU": "/y", "GOLDEN_STRICT": "1", "ENGINE_THREADS": "99", "ENGINE_DEVICE": "gpu",
            "HECKE_LAMBDA_ALL": "1", "HECKE_HIDA_HEAVY_CELLS": "1:2", "ENGINE_KERNEL": "x", "LD_PRELOAD": "evil.so",
            "HECKE_EXT_JSON_OUT": "/z", "KEEP": "me"}
    env = runner.sanitized_env(threads=3, base=base)
    assert env == {"PATH": "/bin", "HOME": "/h", "LANG": "C.UTF-8", "ENGINE_THREADS": "3"}
    assert runner.child_env(3, base=base) == env


def test_child_env_drops_parent_hooks(monkeypatch):
    monkeypatch.setenv("GOLDEN_EMIT", "1")
    monkeypatch.setenv("HECKE_EXT_JSON_OUT", "/tmp/x")
    monkeypatch.setenv("ENGINE_DEVICE", "gpu")
    monkeypatch.setenv("HECKE_LOCALITY_PROBE", "1")
    env = runner.child_env(2)
    for k in ("GOLDEN_EMIT", "HECKE_EXT_JSON_OUT", "ENGINE_DEVICE", "HECKE_LOCALITY_PROBE"):
        assert k not in env
    assert env["ENGINE_THREADS"] == "2"
    assert set(env) <= set(runner.ENV_ALLOWLIST) | {"ENGINE_THREADS"}


def test_child_env_extra():
    env = runner.child_env(1, {"ENGINE_DEVICE": "cpu", "HECKEZ_LOCAL_PAR": "seq", "LC_ALL": "C"}, base={})
    assert env == {"ENGINE_THREADS": "1", "ENGINE_DEVICE": "cpu", "HECKEZ_LOCAL_PAR": "seq", "LC_ALL": "C"}
    for bad in ("GOLDEN_EMIT", "GOLDEN_STRICT", "HECKE_EXT_JSON_OUT", "ORBIFOLD_MP_DUMP", "HECKE_ATLAS_OUT",
                "GOLDEN_OUT", "HECKE_DUMP_TAU", "HECKE_DUMP_NEW", "CLI_MANUAL_EMIT", "CONSOLE_EMIT_EXPECTED",
                "SOMETHING_OUT", "HECKE_LOCALITY_PROBE", "HECKE_HIDA_HEAVY",            # write-capable / interlock
                "HECKE_LAMBDA_ALL", "ENGINE_KERNEL", "HECKE_ATLAS_IN", "LD_PRELOAD",   # not allowlisted
                "ENGINE_THREADS"):                                                    # use `threads`
        with pytest.raises(ValueError):
            runner.child_env(1, {bad: "1"}, base={})
    with pytest.raises(ValueError):
        runner.child_env(1, {"ENGINE_DEVICE": "gpu"}, base={})


def test_parse_tags_fake_stdout():
    out = "noise\n@@A [1, 2]\n@@B {\"x\": \"y z\"}\n@@A 3\n@@bad no tag json\n#~ annotation\n"
    with pytest.raises(runner.HacsParseError):
        runner.parse_tags(out)  # '@@bad no tag json' is malformed JSON and must not pass silently
    with pytest.raises(ValueError):  # HacsParseError stays a ValueError (backward compatible)
        runner.parse_tags(out)
    out = "noise\n@@A [1, 2]\n@@B {\"x\": \"y z\"}\n@@A 3\nplain @@C 1\n"
    t = runner.parse_tags(out)
    assert t == {"A": [[1, 2], 3], "B": [{"x": "y z"}]}


def test_parse_tags_empty_tab_names():
    out = "@@E\n@@F   \n@@G\t\t\n@@T\t[1]\n@@a.b-c_9 2\n@@W  \t {\"k\": 1}  \n@@CR 5\r\n"
    assert runner.parse_tags(out) == {"E": [None], "F": [None], "G": [None], "T": [[1]], "a.b-c_9": [2],
                                      "W": [{"k": 1}], "CR": [5]}


def test_parse_tags_errors_list():
    out = "@@OK 1\n@@\n@@bad/tag 1\n@@TR [1, 2\n@@J nope\n@@OK 2\n"
    for bad in ("@@\n", "@@bad/tag 1\n", "@@TR [1, 2\n", "@@J nope\n"):
        with pytest.raises(runner.HacsParseError):
            runner.parse_tags(bad)
    errs: list = []
    assert runner.parse_tags(out, errs) == {"OK": [1, 2]}
    assert len(errs) == 4 and errs[0].startswith("line 2:")


def test_oc_matrix_format():
    assert oc_matrix(7, [[1, 2], [3, 4]]) == "matrix(7, [[1, 2], [3, 4]])"
    assert oc_matrix(7, [[-1, 8], [14, 6]]) == "matrix(7, [[6, 1], [0, 6]])"
    with pytest.raises(ValueError):
        oc_matrix(7, [[1, 2], [3]])
    with pytest.raises(ValueError):
        oc_matrix(7, [])


def test_find_hacs_missing(tmp_path):
    with pytest.raises(HacsNotFound):
        find_hacs(tmp_path / "nope")
    f = tmp_path / "notexec"
    f.write_text("x")
    f.chmod(0o644)
    with pytest.raises(HacsNotFound):
        find_hacs(f)


def test_find_hacs_env(tmp_path, monkeypatch):
    f = tmp_path / "hacs"
    f.write_text("#!/bin/sh\n")
    f.chmod(0o755)
    monkeypatch.setenv("LANGLANDSCAPE_HACS", str(f))
    assert find_hacs() == f.resolve()


def test_find_hacs_relative(tmp_path, monkeypatch):
    d = tmp_path / "b"
    d.mkdir()
    f = d / "hacs"
    f.write_text("#!/bin/sh\necho '@@R 1'\n")
    f.chmod(0o755)
    monkeypatch.chdir(tmp_path)
    assert find_hacs("b/hacs") == f.resolve() and find_hacs("b/hacs").is_absolute()
    monkeypatch.setenv("LANGLANDSCAPE_HACS", "b/hacs")
    assert find_hacs() == f.resolve()
    assert run_script("x").tags == {"R": [1]}   # child cwd = tempdir: works only with the resolved path


def _fake(tmp_path, body):
    fake = tmp_path / "hacs"
    fake.write_text('#!/bin/sh\nif [ "$1" = "--version" ]; then echo "fake 1.0"; exit 0; fi\n' + body)
    fake.chmod(0o755)
    return fake


def test_run_script_with_fake_binary(tmp_path, monkeypatch):
    fake = _fake(tmp_path, 'echo "@@V [$ENGINE_THREADS]"; echo "GOLDEN_EMIT=${GOLDEN_EMIT:-unset}"; '
                           'echo "HJO=${HECKE_EXT_JSON_OUT:-unset}"; echo "DEV=${ENGINE_DEVICE:-unset}"; '
                           'echo err >&2; exit ${FAKE_RC:-0}\n')
    monkeypatch.setenv("GOLDEN_EMIT", "1")
    monkeypatch.setenv("HECKE_EXT_JSON_OUT", "/tmp/x")
    monkeypatch.setenv("ENGINE_DEVICE", "gpu")
    r = run_script("x", hacs=fake, threads=2)
    assert r.tags == {"V": [[2]]} and r.returncode == 0 and r.parse_errors == []
    assert "GOLDEN_EMIT=unset" in r.stdout and "HJO=unset" in r.stdout and "DEV=unset" in r.stdout
    assert "DEV=cpu" in run_script("x", hacs=fake, env_extra={"ENGINE_DEVICE": "cpu"}).stdout
    with pytest.raises(ValueError):
        run_script("x", hacs=fake, env_extra={"HECKE_EXT_JSON_OUT": "/tmp/x"})
    assert hacs_version(fake) == "fake 1.0"
    monkeypatch.setenv("FAKE_RC", "3")   # not allowlisted: never reaches the child
    assert run_script("x", hacs=fake).returncode == 0


def test_run_script_failure_and_check_false(tmp_path):
    fake = _fake(tmp_path, 'echo "@@OK 1"; echo "@@TRUNC [1, 2"; echo err >&2; exit 3\n')
    with pytest.raises(HacsScriptError) as e:
        run_script("x", hacs=fake)
    assert e.value.returncode == 3 and "err" in e.value.stderr
    r = run_script("x", hacs=fake, check=False)
    assert r.returncode == 3 and r.tags == {"OK": [1]} and len(r.parse_errors) == 1 and "TRUNC" in r.parse_errors[0]
    fake2 = _fake(tmp_path, 'echo "@@J nope"; exit 0\n')
    with pytest.raises(runner.HacsParseError):
        run_script("x", hacs=fake2)
    assert run_script("x", hacs=fake2, check=False).parse_errors


def test_run_script_timeout(tmp_path):
    fake = _fake(tmp_path, 'echo "@@PART 1"; echo partial-err >&2; exec sleep 30\n')
    with pytest.raises(runner.HacsTimeout) as e:
        run_script("x", hacs=fake, timeout=1)
    assert isinstance(e.value, HacsScriptError) and e.value.returncode is None
    assert "@@PART 1" in e.value.stdout and "partial-err" in e.value.stderr


def test_script_result_backward_compatible():
    r = runner.ScriptResult({}, "", "", 0, 0.0)
    assert r.parse_errors == []


def test_public_path(tmp_path):
    root = tmp_path / "repo"
    (root / "code").mkdir(parents=True)
    assert runner.public_path(root / "code" / "x.py", root) == "code/x.py"
    assert runner.public_path("/home/someone/data/hacs-build/laneA/hacs", root) == "hacs-build/laneA/hacs"
    assert runner.public_path("code/python/x.py", root) == "code/python/x.py"


def test_provenance_fake(tmp_path, monkeypatch):
    fake = _fake(tmp_path, 'exit 0\n')
    p = provenance(str(runner._repo_root() / "code/python/x.py"), {"a": 1, "f": str(fake)}, 0.5, fake, notes="n")
    import hashlib
    from langlandscape import results
    assert p["hacs_sha256"] == hashlib.sha256(fake.read_bytes()).hexdigest()
    assert p["script"] == "code/python/x.py" and p["notes"] == "n" and p["hacs_version"] == "fake 1.0"
    home = os.path.expanduser("~")
    for v in (p["hacs_binary"], p["script"], p["params"]["f"]):
        assert not os.path.isabs(v) and home not in v and str(tmp_path) not in v
    assert p["params"]["f"] == p["hacs_binary"] == "/".join(fake.parts[-3:])
    assert {"script", "commit", "params", "date", "runtime_s", "python", "pari_version", "notes"} <= set(p)
    assert isinstance(p["dirty"], bool)
    # hz settings from a binary that cannot report them: the documented values
    h = provenance("x.py", {}, 0.0, fake, hz=True)["hz_settings"]
    assert h == {"default_fp": "0x8ffc29730c4f9672", "hz_theta_order": "lex", "source": "documented-not-reported"}


def test_sha256_cache(tmp_path):
    fake = _fake(tmp_path, 'exit 0\n')
    a = runner.hacs_sha256(fake)
    fake.write_text(fake.read_text() + "# changed\n")
    os.utime(fake, ns=(fake.stat().st_atime_ns, fake.stat().st_mtime_ns + 10**9))
    assert runner.hacs_sha256(fake) != a


# ---- integration tests -------------------------------------------------------------------------------------------

@needs_hacs
def test_version():
    assert "hacs" in hacs_version().lower() or hacs_version()


@needs_hacs
def test_tiny_script():
    r = run_script('print("@@HELLO " + json([1, 2, 3]));\n', threads=1, timeout=120)
    assert r.returncode == 0 and r.tags["HELLO"] == [[1, 2, 3]]


@needs_hacs
def test_script_failure_raises():
    with pytest.raises(HacsScriptError):
        run_script('assert(false, "boom");\n', timeout=120)


@needs_hacs
def test_matrix_roundtrip_charpoly():
    # [[1,2],[3,4]] mod 7: charpoly x^2 - 5x - 2 = x^2 + 2x + 5; console coefficients are printed low -> high.
    src = (f"A = {oc_matrix(7, [[1, 2], [3, 4]])};\n"
           'cp = charpoly(A);\nprint("@@CP " + json(coeffs(cp)));\nprint("@@RK " + json(rank(A)));\n')
    r = run_script(src, threads=1, timeout=120)
    assert r.tags["CP"] == [[5, 2, 1]]
    assert r.tags["RK"] == [2]


@needs_hacs
def test_provenance_keys():
    p = provenance("tests/x.py", {"a": 1}, 0.5, hz=True)
    for k in ("script", "commit", "dirty", "params", "date", "runtime_s", "python", "pari_version", "notes",
              "hacs_version", "hacs_sha256", "hacs_binary", "hz_settings"):
        assert k in p
    assert isinstance(p["dirty"], bool) and len(p["hacs_sha256"]) == 64
    assert not os.path.isabs(p["hacs_binary"]) and os.path.expanduser("~") not in p["hacs_binary"]


@needs_hacs
def test_hz_settings_reported():
    h = runner.hz_settings()
    assert h["default_fp"] == "0x8ffc29730c4f9672" and h["hz_theta_order"] == "lex"
    assert h["source"].startswith("reported")


@needs_hacs
def test_real_child_env_drops_engine_hooks(monkeypatch):
    # settings() shows the env-only engine knobs the child saw: a parent ENGINE_TRACE_NODES must not arrive
    monkeypatch.setenv("ENGINE_TRACE_NODES", "1")
    monkeypatch.setenv("GOLDEN_EMIT", "1")
    monkeypatch.setenv("ENGINE_DEVICE", "gpu")
    r = run_script('s = settings();\nprint("@@S " + json([s.trace_nodes.value, s.device.value, s.threads.value]));\n',
                   threads=2, timeout=120)
    assert r.tags["S"] == [["", "cpu", 2]]


@needs_hacs
def test_smoke_script_runs():
    import pathlib
    src = (pathlib.Path(__file__).resolve().parents[2] / "hacs/jl/smoke/hj0_smoke.oc").read_text()
    r = run_script(src, threads=4, timeout=120)
    assert r.returncode == 0 and r.wall_s < 60 and r.parse_errors == []
    assert r.tags["descent_module"][0][0] == "ok"
    assert [o[2] for o in r.tags["descent_module_op"]] == [[1, 1, 17, 13], [1, 23, 18, 21]]
    assert r.tags["hida_lambda"][0][2][2]["charpoly"] == [450, 1] and (-450) % 11**3 == 534612 % 11**3
