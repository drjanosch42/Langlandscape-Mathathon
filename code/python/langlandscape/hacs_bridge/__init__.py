# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Python bridge to the HACS console (``hacs --script``): generate ``.oc`` source, run, parse ``@@TAG <json>``.

Console only: no hooks into, and no edits of, upstream HACS (plan HACS-JL-PLAN, HJ-0 / Lane A).
"""

from .runner import (
    HacsError,
    HacsNotFound,
    HacsParseError,
    HacsScriptError,
    HacsTimeout,
    ScriptResult,
    child_env,
    find_hacs,
    forbidden_env,
    hacs_sha256,
    hz_settings,
    is_forbidden,
    public_path,
    hacs_version,
    oc_matrix,
    provenance,
    run_script,
)

__all__ = [
    "HacsError", "HacsNotFound", "HacsScriptError", "ScriptResult", "find_hacs",
    "forbidden_env", "hacs_version", "oc_matrix", "provenance", "run_script",
    "HacsParseError", "HacsTimeout", "child_env", "hacs_sha256", "hz_settings", "is_forbidden", "public_path",
]
