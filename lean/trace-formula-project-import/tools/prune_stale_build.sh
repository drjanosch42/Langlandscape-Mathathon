#!/usr/bin/env bash
# COPY for the algebraic_jl fork (L-A, 2026-11-14) of tools/prune_stale_build.sh @84818d0, unchanged except this line: repo resolves to algebraic_jl/, lean dir = algebraic_jl/lean.
# tools/prune_stale_build.sh [--dry-run]   (T-13)
# Deletes our own artifacts under lean/.lake/build/{lib,ir}/ whose module has no source file in lean/.
# Never touches .lake/packages, never runs `lake clean`. lbuild.sh calls it before every build; it needs no Lean.
set -euo pipefail
repo="$(cd "$(dirname "$0")/.." && pwd)"
exec python3 "$repo/tools/stale_build.py" prune "$@"
