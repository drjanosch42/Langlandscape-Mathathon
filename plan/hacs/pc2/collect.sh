#!/bin/bash
# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
# Run on the laptop after the census: copy the tarball back and place it. Usage: collect.sh <ssh-host:WORK> [repo-root]
set -euo pipefail
SRCDIR="${1:?usage: collect.sh <host:WORK dir> [repo-root]}"; REPO="${2:-.}"
T="$(mktemp -d)"
rsync -av "$SRCDIR"/census_out/ "$T"/
( cd "$T" && sha256sum -c census_q*.tar.gz.sha256 )
SZ=$(du -sb "$T"/census_q*.tar.gz | cut -f1)
if [ "$SZ" -le 10000000 ]; then
    D="$REPO/code/results/laneB/census"; mkdir -p "$D"; cp "$T"/census_q*.tar.gz* "$T"/reads.log "$T"/congruence_k.json "$T"/binaries.sha256 "$D"/
    echo "copied to $D (<= 10 MB, may be committed on wip-code via the global master)"
else
    echo "tarball is $SZ bytes > 10 MB: keep it OUTSIDE git (e.g. ~/data/hacs-run/laneB/census/) and reference its sha256 only"
    mkdir -p "$HOME/data/hacs-run/laneB/census"; cp "$T"/* "$HOME/data/hacs-run/laneB/census/"
    echo "small files (reads.log? congruence_k.json, binaries.sha256) may still go to $REPO/code/results/laneB/census/ if each is small"
fi
