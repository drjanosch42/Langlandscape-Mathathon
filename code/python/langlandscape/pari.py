"""Shared PARI instance (cypari2).

One ``cypari2.Pari()`` per process, with 1 GiB of PARI stack allocated once.
Single-threaded by policy: PARI's ``nbthreads`` is pinned to 1.
"""

from __future__ import annotations

import cypari2

_PARI = None


def get_pari():
    """Return the shared ``cypari2.Pari()`` instance, initialising it on first use."""
    global _PARI
    if _PARI is None:
        pari = cypari2.Pari()
        try:
            pari.default("debugmem", 0)
        except Exception:
            pass
        pari.allocatemem(1 << 30)
        try:
            pari.default("nbthreads", 1)
        except Exception:
            pass
        _PARI = pari
    return _PARI
