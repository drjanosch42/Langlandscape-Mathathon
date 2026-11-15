# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S05-C3 (T05-3): (X2) at Gamma_0-level, pointer to stage-03 T1 (rem:s05-O46).

No new heavy computation: reads ``code/results/s03/T1.json`` (Mazur check at level 1, DR graph of B_q at
``O^_^x``), recomputes ``num((q-1)/12)`` with :class:`fractions.Fraction` and compares it with the stored
``|Phi^comb|``.  Output: ``code/results/s05/T05-3.json``.
"""

from __future__ import annotations

import time
from fractions import Fraction

from .. import results

QS = (11, 23, 37, 101, 131)
SOURCE = "code/results/s03/T1.json"


def num_q_minus_1_over_12(q: int) -> int:
    """Numerator of ``(q-1)/12`` as a reduced fraction."""
    return Fraction(q - 1, 12).numerator


def summarise(stage3: dict) -> dict:
    """Per-q summary of the stage-03 T1 rows, with the recomputed Mazur value."""
    rows = stage3["data"]
    out = {}
    for q in QS:
        r = rows[str(q)]
        num = num_q_minus_1_over_12(q)
        out[str(q)] = {
            "q": q,
            "h": r["h"],
            "phi_order_stage03": r["phi_order"],
            "phi_divisors_stage03": r["phi_divisors"],
            "phi_cyclic_stage03": r["phi_cyclic"],
            "num_q_minus_1_over_12": num,
            "equal": r["phi_order"] == num,
        }
    return out


def main() -> None:
    t0 = time.perf_counter()
    stage3 = results.read("s03/T1.json")
    data = summarise(stage3)
    runtime = time.perf_counter() - t0
    results.write(
        "s05/T05-3.json",
        data,
        script="python3 -m langlandscape.comparison.pointer_s03",
        params={
            "q": list(QS),
            "source": SOURCE,
            "source_commit": stage3["provenance"]["commit"],
            "source_script": stage3["provenance"]["script"],
            "source_date": stage3["provenance"]["date"],
        },
        runtime_s=runtime,
        notes="pointer to stage-03 T1; no new computation beyond num((q-1)/12)",
    )
    for q in QS:
        r = data[str(q)]
        print(q, r["h"], r["phi_order_stage03"], r["num_q_minus_1_over_12"], r["equal"])


if __name__ == "__main__":
    main()
