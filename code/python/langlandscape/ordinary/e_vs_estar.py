# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S04-M10a (audit item M9.5): ``e != e*`` on ``Z_p[X_1]`` for ``D = 2``, ``M = 7``, ``p = 5``, ``s = 1``.

Uses the S04-C3a setting of :mod:`langlandscape.ordinary.sign_pin` (Hurwitz order, level ``U_1(35)``, 48 points,
``w_x = 1``, so the Brandt adjoint is the transpose).  ``e = e_{U_p}`` and ``e* = e_{U_p^*}`` (``U_p^* = U_p^T``) are
computed mod ``5^4`` with :func:`langlandscape.ordinary.proj.ordinary_projector`; ``e* = e^T`` is checked, and
``e != e*`` is shown by ``e - e^T != 0 mod 5`` (lem:s04-ekills(d), rem:s04-eestar).

Run: ``cd code/python && python -m langlandscape.ordinary.e_vs_estar``.
"""

from __future__ import annotations

import numpy as np

from .. import results
from . import sign_pin
from .proj import ordinary_projector

M_EXP = 4


def run(write: bool = True) -> dict:
    with results.Timer() as tm:
        C = sign_pin.Setting()
        U = C.Up()
        p = sign_pin.P
        q = p**M_EXP
        E = ordinary_projector(U, p, M_EXP)
        Es = ordinary_projector(U.T, p, M_EXP)
        e, es = E.e % q, Es.e % q
        idem = bool(((e @ e - e) % q == 0).all()) and bool(((es @ es - es) % q == 0).all())
        estar_is_transpose = bool(((es - e.T) % q == 0).all())
        e_eq_estar_mod_p = bool(((e - es) % p == 0).all())
        commute_mod_p = bool(((e @ es - es @ e) % p == 0).all())
    assert idem and estar_is_transpose and not e_eq_estar_mod_p
    data = {
        "example": {"D": sign_pin.D, "B": "Hurwitz quaternions (-1,-1)_Q", "M": sign_pin.M, "p": p, "s": sign_pin.S,
                    "level": "U_1(35)", "S_1_size": int(U.shape[0]), "w_x": 1},
        "precision": f"mod {p}^{M_EXP}",
        "checks": {
            "rank_e": int(E.rank), "rank_e_star": int(Es.rank),
            "e_and_e_star_idempotent": idem,
            "e_star_eq_e_transpose": estar_is_transpose,
            "e_eq_e_star_mod_p": e_eq_estar_mod_p,
            "e_e_star_commute_mod_p": commute_mod_p,
        },
        "conclusion": "e != e* (e is not symmetric mod 5)",
    }
    if write:
        results.write("s04/M95_e_vs_estar.json", data,
                      script="code/python/langlandscape/ordinary/e_vs_estar.py "
                      "(cd code/python && python -m langlandscape.ordinary.e_vs_estar)",
                      params={"D": sign_pin.D, "M": sign_pin.M, "p": p, "s": sign_pin.S, "m": M_EXP},
                      runtime_s=round(tm.seconds, 3), notes="S04-M10a / audit M9.5: e != e* at D=2, M=7, p=5, s=1")
    return data


if __name__ == "__main__":
    print(run()["checks"])
