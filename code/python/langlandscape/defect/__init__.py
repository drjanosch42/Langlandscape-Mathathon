# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""Stage-6 integral JL defect computations.

Modules: :mod:`.gram` (S06-C5, definite side: Brandt Gram matrices, ``eta^B``); :mod:`.hecke_alg` and
:mod:`.congruence` (S06-C1: Z-orders from Hecke matrices, localisation, ``a``, ``b``, ``eta(S, mu)``, ``c = lam(b)``,
Gorenstein test; API overview at the top of :mod:`.congruence`).
"""
