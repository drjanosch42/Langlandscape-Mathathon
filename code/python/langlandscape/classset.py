"""Class sets ``X_B = B^x \\ B^_f^x / O^_^x`` of definite quaternion algebras and the Eichler mass check.

Statements: ``def:s01-classset`` and ``thm:s01-mass`` (a) / ``ex:s01-masschecks`` of
``plan/staged/stage-01-quaternion-foundations.tex`` (mass formula cited: Voight, *Quaternion Algebras*,
Thm. 25.1.1); background under ``mathematics/``. Computation: :mod:`langlandscape.quat` (left ideals and right
orders; see its docstring for the side convention and ``Gamma_x = O_r(I_x)^x``).

Run ``python -m langlandscape.classset`` (from ``code/python``) to write ``code/results/s01/classsets.json``;
this is the only writer of that file.
"""

from __future__ import annotations

from fractions import Fraction

from . import results
from .quat import DefiniteAlgebra, is_squarefree, prime_factors

TABLE_D_MAX = 60
EXTRA_D = (66, 70, 78)
PRIME_D_MAX = 53


def euler_phi_ram(D: int) -> int:
    """``phi(D) = prod_{p | D} (p - 1)``."""
    out = 1
    for p in prime_factors(D):
        out *= p - 1
    return out


def definite_D_list() -> list[int]:
    """Squarefree ``D <= 60`` with omega(D) odd, plus 66, 70, 78."""
    Ds = [D for D in range(2, TABLE_D_MAX + 1) if is_squarefree(D) and len(prime_factors(D)) % 2 == 1]
    return Ds + list(EXTRA_D)


def class_set(D: int) -> dict:
    """Class number, sorted ``|Gamma_x|`` multiset and mass of ``B_D`` at ``O^_^x``."""
    B = DefiniteAlgebra(D)
    cs = B.class_set()
    gammas = sorted(c["gamma"] for c in cs)
    mass = sum(Fraction(1, g) for g in gammas)
    return {"D": D, "a": B.a, "b": B.b, "h": len(gammas), "gammas": gammas,
            "mass": mass, "expected_mass": Fraction(euler_phi_ram(D), 24)}


def compute_all() -> dict:
    Ds = sorted(set(definite_D_list()))
    return {str(D): class_set(D) for D in Ds}


def main() -> None:
    with results.Timer() as t:
        data = compute_all()
    results.write(
        "s01/classsets.json", data, script="code/python/langlandscape/classset.py",
        params={"D_list": sorted(int(k) for k in data), "ell": "smallest prime not dividing D"},
        runtime_s=t.seconds,
        notes="mass = sum 1/|Gamma_x| compared with phi(D)/24; |Gamma_x| = |O_r(I_x)^x| (including -1)",
    )


if __name__ == "__main__":
    main()
