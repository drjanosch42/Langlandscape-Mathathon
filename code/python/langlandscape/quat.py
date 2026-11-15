"""Definite quaternion algebras over Q ramified exactly at a squarefree D (odd omega(D)).

``DefiniteAlgebra(D)`` builds ``B = (a, b)_Q`` with ``a, b < 0``, a maximal order ``O`` (PARI ``alginit``),
and does exact lattice arithmetic (Fractions, PARI ``mathnf``/``qfminim``) on left ideals of ``O``:

* right order of an ideal,
* ``l``-neighbours (left ideals ``I*K`` with ``K`` a left ideal of norm ``l`` of the right order),
* principality of ``conj(I)*J`` (a lattice vector of minimal reduced norm; ``qfminim`` on the norm form),
* unit group order ``|Gamma_x| = |O_r(I)^x|``.

References: stage tex ``plan/staged/stage-01-quaternion-foundations.tex``, ``def:s01-classset`` (class set
``X_B = B^x \\ B^_f^x / O^_^x``) and ``thm:s01-mass`` (a) (Eichler mass formula, cited: Voight, *Quaternion
Algebras*, Thm. 25.1.1; class sets: Voight Thm. 17.1.1); the mathematical write-up lives under ``mathematics/``.

Convention. We work with *left* ideals ``I = O x`` (``x in B^_f^x``) and their *right* orders
``O_r(I) = x^{-1} O x``; the tex uses the mirror side ``x O^``. Conjugation ``I -> conj(I)`` swaps the two sides,
so both give the same class set and the same multiset ``{|Gamma_x|}``, where
``Gamma_x = B^x cap x O^^x x^{-1}`` is identified with ``O_r(I)^x`` (units of reduced norm 1, including ``-1``).

Deviation from the brief ("isometry by ``qfisom`` on norm forms"). The class test used here is exact:
``I ~ J`` (i.e. ``J = I alpha`` with ``alpha in B^x``) iff ``conj(I) J`` contains an element of reduced norm
``nrd(I) nrd(J)``, which ``qfminim`` decides on the integral norm form of ``conj(I) J``. Isometry of the
normalised norm forms ``(I, nrd/nrd(I))`` and ``(J, nrd/nrd(J))`` is only a *necessary* condition (``x -> x alpha``),
and it is a coarser invariant: the norm form only sees the lattice up to isometry, and the natural "isometry of
norm forms" classification -- that of the right orders ``(O_r(I), nrd)`` -- detects ``O_r(I) ~= O_r(J)``
(conjugacy of maximal orders), so it counts the *type number* ``t(D) <= h(D)``, not ``h(D)`` (e.g. ``D = 37``:
``t = 2``, ``h = 3``; the two classes with conjugate right orders are not separated). We use
``qfisom`` only as a fast necessary-condition pre-filter in :meth:`DefiniteAlgebra.equivalent`.
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from functools import reduce
from math import gcd

from .pari import get_pari



def _lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def prime_factors(n: int) -> list[int]:
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def is_squarefree(n: int) -> bool:
    return all(n % (p * p) for p in prime_factors(n))


def find_ab(D: int, bound: int = 400) -> tuple[int, int]:
    """Smallest-height ``(a, b)``, ``a, b < 0``, with ``(a, b)_Q`` ramified exactly at ``D`` and infinity.

    Candidates ``-bound <= b <= a <= -1`` are tried by increasing ``|ab|``; only ``|ab| <= 8*bound`` is kept, which
    keeps the candidate list small (``(-D, -1)``, ``(-D, -2)``, ``(-2D, -p)`` etc. have ``|ab| <= 8*bound`` for all
    ``D <= bound``). If no candidate works a ``RuntimeError`` is raised and ``bound`` must be increased.
    """
    pari = get_pari()
    target = set(prime_factors(D))
    if len(target) % 2 == 0:
        raise ValueError("omega(D) must be odd for a definite algebra")
    cands = sorted(((-a) * (-b), a, b) for a in range(-bound, 0) for b in range(a, 0) if a * b <= bound * 8)
    for _, a, b in cands:
        ps = set(prime_factors(2 * a * b))
        ram = {p for p in ps if int(pari.hilbert(a, b, p)) == -1}
        if ram == target:
            return a, b
    raise RuntimeError(f"no (a,b) found for D={D}")


class Lattice:
    """Full-rank lattice in B, canonical HNF basis (4 tuples of Fractions in PARI's algebra basis); hashable key ``.key``."""

    __slots__ = ("basis", "key")

    def __init__(self, gens):
        pari = get_pari()
        gens = [tuple(Fraction(c) for c in g) for g in gens]
        den = reduce(_lcm, (c.denominator for g in gens for c in g), 1)
        cols = [[int(c * den) for c in g] for g in gens]
        M = pari.matrix(4, len(cols), [cols[j][i] for i in range(4) for j in range(len(cols))])
        H = pari.mathnf(M)
        if int(pari.matsize(H)[1]) != 4:
            raise ValueError("lattice is not of full rank")
        self.basis = [tuple(Fraction(int(H[i, j]), den) for i in range(4)) for j in range(4)]
        self.key = tuple(self.basis)


class DefiniteAlgebra:
    def __init__(self, D: int):
        if D < 2 or not is_squarefree(D):
            raise ValueError("D must be squarefree >= 2")
        self.D = D
        pari = get_pari()
        self.a, self.b = find_ab(D)
        A = pari(f"alginit(nfinit(y),[{self.a},{self.b}])")
        mt = pari.algmultable(A)
        # C[k][i][j] = coefficient of e_i in e_k * e_j
        self.C = [[[Fraction(int(mt[k][i, j])) for j in range(4)] for i in range(4)] for k in range(4)]
        # regular representation has trace 2*trd
        self.trd_basis = [sum(self.C[k][i][i] for i in range(4)) / 2 for k in range(4)]
        basis = [tuple(Fraction(int(k == m)) for m in range(4)) for k in range(4)]
        self.one = basis[0]
        if any(self.mul(self.one, x) != x or self.mul(x, self.one) != x for x in basis):
            raise RuntimeError("PARI's first algebra basis vector is not 1")
        # PARI's algebra basis is already an integral basis of a maximal order (checked in _check_maximal)
        self.O = Lattice(basis)
        # smallest prime l not dividing D (l-neighbour graph is connected for l unramified)
        self.ell = next(p for p in itertools.count(2) if prime_factors(p) == [p] and D % p)
        self._check_maximal()

    # ---- arithmetic -------------------------------------------------
    def mul(self, x: tuple, y: tuple) -> tuple:
        out = [Fraction(0)] * 4
        for k in range(4):
            if x[k] == 0:
                continue
            for i in range(4):
                out[i] += x[k] * sum(self.C[k][i][j] * y[j] for j in range(4))
        return tuple(out)

    def trd(self, x: tuple) -> Fraction:
        return sum(t * c for t, c in zip(self.trd_basis, x))

    def conj(self, x: tuple) -> tuple:
        t = self.trd(x)
        return tuple(t * o - c for o, c in zip(self.one, x))

    def nrd(self, x: tuple) -> Fraction:
        return self.mul(self.conj(x), x)[0]

    def lmul(self, L1: Lattice, L2: Lattice) -> Lattice:
        return Lattice([self.mul(x, y) for x in L1.basis for y in L2.basis])

    def lconj(self, L: Lattice) -> Lattice:
        return Lattice([self.conj(x) for x in L.basis])

    def scale(self, L: Lattice, s) -> Lattice:
        s = Fraction(s)
        return Lattice([tuple(s * c for c in x) for x in L.basis])

    def gram(self, L: Lattice):
        """Integer Gram matrix (PARI) of ``(x,y) -> trd(x conj(y))`` on ``L``; ``x^T G x = 2 nrd(x)``."""
        pari = get_pari()
        n = [[self.trd(self.mul(x, self.conj(y))) for y in L.basis] for x in L.basis]
        if any(c.denominator != 1 for r in n for c in r):
            raise ValueError("non-integral Gram matrix (lattice not in O)")
        return pari.matrix(4, 4, [int(n[i][j]) for i in range(4) for j in range(4)])

    def _check_maximal(self):
        pari = get_pari()
        G = self.gram(self.O)
        d = abs(int(pari.matdet(G)))
        if d != self.D**2:
            raise RuntimeError(f"order is not maximal / wrong discriminant: det={d}, D^2={self.D**2}")

    # ---- ideals -----------------------------------------------------
    def right_order(self, I: Lattice, N: int) -> Lattice:
        return self.scale(self.lmul(self.lconj(I), I), Fraction(1, N))

    def neighbours(self, I: Lattice, N: int) -> list[tuple[Lattice, int]]:
        """The ``l+1`` left ideals ``I*K`` (reduced norm ``N*l``), ``K`` a norm-``l`` left ideal of ``O_r(I)``."""
        l = self.ell
        R = self.right_order(I, N)
        lR = self.scale(R, l)
        seen: dict = {}
        for co in itertools.product(range(l), repeat=4):
            if not any(co):
                continue
            alpha = tuple(sum(c * r[i] for c, r in zip(co, R.basis)) for i in range(4))
            if self.nrd(alpha) % l:
                continue
            K = Lattice([self.mul(r, alpha) for r in R.basis] + lR.basis)
            if K.key in seen:
                continue
            seen[K.key] = K
        if len(seen) != l + 1:
            raise RuntimeError(f"expected {l+1} neighbours, got {len(seen)}")
        return [(self.lmul(I, K), N * l) for K in seen.values()]

    def equivalent(self, I: Lattice, NI: int, J: Lattice, NJ: int) -> bool:
        """Left ideals ``I, J`` of ``O`` lie in the same class iff ``conj(I) J`` has an element of reduced norm ``NI*NJ``.

        Pre-filter (necessary condition): if ``J = I alpha`` then ``x -> x alpha`` is an isometry
        ``(I, nrd/NI) -> (J, nrd/NJ)``, so non-isometric normalised norm forms (``qfisom``) exclude equivalence.
        """
        pari = get_pari()
        if I.key == J.key:
            return True
        if not pari.qfisom(self.gram(I) / NI, self.gram(J) / NJ):
            return False
        L = self.lmul(self.lconj(I), J)
        G = self.gram(L)
        res = pari.qfminim(G, 2 * NI * NJ, None, 0)
        return int(res[0]) > 0

    def unit_count(self, I: Lattice, N: int) -> int:
        """``|O_r(I)^x|`` (elements of reduced norm 1, including ``-1``)."""
        pari = get_pari()
        R = self.right_order(I, N)
        # x^T G x = 2 nrd(x); nrd is positive definite and integral on R, so the nonzero vectors with
        # x^T G x <= 2 are exactly the units. qfminim's first component is the number of all such vectors
        # (counting x and -x separately), i.e. |R^x|.
        return int(pari.qfminim(self.gram(R), 2, 10**6, 0)[0])

    def class_set(self) -> list[dict]:
        """Left ideal classes of ``O`` by BFS over ``l``-neighbours, with ``|Gamma_x|``."""
        reps: list[tuple[Lattice, int]] = [(self.O, 1)]
        queue = [0]
        while queue:
            idx = queue.pop(0)
            I, N = reps[idx]
            for J, NJ in self.neighbours(I, N):
                if not any(self.equivalent(R, NR, J, NJ) for R, NR in reps):
                    reps.append((J, NJ))
                    queue.append(len(reps) - 1)
        return [{"norm": N, "gamma": self.unit_count(I, N)} for I, N in reps]
