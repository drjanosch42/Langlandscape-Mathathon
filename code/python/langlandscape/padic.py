"""p-adic splittings of definite quaternion algebras over Q (mod p^n).

Conventions
-----------
* ``B = (a, b)_Q`` has Q-basis ``1, i, j, ij`` with ``i^2 = a``, ``j^2 = b``, ``ji = -ij``.
  Elements are 4-tuples of rationals (``fractions.Fraction``) in this basis.
* A maximal order ``O`` is given by a Z-basis ``basis = [b_0, .., b_3]`` (each a 4-tuple in
  the basis ``1, i, j, ij``); elements of ``O`` are integer 4-tuples w.r.t. ``basis``.
* For a prime ``p`` with ``p`` not dividing ``2ab`` (so in particular ``p`` does not divide
  ``disc B``) we construct matrices ``I, J`` in ``M_2(Z/p^n)`` with ``I^2 = a``, ``J^2 = b``,
  ``IJ = -JI`` (Hensel lifting):

  - if ``a`` is a square mod ``p``: ``I = diag(alpha, -alpha)``, ``J = [[0, b], [1, 0]]``
    with ``alpha^2 = a``;
  - otherwise ``I = [[0, a], [1, 0]]``, ``J = [[c, -a e], [e, -c]]`` with ``c^2 - a e^2 = b``.

  ``iota(x0 + x1 i + x2 j + x3 ij) = x0 + x1 I + x2 J + x3 IJ``.  Since ``p`` does not divide
  ``2ab`` the coordinates of elements of ``O`` are ``p``-integral, so ``iota(O)`` lies in
  ``M_2(Z_p)``; we *check* that the images of ``basis`` span ``M_2(F_p)`` (bijectivity mod ``p``),
  hence ``iota: O tensor Z_p -> M_2(Z_p)`` is an isomorphism (Nakayama), and that ``iota`` is
  multiplicative on ``basis`` (structure constants of ``O``) modulo ``p^n``.
  This ``iota`` is the ``iota_p`` of ``def:s01-B``; matrices act on column vectors, products are
  the usual ones, so ``iota(xy) = iota(x) iota(y)``.

The case ``p | ab`` would require a conjugation of ``iota`` to make ``iota(O_p) = M_2(Z_p)``;
it raises ``NotImplementedError``.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Sequence

Quat = tuple  # 4-tuple of Fraction / int


# ---------------------------------------------------------------------------
# quaternion arithmetic in the basis 1, i, j, ij
# ---------------------------------------------------------------------------

def quat_mul(a: int, b: int, x: Sequence, y: Sequence) -> Quat:
    """Product ``xy`` in ``(a, b)_Q`` (coordinates w.r.t. ``1, i, j, ij``)."""
    x0, x1, x2, x3 = x
    y0, y1, y2, y3 = y
    # i^2=a, j^2=b, k=ij, k^2=-ab, ji=-k, ik=a j, ki=-a j, jk=-b i, kj=b i
    return (
        x0 * y0 + a * x1 * y1 + b * x2 * y2 - a * b * x3 * y3,
        x0 * y1 + x1 * y0 - b * x2 * y3 + b * x3 * y2,
        x0 * y2 + x2 * y0 + a * x1 * y3 - a * x3 * y1,
        x0 * y3 + x3 * y0 + x1 * y2 - x2 * y1,
    )


def quat_nrd(a: int, b: int, x: Sequence):
    """Reduced norm ``x0^2 - a x1^2 - b x2^2 + ab x3^2``."""
    x0, x1, x2, x3 = x
    return x0 * x0 - a * x1 * x1 - b * x2 * x2 + a * b * x3 * x3


def quat_trd(x: Sequence):
    return 2 * x[0]


def quat_conj(x: Sequence) -> Quat:
    return (x[0], -x[1], -x[2], -x[3])


def to_B(basis: Sequence[Sequence], c: Sequence[int]) -> Quat:
    """Element of ``B`` with integer coordinates ``c`` w.r.t. the order basis."""
    return tuple(sum(Fraction(c[k]) * Fraction(basis[k][t]) for k in range(4)) for t in range(4))


def _solve4(basis: Sequence[Sequence], x: Sequence) -> list[Fraction]:
    """Coordinates of ``x`` w.r.t. ``basis`` (exact Gaussian elimination)."""
    m = [[Fraction(basis[k][t]) for k in range(4)] + [Fraction(x[t])] for t in range(4)]
    for col in range(4):
        piv = next(r for r in range(col, 4) if m[r][col] != 0)
        m[col], m[piv] = m[piv], m[col]
        pv = m[col][col]
        m[col] = [v / pv for v in m[col]]
        for r in range(4):
            if r != col and m[r][col] != 0:
                f = m[r][col]
                m[r] = [vr - f * vc for vr, vc in zip(m[r], m[col])]
    return [m[t][4] for t in range(4)]


def structure_constants(a: int, b: int, basis: Sequence[Sequence]) -> list:
    """``C[k][l]`` = coordinates of ``b_k b_l`` w.r.t. ``basis`` (Fractions)."""
    return [[_solve4(basis, quat_mul(a, b, basis[k], basis[l])) for l in range(4)] for k in range(4)]


def is_order(a: int, b: int, basis: Sequence[Sequence]) -> bool:
    """``basis`` spans a ring containing 1 (integral structure constants, 1 in the span)."""
    one = _solve4(basis, (1, 0, 0, 0))
    if any(c.denominator != 1 for c in one):
        return False
    C = structure_constants(a, b, basis)
    return all(c.denominator == 1 for row in C for v in row for c in v)


def discriminant(a: int, b: int, basis: Sequence[Sequence]) -> Fraction:
    """``|det(trd(b_k b_l))|``; equals ``(reduced discriminant)^2`` for an order."""
    from sympy import Matrix

    G = Matrix(4, 4, lambda k, l: quat_trd(quat_mul(a, b, basis[k], basis[l])))
    return abs(Fraction(str(G.det())))


# ---------------------------------------------------------------------------
# modular helpers
# ---------------------------------------------------------------------------

def _inv(x: int, m: int) -> int:
    return pow(x % m, -1, m)


def _frac_mod(q, m: int) -> int:
    q = Fraction(q)
    return q.numerator * _inv(q.denominator, m) % m


def _legendre(x: int, p: int) -> int:
    x %= p
    if x == 0:
        return 0
    return 1 if pow(x, (p - 1) // 2, p) == 1 else -1


def _sqrt_mod_p(x: int, p: int) -> int:
    x %= p
    for r in range(p):  # p is small in all our applications; fall back to sympy for large p
        if r * r % p == x:
            return r
        if r > 10000:
            from sympy.ntheory import sqrt_mod
            return int(sqrt_mod(x, p))
    raise ValueError("not a square")


def hensel_sqrt(x: int, p: int, n: int) -> int:
    """``r`` with ``r^2 = x mod p^n``, for ``x`` a nonzero square mod odd ``p``."""
    r = _sqrt_mod_p(x, p)
    q = p
    while q < p**n:
        q = min(q * q, p**n)
        r = (r - (r * r - x) * _inv(2 * r, q)) % q
    assert (r * r - x) % p**n == 0
    return r


def mat_mul(X, Y, m: int):
    return [[(X[0][0] * Y[0][0] + X[0][1] * Y[1][0]) % m, (X[0][0] * Y[0][1] + X[0][1] * Y[1][1]) % m],
            [(X[1][0] * Y[0][0] + X[1][1] * Y[1][0]) % m, (X[1][0] * Y[0][1] + X[1][1] * Y[1][1]) % m]]


def mat_add(X, Y, m: int):
    return [[(X[r][c] + Y[r][c]) % m for c in range(2)] for r in range(2)]


def mat_scale(t: int, X, m: int):
    return [[t * X[r][c] % m for c in range(2)] for r in range(2)]


def mat_det(X, m: int) -> int:
    return (X[0][0] * X[1][1] - X[0][1] * X[1][0]) % m


def mat_adj(X, m: int):
    return [[X[1][1] % m, -X[0][1] % m], [-X[1][0] % m, X[0][0] % m]]


# ---------------------------------------------------------------------------
# the splitting
# ---------------------------------------------------------------------------

class Splitting:
    """``iota: O -> M_2(Z/p^n)``; see the module docstring for the convention."""

    def __init__(self, a: int, b: int, basis: Sequence[Sequence], p: int, n: int, I, J, method: str):
        self.a, self.b, self.p, self.n = a, b, p, n
        self.mod = p**n
        self.basis = [tuple(Fraction(c) for c in v) for v in basis]
        self.I, self.J = I, J
        self.IJ = mat_mul(I, J, self.mod)
        self.method = method
        self.basis_images = [self.image_B(v) for v in self.basis]

    def image_B(self, x: Sequence):
        """``iota(x)`` for ``x`` in ``B`` with ``p``-integral coordinates w.r.t. ``1, i, j, ij``."""
        m = self.mod
        one = [[1, 0], [0, 1]]
        out = [[0, 0], [0, 0]]
        for coeff, E in zip(x, (one, self.I, self.J, self.IJ)):
            out = mat_add(out, mat_scale(_frac_mod(coeff, m), E, m), m)
        return out

    def image(self, c: Sequence[int]):
        """``iota`` of the element of ``O`` with integer coordinates ``c`` w.r.t. ``basis``."""
        m = self.mod
        out = [[0, 0], [0, 0]]
        for ck, E in zip(c, self.basis_images):
            out = mat_add(out, mat_scale(int(ck), E, m), m)
        return out

    def check(self) -> None:
        """Assert multiplicativity mod ``p^n`` and bijectivity mod ``p``."""
        m, p = self.mod, self.p
        C = structure_constants(self.a, self.b, self.basis)
        for k in range(4):
            for l in range(4):
                assert all(c.denominator == 1 for c in C[k][l]), "basis is not an order"
                lhs = mat_mul(self.basis_images[k], self.basis_images[l], m)
                rhs = self.image([int(c) for c in C[k][l]])
                assert lhs == rhs, f"iota not multiplicative on b_{k} b_{l}"
        # bijective mod p: the 4 images are linearly independent in M_2(F_p)
        rows = [[E[0][0] % p, E[0][1] % p, E[1][0] % p, E[1][1] % p] for E in self.basis_images]
        assert _rank_mod_p(rows, p) == 4, "iota is not bijective mod p"


def _rank_mod_p(rows, p: int) -> int:
    rows = [list(r) for r in rows]
    rank, ncol = 0, len(rows[0])
    for col in range(ncol):
        piv = next((r for r in range(rank, len(rows)) if rows[r][col] % p), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        iv = _inv(rows[rank][col], p)
        rows[rank] = [v * iv % p for v in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col] % p:
                f = rows[r][col]
                rows[r] = [(vr - f * vc) % p for vr, vc in zip(rows[r], rows[rank])]
        rank += 1
    return rank


def split(a: int, b: int, basis: Sequence[Sequence], p: int, n: int) -> Splitting:
    """Return a checked splitting ``iota: O -> M_2(Z/p^n)`` (``p`` odd, ``p`` not dividing ``ab``)."""
    if p == 2 or a % p == 0 or b % p == 0:
        raise NotImplementedError("split() requires an odd prime p not dividing ab")
    m = p**n
    if _legendre(a, p) == 1:
        alpha = hensel_sqrt(a, p, n)
        I = [[alpha, 0], [0, (-alpha) % m]]
        J = [[0, b % m], [1, 0]]
        method = "a square: I = diag(alpha, -alpha), J = [[0, b], [1, 0]]"
    else:
        # solve c^2 - a e^2 = b mod p with c a unit, then lift c (e fixed)
        sol = None
        for e in range(p):
            t = (b + a * e * e) % p
            if t and _legendre(t, p) == 1:
                sol = e
                break
        assert sol is not None
        e = sol
        c = hensel_sqrt(b + a * e * e, p, n)
        I = [[0, a % m], [1, 0]]
        J = [[c, (-a * e) % m], [e, (-c) % m]]
        method = "a non-square: I = [[0, a], [1, 0]], J = [[c, -a e], [e, -c]], c^2 - a e^2 = b"
    S = Splitting(a, b, basis, p, n, I, J, method)
    assert mat_mul(I, I, m) == [[a % m, 0], [0, a % m]]
    assert mat_mul(J, J, m) == [[b % m, 0], [0, b % m]]
    assert mat_add(S.IJ, mat_mul(J, I, m), m) == [[0, 0], [0, 0]]
    S.check()
    return S
