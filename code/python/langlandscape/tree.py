"""S02-C1: tree-quotient builder (H02.1) -- the bipartite Brandt graph ``BG(U, q)`` of ``def:s02-BG``.

Tex labels (``plan/staged/stage-02-tree-quotients.tex``): ``def:s02-BG``, ``prop:s02-BG``, ``prop:s02-quot``, H02.1.

Input ``(B, O, U, q)``: ``B = B_D`` definite of discriminant ``D`` with the maximal order ``O`` of
:mod:`langlandscape.quat` (PARI's ``alginit`` basis), a level ``U = U_1(N1) cap U_0(N0)`` (``Level``: ``Level.max()``,
``Level.U0(M)``, ``Level.U1(N)``; ``gcd(N1, N0) = gcd(N1 N0, D) = 1``) and a prime ``q`` with ``q`` not dividing
``D N1 N0``.  Output (``build(D, q, U) -> TreeQuotient``):

* ``vertices0`` = ``X_B(U) x {0}``, ``vertices1`` = ``X_B(U) x {1}`` (the same list of ``Cell`` s; the type-1 copy is
  the class set reached through ``x -> x alpha``, ``alpha = iota_q^{-1} diag(1, q)``, see ``prop:s02-quot`` (a));
* ``edges`` = ``X_B(U_0(q) U)``;
* ``s0[e] = [y]`` and ``s1[e] = [y alpha]`` (indices into ``vertices0`` resp. ``vertices1``); an edge ``e`` joins
  ``(s0[e], 0)`` to ``(s1[e], 1)`` (orientation type 0 -> type 1);
* per cell: ``stab = |Gamma_x|`` (the full stabiliser ``B^x cap x U' x^{-1}``, *including* ``-1`` when ``-1 in U'``)
  and ``w = |Gamma_x / (Gamma_x cap {+-1})|`` (the weight of the conventions; ``w = stab/2`` iff ``-1 in U'``);
  the stabilisers of the type-1 vertex ``(x, 1)`` are those of ``x`` (``prop:s02-quot`` (b));
* ``incidence(j)``: the ``|X| x |E|`` 0/1 matrix ``S_j[x][e] = [s_j(e) = x]``; ``adjacency()`` = ``S_0 S_1^T``
  (edge counts between ``(x,0)`` and ``(x',1)``); ``hecke_matrix()`` = ``sum_{s0 e = x, s1 e = x'} |Gamma_x|/|Gamma_e|``,
  which at ``U = O^x`` is the Brandt matrix ``T_q`` of :mod:`langlandscape.brandt` (tested), and at general level
  is the matrix of ``T_q = [U alpha U]`` (row ``x``: the ``q+1`` lattices ``y alpha``, ``y`` over ``x``).
  The ratio ``|Gamma_x|/|Gamma_e| = w_x/w_e`` since ``-1 in U_0(q)U`` iff ``-1 in U``.

Downstream: C2 (connectivity ``components()``, fibre sums, mass), C3 (tables), C5 (``∂ = (-s_{0*}, s_{1*})``).

Coefficients (for C5; ``def:s02-Mhom`` / ``prop:s02-Mhomprops`` in ``mathematics/chapters/s02/3-cohomology.tex``).
Representatives: the cell ``(c, pt)`` stands for the idele ``y = x_c h`` with ``h in O^x``, ``h_l = 1`` for
``l`` not dividing ``N1 N0 q`` (so ``y_p = x_{c,p}``), and ``x_{c,p}`` is the frame of ``psi_c`` at ``p``
(``phi_c(r) = x_{c,p}^{-1} r x_{c,p}``, the S01 splitting ``cd.splitting(c, p)``).  Homological convention
``[y u] (x) v = [y] (x) u_p v``, ``[gamma y] (x) v = [y] (x) v``.  For an edge ``e`` with representative ``y``
and ``x_j`` the representative of ``s_j e``:

* ``move0[e] = gamma_0 in Gamma_c`` with ``gamma_0 y in x_0 U``; ``move1[e] = beta in B^x`` with
  ``beta y alpha in x_1 U`` (``beta = gamma_1 gamma'/q``, ``gamma_1 in Gamma_{c'}``, ``q L_{y alpha} = I_{c'} gamma'``).
* ``coeff_matrix(e, j, p, m)`` = ``u_j = (x_j^{-1} beta_j y alpha^j)_p in GL_2(Z/p^m)`` (``beta_0 = gamma_0``), so
  ``s_{j*}([e] (x) v) = [s_j e] (x) u_j v``  (``3-cohomology.tex`` (ii); then
  ``∂([e] (x) v) = (-[s_0 e] (x) u_0 v, [s_1 e] (x) u_1 v)``).  ``u_0 = phi_{c,p}(gamma_0)``;
  ``u_1 = (x_{c',p}^{-1} beta x_{c,p})``, computed from ``psi_{c'}(w beta^{-1}) = psi_c(w) u_1^{-1}``.
* ``stab_elements(cell)`` / ``Cell.stab_units`` (indices into ``class_data(D).units(c)``): the group ``Gamma_x``
  of the cell; it acts on the summand ``V`` through ``phi_{c,p}`` (``local_matrix``).  ``u_j`` intertwines:
  ``u_j phi_c(g) u_j^{-1} = phi_{c_j}(beta_j g beta_j^{-1})`` with ``beta_j g beta_j^{-1} in Gamma_{s_j e}``.
* ``vertex_of_point(c, pt)`` -> ``(vertex, gamma)`` with ``gamma y_pt in x_vertex U`` (``u = phi_{c,p}(gamma)``).

Comparisons with :mod:`langlandscape.brandt`: two ``DefiniteAlgebra(D)`` objects may carry different PARI
maximal-order bases (seen for ``D = 17``), so use ``brandt_module()`` / ``brandt_perm()`` (same algebra instance),
not ``brandt.module(D)``.

Model (consistent with S01 :mod:`langlandscape.levels`).  An idele ``y`` gives the left ``O``-ideal
``L_y = B cap O^ y^{-1}`` (so ``B^x`` acts by ``L -> L gamma^{-1}``, ``O_r(L_y) = B cap y O^ y^{-1}``).  Fix, for each
prime ``l | N1 N0 q``, an idempotent ``e_0 in O (x) Z_l`` (``= phi_O^{-1}(E_22)`` of the S01 splitting of ``O``); this
fixes ``iota_l``.  Then ``e_0 L_{y,l} = Z_l^2 y_l^{-1}`` (row vectors) and the level datum of ``y`` at ``l`` is the
row ``(0,1) y_l^{-1}`` (mod ``N1``: a vector; mod ``N0`` and mod ``q``: a line).  For each class ``c`` (S01 class
representative ``I_c``) we fix a right-``O_c``-linear isomorphism ``psi_c : e_0 I_c / l^k -> (Z/l^k)^2`` with
``psi_c(w r) = psi_c(w) phi_c(r)``, namely ``psi_c(w) = (0,1) phi_c(t_c w)``, ``t_c = eps_c a e_0``, ``eps_c =
phi_c^{-1}(E_22)``, ``a in I_c^{-1}``.  This is a choice of the representative idele ``x_c`` (up to ``U'``), and it is
exactly the coordinate system in which S01 ``XB`` lists the fibre ``Gamma_c \\ (U/U')``.  Then

* ``y alpha``: ``L_{y alpha} = L_y + O q^{-1} v`` with ``v in e_0 L_y`` lifting the ``q``-line of ``y``
  (``Z_q^2 alpha^{-1} y^{-1} = Z(1,0)y^{-1} + Z q^{-1}(0,1)y^{-1}``), level data away from ``q`` unchanged;
* reduction: ``q L_{y alpha} = I_{c'} gamma'`` (principality as in ``quat.equivalent``), and the row ``r`` of ``y``
  goes to ``psi_{c'}(q w gamma'^{-1})`` for any ``w in I_c`` with ``psi_c(w) = r`` (linear in ``r``: a 2x2 matrix
  per (class, ``q``-line), cached).  The scalar ``q`` here is the diamond ``<q>`` bookkeeping; it is not dropped.

The builder checks (``check=True``) that ``s1`` is constant on every ``Gamma_c``-orbit of edge points
(well-definedness, ``def:s02-BG``) and that ``[I_c : q L_{y alpha}] = q^2``.
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from fractions import Fraction
from functools import lru_cache
from math import gcd

from .levels import PREC, XB, _act, _crt, _factor, canon_line, class_data, minus_one_in_U
from .pari import get_pari
from .quat import Lattice



# ---------------------------------------------------------------- levels
@dataclass(frozen=True)
class Level:
    """``U = U_1(N1) cap U_0(N0)`` inside ``O^x`` (``N1 = N0 = 1``: maximal level)."""

    N1: int = 1
    N0: int = 1

    @staticmethod
    def max() -> "Level":
        return Level(1, 1)

    @staticmethod
    def U0(M: int) -> "Level":
        return Level(1, M)

    @staticmethod
    def U1(N: int) -> "Level":
        return Level(N, 1)

    def __str__(self) -> str:
        parts = ([f"U1({self.N1})"] if self.N1 > 1 else []) + ([f"U0({self.N0})"] if self.N0 > 1 else [])
        return "*".join(parts) or "O^x"


@dataclass(frozen=True)
class Cell:
    """A vertex or edge class: S01 class ``c``, orbit representative ``pt`` (S01 point format), stabiliser data."""

    c: int
    pt: tuple
    stab: int  # |Gamma_x|, including -1 if -1 in U'
    w: int     # |Gamma_x / +-1|
    stab_units: tuple = ()  # Gamma_x as indices into class_data(D).units(c)


# ---------------------------------------------------------------- modular linear algebra
def _solve_mod(A, b, l: int, m: int):
    """Solve ``A x = b`` mod ``m = l^K`` for square ``A`` invertible mod ``l`` (Gauss with unit pivots)."""
    n = len(A)
    M = [[A[i][j] % m for j in range(n)] + [b[i] % m] for i in range(n)]
    for col in range(n):
        piv = next(r for r in range(col, n) if M[r][col] % l)
        M[col], M[piv] = M[piv], M[col]
        inv = pow(M[col][col], -1, m)
        M[col] = [x * inv % m for x in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [(x - f * y) % m for x, y in zip(M[r], M[col])]
    return [M[i][n] for i in range(n)]


def _preimage(rows, target, l: int, m: int):
    """Coefficients ``x`` (len(rows)) with ``sum x_i rows_i = target`` mod ``m = l^k``; rows span ``(Z/l)^2``."""
    for i, j in itertools.combinations(range(len(rows)), 2):
        a, b = rows[i]
        c, d = rows[j]
        det = (a * d - b * c) % m
        if det % l:
            di = pow(det, -1, m)
            t0, t1 = target
            # (x_i, x_j) [[a, b], [c, d]] = (t0, t1)
            xi = (t0 * d - t1 * c) * di % m
            xj = (-t0 * b + t1 * a) * di % m
            x = [0] * len(rows)
            x[i], x[j] = xi, xj
            return x
    raise ValueError("rows do not span (Z/l)^2")


# ---------------------------------------------------------------- per-algebra local data
class _Local:
    """``e_0``, ``eps_c``, ``t_c`` and ``psi_c`` for one ``D`` (cached per prime ``l``)."""

    def __init__(self, D: int):
        self.cd = cd = class_data(D)
        self.B = cd.B
        self._eps: dict = {}
        self._t: dict = {}
        self._minv: dict = {}

    def _elt(self, c: int, coords):
        R = self.cd.orders[c]
        return tuple(sum(Fraction(x) * R.basis[i][k] for i, x in enumerate(coords)) for k in range(4))

    def eps(self, c: int, l: int):
        """Integral lift (element of ``O_c``) of ``phi_c^{-1}(E_22)`` mod ``l^PREC``."""
        if (c, l) not in self._eps:
            mats, m = self.cd.splitting(c, l)
            A = [[mats[i][r][s] for i in range(4)] for r in range(2) for s in range(2)]
            x = _solve_mod(A, [0, 0, 0, 1], l, m)
            self._eps[(c, l)] = self._elt(c, x)
        return self._eps[(c, l)]

    def e0(self, l: int):
        return self.eps(0, l)

    def _psi_raw(self, c: int, t, w, l: int, k: int):
        mod = l**k
        _, to_coords = self.cd.struct(c)
        u = to_coords(self.B.mul(t, w))
        a, b, cc, d = self.cd.phi(c, u, mod)
        if a % mod or b % mod:
            raise RuntimeError("psi: first row not zero (eps not idempotent?)")
        return (cc % mod, d % mod)

    def t(self, c: int, l: int):
        """``t_c = eps_c a e_0`` with ``a in I_c^{-1} = conj(I_c)/N_c`` such that ``psi_c`` is onto mod ``l``."""
        if (c, l) not in self._t:
            B = self.B
            I, N = self.cd.reps[c]
            inv = [tuple(x / N for x in B.conj(b)) for b in I.basis]
            cands = inv + [tuple(x + y for x, y in zip(u, v)) for u, v in itertools.combinations(inv, 2)]
            eps, e0 = self.eps(c, l), self.e0(l)
            for a in cands:
                t = B.mul(B.mul(eps, a), e0)
                rows = [self._psi_raw(c, t, b, l, 1) for b in I.basis]
                if any((r1[0] * r2[1] - r1[1] * r2[0]) % l for r1, r2 in itertools.combinations(rows, 2)):
                    self._t[(c, l)] = t
                    break
            else:
                raise RuntimeError(f"no t_c found (class {c}, l = {l})")
        return self._t[(c, l)]

    def coords(self, c: int, elt) -> list[Fraction]:
        """Rational coordinates of ``elt in B`` in the HNF basis of ``O_c``."""
        if c not in self._minv:
            import flint
            R = self.cd.orders[c]
            M = flint.fmpq_mat(4, 4, [flint.fmpq(R.basis[j][i].numerator, R.basis[j][i].denominator)
                                      for i in range(4) for j in range(4)])
            self._minv[c] = M.inv()
        import flint
        s = self._minv[c] * flint.fmpq_mat(4, 1, [flint.fmpq(Fraction(x).numerator, Fraction(x).denominator) for x in elt])
        return [Fraction(int(s[i, 0].p), int(s[i, 0].q)) for i in range(4)]

    def phi_elt(self, c: int, elt, Q: int):
        """``phi_c(elt)`` mod ``Q`` for ``elt in O_c (x) Z_(Q)`` (coordinate denominators prime to ``Q``)."""
        co = self.coords(c, elt)
        den = 1
        for x in co:
            den = den * x.denominator // gcd(den, x.denominator)
        if gcd(den, Q) != 1:
            raise ValueError("element not integral at Q")
        a, b, cc, d = self.cd.phi(c, [int(x * den) for x in co], Q)
        di = pow(den, -1, Q)
        return (a * di % Q, b * di % Q, cc * di % Q, d * di % Q)

    def psi(self, c: int, w, l: int, k: int):
        """``psi_c(w)`` in ``(Z/l^k)^2`` for ``w in I_c``."""
        return self._psi_raw(c, self.t(c, l), w, l, k)

    def psi_mod(self, c: int, w, Q: int):
        """``psi_c(w)`` mod ``Q`` (CRT over the prime powers of ``Q``)."""
        parts = [(self.psi(c, w, l, k), l**k) for l, k in _factor(Q).items()]
        return tuple(_crt([(r[i], m) for r, m in parts]) for i in range(2))

    def preimage(self, c: int, row, Q: int):
        """Some ``w in I_c`` with ``psi_c(w) = row`` mod ``Q``."""
        I, _ = self.cd.reps[c]
        coeffs = []
        for l, k in _factor(Q).items():
            m = l**k
            rows = [self.psi(c, b, l, k) for b in I.basis]
            coeffs.append((_preimage(rows, (row[0] % m, row[1] % m), l, m), m))
        x = [_crt([(co[i], m) for co, m in coeffs]) for i in range(4)]
        return tuple(sum(x[i] * I.basis[i][j] for i in range(4)) for j in range(4))


@lru_cache(maxsize=None)
def _local(D: int) -> _Local:
    return _Local(D)


def _find_gamma(B, I: Lattice, NI: int, J: Lattice, NJ):
    """``gamma`` with ``J = I gamma`` if it exists (``mu in conj(I) J`` of reduced norm ``NI NJ``, ``gamma = mu/NI``)."""
    pari = get_pari()
    # pre-filter: x -> x gamma is a similitude (I, nrd) -> (J, nrd) of factor NJ/NI (integral scaling for qfisom)
    if not pari.qfisom(B.gram(I) * NJ, B.gram(J) * NI):
        return None
    L = B.lmul(B.lconj(I), J)
    # any mu of reduced norm NI NJ works (I mu subset NI J, equal norms), so a truncated list is harmless as long
    # as it is non-empty; qfminim returns half of the vectors (up to sign)
    res = pari.qfminim(B.gram(L), 2 * NI * NJ, 10**4, 0)
    vecs = res[2]
    ncols = int(pari.matsize(vecs)[1])
    if int(res[0]) > 0 and ncols == 0:
        raise RuntimeError("qfminim returned no vectors although the count is positive")
    for col in range(ncols):
        co = [int(vecs[i, col]) for i in range(4)]
        mu = tuple(sum(co[i] * L.basis[i][k] for i in range(4)) for k in range(4))
        if B.nrd(mu) != NI * NJ:
            continue
        gamma = tuple(x / NI for x in mu)
        if Lattice([B.mul(b, gamma) for b in I.basis]).key == J.key:
            return gamma
    if int(res[0]) > 0:
        raise RuntimeError("_find_gamma: vector of norm NI NJ found but J != I gamma")
    return None


def _inv2(M, m: int):
    a, b, c, d = M
    det = (a * d - b * c) % m
    di = pow(det, -1, m)
    return (d * di % m, -b * di % m, -c * di % m, a * di % m)


def _mul2(A, B, m: int):
    return ((A[0] * B[0] + A[1] * B[2]) % m, (A[0] * B[1] + A[1] * B[3]) % m,
            (A[2] * B[0] + A[3] * B[2]) % m, (A[2] * B[1] + A[3] * B[3]) % m)


def _index(L_big: Lattice, L_small: Lattice) -> Fraction:
    import flint
    det = lambda L: flint.fmpq_mat(4, 4, [flint.fmpq(c.numerator, c.denominator) for v in L.basis for c in v]).det()
    d = det(L_small) / det(L_big)
    return abs(Fraction(int(d.p), int(d.q)))


# ---------------------------------------------------------------- the graph
@dataclass
class TreeQuotient:
    """``BG(U, q)`` (``def:s02-BG``).  Vertex lists are indexed ``0..X-1``; ``s0, s1 : range(E) -> range(X)``.

    ``move0[e]``, ``move1[e]``: elements of ``B`` (4-tuples of Fractions in the PARI basis) relating the edge
    representative to the vertex representatives; see the module docstring for the exact formulas.
    """

    D: int
    q: int
    level: Level
    vertices0: list[Cell]
    vertices1: list[Cell]
    edges: list[Cell]
    s0: list[int]
    s1: list[int]
    minus_one_in_U: bool
    _vindex: dict = field(default_factory=dict, repr=False)
    move0: list = field(default_factory=list, repr=False)
    move1: list = field(default_factory=list, repr=False)
    _ctx: object = field(default=None, repr=False)

    @property
    def X(self) -> int:
        return len(self.vertices0)

    @property
    def E(self) -> int:
        return len(self.edges)

    @property
    def stab_v(self) -> list[int]:
        return [v.stab for v in self.vertices0]

    @property
    def stab_e(self) -> list[int]:
        return [e.stab for e in self.edges]

    @property
    def w_v(self) -> list[int]:
        return [v.w for v in self.vertices0]

    @property
    def w_e(self) -> list[int]:
        return [e.w for e in self.edges]

    def incidence(self, j: int) -> list[list[int]]:
        """``S_j[x][e] = 1`` iff ``s_j(e) = x`` (``|X| x |E|``)."""
        s = self.s0 if j == 0 else self.s1
        M = [[0] * self.E for _ in range(self.X)]
        for e, x in enumerate(s):
            M[x][e] = 1
        return M

    def adjacency(self) -> list[list[int]]:
        """``A[x][x'] = #{e : s0 e = x, s1 e = x'}`` (= ``S_0 S_1^T``)."""
        A = [[0] * self.X for _ in range(self.X)]
        for a, b in zip(self.s0, self.s1):
            A[a][b] += 1
        return A

    def hecke_matrix(self) -> list[list[int]]:
        """``H[x][x'] = sum_{s0 e = x, s1 e = x'} |Gamma_x| / |Gamma_e|`` (the ``T_q`` matrix; rows sum to ``q+1``)."""
        H = [[0] * self.X for _ in range(self.X)]
        for e, (a, b) in enumerate(zip(self.s0, self.s1)):
            r, rem = divmod(self.vertices0[a].stab, self.edges[e].stab)
            if rem:
                raise RuntimeError("|Gamma_e| does not divide |Gamma_{s0 e}|")
            H[a][b] += r
        return H

    def components(self) -> int:
        """Number of connected components of ``BG(U, q)`` (``2X`` vertices)."""
        parent = list(range(2 * self.X))

        def find(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i

        for a, b in zip(self.s0, self.s1):
            ra, rb = find(a), find(self.X + b)
            if ra != rb:
                parent[ra] = rb
        return len({find(i) for i in range(2 * self.X)})

    def vertex_of(self, c: int, pt: tuple) -> int:
        """Index of the vertex whose representative is exactly ``(c, pt)``."""
        return self._vindex[(c, pt)]

    # ---- group elements and coefficients
    def unit(self, c: int, i: int):
        """The ``i``-th element of ``Gamma_c = O_c^x`` (``class_data(D).units(c)``) as an element of ``B``."""
        return self._ctx.loc._elt(c, self._ctx.cd.units(c)[i])

    def stab_elements(self, cell: Cell) -> list:
        """``Gamma_x`` of a vertex or edge cell, as elements of ``B``."""
        return [self.unit(cell.c, i) for i in cell.stab_units]

    def local_matrix(self, c: int, elt, p: int, m: int = 1):
        """``phi_{c,p}(elt) = x_{c,p}^{-1} elt x_{c,p}`` mod ``p^m`` (``elt in O_c (x) Z_(p)``) as ``(a, b, c, d)``."""
        self._ctx.check_p(p, m)
        return self._ctx.loc.phi_elt(c, elt, p**m)

    def coeff_matrix(self, e: int, j: int, p: int, m: int = 1):
        """``u_j`` with ``s_{j*}([e] (x) v) = [s_j e] (x) u_j v``, in ``GL_2(Z/p^m)`` as ``(a, b, c, d)``."""
        ctx = self._ctx
        ctx.check_p(p, m)
        c = self.edges[e].c
        if j == 0:
            return ctx.loc.phi_elt(c, self.move0[e], p**m)
        if j == 1:
            return ctx.u_beta(c, self.vertices1[self.s1[e]].c, self.move1[e], p, m)
        raise ValueError("j must be 0 or 1")

    def vertex_of_point(self, c: int, pt: tuple):
        """Any point ``(c, pt)`` of ``X_B(U)`` (S01 format) -> ``(vertex index, gamma)``, ``gamma y_pt in x_vertex U``."""
        return self._ctx.locate(c, pt)

    def s1_lattice(self, e: int) -> Lattice:
        """``L_{y alpha} = B cap O^ (y alpha)^{-1}`` for the edge representative ``y`` (left ``O``-ideal)."""
        c, pt = self.edges[e].c, self.edges[e].pt
        qL = self._ctx.transport(c, self._ctx._split_line(pt[1])[1])[3]
        return Lattice([tuple(x / self.q for x in b) for b in qL.basis])

    def brandt_module(self):
        """S01 ``BrandtModule`` of ``O`` over the *same* algebra instance as the class reps (``brandt.module`` may not be)."""
        from .brandt import BrandtModule
        if getattr(self._ctx, "_bm", None) is None:
            B = self._ctx.cd.B
            self._ctx._bm = BrandtModule(B, B.O, self.D, 1, B.ell)
        return self._ctx._bm

    def brandt_perm(self) -> list[int]:
        """``perm[c]`` = index of the S01 class ``c`` in ``brandt_module().reps``."""
        cd, m = self._ctx.cd, self.brandt_module()
        out = []
        for I, N in cd.reps:
            k = next((k for k, (J, NJ) in enumerate(m.reps) if _find_gamma(cd.B, J, NJ, I, N) is not None), None)
            if k is None:
                raise RuntimeError("class not found in the Brandt module")
            out.append(k)
        return out


class _Builder:
    def __init__(self, D: int, q: int, level: Level, check: bool):
        N1, N0 = level.N1, level.N0
        if gcd(N1, N0) != 1 or gcd(N1 * N0, D) != 1:
            raise ValueError("need gcd(N1, N0) = gcd(N1 N0, D) = 1")
        if q < 2 or _factor(q) != {q: 1} or D % q == 0 or (N1 * N0) % q == 0:
            raise ValueError("q must be a prime not dividing D N1 N0")
        self.D, self.q, self.N1, self.N0 = D, q, N1, N0
        self.Q = N1 * N0
        self.loc = _local(D)
        self.cd = self.loc.cd
        self.check = check
        self.XU = XB(D, N1, N0)
        self.XE = XB(D, N1, N0 * q)
        self._trans: dict = {}
        self._umats: dict = {}
        self._bm = None
        self._vindex: dict = {}

    def check_p(self, p: int, m: int):
        if _factor(p) != {p: 1} or self.D % p == 0 or p == self.q:
            raise ValueError("p must be a prime not dividing D q")
        if not 1 <= m <= PREC:
            raise ValueError(f"need 1 <= m <= {PREC} (precision of the S01 splittings)")

    # ---- unit action on points
    def _unit_mats(self, c: int, N0: int):
        key = (c, N0)
        if key not in self._umats:
            cd = self.cd
            self._umats[key] = [(cd.phi(c, u, self.N1), cd.phi(c, u, N0)) for u in cd.units(c)]
        return self._umats[key]

    def _act_unit(self, c: int, i: int, pt, N0: int):
        g1, g0 = self._unit_mats(c, N0)[i]
        return _act(pt, g1, g0, self.N1, N0)

    def _stab_units(self, c: int, pt, N0: int) -> tuple:
        return tuple(i for i in range(len(self.cd.units(c))) if self._act_unit(c, i, pt, N0) == pt)

    def _mover(self, c: int, pt, target, N0: int):
        """``gamma in Gamma_c`` with ``point(gamma y_pt) = target``, i.e. ``target = pt phi(gamma)^{-1}``."""
        for i, u in enumerate(self.cd.units(c)):
            if self._act_unit(c, i, pt, N0) == target:  # target = pt phi(u), so gamma = u^{-1} = conj(u)
                return self.cd.B.conj(self.loc._elt(c, u))
        raise RuntimeError("point not in the orbit of the target")

    def locate(self, c: int, pt):
        XU = self.XU
        k = XU.orbit_of[c][pt]
        rep = XU.orbits[c][k]["rep"]
        return self._vindex[(c, rep)], self._mover(c, pt, rep, self.N0)

    # ---- q-move per (class, q-line): (c', 2x2 transport matrix mod Q, g = gamma'/q, q L_{y alpha})
    def transport(self, c: int, lam: tuple):
        key = (c, lam)
        if key in self._trans:
            return self._trans[key]
        B, loc, q = self.cd.B, self.loc, self.q
        I, N = self.cd.reps[c]
        wq = loc.preimage(c, lam, q)
        v = B.mul(loc.e0(q), wq)  # in e_0 I_c, psi_c(v) spans lam mod q
        if canon_line(loc.psi(c, v, q, 1), q) != lam:
            raise RuntimeError("q-line preimage failed")
        qL = Lattice([tuple(q * x for x in b) for b in I.basis] + [B.mul(o, v) for o in B.O.basis])
        if self.check and _index(I, qL) != q * q:
            raise RuntimeError("q L_{y alpha} must have index q^2 in I_c")
        found = None
        for c2, (J, NJ) in enumerate(self.cd.reps):
            g = _find_gamma(B, J, NJ, qL, N * q)
            if g is not None:
                found = (c2, g)
                break
        if found is None:
            raise RuntimeError("q-neighbour lies in no known class")
        c2, gp = found
        g = tuple(x / q for x in gp)  # L_{y alpha} = I_{c'} g
        G = None
        if self.Q > 1:
            ginv = _inv_elt(B, g)
            G = []
            for row in ((1, 0), (0, 1)):
                w = loc.preimage(c, row, self.Q)
                G.append(loc.psi_mod(c2, B.mul(w, ginv), self.Q))  # w g^{-1} in I_{c'}
        self._trans[key] = (c2, G, g, qL)
        return self._trans[key]

    def u_beta(self, c: int, c2: int, beta, p: int, m: int):
        """``(x_{c2,p}^{-1} beta x_{c,p})`` mod ``p^m`` for ``beta`` with ``I_c beta^{-1} subset I_{c2}`` locally at ``p``."""
        B, loc, mod = self.cd.B, self.loc, p**m
        binv = _inv_elt(B, beta)
        rows = [loc.psi_mod(c2, B.mul(loc.preimage(c, r, mod), binv), mod) for r in ((1, 0), (0, 1))]
        return _inv2((rows[0][0], rows[0][1], rows[1][0], rows[1][1]), mod)

    def _split_line(self, line):
        """Line mod ``N0 q`` -> (line mod ``N0`` or (), line mod ``q``)."""
        N0, q = self.N0, self.q
        l0 = canon_line((line[0] % N0, line[1] % N0), N0) if N0 > 1 else ()
        lq = canon_line((line[0] % q, line[1] % q), q)
        return l0, lq

    def s0_point(self, c: int, pt: tuple):
        v, line = pt
        return c, (v, self._split_line(line)[0])

    def s1_point(self, c: int, pt: tuple):
        """``(c', pt')``: ``y alpha in g^{-1} x_{c'} h' U`` with ``pt'`` the level-``U`` point of ``h'`` (``g`` of ``transport``)."""
        v, line = pt
        N1, N0, Q = self.N1, self.N0, self.Q
        l0, lq = self._split_line(line)
        c2, G = self.transport(c, lq)[:2]
        if Q == 1:
            return c2, ((), ())
        parts = []
        if N1 > 1:
            parts.append((v, N1))
        if N0 > 1:
            parts.append((l0, N0))
        row = tuple(_crt([(p[i], m) for p, m in parts]) for i in range(2))
        r2 = tuple((row[0] * G[0][i] + row[1] * G[1][i]) % Q for i in range(2))
        v2 = (r2[0] % N1, r2[1] % N1) if N1 > 1 else ()
        l2 = canon_line((r2[0] % N0, r2[1] % N0), N0) if N0 > 1 else ()
        return c2, (v2, l2)

    def s0_full(self, c: int, pt: tuple):
        """``(vertex, gamma_0)`` with ``gamma_0 y in x_vertex U``."""
        return self.locate(*self.s0_point(c, pt))

    def s1_full(self, c: int, pt: tuple):
        """``(vertex, beta)`` with ``beta y alpha in x_vertex U``."""
        c2, p2 = self.s1_point(c, pt)
        vtx, g1 = self.locate(c2, p2)
        g = self.transport(c, self._split_line(pt[1])[1])[2]
        return vtx, self.cd.B.mul(g1, g)

    def build(self) -> TreeQuotient:
        XU, XE, N0, q = self.XU, self.XE, self.N0, self.q
        verts = []
        for c, orbs in enumerate(XU.orbits):
            for o in orbs:
                verts.append(Cell(c, o["rep"], o["stab"], o["w"], self._stab_units(c, o["rep"], N0)))
        self._vindex = {(v.c, v.pt): k for k, v in enumerate(verts)}
        tq = TreeQuotient(self.D, q, Level(self.N1, self.N0), verts, list(verts), [], [], [],
                          minus_one_in_U(self.N1, self.N0), dict(self._vindex), [], [], self)

        if self.check:
            members: dict = {}
            for c, of in enumerate(XE.orbit_of):
                for p, k in of.items():
                    members.setdefault((c, k), []).append(p)
        for c, orbs in enumerate(XE.orbits):
            for k, o in enumerate(orbs):
                su = self._stab_units(c, o["rep"], N0 * q)
                if len(su) != o["stab"]:
                    raise RuntimeError("stabiliser enumeration disagrees with S01 XB")
                tq.edges.append(Cell(c, o["rep"], o["stab"], o["w"], su))
                a, g0 = self.s0_full(c, o["rep"])
                b, beta = self.s1_full(c, o["rep"])
                if self.check:
                    for p in members[(c, k)]:
                        if self.s0_full(c, p)[0] != a:
                            raise RuntimeError("s0 not constant on a Gamma-orbit")
                        if self.s1_full(c, p)[0] != b:
                            raise RuntimeError("s1 not constant on a Gamma-orbit")
                tq.s0.append(a)
                tq.s1.append(b)
                tq.move0.append(g0)
                tq.move1.append(beta)
        return tq


def _inv_elt(B, g):
    n = B.nrd(g)
    return tuple(x / n for x in B.conj(g))


def build(D: int, q: int, U: Level = Level(), check: bool = True) -> TreeQuotient:
    """``BG(U, q)`` for ``B_D`` with its maximal order ``O``; ``check`` verifies ``s1`` is well defined on orbits."""
    return _Builder(D, q, U, check).build()


def build_U(D: int, q: int, N1: int = 1, N0: int = 1, check: bool = True) -> TreeQuotient:
    return build(D, q, Level(N1, N0), check)


__all__ = ["Level", "Cell", "TreeQuotient", "build", "build_U"]
