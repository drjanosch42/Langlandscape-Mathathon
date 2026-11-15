"""S01-C4: Brandt modules with ``Sym^n`` coefficients at level ``O^x`` and the classical JL char-poly check.

Conventions (``eq:s01-Vk``, ``def:s01-brandt``, ``rem:s01-dictionary``, ``def:s01-hecke``):

* ``B = (a, b)_Q`` as in ``quat.DefiniteAlgebra`` (``i^2 = a``, ``j^2 = b``, ``ij = -ji``; ``i, j`` located in PARI's
  order basis via ``algalgtobasis`` and checked against the multiplication table).  ``K = Q(sqrt a)`` (imaginary
  quadratic), elements ``r + s sqrt(a)`` with ``r, s`` Fractions (class ``QS``).  The splitting
  ``s : B (x) K -> M_2(K)`` is ``i -> diag(sqrt a, -sqrt a)``, ``j -> (0 b; 1 0)`` (asserted multiplicative).
* ``V_k = Sym^n(K^2)``, ``n = k - 2``, homogeneous polynomials of degree ``n`` with the **left** action
  ``(g.P)(X, Y) = P((X, Y) g) = P(aX + cY, bX + dY)`` of ``eq:s01-Vk``; basis ``X^{n-t} Y^t``, ``t = 0..n``;
  ``rho(gh) = rho(g) rho(h)`` is asserted.
* Brandt module in Gross's global form (``rem:s01-dictionary``, with the global splitting ``s`` in place of
  ``iota_p``): ``F : B^^x -> V_k``, ``F(gamma x u) = s(gamma).F(x)``.  Writing ``L_x = B cap O^ x^{-1}`` (a left
  ``O``-ideal; ``L_{gamma x u} = L_x gamma^{-1}``) this is ``Phi(L alpha) = alpha^{-1}.Phi(L)`` on left ideals, so
  ``M(O^x; V_k) = (+)_c V_k^{Gamma_c}``, ``Gamma_c = O_r(L_c)^x`` (including ``-1``), over the class reps ``L_c`` of
  ``brandt.module(D)``.  ``rem:s01-dictionary`` identifies it with the seed-side ``M(O^x; V_k)`` compatibly with ``T_g``.
* ``T_l = [U varpi_l U]`` acts by ``(T F)(x) = sum_i F(x g_i)``.  ``L_{x g_i} = l^{-1} J_i`` with ``J_i`` running over
  the ``l + 1`` neighbours ``J = L_c K`` (``brandt.neighbours``); writing ``J = L_{c'} beta`` (``beta`` from a
  minimal vector of ``conj(L_{c'}) J``, ``beta = delta / N(L_{c'})``):
  ``(T Phi)(L_c) = sum_J l^n . beta_J^{-1} . Phi(L_{c'(J)})`` (``l`` central acts by ``l^n``).
  For ``k = 2`` this is the weight-2 Brandt matrix of ``brandt.py``.
* ``Q``-structure (``k`` even): ``sigma`` = Galois conjugation of ``K``.  Since ``s(gamma)^sigma = s(j) s(gamma) s(j)^{-1}``,
  ``phi(P) = b^{n/2} rho(s(j))^{-1} sigma(P)`` is a ``sigma``-semilinear involution commuting with ``rho(s(B))``;
  ``V_Q = V^phi`` is a ``Q``-form.  Asserted: ``phi^2 = 1``, ``phi`` commutes with ``T_l`` on ``(+)V^{Gamma_c}``, the
  matrices of ``rho(s(gamma))`` in a ``Q``-basis of ``V_Q`` are rational, and the char-poly of ``T_l`` computed over
  ``K`` lies in ``Q[x]`` and equals that of the rational model.  For odd ``k``, ``-1 in Gamma_c`` acts by ``-1``, so
  every ``V^{Gamma_c} = 0`` (recorded, trivially consistent with ``S_k(Gamma_0(D)) = 0``).

JL check (``thm:s01-JLclassical``, ``M = 1``): ``charpoly(T_l | M(O^x; V_k)) = (x - l - 1)^{[k = 2]} *
charpoly(mfheckemat(mfinit([D, k], 0), l))`` and ``dim M(O^x; V_k) = dim S_k(Gamma_0(D))^new + [k = 2]``.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache

import flint

from . import brandt, results
from .pari import get_pari

DS = (2, 3, 5, 7, 11, 13)
KS = tuple(range(2, 13))
ELLS = (2, 3)


# ---------------------------------------------------------------- the field Q(sqrt a)
class QS:
    """Element ``r + s sqrt(a)`` of ``Q(sqrt a)``, ``a`` a non-square integer (exact, Fractions)."""

    __slots__ = ("r", "s", "a")

    def __init__(self, r, s=0, a=None):
        self.r, self.s, self.a = Fraction(r), Fraction(s), a

    def _c(self, o):
        if isinstance(o, QS):
            return o
        return QS(o, 0, self.a)

    def __add__(self, o):
        o = self._c(o)
        return QS(self.r + o.r, self.s + o.s, self.a)

    __radd__ = __add__

    def __neg__(self):
        return QS(-self.r, -self.s, self.a)

    def __sub__(self, o):
        o = self._c(o)
        return QS(self.r - o.r, self.s - o.s, self.a)

    def __rsub__(self, o):
        return self._c(o) - self

    def __mul__(self, o):
        o = self._c(o)
        return QS(self.r * o.r + self.a * self.s * o.s, self.r * o.s + self.s * o.r, self.a)

    __rmul__ = __mul__

    def conj(self):
        return QS(self.r, -self.s, self.a)

    def norm(self) -> Fraction:
        return self.r * self.r - self.a * self.s * self.s

    def __truediv__(self, o):
        o = self._c(o)
        n = o.norm()
        assert n != 0, "division by zero in Q(sqrt a)"
        num = self * o.conj()
        return QS(num.r / n, num.s / n, self.a)

    def __rtruediv__(self, o):
        return self._c(o) / self

    def __eq__(self, o):
        o = self._c(o)
        return self.r == o.r and self.s == o.s

    def __hash__(self):
        return hash((self.r, self.s))

    def is_zero(self) -> bool:
        return self.r == 0 and self.s == 0

    def is_rational(self) -> bool:
        return self.s == 0

    def __repr__(self):
        return f"({self.r}+{self.s}*sqrt({self.a}))"


# ---------------------------------------------------------------- generic exact linear algebra
def _is_zero(x) -> bool:
    return x.is_zero() if isinstance(x, QS) else x == 0


def mat_mul(A, B):
    n, m, p = len(A), len(B), len(B[0]) if B else 0
    return [[sum((A[i][t] * B[t][j] for t in range(m)), A[i][0] * 0) for j in range(p)] for i in range(n)]


def rref(A):
    """Reduced row echelon form; returns ``(R, pivots)``."""
    R = [list(r) for r in A]
    piv, row = [], 0
    ncols = len(R[0]) if R else 0
    for col in range(ncols):
        pr = next((r for r in range(row, len(R)) if not _is_zero(R[r][col])), None)
        if pr is None:
            continue
        R[row], R[pr] = R[pr], R[row]
        inv = 1 / R[row][col]
        R[row] = [x * inv for x in R[row]]
        for r in range(len(R)):
            if r != row and not _is_zero(R[r][col]):
                f = R[r][col]
                R[r] = [x - f * y for x, y in zip(R[r], R[row])]
        piv.append(col)
        row += 1
        if row == len(R):
            break
    return R, piv


def nullspace(A, ncols: int, zero, one):
    """Basis (list of column vectors) of ``{v : A v = 0}``."""
    if not A:
        return [[one if i == j else zero for i in range(ncols)] for j in range(ncols)]
    R, piv = rref(A)
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [zero] * ncols
        v[f] = one
        for r, p in enumerate(piv):
            v[p] = -R[r][f]
        basis.append(v)
    return basis


def solve_in_span(W, v, zero):
    """Coordinates ``c`` with ``sum_j c_j W[j] = v`` (``W`` a list of independent vectors); asserts solvability."""
    m = len(W)
    rows = [[W[j][i] for j in range(m)] + [v[i]] for i in range(len(v))]
    R, piv = rref(rows)
    assert m not in piv, "vector not in the span (T does not preserve the invariants)"
    c = [zero] * m
    for r, p in enumerate(piv):
        c[p] = R[r][m]
    return c


def charpoly(M, zero, one) -> list:
    """``det(x - M)`` by Faddeev--LeVerrier (char 0); coefficients constant term first."""
    n = len(M)
    if n == 0:
        return [one]
    coeffs = [zero] * (n + 1)
    coeffs[n] = one
    I = [[one if i == j else zero for j in range(n)] for i in range(n)]
    Mk = [[zero] * n for _ in range(n)]
    for k in range(1, n + 1):
        Mk = mat_mul(M, [[Mk[i][j] + (coeffs[n - k + 1] * I[i][j]) for j in range(n)] for i in range(n)])
        tr = sum((Mk[i][i] for i in range(n)), zero)
        coeffs[n - k] = tr * Fraction(-1, k)
    return coeffs


# ---------------------------------------------------------------- Sym^n
def sym_matrix(g, n: int, zero, one):
    """Matrix of ``P -> P((X,Y) g)`` on ``Sym^n``, basis ``X^{n-t} Y^t`` (columns = images of basis vectors)."""
    (a, b), (c, d) = g
    # (aX + cY) and (bX + dY) as coefficient lists in Y-degree
    def pmul(p, q):
        out = [zero] * (len(p) + len(q) - 1)
        for i, x in enumerate(p):
            for j, y in enumerate(q):
                out[i + j] = out[i + j] + x * y
        return out

    lin1, lin2 = [a, c], [b, d]
    pw1, pw2 = [[one]], [[one]]
    for _ in range(n):
        pw1.append(pmul(pw1[-1], lin1))
        pw2.append(pmul(pw2[-1], lin2))
    cols = [pmul(pw1[n - t], pw2[t]) for t in range(n + 1)]
    return [[cols[t][s] for t in range(n + 1)] for s in range(n + 1)]


# ---------------------------------------------------------------- the algebra, its splitting
class SplitAlgebra:
    """``B_D`` with ``i, j`` in the order basis and the exact splitting ``s : B -> M_2(Q(sqrt a))``."""

    def __init__(self, D: int):
        self.D = D
        self.mod = brandt.module(D)
        self.B = B = self.mod.B
        self.a, self.b = B.a, B.b
        pari = get_pari()
        # alginit is randomised (D = 17: two different maximal-order bases occur); i, j must be located in the very
        # basis DefiniteAlgebra uses, so redo alginit until its multiplication table equals B.C.
        for _attempt in range(200):
            A = pari(f"alginit(nfinit(y),[{self.a},{self.b}])")
            pol = pari("L -> L.pol")(pari.algsplittingfield(A))  # before algmultable (cypari2 stack quirk)
            mt = pari.algmultable(A)
            if all(Fraction(int(mt[k][i, j])) == B.C[k][i][j] for k in range(4) for i in range(4) for j in range(4)):
                break
        else:
            raise RuntimeError("could not reproduce DefiniteAlgebra's alginit basis")
        assert pol == pari(f"x^2 - ({self.a})"), pol
        vi = pari.algalgtobasis(A, pari(f"[Mod(x, x^2 - ({self.a})), 0]~"))
        vj = pari.algalgtobasis(A, pari("[0, 1]~"))
        fr = lambda v: tuple(Fraction(int(pari.numerator(c)), int(pari.denominator(c))) for c in v)
        self.I, self.J = fr(vi), fr(vj)
        self.IJ = B.mul(self.I, self.J)
        one = B.one
        sc = lambda s, v: tuple(s * c for c in v)
        assert B.mul(self.I, self.I) == sc(self.a, one) and B.mul(self.J, self.J) == sc(self.b, one)
        assert self.IJ == sc(-1, B.mul(self.J, self.I))
        # coordinates w.r.t. (1, i, j, ij): invert the matrix with columns 1, I, J, IJ (order coordinates)
        cols = [one, self.I, self.J, self.IJ]
        M = flint.fmpq_mat(4, 4, [flint.fmpq(cols[c][r].numerator, cols[c][r].denominator)
                                  for r in range(4) for c in range(4)])
        Mi = M.inv()
        self.to_std = [[Fraction(int(Mi[r, c].p), int(Mi[r, c].q)) for c in range(4)] for r in range(4)]
        self.zero, self.one = QS(0, 0, self.a), QS(1, 0, self.a)
        self._rho: dict = {}
        self.sqa = QS(0, 1, self.a)
        for x in (self.I, self.J):
            for y in [tuple(Fraction(int(k == m)) for m in range(4)) for k in range(4)] + [self.I]:
                assert mat_mul(self.split(x), self.split(y)) == self.split(B.mul(x, y)), "splitting not multiplicative"
        es = [tuple(Fraction(int(k == m)) for m in range(4)) for k in range(4)]
        for x in es:
            for y in es:
                assert mat_mul(self.split(x), self.split(y)) == self.split(B.mul(x, y)), "splitting not multiplicative"

    def std(self, x):
        return [sum(self.to_std[r][c] * x[c] for c in range(4)) for r in range(4)]

    def split(self, x):
        """``s(x)`` for ``x`` in order coordinates: ``c0 + c1 i + c2 j + c3 ij``."""
        c0, c1, c2, c3 = self.std(x)
        a, b = self.a, self.b
        return [[QS(c0, c1, a), QS(b * c2, b * c3, a)], [QS(c2, -c3, a), QS(c0, -c1, a)]]

    def rho(self, x, n: int):
        key = (x, n)
        if key not in self._rho:
            self._rho[key] = sym_matrix(self.split(x), n, self.zero, self.one)
        return self._rho[key]

    def inv(self, x):
        nr = self.B.nrd(x)
        return tuple(c / nr for c in self.B.conj(x))


# ---------------------------------------------------------------- units and connecting elements
def lattice_vectors(B, L, bound: int):
    """All ``x in L`` with ``2 nrd(x) <= bound`` (both signs), as algebra elements."""
    pari = get_pari()
    res = pari.qfminim(B.gram(L), bound, None, 0)
    V = res[2]
    out = []
    for jj in range(int(pari.matsize(V)[1])):
        co = [int(V[i, jj]) for i in range(4)]
        x = tuple(sum(co[i] * L.basis[i][m] for i in range(4)) for m in range(4))
        out += [x, tuple(-c for c in x)]
    return out


def units(B, L, N):
    R = B.right_order(L, N)
    U = [x for x in lattice_vectors(B, R, 2) if B.nrd(x) == 1]
    return U


def generators(B, U):
    """A generating subset of the finite group ``U`` (greedy, via closure under multiplication)."""
    gens, H = [], {B.one}
    for g in U:
        if g in H:
            continue
        gens.append(g)
        H = set(H) | {g}
        while True:
            new = {B.mul(x, y) for x in H for y in H} - H
            if not new:
                break
            H |= new
    assert len(H) == len(U)
    return gens


def mat_vec(A, v, zero):
    return [sum((A[i][t] * v[t] for t in range(len(v))), zero) for i in range(len(A))]


def connecting(B, Lp, Np, J, NJ):
    """``beta`` with ``J = Lp * beta`` (or ``None``): ``beta = delta / N(Lp)``, ``delta in conj(Lp) J`` of norm ``Np*NJ``."""
    L = B.lmul(B.lconj(Lp), J)
    for d in lattice_vectors(B, L, 2 * Np * NJ):
        if B.nrd(d) == Np * NJ:
            beta = tuple(c / Np for c in d)
            assert brandt.Lattice([B.mul(x, beta) for x in Lp.basis]).key == J.key, "J != Lp*beta"
            return beta
    return None


# ---------------------------------------------------------------- the Brandt module M(O^x; V_k)
class SymBrandt:
    def __init__(self, D: int, k: int):
        self.S = S = split_algebra(D)
        self.D, self.k, self.n = D, k, k - 2
        B, mod = S.B, S.mod
        self.h = mod.h
        self.gammas = mod.gammas
        self.units = [units(B, L, N) for L, N in mod.reps]
        assert [len(u) for u in self.units] == self.gammas
        zero, one = S.zero, S.one
        dim = self.n + 1
        # V^{Gamma_c}: kernel of the stacked rho(gamma) - 1
        self.inv_basis = []
        for U in self.units:
            rows = []
            for g in generators(B, U):
                Rg = S.rho(g, self.n)
                rows += [[Rg[i][j] - (one if i == j else zero) for j in range(dim)] for i in range(dim)]
            self.inv_basis.append(nullspace(rows, dim, zero, one))
        self._ops: dict = {}
        self.dims = [len(W) for W in self.inv_basis]
        self.dim = sum(self.dims)
        self._T: dict = {}

    # -- action
    def apply_formula(self, ell: int, Phi):
        """``(T Phi)(L_c) = sum_J ell^n beta_J^{-1} . Phi(L_{c'(J)})`` for a tuple ``Phi`` of vectors in ``V``."""
        S = self.S
        out = []
        for row in self.ops(ell):
            acc = [S.zero] * (self.n + 1)
            for cp, Rg in row:
                if all(x.is_zero() for x in Phi[cp]):
                    continue
                acc = [x + y for x, y in zip(acc, mat_vec(Rg, Phi[cp], S.zero))]
            out.append(acc)
        return out

    def ops(self, ell):
        """Per class ``c``: the list of ``(c', ell^n rho(beta_J^{-1}))`` over the neighbours ``J`` of ``L_c``."""
        if ell not in self._ops:
            S, sc = self.S, Fraction(ell) ** self.n
            self._ops[ell] = [[(cp, [[sc * x for x in r] for r in S.rho(S.inv(beta), self.n)])
                               for (cp, beta), _NJ in row] for row in _neighbour_table(self.D, ell)]
        return self._ops[ell]

    def T(self, ell: int):
        """Matrix of ``T_ell`` on ``(+)_c V^{Gamma_c}`` in the basis ``inv_basis`` (entries in ``Q(sqrt a)``)."""
        if ell in self._T:
            return self._T[ell]
        S = self.S
        cols = []
        for c, W in enumerate(self.inv_basis):
            for w in W:
                Phi = [[S.zero] * (self.n + 1) for _ in range(self.h)]
                Phi[c] = w
                TPhi = self.apply_formula(ell, Phi)
                col = []
                for cc in range(self.h):
                    col += solve_in_span(self.inv_basis[cc], TPhi[cc], S.zero) if self.inv_basis[cc] else []
                    if not self.inv_basis[cc]:
                        assert all(x.is_zero() for x in TPhi[cc])
                cols.append(col)
        M = [[cols[j][i] for j in range(self.dim)] for i in range(self.dim)]
        self._T[ell] = M
        return M

    # -- Q-structure (k even)
    def phi(self, P):
        """``phi(P) = b^{n/2} rho(s(j))^{-1} sigma(P)``."""
        S, n = self.S, self.n
        Rj_inv = S.rho(S.inv(S.J), n)
        sc = Fraction(S.b) ** (n // 2)
        return [sc * x for x in mat_vec(Rj_inv, [x.conj() for x in P], S.zero)]

    def q_structure_report(self, ells) -> dict:
        S, n = self.S, self.n
        if n % 2:
            assert self.dim == 0
            return {"applicable": False, "reason": "k odd: -1 in Gamma_c acts by -1, all invariants vanish"}
        dim = n + 1
        E = [[S.one if i == t else S.zero for i in range(dim)] for t in range(dim)]
        # phi^2 = 1 on the K-basis and on sqrt(a) * basis (semilinear)
        assert all(self.phi(self.phi(e)) == e for e in E)
        assert all(self.phi(self.phi([S.sqa * x for x in e])) == [S.sqa * x for x in e] for e in E)
        # phi commutes with rho(s(gamma)) for the order basis
        es = [tuple(Fraction(int(kk == m)) for m in range(4)) for kk in range(4)]
        for g in es:
            Rg = S.rho(g, n)
            for e in E:
                lhs = self.phi([sum((Rg[i][t] * e[t] for t in range(dim)), S.zero) for i in range(dim)])
                pe = self.phi(e)
                rhs = [sum((Rg[i][t] * pe[t] for t in range(dim)), S.zero) for i in range(dim)]
                assert lhs == rhs, "phi does not commute with rho(s(B))"
        # Q-basis of V^phi
        cand = []
        for e in E:
            cand.append([x + y for x, y in zip(e, self.phi(e))])
            se = [S.sqa * x for x in e]
            cand.append([x + y for x, y in zip(se, self.phi(se))])
        Qb = []
        for v in cand:
            trial = Qb + [v]
            _, piv = rref([[w[i] for w in trial] for i in range(dim)])
            if len(piv) == len(trial):
                Qb = trial
            if len(Qb) == dim:
                break
        assert len(Qb) == dim
        Cm = [[Qb[j][i] for j in range(dim)] for i in range(dim)]  # columns = Q-basis
        Rr, piv = rref([Cm[i] + [S.one if i == j else S.zero for j in range(dim)] for i in range(dim)])
        assert piv == list(range(dim))
        Cinv = [r[dim:] for r in Rr]
        # rho(s(gamma)) in the Q-basis is rational (order basis; hence on all of O, B)
        for g in es:
            Rq = mat_mul(Cinv, mat_mul(S.rho(g, n), Cm))
            assert all(x.is_rational() for r in Rq for x in r), "rho(s(B)) not rational on V^phi"
        # phi commutes with T_ell on (+) V^{Gamma_c}
        comm = {}
        for ell in ells:
            ok = True
            for c, W in enumerate(self.inv_basis):
                for w in W:
                    for scal in (S.one, S.sqa):
                        Phi = [[S.zero] * dim for _ in range(self.h)]
                        Phi[c] = [scal * x for x in w]
                        a1 = [self.phi(v) for v in self.apply_formula(ell, Phi)]
                        a2 = self.apply_formula(ell, [self.phi(v) for v in Phi])
                        ok &= a1 == a2
            comm[str(ell)] = ok
        # rational model: Gamma_c-invariants in V_Q and T_ell there, char-poly over Q
        qcp = {}
        for ell in ells:
            qcp[str(ell)] = self._rational_model_charpoly(ell, Cm, Cinv)
        return {"applicable": True, "phi_involution": True, "phi_commutes_rho": True, "rho_rational_on_V_Q": True,
                "phi_commutes_T": comm, "rational_model_charpoly": qcp}

    def _rational_model_charpoly(self, ell, Cm, Cinv):
        """Char-poly of ``T_ell`` on ``(+)_c V_Q^{Gamma_c}``, computed in ``Q``-coordinates (``V_Q = Cm Q^{n+1}``)."""
        S, n, dim = self.S, self.n, self.n + 1
        if not hasattr(self, "_Winv"):
            Winv = []
            for U in self.units:
                rows = []
                for g in generators(S.B, U):
                    Rq = mat_mul(Cinv, mat_mul(S.rho(g, n), Cm))
                    rows += [[Rq[i][j].r - (1 if i == j else 0) for j in range(dim)] for i in range(dim)]
                Winv.append(nullspace(rows, dim, Fraction(0), Fraction(1)))
            assert [len(W) for W in Winv] == self.dims
            self._Winv = Winv
        Winv = self._Winv
        emb = lambda q: mat_vec(Cm, [QS(x, 0, S.a) for x in q], S.zero)
        cols = []
        for c, W in enumerate(Winv):
            for w in W:
                Phi = [[S.zero] * dim for _ in range(self.h)]
                Phi[c] = emb(w)
                TPhi = self.apply_formula(ell, Phi)
                col = []
                for cc in range(self.h):
                    q = mat_vec(Cinv, TPhi[cc], S.zero)
                    assert all(x.is_rational() for x in q), "T_ell leaves V_Q"
                    col += solve_in_span(Winv[cc], [x.r for x in q], Fraction(0)) if Winv[cc] else []
                cols.append(col)
        M = [[cols[j][i] for j in range(self.dim)] for i in range(self.dim)]
        if self.dim == 0:
            return [1]
        fm = flint.fmpq_mat(self.dim, self.dim, [flint.fmpq(x.numerator, x.denominator) for r in M for x in r])
        return [_frac_to_int(Fraction(int(c.p), int(c.q))) for c in fm.charpoly().coeffs()]


def _frac_to_int(x: Fraction):
    return int(x) if x.denominator == 1 else str(x)


@lru_cache(maxsize=None)
def split_algebra(D: int) -> SplitAlgebra:
    return SplitAlgebra(D)


@lru_cache(maxsize=None)
def _neighbour_table(D: int, ell: int):
    """For each class ``c`` the list of ``((c', beta), N(J))`` over the ``ell + 1`` neighbours ``J = L_{c'} beta`` of ``L_c``."""
    S = split_algebra(D)
    B, mod = S.B, S.mod
    assert D % ell, "ell must not divide D"
    table = []
    for L, N in mod.reps:
        row = []
        for Jl, NJ in brandt.neighbours(B, L, N, ell):
            found = None
            for cp, (Lp, Np) in enumerate(mod.reps):
                beta = connecting(B, Lp, Np, Jl, NJ)
                if beta is not None:
                    found = (cp, beta)
                    break
            assert found is not None, "neighbour in no class"
            row.append((found, NJ))
        table.append(row)
    return table


@lru_cache(maxsize=None)
def sym_brandt(D: int, k: int) -> SymBrandt:
    return SymBrandt(D, k)


# ---------------------------------------------------------------- modular forms side
def mf_new(D: int, k: int, ell: int) -> tuple[int, list[int]]:
    """``(dim, charpoly)`` of ``T_ell`` on ``S_k(Gamma_0(D))^new`` (``mfinit([D,k],0)``), constant term first."""
    pari = get_pari()
    mf = pari.mfinit([D, k], 0)
    d = int(pari.mfdim(mf))
    if d == 0:
        return 0, [1]
    cp = pari.charpoly(pari.mfheckemat(mf, ell))
    return d, [_frac_to_int(Fraction(int(pari.numerator(c)), int(pari.denominator(c)))) for c in reversed(list(pari.Vec(cp)))]


def ells_for(D: int) -> list[int]:
    return [l for l in ELLS if D % l]


def check(D: int, k: int, with_q: bool = True) -> dict:
    """The JL check for one ``(D, k)`` and all ``ell in {2,3}``, ``ell`` prime to ``D``."""
    M = sym_brandt(D, k)
    out = {"D": D, "k": k, "a": M.S.a, "b": M.S.b, "h": M.h, "gammas": M.gammas, "dims_V_Gamma": M.dims,
           "dim_brandt": M.dim, "ell": {}}
    dim_new = None
    for ell in ells_for(D):
        dn, cpn = mf_new(D, k, ell)
        dim_new = dn
        rhs = brandt.poly_mul([-(ell + 1), 1], cpn) if k == 2 else cpn
        T = M.T(ell)
        cpK = charpoly(T, M.S.zero, M.S.one)
        in_Q = all(c.is_rational() for c in cpK)
        cp = [_frac_to_int(c.r) for c in cpK] if in_Q else [repr(c) for c in cpK]
        out["ell"][str(ell)] = {"charpoly_brandt": cp, "charpoly_in_Q": in_Q, "charpoly_mf_new": cpn,
                                "rhs": rhs, "equal": in_Q and cp == rhs}
    out["dim_mf_new"] = dim_new
    out["dim_expected"] = dim_new + (1 if k == 2 else 0)
    out["dim_equal"] = M.dim == out["dim_expected"]
    if with_q:
        qr = M.q_structure_report(tuple(ells_for(D)))
        if qr["applicable"]:
            for ell in ells_for(D):
                qr.setdefault("rational_model_matches", {})[str(ell)] = \
                    qr["rational_model_charpoly"][str(ell)] == out["ell"][str(ell)]["charpoly_brandt"]
        out["Q_structure"] = qr
    out["all_ok"] = out["dim_equal"] and all(v["equal"] for v in out["ell"].values()) and (
        not with_q or not out["Q_structure"]["applicable"]
        or (all(out["Q_structure"]["phi_commutes_T"].values())
            and all(out["Q_structure"]["rational_model_matches"].values())))
    return out


def compute_all() -> dict:
    grid = {f"{D},{k}": check(D, k) for D in DS for k in KS}
    return {
        "conventions": {
            "splitting": "B=(a,b)_Q, i->diag(sqrt a,-sqrt a), j->(0 b;1 0), exact over Q(sqrt a)",
            "V_k": "Sym^{k-2}, (g.P)(X,Y)=P((X,Y)g)=P(aX+cY,bX+dY) (eq:s01-Vk), left action; basis X^{n-t}Y^t",
            "brandt": "Gross form F(gamma x u)=s(gamma).F(x) (rem:s01-dictionary, global splitting); "
                      "Phi(L alpha)=alpha^{-1}.Phi(L) on left O-ideals; (+)_c V^{Gamma_c}, Gamma_c=O_r(L_c)^x incl. -1",
            "T_ell": "(T Phi)(L_c) = sum_{J=L_c K, nrd K=ell} ell^n beta_J^{-1}.Phi(L_{c'}), J=L_{c'} beta_J",
            "Q_structure": "phi(P)=b^{n/2} rho(s(j))^{-1} sigma(P); V_Q = V^phi (k even)",
            "rhs": "charpoly(mfheckemat(mfinit([D,k],0),ell)) times (x-ell-1) iff k=2",
        },
        "grid": grid,
        "all_ok": all(v["all_ok"] for v in grid.values()),
    }


def main() -> None:
    with results.Timer() as t:
        data = compute_all()
    results.write(
        "s01/symn.json", data, script="code/python/langlandscape/symn.py",
        params={"Ds": list(DS), "ks": list(KS), "ells": list(ELLS)},
        runtime_s=t.seconds,
        notes="Sym^n Brandt modules at level O^x vs S_k(Gamma_0(D))^new; see module docstring for conventions",
    )
    assert data["all_ok"], "JL char-poly check failed for some (D, k, ell)"


if __name__ == "__main__":
    main()
