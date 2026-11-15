"""S01-C3: weight-2 Brandt matrices ``T_l`` at ``U_0(M)`` for definite quaternion algebras ``B_D``.

Conventions (``def:s01-brandt``):

* Classes ``c`` are left ideal classes ``I ~ I*alpha`` of an order ``R`` (maximal for ``M = 1``; an Eichler order
  of level ``M`` for ``M > 1``), ``Gamma_c = O_r(I_c)^x`` and ``|Gamma_c|`` **includes** ``-1`` (so ``|Gamma_c| = 2 w_c``;
  the ratio statement below is insensitive to the factor 2).
* ``B[c][c'] = #{ l-neighbours J = I_c*K of I_c (K a left ideal of norm l of O_r(I_c)) lying in class c' }``.
  Row sums are ``l+1`` and ``|Gamma_c'| B[c][c'] = |Gamma_c| B[c'][c]``.
* ``M > 1`` (prime ``M`` not dividing ``D``): ``R = O cap O_r(J)`` with ``J`` an ``M``-neighbour of ``O``; this
  is an Eichler order of level ``M`` (checked: ``det Gram = (D M)^2``).  Mass check
  ``sum 1/|Gamma_c| = phi(D) psi(M) / 24``.  Left ideals of ``R`` are locally principal, so
  right order ``conj(I) I / N``, the norm-``l`` neighbours (``l`` prime to ``D M``) and the principality
  test of ``quat.equivalent`` carry over verbatim.

Isogeny side: the supersingular ``l``-isogeny graph over ``F_{q^2}``; vertices are the supersingular
``j``-invariants (found by testing every ``j`` in ``F_{q^2}`` with ``ellissupersingular``; PARI 2.15.4 has no
``ellsupersingularj``), ``A[j][j']`` = multiplicity of ``j'`` as a root of ``Phi_l(j, Y)`` (``polmodular``).
"""

from __future__ import annotations

import itertools
from fractions import Fraction
from functools import lru_cache

import flint

from . import results
from .pari import get_pari
from .quat import DefiniteAlgebra, Lattice, prime_factors

ELLS = (2, 3, 5, 7)
SEED_QS = (11, 17, 19, 23, 37, 53)
DNEW_CASES = ((2, 11), (3, 5), (5, 7))
PRIMES_D = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)


# ---------------------------------------------------------------- lattices
def _dual(L: Lattice) -> list[tuple]:
    m = flint.fmpq_mat(4, 4, [flint.fmpq(c.numerator, c.denominator) for v in L.basis for c in v])
    inv = m.inv().transpose()
    return [tuple(Fraction(int(inv[i, j].p), int(inv[i, j].q)) for j in range(4)) for i in range(4)]


def intersect(L1: Lattice, L2: Lattice) -> Lattice:
    """``L1 cap L2`` as ``(L1^* + L2^*)^*``."""
    S = Lattice(_dual(L1) + _dual(L2))
    return Lattice(_dual(S))


# ---------------------------------------------------------------- neighbours
def neighbours(B: DefiniteAlgebra, I: Lattice, N: int, ell: int) -> list[tuple[Lattice, int]]:
    """The ``ell+1`` neighbours ``I*K`` (``K`` left ideal of norm ``ell`` of ``O_r(I)``), any prime ``ell`` prime to the level."""
    R = B.right_order(I, N)
    lR = B.scale(R, ell)
    seen: dict = {}
    for co in itertools.product(range(ell), repeat=4):
        nz = next((c for c in co if c), None)
        if nz != 1:  # projective normalisation: scalars mod ell give the same ideal
            continue
        alpha = tuple(sum(c * r[i] for c, r in zip(co, R.basis)) for i in range(4))
        if B.nrd(alpha) % ell:
            continue
        K = Lattice([B.mul(r, alpha) for r in R.basis] + lR.basis)
        seen.setdefault(K.key, K)
    assert len(seen) == ell + 1, f"expected {ell + 1} neighbours, got {len(seen)}"
    return [(B.lmul(I, K), N * ell) for K in seen.values()]


def squarefree_neighbours(B: DefiniteAlgebra, I: Lattice, N: int, n: int) -> list[tuple[Lattice, int]]:
    """All ``prod_{p|n}(p+1)`` ideals ``I*K``, ``K`` left ideal of norm ``n`` (squarefree), by direct enumeration in ``R/nR``."""
    ps = prime_factors(n)
    R = B.right_order(I, N)
    nR = B.scale(R, n)
    seen: dict = {}
    for co in itertools.product(range(n), repeat=4):
        if any(all(c % p == 0 for c in co) for p in ps):
            continue
        alpha = tuple(sum(c * r[i] for c, r in zip(co, R.basis)) for i in range(4))
        if B.nrd(alpha) % n:
            continue
        K = Lattice([B.mul(r, alpha) for r in R.basis] + nR.basis)
        seen.setdefault(K.key, K)
    want = 1
    for p in ps:
        want *= p + 1
    assert len(seen) == want, (len(seen), want)
    return [(B.lmul(I, K), N * n) for K in seen.values()]


# ---------------------------------------------------------------- class sets of an order
class BrandtModule:
    """Left ideal classes of an order ``R`` (given as the lattice ``order``) with Brandt matrices ``T(l)``."""

    def __init__(self, B: DefiniteAlgebra, order: Lattice, D: int, M: int, ell0: int):
        self.B, self.D, self.M = B, D, M
        self.reps: list[tuple[Lattice, int]] = [(order, 1)]
        queue = [0]
        while queue:
            idx = queue.pop(0)
            I, N = self.reps[idx]
            for J, NJ in neighbours(B, I, N, ell0):
                if self.class_of(J, NJ) is None:
                    self.reps.append((J, NJ))
                    queue.append(len(self.reps) - 1)
        self.gammas = [B.unit_count(I, N) for I, N in self.reps]
        self.h = len(self.reps)
        self.mass = sum(Fraction(1, g) for g in self.gammas)
        phi = 1
        for p in prime_factors(D):
            phi *= p - 1
        psi = M + 1 if M > 1 else 1
        assert self.mass == Fraction(phi * psi, 24), (self.mass, phi, psi)
        self._T: dict = {}

    def class_of(self, J: Lattice, NJ: int):
        for k, (R, NR) in enumerate(self.reps):
            if self.B.equivalent(R, NR, J, NJ):
                return k
        return None

    def _row_counts(self, nbrs) -> list[int]:
        row = [0] * self.h
        for J, NJ in nbrs:
            k = self.class_of(J, NJ)
            assert k is not None, "neighbour not in any known class (class set incomplete)"
            row[k] += 1
        return row

    def T(self, ell: int) -> list[list[int]]:
        """Brandt matrix of the prime ``ell`` (prime to ``D M``)."""
        if ell not in self._T:
            assert (self.D * self.M) % ell, "ell must be prime to D*M"
            self._T[ell] = [self._row_counts(neighbours(self.B, I, N, ell)) for I, N in self.reps]
        return self._T[ell]

    def T_direct(self, n: int) -> list[list[int]]:
        """Matrix of the squarefree composite ``n`` by direct enumeration of norm-``n`` ideals (independent of ``T(l)``)."""
        return [self._row_counts(squarefree_neighbours(self.B, I, N, n)) for I, N in self.reps]


@lru_cache(maxsize=None)
def algebra(D: int) -> DefiniteAlgebra:
    return DefiniteAlgebra(D)


def eichler_order(B: DefiniteAlgebra, M: int) -> Lattice:
    """Eichler order ``O cap O_r(J)`` of level ``M`` (``M`` prime, ``M`` prime to ``D``)."""
    if M == 1:
        return B.O
    J, NJ = neighbours(B, B.O, 1, M)[0]
    R = intersect(B.O, B.right_order(J, NJ))
    det = abs(int(get_pari().matdet(B.gram(R))))
    assert det == (B.D * M) ** 2, f"not an Eichler order of level {M}: det {det}"
    return R


@lru_cache(maxsize=None)
def module(D: int, M: int = 1) -> BrandtModule:
    B = algebra(D)
    ell0 = next(p for p in (2, 3, 5, 7, 11, 13) if (D * M) % p)
    return BrandtModule(B, eichler_order(B, M), D, M, ell0)


# ---------------------------------------------------------------- linear algebra helpers (PARI)
def _pmat(A):
    n = len(A)
    return get_pari().matrix(n, n, [int(A[i][j]) for i in range(n) for j in range(n)])


def charpoly_coeffs(A) -> list[int]:
    """Integer coefficients of ``det(x - A)``, constant term first."""
    pari = get_pari()
    cp = pari.charpoly(_pmat(A))
    return [int(c) for c in reversed(list(pari.Vec(cp)))]


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def matmul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def eigenvalues(A) -> list:
    """Eigenvalues as sorted integer roots of the charpoly if it splits over Z (else the charpoly)."""
    pari = get_pari()
    f = pari.charpoly(_pmat(A))
    fac = pari.factor(f)
    roots = []
    for k in range(int(pari.matsize(fac)[0])):
        g = fac[0][k]
        if int(pari.poldegree(g)) != 1:
            return {"charpoly_factorisation": str(fac)}
        r = -int(pari.polcoef(g, 0)) // int(pari.polcoef(g, 1))
        roots += [r] * int(fac[1][k])
    return sorted(roots, reverse=True)


# ---------------------------------------------------------------- PARI modular forms side
def mf_charpoly(N: int, ell: int, new: bool) -> list[int]:
    """Charpoly of ``T_ell`` on ``S_2(Gamma_0(N))`` (``new=False``) or its newspace (``new=True``), constant term first."""
    pari = get_pari()
    mf = pari.mfinit([N, 2], 0 if new else 1)
    if int(pari.mfdim(mf)) == 0:
        return [1]
    cp = pari.charpoly(pari.mfheckemat(mf, ell))
    return [int(c) for c in reversed(list(pari.Vec(cp)))]


def mf_dim(N: int, new: bool) -> int:
    pari = get_pari()
    return int(pari.mfdim(pari.mfinit([N, 2], 0 if new else 1)))


def seed_rhs(q: int, ell: int) -> list[int]:
    """``(x - ell - 1) * charpoly(T_ell | S_2(Gamma_0(q)))``."""
    return poly_mul([-(ell + 1), 1], mf_charpoly(q, ell, new=False))


def dnew_rhs(D: int, M: int, ell: int) -> list[int]:
    """Old/new bookkeeping for ``D`` prime, ``M`` prime, ``(D, M) = 1``, ``ell`` prime to ``DM``.

    The Brandt module at ``U_0(M)`` of ``B_D`` is, Hecke-equivariantly, the constant line (eigenvalue ``ell+1``)
    plus the ``D``-new part of ``S_2(Gamma_0(DM))``.  Level-``DM`` forms that are ``D``-new are:
    ``new(DM)`` (once) and ``new(D)`` embedded by ``f(z), f(Mz)`` (twice); forms coming from level ``M``
    are ``D``-old and excluded.  So rhs = ``(x - ell - 1) * cp(new(DM)) * cp(new(D))^2``.
    """
    out = poly_mul([-(ell + 1), 1], mf_charpoly(D * M, ell, new=True))
    c = mf_charpoly(D, ell, new=True)
    return poly_mul(poly_mul(out, c), c)


def dnew_dim(D: int, M: int) -> int:
    return 1 + mf_dim(D * M, True) + 2 * mf_dim(D, True)


# ---------------------------------------------------------------- supersingular isogeny graph
_GP = [
    "{ssjs(q)=my(g=ffgen(q^2,'t),L=List());for(a=0,q-1,for(b=0,q-1,my(j=a+b*g);"
    "if(ellissupersingular(ellinit(ellfromj(j))),listput(L,j))));Vec(L)}",
    "{isoadj(J,l,q)=my(n=#J,A=matrix(n,n),P=polmodular(l));for(i=1,n,my(F=factor(subst(P,x,J[i])));"
    "for(r=1,matsize(F)[1],my(f=F[r,1]);if(poldegree(f)!=1,error(\"non-linear factor\"));"
    "my(rt=-polcoef(f,0)/polcoef(f,1),k=0);for(m=1,n,if(J[m]==rt,k=m));if(k==0,error(\"root outside list\"));"
    "A[i,k]+=F[r,2]));A}",
    "autord(J,q)=vector(#J,i,if(J[i]==0,6,if(J[i]==1728*J[i]^0,4,2)))",
]


def isogeny_graph(q: int, ells=ELLS) -> dict:
    pari = get_pari()
    for src in _GP:
        pari(src)
    pari(f"JSS=ssjs({q})")
    n = int(pari("#JSS"))
    J = [pari(f"JSS[{i + 1}]") for i in range(n)]
    auts = [int(a) for a in pari(f"autord(JSS,{q})")]
    mats = {}
    for ell in ells:
        if ell == q:
            continue
        A = pari(f"isoadj(JSS,{ell},{q})")
        mats[ell] = [[int(A[i, j]) for j in range(n)] for i in range(n)]
    return {"j": [str(j) for j in J], "aut": auts, "A": mats}


def match_permutation(mod_T: dict, gammas: list[int], graph: dict):
    """Find ``pi`` (class ``i`` -> j-invariant ``pi[i]``) with ``A_l[pi i][pi k] = B_l[i][k]`` for all ``l`` simultaneously.

    Method: brute-force search over permutations respecting ``|Gamma_i| = |Aut(E_{pi i})|`` (vertex weights),
    checking all matrices ``B_l`` at once (``h <= 5`` here).  Tries ``B`` and ``B^T`` (the convention
    left/right ideal vs. source/target); returns ``(pi, "B" or "B^T")`` or ``None``.
    """
    h = len(gammas)
    auts = graph["aut"]
    for mode in ("B", "B^T"):
        for pi in itertools.permutations(range(h)):
            if any(gammas[i] != auts[pi[i]] for i in range(h)):
                continue
            ok = True
            for ell, T in mod_T.items():
                A = graph["A"][ell]
                for i in range(h):
                    for k in range(h):
                        b = T[i][k] if mode == "B" else T[k][i]
                        if A[pi[i]][pi[k]] != b:
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    break
            if ok:
                return list(pi), mode
    return None


# ---------------------------------------------------------------- driver
def ells_for(D: int, M: int = 1) -> list[int]:
    return [l for l in ELLS if (D * M) % l]


def relations_report(m: BrandtModule) -> dict:
    ells = ells_for(m.D, m.M)
    Ts = {l: m.T(l) for l in ells}
    rows = all(sum(r) == l + 1 for l, T in Ts.items() for r in T)
    sym = all(m.gammas[j] * T[i][j] == m.gammas[i] * T[j][i]
              for T in Ts.values() for i in range(m.h) for j in range(m.h))
    comm = all(matmul(Ts[a], Ts[b]) == matmul(Ts[b], Ts[a]) for a in ells for b in ells)
    return {"row_sums": rows, "weighted_symmetry": sym, "commutative": comm}


def seed_c4ii(q: int) -> dict:
    m = module(q)
    graph = isogeny_graph(q)
    Ts = {l: m.T(l) for l in ells_for(q)}
    res = {"h": m.h, "gammas": m.gammas, "reps_norms": [N for _, N in m.reps], "relations": relations_report(m), "ell": {}}
    for l, T in Ts.items():
        cp = charpoly_coeffs(T)
        res["ell"][str(l)] = {"T": T, "charpoly": cp, "pari_rhs": seed_rhs(q, l), "equal": cp == seed_rhs(q, l)}
    match = match_permutation(Ts, m.gammas, graph)
    res["isogeny"] = {"j_invariants_Fq2": graph["j"], "aut_orders": graph["aut"], "A": {str(l): A for l, A in graph["A"].items()},
                      "matching": None if match is None else {"perm_class_to_j": match[0], "mode": match[1]},
                      "method": "brute-force permutation respecting |Gamma|=|Aut|, simultaneous for all l"}
    return res


def dnew_check(D: int, M: int) -> dict:
    m = module(D, M)
    res = {"h": m.h, "gammas": m.gammas, "dim_expected": dnew_dim(D, M), "relations": relations_report(m), "ell": {}}
    for l in ells_for(D, M):
        cp = charpoly_coeffs(m.T(l))
        rhs = dnew_rhs(D, M, l)
        res["ell"][str(l)] = {"T": m.T(l), "charpoly": cp, "pari_rhs": rhs, "equal": cp == rhs}
    return res


def t1_numbers() -> dict:
    pari = get_pari()
    m = module(11)
    T2 = m.T(2)
    E = pari("ellinit([0,-1,1,-10,-20])")  # 11a1
    mf = pari.mfinit([11, 2], 1)
    return {
        "D": 11, "h": m.h, "gammas": m.gammas, "mass": m.mass, "mass_expected": Fraction(10, 24),
        "T2": T2, "T2_eigenvalues": eigenvalues(T2),
        "X0_11": {"genus": int(pari.mfdim(mf)), "genus_via": "dim S_2(Gamma_0(11)) (mfinit)",
                  "a2_mf": int(pari.mfheckemat(mf, 2)[0, 0]), "a2_11a1_ellap": int(pari.ellap(E, 2)),
                  "weil_curve": "11a1 = [0,-1,1,-10,-20]"},
    }


def t2_table() -> dict:
    out = {}
    for D in PRIMES_D:
        m = module(D)
        ell = 2 if D != 2 else 3  # T_2 at l = D = 2 is not a Brandt T_l (ramified prime)
        T = m.T(ell)
        out[str(D)] = {"h": m.h, "gammas_multiset": sorted(m.gammas), "gammas_in_rep_order": m.gammas,
                       "ell": ell, "T": T, "charpoly": charpoly_coeffs(T), "eigenvalues": eigenvalues(T)}
    return out


def compute_all() -> dict:
    return {
        "conventions": {
            "gamma": "|Gamma_c| = |O_r(I_c)^x| including -1",
            "B": "B[c][c'] = number of l-neighbours I_c*K lying in class c'; row sums l+1; |Gamma_c'| B[c][c'] = |Gamma_c| B[c'][c]",
            "M>1": "Eichler order O cap O_r(J), J an M-neighbour of O",
        },
        "T1": t1_numbers(),
        "seed_C4ii": {str(q): seed_c4ii(q) for q in SEED_QS},
        "dnew": {f"{D},{M}": dnew_check(D, M) for D, M in DNEW_CASES},
        "T2_table": t2_table(),
    }


def main() -> None:
    with results.Timer() as t:
        data = compute_all()
    results.write(
        "s01/brandt_w2.json", data, script="code/python/langlandscape/brandt.py",
        params={"seed_qs": list(SEED_QS), "ells": list(ELLS), "dnew_cases": [list(c) for c in DNEW_CASES]},
        runtime_s=t.seconds,
        notes="weight-2 Brandt matrices; see module docstring for conventions",
    )


if __name__ == "__main__":
    main()
