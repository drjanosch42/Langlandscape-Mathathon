"""S01-C7: the operator ``Pi_ell`` (``ell = D`` prime) on ``M(O^x; V_k)`` and its sign against ``a_D`` of the newforms.

Definition (``def:s01-hecke``): ``(Pi_ell F)(x) = F(x Pi_ell)`` with ``Pi_ell in B_ell^x`` a uniformiser of ``O_ell``
(``Pi_ell O_ell = P_ell`` the two-sided prime), in the convention of ``symn.py`` (Gross form ``F(gamma x u) = s(gamma).F(x)``,
``Phi(L alpha) = alpha^{-1}.Phi(L)`` on left ideals ``L_x = B cap O^ x^{-1}``).

Transport (derived).  ``L_{x Pi} = B cap O^ Pi^{-1} x^{-1} = P^{-1} L_x`` because ``O^ Pi^{-1} = P^{-1}`` locally at ``ell`` and
``P`` is two-sided; ``P^{-1} = P/ell`` since ``P^2 = ell O``.  With ``J = P L_c`` (a left ideal of norm ``ell N(L_c)``;
``P`` = the elements of ``O`` of reduced norm divisible by ``ell``; ``conj P = P``) and ``J = L_{c'} beta``:

    ``(Pi Phi)(L_c) = Phi(ell^{-1} J) = ell^n . beta^{-1} . Phi(L_{c'})``,       ``n = k - 2``,

on ideal classes ``[L] -> [P L] = [L P_R]``.  The factor ``ell^n`` (central ``ell^{-1}`` acting on ``V_k`` by ``ell^{-n}``
under ``Phi``) is *forced* by the definition, not a normalisation chosen by us: it gives ``Pi^2 = ell^{k-2} = S_ell``
(``prop:s01-relations``(b); ``Pi^2`` multiplies ``L`` by ``P^{-2} = ell^{-1}``).  So the eigenvalues of ``Pi_ell`` are
``+-ell^{(k-2)/2}`` and are directly comparable with ``a_ell(f) = +-ell^{k/2-1}`` of a newform of level ``ell`` and weight
``k``: *no further power of ell* appears in the comparison (``a_ell = - ell^{k/2-1} w_ell``, ``w_ell`` the Atkin-Lehner
sign).  ``U_ell -> +Pi_ell`` (F6/D3) means: the ``Pi``-eigenvalue of the eigensystem matched with ``f`` is exactly ``a_ell(f)``.

Matching.  ``Pi`` commutes with ``T_ell'`` (``ell' != D``).  On the ``Pi``-eigenspace ``lambda = +-ell^{n/2}`` we compute the
char-poly of ``T_ell'`` and compare with the char-poly of ``T_ell'`` restricted to the ``U_D = a_D``-eigenspace of the same
``lambda`` in ``S_k(Gamma_0(D))^new`` (PARI ``mfheckemat``).  For ``k = 2`` the Eisenstein line ``1`` (``T_ell' = ell'+1``) has
``Pi = +1``.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache

from . import results, symn
from .pari import get_pari

DS = (11, 13, 17, 19)
KS = (2, 4)
ELLS = (2, 3, 5)


def prime_ideal_lattice(S: "symn.SplitAlgebra"):
    """The two-sided prime ``P`` of ``O`` above ``D`` (elements of reduced norm divisible by ``D``) as a ``Lattice``."""
    B, D = S.B, S.D
    pari = get_pari()
    Gm = B.gram(B.O)
    Gi = [[int(Gm[i, j]) for j in range(4)] for i in range(4)]

    def nrd2(v):
        return sum(v[i] * Gi[i][j] * v[j] for i in range(4) for j in range(4))  # 2 nrd

    import itertools

    sols = [v for v in itertools.product(range(D), repeat=4) if any(v) and nrd2(v) % (2 * D) == 0 and nrd2(v) % D == 0]
    # P/DO is a 2-dim F_D-subspace: pick two independent solutions
    basis_vecs = []
    for v in sols:
        if not basis_vecs:
            basis_vecs.append(v)
            continue
        w = basis_vecs[0]
        # independent of w mod D?
        if any((v[i] * w[j] - v[j] * w[i]) % D for i in range(4) for j in range(i + 1, 4)):
            basis_vecs.append(v)
            break
    assert len(basis_vecs) == 2, "P/DO is not 2-dimensional"
    from .quat import Lattice

    gens = [tuple(Fraction(c) for c in v) for v in basis_vecs] + [
        tuple(Fraction(D * int(i == j)) for j in range(4)) for i in range(4)]
    P = Lattice(gens)
    # index D^2 in O  (det of basis = D^2 in the standard basis)
    d = abs(int(pari.matdet(pari.matrix(4, 4, [int(P.basis[j][i]) for i in range(4) for j in range(4)]))))
    assert d == D * D, d
    return P


@lru_cache(maxsize=None)
def _pi_table(D: int):
    """Per class ``c``: ``(c', beta)`` with ``P L_c = L_{c'} beta`` (reduced norm ``D N_c``)."""
    S = symn.split_algebra(D)
    B, mod = S.B, S.mod
    P = prime_ideal_lattice(S)
    # P is two-sided with P^2 = D O
    assert B.lmul(P, P).key == B.scale(B.O, D).key
    table = []
    for L, N in mod.reps:
        J = B.lmul(P, L)
        found = None
        for cp, (Lp, Np) in enumerate(mod.reps):
            beta = symn.connecting(B, Lp, Np, J, D * N)
            if beta is not None:
                found = (cp, beta)
                break
        assert found is not None
        table.append(found)
    return table


def pi_matrix(D: int, k: int):
    """Matrix of ``Pi_D`` on ``(+)_c V^{Gamma_c}`` in the basis ``inv_basis`` of ``symn.sym_brandt(D, k)`` (entries in Q(sqrt a))."""
    M = symn.sym_brandt(D, k)
    S, n = M.S, M.n
    sc = Fraction(D) ** n
    table = _pi_table(D)
    cols = []
    for c, W in enumerate(M.inv_basis):
        for w in W:
            # (Pi Phi)(L_{c0}) = D^n rho(beta^{-1}) Phi(L_{c'(c0)}) for Phi supported on c
            out = []
            for c0, (cp, beta) in enumerate(table):
                if cp == c:
                    Rg = S.rho(S.inv(beta), n)
                    out.append([sc * x for x in symn.mat_vec(Rg, w, S.zero)])
                else:
                    out.append([S.zero] * (n + 1))
            col = []
            for cc in range(M.h):
                if M.inv_basis[cc]:
                    col += symn.solve_in_span(M.inv_basis[cc], out[cc], S.zero)
                else:
                    assert all(x.is_zero() for x in out[cc])
            cols.append(col)
    return [[cols[j][i] for j in range(M.dim)] for i in range(M.dim)]


def _eye(m, S):
    return [[S.one if i == j else S.zero for j in range(m)] for i in range(m)]


def _scalar_minus(A, lam, S):
    m = len(A)
    return [[A[i][j] - (lam if i == j else 0) * S.one for j in range(m)] for i in range(m)]


def _intlist(cp):
    if not all(c.is_rational() for c in cp):
        return None
    out = []
    for c in cp:
        r = c.r
        out.append(int(r) if r.denominator == 1 else str(r))
    return out


def brandt_side(D: int, k: int, ells=ELLS) -> dict:
    """Pi matrix, relations, and char-polys of ``T_ell`` on the ``Pi``-eigenspaces (key = eigenvalue as string)."""
    M = symn.sym_brandt(D, k)
    S, n = M.S, M.n
    m = M.dim
    Pi = pi_matrix(D, k)
    Pi2 = symn.mat_mul(Pi, Pi)
    Dn = Fraction(D) ** n
    out = {"dim": m, "n": n}
    out["Pi_squared_equals_D^n"] = Pi2 == [[Dn * S.one if i == j else S.zero for j in range(m)] for i in range(m)]
    out["commutes_with_T"] = {str(l): symn.mat_mul(Pi, M.T(l)) == symn.mat_mul(M.T(l), Pi) for l in ells if D % l}
    half = Fraction(D) ** (n // 2)  # k even
    eig = {}
    for sign in (+1, -1):
        lam = sign * half
        W = symn.nullspace(_scalar_minus(Pi, lam, S), m, S.zero, S.one)
        info = {"lambda": str(lam), "dim": len(W), "charpoly_T": {}}
        for l in ells:
            if D % l == 0 or not W:
                continue
            T = M.T(l)
            cols = [symn.solve_in_span(W, symn.mat_vec(T, w, S.zero), S.zero) for w in W]
            R = [[cols[j][i] for j in range(len(W))] for i in range(len(W))]
            info["charpoly_T"][str(l)] = _intlist(symn.charpoly(R, S.zero, S.one))
        eig[("+" if sign > 0 else "-")] = info
    out["eigenspaces"] = eig
    out["eigenvalues_exhaust"] = sum(e["dim"] for e in eig.values()) == m
    return out


def mf_side(D: int, k: int, ells=ELLS) -> dict:
    """``S_k(Gamma_0(D))^new``: split by the ``U_D = a_D`` eigenvalue ``+-D^{(k-2)/2}``; char-polys of ``T_ell``."""
    pari = get_pari()
    mf = pari.mfinit([D, k], 0)
    d = int(pari.mfdim(mf))
    UD = pari.mfheckemat(mf, D) if d else None
    half = Fraction(D) ** ((k - 2) // 2)
    out = {"dim": d, "eigenspaces": {}}
    Ts = {l: pari.mfheckemat(mf, l) for l in ells if D % l} if d else {}
    tot = 0
    for sign, key in ((1, "+"), (-1, "-")):
        lam = int(sign * half)
        K = pari.matker(UD - lam * pari.matid(d)) if d else None
        dim = int(pari.matsize(K)[1]) if d else 0
        tot += dim
        info = {"lambda": str(lam), "dim": dim, "charpoly_T": {}}
        for l, T in Ts.items():
            if dim == 0:
                continue
            R = pari.matinverseimage(K, T * K)
            cp = pari.charpoly(R)
            info["charpoly_T"][str(l)] = [int(c) for c in reversed(list(pari.Vec(cp)))]
        out["eigenspaces"][key] = info
    out["UD_semisimple_with_eigenvalues_pm"] = tot == d
    return out


def _times_x_minus(cp, r):
    """constant-term-first coefficients of ``(x - r) * cp``."""
    out = [0] * (len(cp) + 1)
    for i, c in enumerate(cp):
        out[i + 1] += c
        out[i] -= r * c
    return out


def compare(D: int, k: int, ells=ELLS) -> dict:
    b, f = brandt_side(D, k, ells), mf_side(D, k, ells)
    res = {"D": D, "k": k, "brandt": b, "mf": f}
    ok_by_sign, flipped_by_sign = {}, {}
    for key, other in (("+", "-"), ("-", "+")):
        eb, ef = b["eigenspaces"][key], f["eigenspaces"][key]
        eisen = 1 if (k == 2 and key == "+") else 0  # Eisenstein line: Pi = +1, T_ell = ell+1
        ok = eb["dim"] == ef["dim"] + eisen
        for l in eb["charpoly_T"]:
            rhs = ef["charpoly_T"].get(l, [1])
            if eisen:
                rhs = _times_x_minus(rhs, int(l) + 1)
            ok = ok and eb["charpoly_T"][l] == rhs
        ok_by_sign[key] = ok
        # would the opposite assignment (Pi = -a_D) also match?  (detects an ambiguity of the test)
        eo = f["eigenspaces"][other]
        fl = eb["dim"] == eo["dim"] + eisen
        for l in eb["charpoly_T"]:
            rhs = eo["charpoly_T"].get(l, [1])
            if eisen:
                rhs = _times_x_minus(rhs, int(l) + 1)
            fl = fl and eb["charpoly_T"][l] == rhs
        flipped_by_sign[key] = fl
    res["no_newforms"] = f["dim"] == 0
    res["match_Pi_eq_plus_aD"] = ok_by_sign["+"] and ok_by_sign["-"]
    res["match_Pi_eq_minus_aD"] = flipped_by_sign["+"] and flipped_by_sign["-"]
    # a sign statement is meaningful only if the Pi-eigenspaces other than the Eisenstein line are non-empty
    res["ambiguous"] = res["match_Pi_eq_plus_aD"] and res["match_Pi_eq_minus_aD"] and not res["no_newforms"]
    res["sign_contradiction"] = (not res["match_Pi_eq_plus_aD"]) and res["match_Pi_eq_minus_aD"]
    res["relation"] = (
        "Pi_D-eigenvalue = +a_D(f)  [U_D -> +Pi_D]; a_D = -D^{k/2-1} w_D; no extra power of D (Pi^2 = D^{k-2} built in)"
        if res["match_Pi_eq_plus_aD"] and not res["match_Pi_eq_minus_aD"] else
        "no newforms (S_k(Gamma_0(D))^new = 0); only the Eisenstein line, Pi = +1" if res["no_newforms"] and res["match_Pi_eq_plus_aD"] else
        "SIGN CONTRADICTION: Pi_D-eigenvalue = -a_D(f)" if res["sign_contradiction"] else
        "AMBIGUOUS or unmatched; see flags")
    res["Pi_squared_equals_D^n"] = b["Pi_squared_equals_D^n"]
    res["commutes_with_T"] = b["commutes_with_T"]
    return res


def compute_all() -> dict:
    grid = {f"{D},{k}": compare(D, k) for D in DS for k in KS}
    d11 = grid["11,2"]
    pi11 = pi_matrix(11, 2)
    ex = {"Pi_11_is_identity_k2": all((c.r == (1 if i == j else 0) and c.s == 0) for i, r in enumerate(pi11)
                                       for j, c in enumerate(r)),
          "a_11(11a)": +1 if d11["mf"]["eigenspaces"]["+"]["dim"] == 1 else -1}
    return {
        "conventions": {
            "Pi": "(Pi F)(x) = F(x Pi_D); on left ideals Phi(L) -> Phi(P^{-1} L) = D^n beta^{-1}.Phi(L_{c'}), P L_c = L_{c'} beta",
            "normalisation": "Pi^2 = D^{k-2} = S_D; eigenvalues +-D^{(k-2)/2}; a_D = +-D^{k/2-1}; compared directly",
            "mf": "U_D = mfheckemat(mfinit([D,k],0), D) = a_D on the newspace",
        },
        "grid": grid,
        "ex_s01_Pi11": ex,
        "all_plus": all(v["match_Pi_eq_plus_aD"] for v in grid.values()),
        "any_sign_contradiction": any(v["sign_contradiction"] for v in grid.values()),
        "any_ambiguous": any(v["ambiguous"] for v in grid.values()),
    }


def main() -> None:  # pragma: no cover - script entry point
    with results.Timer() as t:
        data = compute_all()
    results.write(
        "s01/pi_sign.json", data, script="code/python/langlandscape/pi_ell.py",
        params={"Ds": list(DS), "ks": list(KS), "ells": list(ELLS)}, runtime_s=t.seconds,
        notes="Pi_D eigenvalues vs a_D on S_k(Gamma_0(D))^new (U_ell -> +Pi_ell check, stage 05)")
    for key, v in data["grid"].items():
        print(key, v["relation"])
    if data["any_sign_contradiction"]:
        print("SIGN CONTRADICTION")


if __name__ == "__main__":
    main()
