# SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
# Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
"""S05-C1 / T05-1 (validation of FD2, ``tc:s05-sign``): ``a_q = +lambda(Pi_q)`` on every Brandt eigenline.

``q in {11,23,37,43}``, ``M = 1``, ``k in {2,4,6,8}``.  The Brandt module ``M(O^x; V_k)`` of ``B_q`` carries
``Pi_q`` (stage-1 normalisation ``Pi^2 = q^{k-2}``, ``pi_ell.pi_matrix``) and ``T_2, T_3, T_5``.  Both sides are split by the
``Pi_q`` / ``U_q = a_q`` eigenvalue ``+-q^{(k-2)/2}``.  On each eigenspace the *joint test operator*
``C = T_2 + 3 T_3 + 7 T_5`` is formed; its char-poly is factored over Q.  An irreducible factor ``g`` (degree ``d``,
multiplicity ``m``) is one Galois orbit of Hecke eigensystems = ``d*m`` eigenlines over Qbar.  A Brandt factor is matched with
the newform orbit whose ``C``-factor is the same ``g`` (equal ``C``-eigenvalues, hence equal ``T_2,T_3,T_5``-eigensystems
generically; additionally the individual char-polys of ``T_2,T_3,T_5`` on the full eigenspace must agree).  The Eisenstein
line at ``k = 2`` (``Pi = +1``, ``T_l = l+1``, ``C = 57``) is divided out.  An orbit is ``plus`` if the Brandt ``Pi_q``-sign
equals the sign of ``a_q`` of the matched newform orbit, ``minus`` if the opposite sign matches.
"""

from __future__ import annotations

from fractions import Fraction

from .. import pi_ell, results, symn
from ..pari import get_pari

QS = (11, 23, 37, 43)
KS = (2, 4, 6, 8)
ELLS = (2, 3, 5)
COEF = {2: 1, 3: 3, 5: 7}


def _pol(coeffs_const_first):
    pari = get_pari()
    return pari.Pol([int(c) for c in reversed(coeffs_const_first)])


def _factors(f):
    """``[(coeffs const-first, degree, multiplicity)]`` of the irreducible factors of ``f`` over Q."""
    pari = get_pari()
    fa = pari.factor(f)
    out = []
    for i in range(int(pari.matsize(fa)[0])):
        g, m = fa[0][i], int(fa[1][i])
        out.append(([int(c) for c in reversed(list(pari.Vec(g)))], int(pari.poldegree(g)), m))
    return sorted(out, key=lambda t: (t[1], t[0]))


def _div_eisenstein(f, k):
    if k != 2:
        return f
    pari = get_pari()
    ev = sum(COEF[l] * (l + 1) for l in ELLS)
    x = pari.Pol([1, 0])
    qt, r = pari.divrem(f, x - ev)[0], pari.divrem(f, x - ev)[1]
    assert r == 0
    return qt


def brandt_side(q: int, k: int) -> dict:
    M = symn.sym_brandt(q, k)
    S, n, m = M.S, M.n, M.dim
    Pi = pi_ell.pi_matrix(q, k)
    Dn = Fraction(q) ** n
    ok2 = symn.mat_mul(Pi, Pi) == [[Dn * S.one if i == j else S.zero for j in range(m)] for i in range(m)]
    Ts = {l: M.T(l) for l in ELLS}
    comm = all(symn.mat_mul(Pi, T) == symn.mat_mul(T, Pi) for T in Ts.values())
    half = Fraction(q) ** (n // 2)
    out = {"dim": m, "Pi_squared_equals_q^n": ok2, "Pi_commutes_with_T": comm, "eig": {}}
    tot = 0
    for sg in (1, -1):
        W = symn.nullspace(pi_ell._scalar_minus(Pi, sg * half, S), m, S.zero, S.one)
        tot += len(W)
        info = {"dim": len(W), "charpoly_T": {}}
        Rs = {}
        for l, T in Ts.items():
            cols = [symn.solve_in_span(W, symn.mat_vec(T, w, S.zero), S.zero) for w in W]
            Rs[l] = [[cols[j][i] for j in range(len(W))] for i in range(len(W))]
            cp = symn.charpoly(Rs[l], S.zero, S.one) if W else [S.one]
            info["charpoly_T"][l] = pi_ell._intlist(cp)
            assert info["charpoly_T"][l] is not None, "non-rational char-poly"
        if W:
            C = [[sum((COEF[l] * Rs[l][i][j] for l in ELLS), S.zero) for j in range(len(W))] for i in range(len(W))]
            cC = pi_ell._intlist(symn.charpoly(C, S.zero, S.one))
        else:
            cC = [1]
        info["charpoly_C"] = cC
        out["eig"][sg] = info
    out["eigenvalues_exhaust"] = tot == m
    return out


def mf_side(q: int, k: int) -> dict:
    pari = get_pari()
    mf = pari.mfinit([q, k], 0)
    d = int(pari.mfdim(mf))
    out = {"dim": d, "eig": {}}
    half = int(Fraction(q) ** ((k - 2) // 2))
    if d:
        Uq = pari.mfheckemat(mf, q)
        Ts = {l: pari.mfheckemat(mf, l) for l in ELLS}
    tot = 0
    for sg in (1, -1):
        info = {"dim": 0, "charpoly_T": {}, "charpoly_C": [1]}
        if d:
            Kr = pari.matker(Uq - sg * half * pari.matid(d))
            dim = int(pari.matsize(Kr)[1])
            info["dim"] = dim
            tot += dim
            if dim:
                Rs = {l: pari.matinverseimage(Kr, T * Kr) for l, T in Ts.items()}
                for l, R in Rs.items():
                    info["charpoly_T"][l] = [int(c) for c in reversed(list(pari.Vec(pari.charpoly(R))))]
                C = sum((COEF[l] * Rs[l] for l in ELLS[1:]), COEF[ELLS[0]] * Rs[ELLS[0]])
                info["charpoly_C"] = [int(c) for c in reversed(list(pari.Vec(pari.charpoly(C))))]
        out["eig"][sg] = info
    out["Uq_eigenvalues_pm_only"] = tot == d
    return out


def compare(q: int, k: int) -> dict:
    b, f = brandt_side(q, k), mf_side(q, k)
    row = {"q": q, "k": k, "brandt_dim": b["dim"], "newform_dim": f["dim"],
           "Pi_squared_equals_q^n": b["Pi_squared_equals_q^n"], "Pi_commutes_with_T": b["Pi_commutes_with_T"],
           "eigenvalues_exhaust": b["eigenvalues_exhaust"] and f["Uq_eigenvalues_pm_only"],
           "eisenstein_excluded": k == 2, "orbits": []}
    n_lines = n_plus = n_minus = n_unmatched = 0
    n_forms = f["dim"]
    ok_T = True
    for sg, key in ((1, "+"), (-1, "-")):
        eb, ef = b["eig"][sg], f["eig"][sg]
        eisen = 1 if (k == 2 and sg == 1) else 0
        cpC = _div_eisenstein(_pol(eb["charpoly_C"]), k) if eisen else _pol(eb["charpoly_C"])
        # individual T_l char-polys must agree (Eisenstein factor removed)
        for l in ELLS:
            lhs = _pol(eb["charpoly_T"][l])
            if eisen:
                pari = get_pari()
                lhs = pari.divrem(lhs, pari.Pol([1, -(l + 1)]))[0]
            ok_T = ok_T and (lhs == _pol(ef["charpoly_T"].get(l, [1])))
        fb = {tuple(g): (d, m) for g, d, m in _factors(cpC)}
        mf_other = {tuple(g): (d, m) for g, d, m in _factors(_pol(f["eig"][-sg]["charpoly_C"]))}
        ff = {tuple(g): (d, m) for g, d, m in _factors(_pol(ef["charpoly_C"]))}
        for g, (d, m) in fb.items():
            lines = d * m
            n_lines += lines
            if ff.get(g) == (d, m) and g not in mf_other:
                n_plus += lines
                st = "plus"
            elif mf_other.get(g) == (d, m) and g not in ff:
                n_minus += lines
                st = "minus"
            else:
                n_unmatched += lines
                st = "unmatched_or_ambiguous"
            row["orbits"].append({"Pi_sign": key, "C_factor_const_first": list(g), "degree": d, "multiplicity": m,
                                  "eigenlines": lines, "status": st})
        # newform orbits with no Brandt partner of the same sign
        row.setdefault("mf_orbits_without_brandt_partner", []).extend(
            {"a_q_sign": key, "C_factor_const_first": list(g)} for g in ff if g not in fb)
    row.update({"eigenlines_checked": n_lines, "newforms_checked_with_dimension": n_forms,
                "n_plus": n_plus, "n_minus": n_minus, "n_unmatched": n_unmatched,
                "T_charpolys_agree_per_sign": ok_T,
                "all_plus": (n_plus == n_lines == n_forms and n_minus == 0 and n_unmatched == 0 and ok_T
                             and not row["mf_orbits_without_brandt_partner"])})
    return row


def compute_all(qs=QS, ks=KS) -> dict:
    rows = [compare(q, k) for q in qs for k in ks]
    return {
        "convention": "Pi_q-eigenvalue lambda vs a_q = U_q-eigenvalue of the matched q-new form in S_k(Gamma_0(q)); "
                      "stage-1 normalisation Pi^2 = q^{k-2} (pi_ell.py); Eisenstein line at k=2 excluded",
        "matching": "joint test operator C = T_2 + 3 T_3 + 7 T_5 on each Pi/U_q eigenspace; irreducible factors over Q of its "
                    "char-poly = Galois orbits; plus T_2,T_3,T_5 char-polys compared per eigenspace",
        "rows": rows,
        "total_eigenlines": sum(r["eigenlines_checked"] for r in rows),
        "total_newforms_with_dimension": sum(r["newform_dim"] for r in rows),
        "total_plus": sum(r["n_plus"] for r in rows),
        "total_minus": sum(r["n_minus"] for r in rows),
        "total_unmatched": sum(r["n_unmatched"] for r in rows),
        "all_plus": all(r["all_plus"] for r in rows),
    }


def main() -> None:  # pragma: no cover
    with results.Timer() as t:
        data = compute_all()
    results.write("s05/T05-1.json", data, script="code/python/langlandscape/comparison/sign.py",
                  params={"qs": list(QS), "ks": list(KS), "ells": list(ELLS), "M": 1, "C": COEF},
                  runtime_s=t.seconds, notes="T05-1 (S05-C1): FD2 sign check a_q = +lambda(Pi_q) on Brandt eigenlines")
    for r in data["rows"]:
        print(r["q"], r["k"], f"lines={r['eigenlines_checked']} forms={r['newform_dim']} plus={r['n_plus']} "
              f"minus={r['n_minus']} unmatched={r['n_unmatched']} all_plus={r['all_plus']}")
    print("TOTAL", data["total_plus"], "/", data["total_eigenlines"], "all_plus", data["all_plus"])


if __name__ == "__main__":
    main()
