"""S01-C6: the modular-forms side of the ``U_p`` comparison (``D = 3``, ``p = 5``).

For ``s in {1, 2}`` the Brandt class set ``S_s = X_B(U_1(5^s))`` of the definite quaternion algebra of
discriminant 3 corresponds (JL, ``thm:s01-JLclassical``, weight 2) to

    Q[S_s] (x) C  =  C.1 (+) (+)_chi S_2(Gamma_0(3 * 5^s), chi)^{3-new},

``chi`` running over the *even* Dirichlet characters mod ``5^s`` (viewed mod ``3 * 5^s``, trivial at 3), and
``C.1`` the line of functions factoring through ``Nrd`` (``lem:s01-nrd``).  This module computes, with PARI
(``mfinit`` flag 1 = cuspidal space, ``mfheckemat`` for ``T_5 = U_5``):

* the even characters, Conrey labels, ``chi(2)`` (2 generates ``(Z/5^s)^x``, so ``chi`` is fixed by ``chi(2)``)
  and Galois orbits (``(Z/5^s)^x`` is cyclic, so an orbit = all characters of a given order);
* ``dim S_2(3*5^s, chi)``, ``dim S_2(5^s, chi)`` and the 3-new dimension ``dim(3*5^s) - 2*dim(5^s)``
  (the 3-old space is ``S_2(5^s,chi)|B_1 (+) S_2(5^s,chi)|B_3`` and ``U_5`` commutes with ``B_3``);
* ``charpoly(U_5 | 3-new, chi) = charpoly(U_5 | S_2(3*5^s,chi)) / charpoly(U_5 | S_2(5^s,chi))^2`` over
  ``Q(chi)`` (exact division asserted), and its norm to ``Q`` (= the charpoly on the whole Galois orbit);
* ``P_s(x) = (x - 5) * prod_chi charpoly(U_5 | 3-new, chi)`` in ``Z[x]``, factored.

Conventions.  PARI writes ``Q(chi) = Q[t]/Phi_o(t)`` with ``o = ord(chi)`` and ``t = exp(2 pi i / o)``
(verified in the tests through ``T_2^2 - T_4 = 2 chi(2)``).  For exact comparisons across characters
everything is also transported to the common field ``Q(z) = Q[z]/Phi_n(z)``, ``z = exp(2 pi i / n)``, with
``n = 2`` (``s = 1``) resp. ``n = 10`` (``s = 2``) (the exponent of the group of even characters).
Polynomial coefficient lists are always in *descending* order (leading coefficient first, as PARI ``Vec``).

Normalisation remark (for phase 2).  ``chi`` and ``chi^{-1} = conj(chi)`` lie in the same Galois orbit, and
``charpoly(U_5 | S(chi^{-1})) = conj(charpoly(U_5 | S(chi)))`` (complex conjugation of ``q``-expansions); the
Petersson adjoint ``U_5^* = W U_5 W^{-1}`` on ``S(chi)`` has the charpoly of ``U_5`` on ``S(chi^{-1})``.
Hence *over Q, per Galois orbit*, the candidates "classical U_5 on chi", "on chi^{-1}", "adjoint / complex
conjugate a_5" all have the same charpoly; on the Brandt side ``U'_p`` is the adjoint of ``N_{U_p}``
(``lem:s01-Up``(d), ``M = 1``) and has the same charpoly as well.  Only per-character data over ``Q(chi)``
(via the diamond eigenspaces, :func:`compare_matrices`) can separate ``chi`` from ``chi^{-1}``, and that
separation is entangled with the diamond convention (adelic ``<d>`` = classical ``<d>^{-1}``,
``def:s01-hecke``).  The transpose (homology vs functions) does not change the per-eigenspace verdict.
The joint test with ``T_2`` (:func:`compare_matrices` with ``T2=``) removes the global adjoint ambiguity.

Phase-2 result (*computed*, :func:`brandt_comparison`, S01-C5 matrices): on the ``psi``-eigenspace of the
adelic ``<2>``, ``N_{U_p}`` has the ``a_5`` of ``S_2(3*5^s, psi^{-1})^{3-new}`` (plus 5 on the Nrd line),
jointly with ``T_2`` (s = 1, 2): ``N_{U_p}`` <-> classical ``U_5`` and adelic ``<d>`` = classical
``<d>^{-1}`` (R1 OK).  ``U'_p`` matches ``chi = psi`` alone and nothing jointly with ``T_2``: it is the
adjoint ``U_5^*``.
"""

from __future__ import annotations

import cmath
import math
from fractions import Fraction
from typing import Any

from .pari import get_pari

P = 5           #: the prime p
D = 3           #: the discriminant of B
WEIGHT = 2
EXPECTED_NEW3_SUM = {1: 1, 2: 49}       #: plan numbers (genus count, stage-01 §5 S01-C6)
EXPECTED_CLASS_SET = {1: 2, 2: 50}      #: |S_s| (S01-C2)


# ----------------------------------------------------------------------------------------------------------
# small PARI helpers
# ----------------------------------------------------------------------------------------------------------

def _gp(expr: str):
    return get_pari()(expr)


def _common_n(s: int) -> int:
    """Exponent of the group of even characters mod ``5^s`` (``2`` for s=1, ``10`` for s=2)."""
    return (P - 1) * P ** (s - 1) // 2


def _to_common(pol, o: int, n: int):
    """Transport a polynomial in x with coefficients in ``Q[t]/Phi_o`` (t = e(1/o)) to ``Q[z]/Phi_n``."""
    pari = get_pari()
    assert n % o == 0
    f = pari(f"(P, e, n) -> Pol(apply(c -> Mod(subst(lift(c), 't, 'z^e), polcyclo(n, 'z)), Vec(P)), 'x)")
    return f(pol, n // o, n)


def _coeff_strings(pol) -> list[str]:
    """Descending coefficients of ``pol`` as GP strings (polmods lifted)."""
    pari = get_pari()
    return [str(pari.lift(c)) for c in pari.Vec(pol)]


def _int_coeffs(pol) -> list[int]:
    pari = get_pari()
    out = []
    for c in pari.Vec(pol):
        c = pari.simplify(pari.lift(c))
        assert str(pari.type(c)) == "t_INT", f"non-integral coefficient {c}"
        out.append(int(c))
    return out


def _factor_string(pol) -> str:
    """Human-readable factorisation of an integer polynomial, e.g. ``(x - 5)*(x - 1)*x^4``."""
    pari = get_pari()
    F = pari.factor(pol)
    parts = []
    for i in range(int(pari.matsize(F)[0])):
        f, e = F[i, 0], int(F[i, 1])
        s = str(f)
        if pari.poldegree(f) > 1 or "+" in s[1:] or "-" in s[1:]:
            s = f"({s})"
        parts.append(s if e == 1 else f"{s}^{e}")
    return "*".join(parts) if parts else "1"


def _factor_list(pol) -> list[dict]:
    pari = get_pari()
    F = pari.factor(pol)
    return [{"factor": _int_coeffs(F[i, 0]), "factor_str": str(F[i, 0]), "mult": int(F[i, 1])}
            for i in range(int(pari.matsize(F)[0]))]


def _embed_roots(pol, o: int) -> list[list[float]]:
    """Complex roots of ``pol`` (coefficients in Q[t]/Phi_o) under t = e(1/o); sorted, rounded to 10 digits."""
    pari = get_pari()
    if pari.poldegree(pol) <= 0:
        return []
    zeta = cmath.exp(2j * math.pi / o)
    tt = pari(complex(zeta.real, zeta.imag))
    cpol = pari("(P, w) -> Pol(apply(c -> subst(lift(c), 't, w), Vec(P)), 'x)")(pol, tt)
    roots = pari.polroots(cpol)
    out = []
    for r in roots:
        re, im = float(pari.real(r)), float(pari.imag(r))
        out.append([round(re, 10) + 0.0, round(im, 10) + 0.0])
    return sorted(out)


# ----------------------------------------------------------------------------------------------------------
# characters
# ----------------------------------------------------------------------------------------------------------

def even_characters(s: int) -> list[dict]:
    """The even Dirichlet characters mod ``5^s``, as characters mod ``3*5^s`` trivial at 3.

    Each entry: ``conrey`` (label mod 5^s), ``conrey_level`` (label mod 3*5^s, the CRT lift ``= 1 mod 3``),
    ``order``, ``conductor``, ``chi2`` (``chi(2) = e(chi2)`` as a ``Fraction`` in [0,1)), ``chi2_common``
    (``chi(2)`` as a polynomial string in ``z``, ``z = e(1/n)``), ``orbit`` (orbit key ``"o<order>"``),
    ``orbit_rep`` (smallest Conrey label mod 5^s in the orbit) and ``inverse`` (Conrey label of ``chi^{-1}``).
    """
    pari = get_pari()
    q = P ** s
    N = D * q
    n = _common_n(s)
    G = pari.znstar(q, 1)
    chars = []
    for a in range(1, q):
        if a % P == 0:
            continue
        L = pari.znconreylog(G, a)
        if int(pari.zncharisodd(G, L)) != 0:
            continue
        o = int(pari.charorder(G, L))
        r = Fraction(str(pari.chareval(G, L, 2)))
        aN = int(pari.lift(pari.chinese(pari.Mod(a, q), pari.Mod(1, D))))
        inv = int(pari.lift(pari.Mod(a, q) ** -1))
        k = r * n
        assert k.denominator == 1
        chars.append({
            "conrey": a, "conrey_level": aN, "modulus": q, "level": N, "order": o,
            "conductor": int(pari.zncharconductor(G, L)), "chi2": r,
            "chi2_common": str(pari.lift(pari.Mod(pari(f"'z^{int(k)}"), pari.polcyclo(n, "z")))),
            "orbit": f"o{o}", "inverse": inv,
        })
    reps: dict[str, int] = {}
    for c in chars:
        reps[c["orbit"]] = min(reps.get(c["orbit"], c["conrey"]), c["conrey"])
    for c in chars:
        c["orbit_rep"] = reps[c["orbit"]]
    return chars


def _space(N: int, a: int):
    pari = get_pari()
    return pari.mfinit([N, WEIGHT, pari.Mod(a, N)], 1)


# ----------------------------------------------------------------------------------------------------------
# dimensions (checked before any eigenvalue data)
# ----------------------------------------------------------------------------------------------------------

def dimensions(s: int) -> dict:
    """Dimension table: per character and per Galois orbit, ``dim S_2(3*5^s,chi)``, ``dim S_2(5^s,chi)``, 3-new."""
    pari = get_pari()
    q = P ** s
    per_char = []
    for c in even_characters(s):
        dN = int(pari.mfdim(_space(D * q, c["conrey_level"])))
        dq = int(pari.mfdim(_space(q, c["conrey"])))
        per_char.append({"conrey": c["conrey"], "conrey_level": c["conrey_level"], "orbit": c["orbit"],
                         "dim_level": dN, "dim_5power": dq, "dim_3new": dN - 2 * dq})
    orbits: dict[str, dict] = {}
    for r in per_char:
        o = orbits.setdefault(r["orbit"], {"n_chars": 0, "dim_level": 0, "dim_5power": 0, "dim_3new": 0})
        o["n_chars"] += 1
        for key in ("dim_level", "dim_5power", "dim_3new"):
            o[key] += r[key]
    total = sum(r["dim_3new"] for r in per_char)
    return {"per_char": per_char, "per_orbit": orbits, "sum_3new": total,
            "nrd_line": 1, "brandt_dim_predicted": 1 + total}


def check_dimensions(s: int) -> dict:
    """Assert ``sum_chi dim S_2(3*5^s, chi)^{3-new}`` against the plan (1 resp. 49) and return the table."""
    dims = dimensions(s)
    for r in dims["per_char"]:
        assert r["dim_3new"] >= 0, r
    assert dims["sum_3new"] == EXPECTED_NEW3_SUM[s], (
        f"PARI: sum of 3-new dims at level {D * P ** s} is {dims['sum_3new']}, plan says {EXPECTED_NEW3_SUM[s]}")
    assert dims["brandt_dim_predicted"] == EXPECTED_CLASS_SET[s]
    return dims


# ----------------------------------------------------------------------------------------------------------
# U_5 on the 3-new part
# ----------------------------------------------------------------------------------------------------------

def _charpoly_U5(N: int, a: int):
    """``(dim, charpoly)`` of ``U_5 = T_5`` on ``S_2(N, Mod(a,N))`` over ``Q(chi)`` (variable x)."""
    pari = get_pari()
    mf = _space(N, a)
    d = int(pari.mfdim(mf))
    if d == 0:
        return 0, pari("1 + 0*'x"), None
    M = pari.mfheckemat(mf, P)
    return d, pari.charpoly(M), M


JOINT_C = 7   #: the "joint" test operator is T_2 + JOINT_C * U_5 (separates the (a_2, a_5) pairs)


def _charpoly_combo(N: int, a: int, alpha: int, beta: int):
    """Charpoly over ``Q(chi)`` of ``alpha*T_2 + beta*U_5`` on ``S_2(N, Mod(a,N))``."""
    pari = get_pari()
    mf = _space(N, a)
    if int(pari.mfdim(mf)) == 0:
        return pari("1 + 0*'x")
    return pari.charpoly(alpha * pari.mfheckemat(mf, 2) + beta * pari.mfheckemat(mf, P))


def _divexact(A, B):
    pari = get_pari()
    qr = pari.divrem(A, B)
    rem = pari.simplify(pari.lift(qr[1]))
    assert rem == 0, f"non-exact division: remainder {rem}"
    return qr[0]


def _norm_to_Q(pol, o: int):
    """``N_{Q(chi)/Q}`` of a polynomial in x over ``Q[t]/Phi_o`` (= product over the Galois orbit)."""
    pari = get_pari()
    if o <= 2:
        return pari.simplify(pari.lift(pol))
    return pari("(P, o) -> polresultant(polcyclo(o, 't), liftall(P), 't)")(pol, o)


def _conj(pol, o: int):
    """Complex conjugate (t -> t^{-1}) of a polynomial over ``Q[t]/Phi_o``."""
    pari = get_pari()
    if o <= 2:
        return pol
    return pari("(P, o) -> Pol(apply(c -> Mod(subst(lift(c), 't, 't^(o-1)), polcyclo(o, 't)), Vec(P)), 'x)")(pol, o)


def _poleq(A, B) -> bool:
    pari = get_pari()
    return pari.simplify(pari.liftall(A - B)) == 0


def mf_side(s: int) -> dict:
    """The full modular-forms side for ``s``: dimensions, per-character and per-orbit charpolys, ``P_s``.

    Dimension checks are asserted first (:func:`check_dimensions`).  Returned keys:

    * ``dimensions``: see :func:`dimensions`;
    * ``per_char``: list, one per even ``chi``: Conrey labels, ``chi(2)``, the charpolys of ``U_5`` on
      ``S_2(3*5^s,chi)``, on ``S_2(5^s,chi)`` and on the 3-new part over ``Q(chi)`` (``Q[t]/Phi_o``, strings
      of descending coefficients) and over the common field ``Q(z)``; the ``a_5`` multiset of the 3-new part
      under ``t = e(1/o)`` (list of ``[re, im]``), and ``charpoly_3new_inverse_common`` = the charpoly for
      ``chi^{-1}`` (checked to be the complex conjugate);
    * ``per_orbit``: dict keyed ``"o<order>"``: ``charpoly_3new_Q`` (integer coefficients, descending), its
      factorisation, its degree, and ``with_nrd`` (times ``(x-5)``, for the trivial orbit only);
    * ``P_s``: integer coefficients of ``(x-5) * prod_chi charpoly(U_5 | 3-new, chi)``, ``P_s_factored``,
      ``P_s_inverse_equal`` (the same with chi -> chi^{-1}: always equal over Q, asserted),
      ``a5_multiset`` (all roots with multiplicity, complex, incl. the Nrd eigenvalue 5).
    """
    pari = get_pari()
    dims = check_dimensions(s)
    q = P ** s
    n = _common_n(s)
    chars = even_characters(s)
    by_label = {c["conrey"]: c for c in chars}
    per_char = []
    new3_K = {}
    for c in chars:
        o = c["order"]
        dN, PN, MN = _charpoly_U5(D * q, c["conrey_level"])
        dq, Pq, _ = _charpoly_U5(q, c["conrey"])
        Pnew = _divexact(PN, Pq ** 2)
        assert int(pari.poldegree(Pnew)) == dN - 2 * dq
        new3_K[c["conrey"]] = Pnew
        entry = dict(c)
        entry.update({
            "field_poly_t": str(pari.polcyclo(o, "t")),
            "dim_level": dN, "dim_5power": dq, "dim_3new": dN - 2 * dq,
            "charpoly_level_K": _coeff_strings(PN),
            "charpoly_5power_K": _coeff_strings(Pq),
            "charpoly_3new_K": _coeff_strings(Pnew),
            "charpoly_3new_common": _coeff_strings(_to_common(Pnew, o, n)),
            "a5_3new": _embed_roots(Pnew, o),
            "U5_matrix_level_K": str(MN) if MN is not None else None,
        })
        # T_2 and T_2 + 7 U_5 on the 3-new part (2 is prime to the level, T_2 commutes with B_3)
        entry["charpoly_3new_ops_common"] = {"U5": entry["charpoly_3new_common"]}
        for name, (al, be) in (("T2", (1, 0)), (f"T2+{JOINT_C}U5", (1, JOINT_C))):
            Pc = _divexact(_charpoly_combo(D * q, c["conrey_level"], al, be),
                           _charpoly_combo(q, c["conrey"], al, be) ** 2)
            entry["charpoly_3new_ops_common"][name] = _coeff_strings(_to_common(Pc, o, n))
        per_char.append(entry)
    for e in per_char:
        o = e["order"]
        Pinv = new3_K[e["inverse"]]
        assert _poleq(Pinv, _conj(new3_K[e["conrey"]], o)), "U_5 on chi^{-1} is not the conjugate"
        e["charpoly_3new_inverse_common"] = _coeff_strings(_to_common(Pinv, o, n))
    per_orbit = {}
    total = pari("'x - 5")
    total_inv = pari("'x - 5")
    seen = set()
    for c in chars:
        o = c["order"]
        if c["orbit"] in seen:
            continue
        seen.add(c["orbit"])
        Nq = _norm_to_Q(new3_K[c["conrey"]], o)
        # product over the orbit computed directly as a check of the norm
        prod = pari("1 + 0*'x")
        prod_inv = pari("1 + 0*'x")
        for c2 in chars:
            if c2["orbit"] == c["orbit"]:
                prod = prod * _to_common(new3_K[c2["conrey"]], o, n)
                prod_inv = prod_inv * _to_common(new3_K[c2["inverse"]], o, n)
        assert _poleq(pari.liftall(prod), Nq) and _poleq(pari.liftall(prod_inv), Nq)
        Nq = pari.simplify(pari.liftall(prod))
        total = total * Nq
        total_inv = total_inv * pari.simplify(pari.liftall(prod_inv))
        rec = {
            "orbit_rep": c["orbit_rep"], "order": o, "conductor": c["conductor"],
            "members": sorted(c2["conrey"] for c2 in chars if c2["orbit"] == c["orbit"]),
            "dim_3new": int(pari.poldegree(Nq)),
            "charpoly_3new_Q": _int_coeffs(Nq),
            "charpoly_3new_Q_factored": _factor_string(Nq),
        }
        if o == 1:
            W = pari("'x - 5") * Nq
            rec["with_nrd"] = _int_coeffs(W)
            rec["with_nrd_factored"] = _factor_string(W)
        per_orbit[c["orbit"]] = rec
    assert _poleq(total, total_inv)
    assert int(pari.poldegree(total)) == EXPECTED_CLASS_SET[s]
    roots = [[5.0, 0.0]]
    for e in per_char:
        roots += e["a5_3new"]
    return {
        "s": s, "level": D * q, "p": P, "D": D, "weight": WEIGHT,
        "common_field": {"n": n, "poly_z": str(pari.polcyclo(n, "z")), "z": f"exp(2*pi*i/{n})"},
        "dimensions": dims,
        "per_char": per_char,
        "per_orbit": per_orbit,
        "P_s": _int_coeffs(total),
        "P_s_factored": _factor_string(total),
        "P_s_factors": _factor_list(total),
        "P_s_inverse_equal": True,
        "a5_multiset": sorted(roots),
        "trace_powers": [int(pari.simplify(pari.lift(sum_pow))) for sum_pow in _power_sums(total, 6)],
    }


def _power_sums(pol, m: int):
    """Newton power sums ``tr U^1..U^m`` of the roots of an integer polynomial."""
    pari = get_pari()
    ps = pari("(P, m) -> my(v = polsym(P, m)); vector(m, i, v[i+1])")(pol, m)
    return list(ps)


# ----------------------------------------------------------------------------------------------------------
# comparison with the Brandt side (phase 2)
# ----------------------------------------------------------------------------------------------------------

def _orbit_key(key, s: int, chars: list[dict]) -> str:
    """Resolve a user key to an orbit key ``"o<order>"``.

    Accepted: ``"o<order>"``; ``"total"``; an int Conrey label (mod 5^s or mod 3*5^s); a ``chi(2)`` value
    given as ``Fraction``/``"k/m"`` string (``chi(2) = e(k/m)``) or ``-1``/``1``-type int via ``("chi2", v)``;
    or a complex number ``chi(2)``.
    """
    if isinstance(key, str):
        if key == "total" or key.startswith("o"):
            return key
        key = Fraction(key)
    if isinstance(key, tuple) and key[0] == "chi2":
        v = key[1]
        key = complex(v) if not isinstance(v, Fraction) else v
    if isinstance(key, bool):
        raise KeyError(key)
    if isinstance(key, int):
        for c in chars:
            if key in (c["conrey"], c["conrey_level"]):
                return c["orbit"]
        raise KeyError(f"{key} is not the Conrey label of an even character mod {P ** s} / {D * P ** s}")
    if isinstance(key, Fraction):
        for c in chars:
            if Fraction(key) % 1 == c["chi2"]:
                return c["orbit"]
        raise KeyError(key)
    if isinstance(key, complex) or isinstance(key, float):
        z = complex(key)
        for c in chars:
            w = cmath.exp(2j * math.pi * float(c["chi2"]))
            if abs(z - w) < 1e-9:
                return c["orbit"]
        raise KeyError(key)
    raise KeyError(key)


def compare(charpoly_brandt_by_orbit: dict, s: int, mf: dict | None = None) -> dict:
    """Compare Brandt-side charpolys (over Q, per diamond-character orbit) with the modular-forms side.

    ``charpoly_brandt_by_orbit`` maps an orbit key (see :func:`_orbit_key`: ``"o<order>"``, a Conrey label
    of any member, ``chi(2)`` as ``Fraction`` / ``"k/m"`` / complex, or ``"total"``) to the integer
    coefficient list (descending) of the Brandt operator's charpoly on the ``Q``-isotypic piece of
    ``Q[S_s]`` for that orbit of diamond characters.  For each key the candidates tested are:

    * ``"Up_3new"``: ``charpoly(U_5 | 3-new)`` of the orbit;
    * ``"Up_3new_times_(x-5)"``: the same times ``(x-5)`` (the Nrd/degree line; belongs to the trivial orbit);
    * ``"Up_3new_times_(x-1)"``: times ``(x-1)`` (if the Nrd line were acted on by 1);
    * ``"Up_3new_inverse_char"`` / ``"adjoint_conjugate"``: ``chi -> chi^{-1}`` resp. ``a_5 -> conj(a_5)``;
      over Q these coincide with ``"Up_3new"`` (same orbit), recorded so the report says so explicitly;
    * for ``"total"``: ``P_s`` and ``P_s`` with ``(x-5)`` replaced by ``(x-1)``.

    Returns ``{"per_key": {key: {"orbit": ..., "matches": [...], "brandt": coeffs}}, "all_match": bool,
    "matching_normalisation": str | None, "note": ...}``.  Orbit-level data cannot distinguish
    ``N_{U_p}`` from its adjoint ``U'_p`` nor ``chi`` from ``chi^{-1}``; use :func:`compare_matrices` for that.
    """
    pari = get_pari()
    mf = mf if mf is not None else mf_side(s)
    chars = even_characters(s)

    def pol(coeffs):
        return pari.Pol([pari(int(c)) for c in coeffs], "x")

    per_key = {}
    for key, coeffs in charpoly_brandt_by_orbit.items():
        okey = _orbit_key(key, s, chars)
        B = pol(coeffs)
        cands = {}
        if okey == "total":
            T = pol(mf["P_s"])
            cands["P_s"] = T
            cands["P_s_nrd_eigenvalue_1"] = _divexact(T, pari("'x-5")) * pari("'x-1")
        else:
            A = pol(mf["per_orbit"][okey]["charpoly_3new_Q"])
            cands["Up_3new"] = A
            cands["Up_3new_inverse_char"] = A
            cands["adjoint_conjugate"] = A
            cands["Up_3new_times_(x-5)"] = A * pari("'x-5")
            cands["Up_3new_times_(x-1)"] = A * pari("'x-1")
        matches = [name for name, C in cands.items() if _poleq(B, C)]
        per_key[str(key)] = {"orbit": okey, "brandt": [int(c) for c in coeffs],
                             "brandt_factored": _factor_string(B), "matches": matches}
    all_match = all(v["matches"] for v in per_key.values())
    common = None
    if all_match:
        sets = [set(v["matches"]) for v in per_key.values()]
        # normalise to the names relevant per orbit
        if all(("Up_3new" in m) or ("Up_3new_times_(x-5)" in m) or ("P_s" in m) for m in sets):
            common = "N_Up <-> classical U_5 (a_5), Nrd line eigenvalue 5"
        elif all(("Up_3new_times_(x-1)" in m) or ("P_s_nrd_eigenvalue_1" in m) or ("Up_3new" in m) for m in sets):
            common = "classical U_5 (a_5), Nrd line eigenvalue 1"
    return {"s": s, "per_key": per_key, "all_match": all_match, "matching_normalisation": common,
            "note": "over Q, per orbit: U_p, U'_p (adjoint), chi vs chi^{-1} are indistinguishable"}


def _brandt_char_charpoly(U, Dm, val, n: int):
    """Charpoly over ``Q(z)`` of ``U`` restricted to ``ker(Dm - val)`` (``val`` in ``Q[z]/Phi_n``)."""
    pari = get_pari()
    f = pari("""(U, Dm, v, n) -> my(Phi = polcyclo(n, 'z), m = #U, A, K, C);
        A = Mod(1, Phi) * Dm - v * matid(m);
        K = matker(A);
        if (#K == 0, return(Pol(Mod(1, Phi), 'x)));
        C = matinverseimage(K, Mod(1, Phi) * U * K);
        charpoly(C, 'x)""")
    return f(U, Dm, val, n)


def _intmat(M):
    pari = get_pari()
    if isinstance(M, list) or hasattr(M, "tolist"):
        M = M.tolist() if hasattr(M, "tolist") else M
        return pari.matrix(len(M), len(M[0]), [int(x) for row in M for x in row])
    return M


def compare_matrices(U, diamond2, s: int, mf: dict | None = None, T2=None) -> dict:
    """Per-character comparison from integer matrices on ``Q[S_s]``.

    ``U``: the integer matrix of the Brandt operator (``N_{U_p}`` or ``U'_p``), ``diamond2``: the integer
    matrix of the Brandt diamond ``<2>`` (any convention; 2 generates ``(Z/5^s)^x``), optionally ``T2``
    (the Brandt ``T_2``), all as lists of rows / numpy arrays / PARI matrices in the same basis.  For every
    even ``psi`` the charpoly of ``U`` on the eigenspace ``ker(<2> - psi(2))`` is computed over ``Q(z)`` and
    compared with

    * ``"same"``: ``charpoly(U_5 | 3-new, chi = psi)`` (times ``(x-5)`` for ``psi = 1``: the Nrd line);
    * ``"inverse"``: the same for ``chi = psi^{-1}``.

    With ``T2`` given, the same is done for ``T_2`` alone (Nrd eigenvalue 3) and for the joint operator
    ``T_2 + 7 U`` versus classical ``T_2 + 7 U_5`` (Nrd eigenvalue 38), which tests the *pairs*
    ``(a_2, a_5)``, i.e. whether ``U`` matches ``U_5`` relative to ``T_2`` and not only up to an adjoint.

    For ``U`` alone, the charpoly on the ``psi``-eigenspace of homological ``<2>`` equals that of the
    transposed (function-side) operator on the ``psi``-eigenspace of the transposed ``<2>``, so homology
    and functions give the same verdict.  Returns per-``psi`` match lists and ``consistent`` /
    ``consistent_T2`` / ``consistent_joint`` in ``{"same", "inverse", "both", None}``.
    """
    pari = get_pari()
    mf = mf if mf is not None else mf_side(s)
    n = mf["common_field"]["n"]
    Um, Dm = _intmat(U), _intmat(diamond2)
    ops = {"U5": (Um, 5)}
    if T2 is not None:
        Tm = _intmat(T2)
        ops["T2"] = (Tm, 3)
        ops[f"T2+{JOINT_C}U5"] = (Tm + JOINT_C * Um, 3 + JOINT_C * 5)
    Phi = pari.polcyclo(n, "z")
    by_label = {e["conrey"]: e for e in mf["per_char"]}

    def common_pol(strings):
        return pari.Pol([pari.Mod(pari(c), Phi) for c in strings], "x")

    per_psi = []
    total_dim = 0
    for e in mf["per_char"]:
        val = pari.Mod(pari(e["chi2_common"]), Phi)
        row = {"conrey": e["conrey"], "chi2": e["chi2"]}
        for name, (X, nrd) in ops.items():
            B = _brandt_char_charpoly(X, Dm, val, n)
            if name == "U5":
                row["eigenspace_dim"] = int(pari.poldegree(B))
                total_dim += row["eigenspace_dim"]
            same = common_pol(e["charpoly_3new_ops_common"][name])
            inv = common_pol(by_label[e["inverse"]]["charpoly_3new_ops_common"][name])
            if e["order"] == 1:
                same = same * pari(f"'x - {nrd}")
                inv = inv * pari(f"'x - {nrd}")
            m = [lab for lab, C in (("same", same), ("inverse", inv)) if _poleq(B, C)]
            key = "matches" if name == "U5" else f"matches_{name}"
            row[key] = m
            row[("brandt_charpoly_common" if name == "U5" else f"brandt_charpoly_{name}_common")] = _coeff_strings(B)
        per_psi.append(row)
    assert total_dim == int(pari.matsize(Um)[0]), "diamond <2> eigenspaces do not span (wrong character set?)"

    def verdict(key):
        ok_same = all("same" in r[key] for r in per_psi)
        ok_inv = all("inverse" in r[key] for r in per_psi)
        return "both" if ok_same and ok_inv else "same" if ok_same else "inverse" if ok_inv else None

    total = pari.charpoly(Um, "x")
    out = {"s": s, "per_psi": per_psi, "consistent": verdict("matches"),
           "total_charpoly_matches_P_s": _poleq(total, pari.Pol([pari(c) for c in mf["P_s"]], "x")),
           "total_charpoly_factored": _factor_string(total)}
    if T2 is not None:
        out["consistent_T2"] = verdict("matches_T2")
        out["consistent_joint"] = verdict(f"matches_T2+{JOINT_C}U5")
    return out


EXPECTED_CONVENTION = "inverse"   #: plan: N_{U_p} <-> classical U_5, adelic <d> = classical <d>^{-1}


def brandt_comparison(s: int, mf: dict | None = None) -> dict:
    """Phase 2: compare the S01-C5 Brandt operators (``langlandscape.up``) with the modular-forms side.

    Uses the homological integer matrices of ``N_{U_p}``, ``U'_p``, adelic ``<2>`` and ``T_2`` on
    ``Q[S_s]`` from :func:`langlandscape.up.context`.  Reports, for ``N_{U_p}`` and for ``U'_p``: whether the
    total charpoly is ``P_s``, and per ``<2>``-eigenspace whether the eigenvalues match the ``a_5`` of
    ``S_2(3*5^s, chi)^{3-new}`` with ``chi = psi`` (``"same"``) or ``chi = psi^{-1}`` (``"inverse"``), alone
    and jointly with ``T_2``.  ``R1_ok`` is the plan's expectation: ``N_{U_p}`` matches classical ``U_5``
    jointly with ``T_2`` under ``"inverse"`` (``rem:s01-Upconv``, ``def:s01-hecke``).
    """
    from . import up

    mf = mf if mf is not None else mf_side(s)
    C = up.context(max(2, s))
    D2, T2 = C.diamond(s, 2), C.T2(s)
    res = {}
    for name, X in (("N_Up", C.Up(s)), ("Up_prime", C.Up_prime(s))):
        res[name] = compare_matrices(X, D2, s, mf=mf, T2=T2)
    nu = res["N_Up"]
    contains = lambda v: v in (EXPECTED_CONVENTION, "both")  # noqa: E731
    r1 = bool(nu["total_charpoly_matches_P_s"] and contains(nu["consistent"])
              and contains(nu["consistent_T2"]) and contains(nu["consistent_joint"]))
    table = {str(r["conrey"]): {"chi2": str(r["chi2"]), "dim": r["eigenspace_dim"],
                                "N_Up": r["matches"], "N_Up_joint_T2": r[f"matches_T2+{JOINT_C}U5"],
                                "T2": r["matches_T2"],
                                "Up_prime": rp["matches"], "Up_prime_joint_T2": rp[f"matches_T2+{JOINT_C}U5"]}
             for r, rp in zip(nu["per_psi"], res["Up_prime"]["per_psi"])}
    return {"s": s, "R1_ok": r1, "expected_convention": EXPECTED_CONVENTION,
            "convention_meaning": {
                "same": "Brandt <2>-eigenvalue psi(2) (homological, adelic <d>) <-> classical character chi = psi",
                "inverse": "... <-> classical chi = psi^{-1} (adelic <d> = classical <d>^{-1})"},
            "table": table, "details": res}


# ----------------------------------------------------------------------------------------------------------
# result file
# ----------------------------------------------------------------------------------------------------------

def main() -> None:  # pragma: no cover - script entry point
    from . import results
    data = {}
    with results.Timer() as tm:
        for s in (1, 2):
            data[f"s{s}"] = mf_side(s)
            data[f"s{s}"]["brandt_comparison"] = brandt_comparison(s, mf=data[f"s{s}"])
    results.write("s01/up_mf.json", data, script="code/python/langlandscape/up_mf.py",
                  params={"D": D, "p": P, "weight": WEIGHT, "s": [1, 2], "mfinit_flag": 1},
                  runtime_s=round(tm.seconds, 3),
                  notes="S01-C6: modular-forms side (U_5 on the 3-new part of S_2(3*5^s, chi), chi even "
                        "mod 5^s) and its comparison with the S01-C5 Brandt matrices (key brandt_comparison). PARI t = exp(2 pi i/ord chi); common field z = exp(2 pi i/n). Coefficients "
                        "descending.")


if __name__ == "__main__":  # pragma: no cover
    main()
