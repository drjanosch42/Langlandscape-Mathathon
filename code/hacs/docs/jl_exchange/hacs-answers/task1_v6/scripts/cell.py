# SPDX-License-Identifier: CC-BY-4.0
"""One cell (p, k) of Task 1.  Usage: cell.py p k [ell ...] [--q 2,3,5,7] [--out file.json]
Level 1 is exact over Q; level p is computed mod l^E (Q = l^E < 2^25) for each requested / candidate l."""
import sys, json, time, math
from fractions import Fraction
import numpy as np
import sympy
import amalgam as A
from amalgam import mm, rho, mat_vec, vadd, vsub, vscale, Cocycle1, cocycle_to_rep, Level, FastLevel, S, U, I2

def args():
    a = sys.argv[1:]; p, k = int(a[0]), int(a[1]); ells = []; qs = None; out = None; i = 2
    while i < len(a):
        if a[i] == '--q': qs = [int(x) for x in a[i+1].split(',')]; i += 2
        elif a[i] == '--out': out = a[i+1]; i += 2
        else: ells.append(int(a[i])); i += 1
    return p, k, ells, qs, out

def main():
    t0 = time.time()
    p, k, ells_req, qs, outf = args(); n = k - 2; d = n + 1; g = (1, 0, 0, p); gp = (p, 0, 0, 1)
    assert n % 2 == 0 and n >= 2
    if qs is None: qs = [q for q in [2, 3, 5, 7, 11, 13] if q != p][:5]
    res = {"p": p, "k": k, "n": n, "q_list": qs}
    # ---------------- level 1 over Q
    RS, RU = np.array(rho(S, n), dtype=object), np.array(rho(U, n), dtype=object)
    Rows1 = A.relation_rows(n, RS, RU, d)
    piv1, np1, proj1 = A.quotient_basis_Q(Rows1)
    r1 = len(np1); res["rank_H1_SL2Z"] = r1
    basis1 = []
    for c in np1:
        v = [0]*d; v[c] = 1; basis1.append(v)
    def cv(v):  # the cocycle c_v: c(S) = 0, c(U) = (U-1)v
        return Cocycle1(n, [0]*d, vsub(mat_vec(rho(U, n), v), v))
    L = Level(p, n)
    # X = omega o dg_p  and  T_q (level 1), exact
    def classV_of(cfun): return proj1(cocycle_to_rep(n, cfun, None, [Fraction(0)]*d))
    X = []; Tq1 = {q: [] for q in qs + [p]}; Y = []; Wcheck = []; dg1check = []
    for v in basis1:
        c = cv(v)
        z = lambda h, c=c: mat_vec(rho(g, n), c((h[0], h[1]*p, h[2]//p, h[3])))   # dg_p(c_v)(h)
        mrep = L.shapiro_forward(z)
        X.append(proj1(L.omega(mrep)))
        # dg_1 two ways at module level: omega(iota v) = (p+1) v
        dg1check.append(proj1(L.omega(L.iota(v))) == proj1([(p+1)*x for x in v]))
        for q in Tq1:
            Tz = A.hecke_cocycle(c, q, n, lambda Y_: True)
            Tq1[q].append(classV_of(Tz))
        # Y = omega' o dg_1 with omega' = kappa^{-1} o cor^{G_2}_{Gamma_0(p)} (independent route)
        uts = [mm(S, s) for s in L.reps]
        def idx(gam): return L.cls(mm(A.Sinv, gam))
        def Ycoc(gam, c=c):
            acc = [Fraction(0)]*d
            for t, ut in enumerate(uts):
                tp = idx(mm(ut, gam))
                inner = mm(mm(ut, gam), A.inv1(uts[tp]))           # in Gamma^0(p)
                h = (inner[0], inner[1]//p, inner[2]*p, inner[3])  # g inner g^{-1} in Gamma_0(p)
                assert inner[1] % p == 0
                acc = vadd(acc, mat_vec(rho(mm(A.inv1(ut), gp), n), c(h)))
            return [x / Fraction(p**n) for x in acc]
        Y.append(classV_of(Ycoc))
        # omega' o dg_p = p+1 (sanity of the cor^{G_2} formula)
        def Wcoc(gam, c=c):
            acc = [Fraction(0)]*d
            for t, ut in enumerate(uts):
                tp = idx(mm(ut, gam))
                inner = mm(mm(ut, gam), A.inv1(uts[tp]))
                hh = (inner[0], inner[1]//p, inner[2]*p, inner[3])
                zz = mat_vec(rho(g, n), c((hh[0], hh[1]*p, hh[2]//p, hh[3])))   # dg_p(c_v)(hh)
                acc = vadd(acc, mat_vec(rho(mm(A.inv1(ut), gp), n), zz))
            return [x / Fraction(p**n) for x in acc]
        Wcheck.append(classV_of(Wcoc))
    Xm = sympy.Matrix(X).T; Ym = sympy.Matrix(Y).T
    Tp1 = sympy.Matrix(Tq1[p]).T
    res["check_X_equals_Tp_level1"] = bool(Xm == Tp1)
    res["check_Y_equals_p^-n_X"] = bool(Ym == Xm / sympy.Integer(p)**n)
    res["check_omega'_dg_p_equals_p+1"] = bool(sympy.Matrix(Wcheck).T == (p+1)*sympy.eye(r1))
    res["check_omega_dg_1_equals_p+1"] = all(dg1check)
    x = sympy.symbols('x')
    res["charpoly_Tq_H1_SL2Z"] = {str(q): str(sympy.factor(sympy.Matrix(Tq1[q]).T.charpoly(x).as_expr())) for q in Tq1}
    res["level1_T_matrices"] = {str(q): [[str(e) for e in row] for row in sympy.Matrix(Tq1[q]).T.tolist()] for q in Tq1}
    I = sympy.eye(r1)
    AA = sympy.BlockMatrix([[(p+1)*I, -Xm], [-Ym, (p+1)*I]]).as_explicit()
    detAA = AA.det()
    res["alpha*alpha"] = [[str(e) for e in row] for row in AA.tolist()]
    res["det_alpha*alpha"] = str(detAA)
    num = sympy.Rational(detAA).p
    fac = sympy.factorint(abs(num)) if num != 0 else {}
    res["det_alpha*alpha_num_factored"] = {str(a): b for a, b in sorted(fac.items())}
    cand = sorted(int(l) for l in fac if l > k and l != p)
    res["candidate_ells"] = cand
    # expected: det = prod over T_p-eigenvalues lambda (each twice? no: once per H^1 eigenline) of ((p+1)^2 - p^{-n} lambda^2)
    res["det_formula_check"] = None
    lam_poly = Tp1.charpoly(x).as_expr()
    # ---------------- level p mod l^E
    res["ell"] = {}
    for ell in sorted(set(ells_req) | set(cand)):
        if ell <= 3 or ell == p: continue
        E = max(2, int(math.floor(25 / math.log2(ell)))); Q = ell**E
        e = {"E": E, "modulus": f"{ell}^{E}"}
        t1 = time.time()
        MS, MU = L.Mmat(S), L.Mmat(U)
        Rows = A.relation_rows(n, MS, MU, L.D)
        piv, nonpiv, P = A.quotient_basis(Rows, Q, ell)
        r = len(nonpiv); e["rank_H1_Gamma0p"] = r
        RowsV = A.relation_rows(n, RS, RU, d)
        pivV, npV, PV = A.quotient_basis(RowsV, Q, ell)
        assert len(npV) == r1
        cols = []
        for c in npV:
            v = [0]*d; v[c] = 1
            col1 = [int(x) % Q for x in P.dot(np.array(L.iota(v), dtype=object))]
            cc = cv(v)
            z = lambda h, cc=cc: mat_vec(rho(g, n), cc((h[0], h[1]*p, h[2]//p, h[3])))
            m2 = [A.to_mod(x, Q) for x in L.shapiro_forward(z)]
            col2 = [int(x) % Q for x in P.dot(np.array(m2, dtype=object))]
            # cross-check res two ways: shapiro_forward(c_v|Gamma_0(p)) == iota(v) in H^1
            m1 = [A.to_mod(x, Q) for x in L.shapiro_forward(lambda h, cc=cc: cc(h))]
            assert [int(x) % Q for x in P.dot(np.array(m1, dtype=object))] == col1
            cols.append((col1, col2))
        alpha = [[c[0][i] for c in cols] + [(-c[1][i]) % Q for c in cols] for i in range(r)]
        vals = A.smith_vals(alpha, Q, ell, E)
        e["basis_H1_Gamma0p_coords"] = nonpiv   # Z_(l)-basis of H^1(Gamma,M): classes of e_c, c in this list (index j*(n+1)+t)
        e["basis_H1_SL2Z_coords"] = npV
        e["alpha_mod_l^E"] = alpha              # columns: dg_1(e_c) (c in npV), then -dg_p(e_c)
        e["alpha_elementary_divisor_valuations"] = vals
        e["coker_alpha_free_rank"] = r - sum(1 for v in vals if v < E) if all(v < E for v in vals) else None
        e["coker_alpha_torsion"] = [f"Z/{ell}^{v}" if v > 1 else f"Z/{ell}" for v in vals if 0 < v < E]
        e["alpha_injective_mod_l^E"] = all(v < E for v in vals)
        # alpha* alpha over Z_(l)
        AAm = [[A.to_mod(Fraction(str(x)), Q) for x in row] for row in AA.tolist()]
        e["alpha*alpha_elementary_divisor_valuations"] = A.smith_vals(AAm, Q, ell, E)
        # Hecke on level p (mod Q) and equivariance
        FL = FastLevel(L, Q, nonpiv) if Q < 2**25 else None
        Pnp = np.array([[int(x) % Q for x in row] for row in P], dtype=np.int64) if FL is not None else None
        Tm = {}; e["charpoly_mod_l_Tq_H1_Gamma0p"] = {}; e["equivariance_T_alpha"] = {}
        for q in qs:
            if q == p: continue
            Tq = FL.hecke(q, Pnp) if FL is not None else None; Tm[q] = Tq
            if Tq is not None: e["charpoly_mod_l_Tq_H1_Gamma0p"][str(q)] = A.charpoly_mod(Tq.tolist(), ell)
            # T_q on H^1(SL2Z) in the Z_(l) basis npV: transport the exact Q-basis matrices
            # (level-1 class of e_c computed exactly then projected by PV)
            T1 = []
            for c in npV:
                v = [0]*d; v[c] = 1
                Tz = A.hecke_cocycle(cv(v), q, n, lambda Y_: True)
                rep = cocycle_to_rep(n, Tz, None, [Fraction(0)]*d)
                T1.append([int(x) % Q for x in PV.dot(np.array([A.to_mod(y, Q) for y in rep], dtype=object))])
            T1 = np.array(T1, dtype=object).T
            Al = np.array(alpha, dtype=object)
            if Tq is None:
                e["equivariance_T_alpha"][str(q)] = "skipped (l^E >= 2^25: level-p Hecke not run)"
                e.setdefault("T1_charpoly_mod_l", {})[str(q)] = A.charpoly_mod(T1.tolist(), ell)
                e.setdefault("_T1", {})[q] = T1
                continue
            lhs = Tq.astype(object).dot(Al) % Q
            blk = np.zeros((2*r1, 2*r1), dtype=object); blk[:r1, :r1] = T1; blk[r1:, r1:] = T1
            rhs = Al.dot(blk) % Q
            e["equivariance_T_alpha"][str(q)] = bool((lhs == rhs).all())
            e.setdefault("T1_charpoly_mod_l", {})[str(q)] = A.charpoly_mod(T1.tolist(), ell)
            # eigenvalue of T_q (level 1, diagonal) on ker(alpha mod l)
            e.setdefault("_T1", {})[q] = T1
        # kernel of alpha mod l -> maximal ideal of the torsion / of the level-raising
        kerv = nullspace_mod(alpha, ell)
        e["dim_ker_alpha_mod_l"] = len(kerv)
        eig = {}
        for q in Tm:
            T1 = e["_T1"][q]
            blk = np.zeros((2*r1, 2*r1), dtype=object); blk[:r1, :r1] = T1; blk[r1:, r1:] = T1
            lam = []
            for v in kerv:
                w = [int(x) % ell for x in blk.dot(np.array(v, dtype=object))]
                i0 = next(i for i, x in enumerate(v) if x % ell)
                lm = w[i0] * pow(v[i0], -1, ell) % ell
                lam.append(lm if all((w[i] - lm*v[i]) % ell == 0 for i in range(len(v))) else None)
            eig[str(q)] = lam
        e["T_q_on_ker_alpha_mod_l"] = eig
        e["eisenstein_value_1+q^(k-1)_mod_l"] = {str(q): (1 + pow(q, k-1, ell)) % ell for q in Tm}
        # same for the kernel of alpha*alpha mod l
        kerAA = nullspace_mod(AAm, ell)
        e["dim_ker_alpha*alpha_mod_l"] = len(kerAA)
        eig2 = {}
        for q in Tm:
            T1 = e["_T1"][q]
            blk = np.zeros((2*r1, 2*r1), dtype=object); blk[:r1, :r1] = T1; blk[r1:, r1:] = T1
            lam = []
            for v in kerAA:
                w = [int(x) % ell for x in blk.dot(np.array(v, dtype=object))]
                i0 = next(i for i, x in enumerate(v) if x % ell)
                lm = w[i0] * pow(v[i0], -1, ell) % ell
                lam.append(lm if all((w[i] - lm*v[i]) % ell == 0 for i in range(len(v))) else None)
            eig2[str(q)] = lam
        e["T_q_on_ker_alpha*alpha_mod_l"] = eig2
        del e["_T1"]
        e["wall_s"] = round(time.time() - t1, 2)
        res["ell"][str(ell)] = e
    res["wall_s"] = round(time.time() - t0, 2)
    js = json.dumps(res, indent=1, default=int)
    if outf: open(outf, "w").write(js)
    print(js)

def nullspace_mod(Mx, ell):
    A_ = [[int(x) % ell for x in row] for row in Mx]
    rows, cols = len(A_), len(A_[0]); piv = []; r0 = 0
    for c in range(cols):
        pr = next((i for i in range(r0, rows) if A_[i][c]), None)
        if pr is None: continue
        A_[r0], A_[pr] = A_[pr], A_[r0]; inv = pow(A_[r0][c], -1, ell)
        A_[r0] = [x*inv % ell for x in A_[r0]]
        for i in range(rows):
            if i != r0 and A_[i][c]:
                f = A_[i][c]; A_[i] = [(x - f*y) % ell for x, y in zip(A_[i], A_[r0])]
        piv.append(c); r0 += 1
    free = [c for c in range(cols) if c not in piv]; out = []
    for fc in free:
        v = [0]*cols; v[fc] = 1
        for i, pc in enumerate(piv): v[pc] = (-A_[i][fc]) % ell
        out.append(v)
    return out

if __name__ == "__main__":
    main()
