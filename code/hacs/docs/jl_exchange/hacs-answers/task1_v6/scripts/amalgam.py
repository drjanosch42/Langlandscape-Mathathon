# SPDX-License-Identifier: CC-BY-4.0
"""Mayer-Vietoris for SL_2(Z[1/p]) = SL_2(Z) *_{Gamma_0(p)} G_2, G_2 = g SL_2(Z) g^{-1}, g = diag(1,p),
with V = Sym^n Z_(l)^2 (n = k-2 even), computed independently of HACS (stdlib Python + numpy only).

Model (all conventions are those of the HACS contract [C] 1.27.0, see ../README.md and results.md section 0):
  * rho_n(A): column j holds the coefficients of (a x + c y)^{n-j} (b x + d y)^j in the basis x^{n-t} y^t
    ([C] def:rhon), a monoid homomorphism on M_2.
  * Gamma = SL_2(Z) = <S> *_{<-I>} <U>, S = [[0,-1],[1,0]] (order 4), U = ST = [[0,-1],[1,1]] (order 6).
    For a Z[Gamma]-module X on which 6 is invertible and -I acts trivially,
        H^1(Gamma, X) = X / (im(1+S) + im(1+U+U^2))           ([C] prop:levelorbit(2), cl:amalgam)
    via x |-> the cocycle c_x with c_x(S) = 0, c_x(U) = (U-1)x.
  * Level p by Shapiro: M = Ind_{Gamma_0(p)}^{Gamma} V = {f : Gamma -> V, f(h x) = h f(x)}, (gamma f)(x) = f(x gamma),
    coordinates f_j = f(s_j), s_j = [[1,0],[j,1]] (0 <= j < p), s_p = S ([C] def:cosetrepsN at N = p);
    (gamma f)_j = rho(h_j(gamma)) f_{j.gamma}, h_j(gamma) = s_j gamma s_{j.gamma}^{-1}  ([C] eq:MH).
  * dg_1 = res: V -> M, v |-> (rho(s_j) v)_j;  omega = cor: M -> V, f |-> sum_j rho(s_j^{-1}) f_j  ([C] prop:levelellU).
  * dg_p: H^1(Gamma,V) -> H^1(Gamma_0(p),V), (dg_p c)(h) = rho(g) c(g^{-1} h g)  ([C] prop:levelcorrespondence(4)(c)),
    = res^{G_2}_{Gamma_0(p)} o kappa, kappa(c)(x) = rho(g) c(g^{-1} x g) the transport H^1(Gamma,V) -> H^1(G_2,V).
  * T_q (q != p), both levels: (T z)(h) = sum_t rho(delta_t) z(delta_t^{-1} h delta_{t'}), delta_t over the left cosets
    [[q,-b],[0,1]] (0 <= b < q), [[1,0],[0,q]] (adjugates of [C] prop:cosets(1)'s right cosets), t' the index with
    delta_t^{-1} h delta_{t'} in the group ([C] eq:heckechain / prop:levelcorrespondence(3)).
"""
import sys, json, math, time
from fractions import Fraction
import numpy as np

# ---------------------------------------------------------------- 2x2 matrices (tuples a,b,c,d)
def mm(A, B):
    a, b, c, d = A; e, f, g, h = B
    return (a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h)
def inv1(A):  # inverse of a det-1 matrix
    a, b, c, d = A; return (d, -b, -c, a)
def adj(A):
    a, b, c, d = A; return (d, -b, -c, a)
def det(A): return A[0]*A[3] - A[1]*A[2]
I2 = (1, 0, 0, 1); S = (0, -1, 1, 0); Sinv = (0, 1, -1, 0); T = (1, 1, 0, 1); Tinv = (1, -1, 0, 1)
U = mm(S, T)          # ST = [[0,-1],[1,1]]
mI = (-1, 0, 0, -1)
assert U == (0, -1, 1, 1)

# ---------------------------------------------------------------- rho_n
_rho_cache = {}
def rho(A, n):
    key = (A, n)
    r = _rho_cache.get(key)
    if r is not None: return r
    a, b, c, d = A
    def pmul(P, Q):
        R = [0]*(len(P) + len(Q) - 1)
        for i, x in enumerate(P):
            if x:
                for j, y in enumerate(Q): R[i+j] += x*y
        return R
    pa = [1]; pw1 = [[1]]
    for _ in range(n): pw1.append(pmul(pw1[-1], [a, c]))
    pw2 = [[1]]
    for _ in range(n): pw2.append(pmul(pw2[-1], [b, d]))
    M = [[0]*(n+1) for _ in range(n+1)]
    for j in range(n+1):
        P = pmul(pw1[n-j], pw2[j])
        for t in range(n+1): M[t][j] = P[t] if t < len(P) else 0
    if len(_rho_cache) < 200000: _rho_cache[key] = M
    return M

def mat_vec(M, v):
    return [sum(M[i][j]*v[j] for j in range(len(v)) if v[j]) for i in range(len(M))]
def vadd(u, v): return [x + y for x, y in zip(u, v)]
def vsub(u, v): return [x - y for x, y in zip(u, v)]
def vscale(s, v): return [s*x for x in v]

# ---------------------------------------------------------------- words in S, T for SL_2(Z)
def word(g):
    """letters: 'S', 'T', 't' (=T^{-1}), 'm' (=-I); product of letters equals g."""
    a, b, c, d = g
    assert a*d - b*c == 1, g
    L = []
    while c != 0:
        q = a // c
        L += (['T']*q if q >= 0 else ['t']*(-q))
        a, b = a - q*c, b - q*d
        L.append('S'); a, b, c, d = c, d, -a, -b
    if a == 1:
        L += (['T']*b if b >= 0 else ['t']*(-b))
    else:
        L.append('m'); L += (['T']*(-b) if -b >= 0 else ['t']*b)
    return L
LET = {'S': S, 'T': T, 't': Tinv, 'm': mI}
def check_word(g):
    P = I2
    for x in word(g): P = mm(P, LET[x])
    assert P == g, (g, P)

# ---------------------------------------------------------------- level-1 cocycles with values in V (exact)
class Cocycle1:
    """A V-valued 1-cocycle on SL_2(Z) given by c(S), c(U) (lists of Fractions/ints)."""
    def __init__(self, n, cS, cU):
        self.n = n; self.cS = cS; self.cU = cU
        Si = rho(Sinv, n)
        cSinv = vscale(-1, mat_vec(Si, cS))
        self.lv = {'S': cS,
                   'T': vadd(cSinv, mat_vec(Si, cU))}            # T = S^{-1} U
        self.lv['t'] = vscale(-1, mat_vec(rho(Tinv, n), self.lv['T']))
        self.lv['m'] = vadd(cS, mat_vec(rho(S, n), cS))          # -I = S^2
    def __call__(self, g):
        n = self.n; P = I2; acc = [0]*(n+1)
        for x in word(g):
            acc = vadd(acc, mat_vec(rho(P, n), self.lv[x])); P = mm(P, LET[x])
        return acc

def cocycle_to_rep(n, cfun, act, zero):
    """class of a cocycle on Gamma (values via cfun(gamma)) in X/(im(1+S)+im(1+U+U^2)):
       m = b - a, a = -(1/4) sum_{i<4} c(S^i), b = -(1/6) sum_{i<6} c(U^i)."""
    a = zero[:]; P = I2
    for i in range(4): a = vadd(a, cfun(P)); P = mm(P, S)
    b = zero[:]; P = I2
    for i in range(6): b = vadd(b, cfun(P)); P = mm(P, U)
    return vsub(vscale(Fraction(-1, 6), b), vscale(Fraction(-1, 4), a))

# ---------------------------------------------------------------- Gamma_0(p) cosets
class Level:
    def __init__(self, p, n):
        self.p, self.n = p, n
        self.reps = [(1, 0, j, 1) for j in range(p)] + [S]
        self.m = p + 1; self.d = n + 1; self.D = self.m * self.d
    def cls(self, g):
        c, d = g[2], g[3]; p = self.p
        return (c * pow(d, -1, p)) % p if d % p else p
    def h(self, j, g):
        x = mm(self.reps[j], g); jj = self.cls(x)
        return mm(x, inv1(self.reps[jj])), jj
    def in_G0(self, g): return g[2] % self.p == 0
    def Mmat(self, g):
        """dense integer matrix of the action of g on M (block row j, block column j.g)"""
        n, d = self.n, self.d
        A = np.zeros((self.D, self.D), dtype=object)
        for j in range(self.m):
            hj, jj = self.h(j, g)
            R = rho(hj, n)
            for t in range(d):
                for s in range(d): A[j*d + t, jj*d + s] = R[t][s]
        return A
    def iota(self, v):           # dg_1 = res : V -> M
        out = []
        for j in range(self.m): out += mat_vec(rho(self.reps[j], self.n), v)
        return out
    def omega(self, f):          # cor : M -> V
        n, d = self.n, self.d; acc = [0]*d
        for j in range(self.m): acc = vadd(acc, mat_vec(rho(inv1(self.reps[j]), n), f[j*d:(j+1)*d]))
        return acc
    def shapiro_forward(self, zfun):
        """Gamma_0(p)-cocycle z (zfun(h) -> V) |-> representative in M of its class in H^1(Gamma, M):
           m_j = (1/4) sum_{i<4} F(s_j S^i) - (1/6) sum_{i<6} F(s_j U^i),  F(x) = z(x s_{[x]}^{-1})."""
        out = []
        for j in range(self.m):
            acc = [Fraction(0)]*self.d
            P = self.reps[j]
            for i in range(4):
                h = mm(P, inv1(self.reps[self.cls(P)])); acc = vadd(acc, vscale(Fraction(1, 4), zfun(h))); P = mm(P, S)
            P = self.reps[j]
            for i in range(6):
                h = mm(P, inv1(self.reps[self.cls(P)])); acc = vsub(acc, vscale(Fraction(1, 6), zfun(h))); P = mm(P, U)
            out += acc
        return out

def hecke_cosets(q):
    return [(q, -b, 0, 1) for b in range(q)] + [(1, 0, 0, q)]

def hecke_cocycle(zfun, q, n, member):
    """(T_q z)(h) = sum_t rho(delta_t) z(delta_t^{-1} h delta_t'), member(.) tests the group (level 1 or Gamma_0(p))."""
    dl = hecke_cosets(q)
    def Tz(h):
        acc = None
        for dt in dl:
            X = mm(adj(dt), h)          # q * delta_t^{-1} h
            found = None
            for d2 in dl:
                Y = mm(X, d2)
                if all(y % q == 0 for y in Y):
                    Y = tuple(y // q for y in Y)
                    if member(Y): found = Y; break
            assert found is not None
            v = mat_vec(rho(dt, n), zfun(found))
            acc = v if acc is None else vadd(acc, v)
        return acc
    return Tz

# ---------------------------------------------------------------- modular linear algebra (mod Q = l^E)
def to_mod(x, Q):
    if isinstance(x, Fraction): return (x.numerator * pow(x.denominator, -1, Q)) % Q
    return x % Q

def relation_rows(n, act_S, act_U, D):
    """rows spanning im(1+S) + im(1+U+U^2) (as integer row vectors)"""
    I = np.identity(D, dtype=object)
    R1 = (I + act_S)
    R2 = (I + act_U + act_U.dot(act_U))
    return np.concatenate([R1.T, R2.T], axis=0)   # rows = images of basis vectors

def quotient_basis(Rows, Q, ell):
    """RREF mod Q with unit pivots; returns (pivcols, nonpiv, P) with P: (r x D) projection X -> X/R (free)."""
    A = [[int(x) % Q for x in row] for row in Rows]
    D = len(A[0]); piv = []; r0 = 0
    for col in range(D):
        pr = None
        for i in range(r0, len(A)):
            if A[i][col] % ell: pr = i; break
        if pr is None: continue
        A[r0], A[pr] = A[pr], A[r0]
        inv = pow(A[r0][col], -1, Q)
        A[r0] = [(x * inv) % Q for x in A[r0]]
        rowp = A[r0]
        for i in range(len(A)):
            if i != r0 and A[i][col]:
                f = A[i][col]; Ai = A[i]
                A[i] = [(x - f*y) % Q for x, y in zip(Ai, rowp)]
        piv.append(col); r0 += 1
    for i in range(r0, len(A)):
        if any(A[i]): raise RuntimeError("relation module not a direct summand mod l^E: torsion at l")
    nonpiv = [c for c in range(D) if c not in set(piv)]
    r = len(nonpiv)
    P = np.zeros((r, D), dtype=object)
    for a, c in enumerate(nonpiv): P[a, c] = 1
    for i, pc in enumerate(piv):
        for a, c in enumerate(nonpiv): P[a, pc] = (-A[i][c]) % Q
    return piv, nonpiv, P

def smith_vals(Mx, Q, ell, E):
    """valuations of the elementary divisors of an integer matrix mod l^E (E = 'zero mod l^E')."""
    A = [[int(x) % Q for x in row] for row in Mx]
    rows, cols = len(A), (len(A[0]) if A else 0)
    def v(x):
        if x % Q == 0: return E
        e = 0
        while x % ell == 0: x //= ell; e += 1
        return e
    vals = []; k = 0
    while k < min(rows, cols):
        best = None
        for i in range(k, rows):
            for j in range(k, cols):
                if A[i][j] % Q:
                    vv = v(A[i][j])
                    if best is None or vv < best[0]: best = (vv, i, j)
        if best is None: break
        _, i, j = best
        A[k], A[i] = A[i], A[k]
        for row in A: row[k], row[j] = row[j], row[k]
        e = best[0]; u = A[k][k] // ell**e; ui = pow(u, -1, Q)
        for i2 in range(rows):
            if i2 != k and A[i2][k] % Q:
                f = (A[i2][k] // ell**e) * ui % Q
                A[i2] = [(x - f*y) % Q for x, y in zip(A[i2], A[k])]
        for j2 in range(cols):
            if j2 != k and A[k][j2] % Q:
                f = (A[k][j2] // ell**e) * ui % Q
                for row in A: row[j2] = (row[j2] - f*row[k]) % Q
        vals.append(e); k += 1
    return vals + [E]*(min(rows, cols) - len(vals))

def charpoly_mod(Mx, P):
    """char poly det(X - M) (coefficients low -> high) of a square integer matrix mod a prime P (Hessenberg route)."""
    n = len(Mx)
    H = [[int(x) % P for x in row] for row in Mx]
    for m in range(1, n - 1):                      # reduce to upper Hessenberg by similarity
        i = next((i for i in range(m, n) if H[i][m-1]), None)
        if i is None: continue
        if i != m:
            H[i], H[m] = H[m], H[i]
            for row in H: row[i], row[m] = row[m], row[i]
        inv = pow(H[m][m-1], -1, P)
        for i in range(m+1, n):
            if H[i][m-1]:
                u = H[i][m-1] * inv % P
                H[i] = [(x - u*y) % P for x, y in zip(H[i], H[m])]
                for row in H: row[m] = (row[m] + u*row[i]) % P
    # recurrence p_0 = 1, p_{k+1}(X) = (X - h_kk) p_k - sum_{i<k} h_ik prod_{j=i+1..k} h_{j,j-1} p_i
    polys = [[1]]
    for k in range(n):
        pk = [0] + polys[k]                         # X * p_k
        pk = [(c - H[k][k]*(polys[k][t] if t < len(polys[k]) else 0)) % P for t, c in enumerate(pk)]
        prod = 1
        for i in range(k-1, -1, -1):
            prod = prod * H[i+1][i] % P
            f = H[i][k] * prod % P
            if f:
                for t, c in enumerate(polys[i]): pk[t] = (pk[t] - f*c) % P
        polys.append(pk)
    return polys[n]

# ---------------------------------------------------------------- exact rational quotient (level 1)
def quotient_basis_Q(Rows):
    A = [[Fraction(int(x)) for x in row] for row in Rows]
    D = len(A[0]); piv = []; r0 = 0
    for col in range(D):
        pr = next((i for i in range(r0, len(A)) if A[i][col] != 0), None)
        if pr is None: continue
        A[r0], A[pr] = A[pr], A[r0]
        inv = 1 / A[r0][col]; A[r0] = [x * inv for x in A[r0]]
        for i in range(len(A)):
            if i != r0 and A[i][col] != 0:
                f = A[i][col]; A[i] = [x - f*y for x, y in zip(A[i], A[r0])]
        piv.append(col); r0 += 1
    nonpiv = [c for c in range(D) if c not in set(piv)]
    def proj(v):
        out = [Fraction(v[c]) for c in nonpiv]
        for i, pc in enumerate(piv):
            if v[pc]:
                for a, c in enumerate(nonpiv): out[a] -= v[pc] * A[i][c]
        return out
    return piv, nonpiv, proj

# ---------------------------------------------------------------- fast Gamma_0(p)-cocycles of classes of H^1(Gamma, M) (mod Q)
class FastLevel:
    def __init__(self, L, Q, basis_cols):
        self.L, self.Q = L, Q; n, d, m = L.n, L.d, L.m
        MS = L.Mmat(S); MU = L.Mmat(U); MSi = L.Mmat(Sinv); MTi = L.Mmat(Tinv)
        I = np.identity(L.D, dtype=object)
        AT = MSi.dot(MU - I); At = -MTi.dot(AT)
        cols = basis_cols
        self.Ab = {}
        for key, A in (('T', AT), ('t', At)):
            Ar = np.array([[int(x) % Q for x in row] for row in A[:, cols]], dtype=np.int64)
            self.Ab[key] = [Ar[j*d:(j+1)*d, :] for j in range(m)]
        self.r = len(cols)
        # rho(h_j(letter)) and j.letter
        self.step = {}
        for key, g in LET.items():
            for j in range(m):
                hj, jj = L.h(j, g)
                self.step[(key, j)] = (np.array([[x % Q for x in row] for row in rho(hj, n)], dtype=np.int64), jj)
        self.zero = np.zeros((d, self.r), dtype=np.int64)
        self.I = np.identity(d, dtype=np.int64)
    def z(self, h):
        """z_c(h) = C_c(h)_{block 0} for all basis classes c at once: (d x r) mod Q"""
        Q = self.Q; R = self.I; j = 0; acc = self.zero.copy()
        for x in word(h):
            if x in ('T', 't'): acc = (acc + R.dot(self.Ab[x][j])) % Q
            st, jj = self.step[(x, j)]
            R = R.dot(st) % Q; j = jj
        return acc
    def shapiro_forward_mod(self, zfun):
        L, Q = self.L, self.Q; d = L.d
        i4 = pow(4, -1, Q); i6 = pow(6, -1, Q)
        out = np.zeros((L.D, self.r), dtype=np.int64)
        for j in range(L.m):
            acc = self.zero.copy(); P = L.reps[j]
            for i in range(4):
                h = mm(P, inv1(L.reps[L.cls(P)])); acc = (acc + i4 * zfun(h)) % Q; P = mm(P, S)
            P = L.reps[j]
            for i in range(6):
                h = mm(P, inv1(L.reps[L.cls(P)])); acc = (acc - i6 * zfun(h)) % Q; P = mm(P, U)
            out[j*d:(j+1)*d, :] = acc
        return out
    def hecke(self, q, Pproj):
        L, Q, n = self.L, self.Q, self.L.n
        dl = hecke_cosets(q)
        rd = [np.array([[x % Q for x in row] for row in rho(dt, n)], dtype=np.int64) for dt in dl]
        def Tz(h):
            acc = self.zero.copy()
            for dt, R in zip(dl, rd):
                X = mm(adj(dt), h); found = None
                for d2 in dl:
                    Y = mm(X, d2)
                    if all(y % q == 0 for y in Y):
                        Y = tuple(y // q for y in Y)
                        if Y[2] % L.p == 0: found = Y; break
                assert found is not None
                acc = (acc + R.dot(self.z(found))) % Q
            return acc
        mo = self.shapiro_forward_mod(Tz)
        return Pproj.dot(mo) % Q
