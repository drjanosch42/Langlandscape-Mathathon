\\ SPDX-License-Identifier: GPL-3.0-or-later WITH LicenseRef-CUDA-exception-GPL
\\ Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team)
\\
\\ S06 cross-check (F4, batch 7), row S06-C3 (T4): p = 17, q = 3, k in {12, 28, 44, 60, 124}.
\\ Definitions: code/cas/s06-xcheck/README.md, Section 1.
\\   m = (17, T_l - tau(l), all primes l incl. 17) in T_k(1);  delta = 16 - 3^(2-k) T_3^2, computed via x = 16*3^(k-2) - T_3^2;
\\   route A: length_{Z_17} T(1)_m/(delta) = sum over (g, P) in m of f(P) ord_P delta(g)  (eigenforms);
\\   route B: Smith normal form of multiplication by x on the Z-lattice T_k(1) (all maximal ideals at 17 together);
\\   t_{G_k}(3) := ord_P(a_3(G_k)^2 - 16*3^(k-2)) from the eigenform coefficient;
\\   extra: level-3 c_3(f') and t^an_{f'}(3) for the 3-new f' in m_N (routines of h3.gp; Z_p route at k = 124).
\\ Requires h3.gp to be read first (run.py does this).

T4_P = 17; T4_Q = 3; T4_WEIGHTS = [12, 28, 44, 60, 124];

\\ (g, P) congruent to Delta mod P at all primes l <= B with l != skip (skip = 0: no prime skipped).
t4_in_m(nf, P, a, B, skip) =
{
  forprime(l = 2, B, if(l != skip,
    my(x = a[l+1] - ramanujantau(l)); if(x != 0 && nfeltval(nf, lift(x), P) == 0, return(0))));
  1;
}

\\ Route B: [v_17 |T/xT|, 17-adic valuations of the elementary divisors (non-zero ones), rank, B, stable].
t4_routeB(mf, k) =
{
  my(p = T4_P, q = T4_Q, d = mfdim(mf), L0 = xc_hecke_lattice(mf, mfsturm(mf) + 1, 0, "coef"), L, H, den, r, T3, X, A, D, vals);
  \\ matrix realisation of T on the stable range found by the coefficient realisation, re-checked for stability
  L = xc_hecke_lattice(mf, L0[5], 0, "mat");
  H = L[3]; den = L[4]; r = #H;
  T3 = mfheckemat(mf, q);
  X = 16*q^(k-2)*matid(d) - T3^2;
  A = matrix(r, r);
  for(j = 1, r,
    my(b = matrix(d, d, s, t, H[(s-1)*d + t, j])/den, Xb = X*b, w);
    w = vector(d*d, i, Xb[(i-1)\d + 1, (i-1)%d + 1])~;
    A[, j] = matinverseimage(H/den, w));
  if(denominator(A) != 1, error("t4_routeB: x*T not inside T"));
  D = matsnf(A);
  vals = select(v -> v > 0, apply(e -> valuation(e, p), D));
  [valuation(matdet(A), p), vals, r, L[5], L[6], valuation(matdet(X), p)];
}

\\ One weight. Returns [k, dim, routeA_rows, lengthA_m, lengthA_all17, rank_m, rank_m_away17, routeB, level3]
\\ (rank_m = sum of e(P) f(P) over (g, P) in m = rank of T(1)_m over Z_17).
\\ routeA_rows: [form idx, field poly, deg, P idx, e, f, in_m, in_m_away_from_17, a_17 unit?, ord_P delta(g), t_G(3), a_3 (polmod)].
t4_weight(k, dolevel3 = 1) =
{
  my(p = T4_P, q = T4_Q, mf = mfinit([1, k], 1), d = mfdim(mf), Bm = max(mfsturm(mf) + 1, 60), Lg, F, rows = List(),
     lenm = 0, lenall = 0, nm = 0, nm17 = 0, rB, l3 = 0);
  Lg = mfeigenbasis(mf); F = mffields(mf);
  for(i = 1, #Lg,
    my(a = mfcoefs(Lg[i], Bm), pol = F[i], nf = nfinit([pol, [p]]), Pl = idealprimedec(nf, p));
    for(j = 1, #Pl,
      my(P = Pl[j], inm, inm17, a17u, od, tg);
      inm = t4_in_m(nf, P, a, Bm, 0);
      inm17 = t4_in_m(nf, P, a, Bm, p);
      a17u = (nfeltval(nf, lift(a[p+1]), P) == 0);
      od = nfeltval(nf, lift(16*q^(k-2) - a[q+1]^2), P);          \\ = ord_P delta(g), 3 a unit
      tg = nfeltval(nf, lift(a[q+1]^2 - 16*q^(k-2)), P);          \\ t_{G}(3) as in the stage tex
      lenall += P.f * od;
      if(inm, lenm += P.f * od; nm += P.e * P.f);
      if(inm17, nm17 += P.e * P.f);
      listput(rows, [i, pol, poldegree(pol), j, P.e, P.f, inm, inm17, a17u, od, tg, a[q+1]])));
  rB = t4_routeB(mf, k);
  if(dolevel3,
    my(B3 = mfsturm(mfinit([q, k], 1)) + 1);
    \\ integral route for k <= 60; Z_p route (xc_level_qp) for k = 124, where the integral HNF overflows 6 GB
    l3 = if(k <= 60, xc_level_q(q, k, p, (nf, P, a) -> t4_in_m(nf, P, a, B3, q)),
                     xc_level_qp(q, k, p, 1, 60, (nf, P, a) -> t4_in_m(nf, P, a, B3, q))));
  [k, d, Vec(rows), lenm, lenall, nm, nm17, rB, l3];
}

t4_run(dolevel3 = 1) = vector(#T4_WEIGHTS, i, t4_weight(T4_WEIGHTS[i], dolevel3));
