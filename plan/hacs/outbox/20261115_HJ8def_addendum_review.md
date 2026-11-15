# Review: HJ-8-def addendum (m-matching guard, eigenspace route)

Verdict: PASS, with one wording defect (a false inference in a comment) and one scoping note.

## 1. Eigenspace route (jl_eta_def.cpp:993-1140, m_rank_shift at :1045)
- Dimension equals rank: the module M⊗Z_p is finite free, and the Hecke algebra A (commutative, finite over Z_p) is a product of local factors. So M⊗Z_p = ⊕_m M_m by idempotent lifting, and M_m⊗F_p is the joint generalized eigenspace of A at m. The dimension therefore equals rk_{Z_p} M_m. Sound.
- Using only some T_l (T2 first, with an early break at dim<=1 at :1062-1063): the joint generalized eigenspace of the subset {T_l} is ⊕ M_{m'} over all m' that agree with m on those l. So it contains M_m and the dimension can only OVERcount rank M_m. A false rank 1 cannot come from too few operators. Confirmed: rank >= 2 is reported as "not determined" (:1134), which is safe.
- Rank 1 implies η^B = 1: T^B_m ⊂ End(M_m) = Z_p, and the congruence module is trivial. This is fine.
- Defect (comment at :996-997, "it is >= 1 when the final space is nonzero"): a nonzero eigenspace of dim 1 proves rk M_m = 1 only if m occurs at weight k+(p-1). Otherwise the line could belong to a different m' that shares the residues at the l used. m does occur there, by the g·E_{p-1} ≡ g mod p lifting that the T5 setup assumes, and the full route detects it through the residual-eigenvalue match. So the conclusion is valid given that input, but the route does not check it. With T2 only, a nonzero dim-1 space is really "rk M_m ≤ 1, and = 1 iff m occurs". Reword the comment, and state the assumption in the addendum.
- The T_l used are those in the target map (l in {2,3,5,7,11}, l != q). Their eigenvalues are F_p-rational (they come from a residual_eigen map). Fine.

## 2. Guard (jl_eta_def.cpp:963-972; n_matches counted at :937)
- Correct and conservative. An empty target gives "not determined". Zero matches gives "not determined". More than one gives "not determined". An overwrite of mfromk in the matching loop is replaced by the guard afterwards.
- Blocks are keyed by residual eigensystem, so a double match should not occur in practice. Blocks with a non-F_p residue (residual_eigen incomplete) never match, which gives n_matches 0 and "not determined". That is safe.
- Scoping note: in --suite shift (:1205-1212) only the empty-target check applies. The target comes from m_eigen_out, which is overwritten per old-congruent block (:933-934), and detection is for dim S_k(1)=1 only. This is fine for the 7 cells, but it is not a general uniqueness guard.

## 3. Dependence of hj8_def_native.json
- The committed JSON does not contain any shift-route output. grep finds no "shift", "m_shift_route" or "computed by the shift route only" in it. Its "not computed" entries are untouched by the route.
- Collector (laneC_hj8def_collect.py:137-168): the route is merged only if --shift dumps are passed. When they are, it (a) adds m_shift_route and shift_route_eq_full_route as a cross-check where the full route has a rank, and (b) for cells marked "not computed" it ADDS numbers, with status "computed by the shift route only" and route="shift". So the route can feed reported numbers when the flag is used, but it is labelled as such. It is not a silent substitute. The present JSON was generated without that flag.
