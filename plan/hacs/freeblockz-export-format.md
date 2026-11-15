<!-- SPDX-License-Identifier: CC-BY-4.0 -->
<!-- Copyright (C) 2026 Fabian Januszewski, Abhijit (the Langlandscape team) -->

# `free_block_z` export format v2 (HJ-B0): the Brandt lattice in the HACS `FreeBlockZ` layout

Status: **spec, v2 (2026-11-15)** = v1 plus the required canonical class order (§1b). Lane B's HJ-6 spike (`Lattice2HeckeZ`) codes against this file. HJ-B0 phase 2
(`code/python/langlandscape/hacs_bridge/brandt_export.py`) writes it. Seed = HACS dev commit `0ea75f73` (`code/hacs/PROVENANCE.md`). Every
citation below is to that tree (`code/hacs/src/hacs/...`) and was read for this note. Items not pinned down are marked
**OPEN**.

## 0. Summary

- **Module.** M = ℤ-valued functions on the class set X_B, as a free ℤ-module of rank r = h with basis b_j = 1_{c_j}, the
  indicator of class c_j. The classes c_1, …, c_h are in the **canonical order** of §1b (v2). This is the k = 2 case; for
  k > 2 see §6.
- **Matrices.** F_p = the Brandt matrix B_p of `brandt.py`, with **no transpose**. In the HACS column convention
  T_p b_j = Σ_i F_ij b_i (§2), stored row-major as decimal strings.
- **Hash.** `F_fnv` = FNV-1a-64 of `"F00,F01,…;F10,…"`. The Python twin reproduces HACS's own printed hash bit-exactly (§4).
- **Call.** `LatticeFromFreeZ(N = D·M, n = k−2, ℓ, K, P, G, ops)` → `ReadLocal(M, {d_target = d_algebra, r_eis = e,
  eis_rational, k_weight = k})` (§5).
- **Tag.** Every downstream value is *computed*, never `certified` (§7).

## 1. File location and naming

- Directory `code/results/s06/brandt_free_block_z/`, with **one file per cell**: `D<D>_M<M>_k<k>.json`, for example
  `D11_M1_k2.json`.
- An `index.json` in the same directory lists every cell with its `status` and file name.
- Size: k ≤ 12 and D ≤ 43 give r ≤ 8 for the symn cells, a few kB each. The total is ≪ 10 MB. Phase 2 checks the
  total and stops above 10 MB.
- Envelope: `{provenance, data}`, exactly as `code/python/langlandscape/results.py` writes it. `provenance` holds
  `script`, `commit`, `params`, `date` and `runtime_s`.
- **No** `hacs --version` and **no** `default_fp` are recorded: this export runs no HACS binary. Lane A interface note 1
  applies only to records that do run it.

## 1a. Writers, versions, required and optional fields (binding)

The format is **writer-neutral**. Two writers are planned:
- the Python exporter (`code/python/langlandscape/hacs_bridge/brandt_export.py`, HJ-B0 phase 2);
- Lane B's native C++ core (`hacs_jl`), which writes from native class sets for the large-q census.

Both write the same field names with the same meaning. Readers never branch on the writer.

- **`schema`** = `"langlandscape_brandt/v2"` (v1 until 2026-11-15, §1b). It appears at the top level of `data` and
  again inside each `free_block_z` record. A v2 reader rejects any other value, except that it may accept a v1 record
  as "class order unspecified" (§1b).
- **`writer`** (required, at the top level of `data`) names the producer:
  - `"python:brandt_export@<git commit>"` for the Python exporter;
  - `"hacs_jl:<sha256 of the hacs binary>"` for the C++ core, which also records its `hacs --version` line in
    `provenance`.

  `origin` (§3) is a different thing: it records the mathematical source of the matrices.
- **Unknown fields.** A reader (v1 or v2) **must ignore** fields it does not know, at every level. Writers may add optional
  fields without a version change.
- **Version rule.** These changes make a new schema string, with the old version still readable during the transition.
  v1 → v2 was such a change (§1b); the next one is `langlandscape_brandt/v3`.
  - adding, removing or renaming a required field;
  - changing the type, encoding or meaning of a required field (for example the column convention, the row-major order,
    the `F_fnv` text, the decimal-string encoding, or the meaning of `ops`, `N` or `n`);
  - changing the allowed values of `status`.

  Changing an optional field's meaning also needs v2. Adding a new optional field does not.
- **Required in every `free_block_z` record:**
  - `schema`, `status`, `D`, `M`, `k`, `n`, `N`, `rank`, `ops`, `F`, `F_fnv`, `proof`, `basis_rule`, `convention`,
    `lattice`, `tag`;
  - plus `d_algebra` and `e_eis` when `status` is `ok`;
  - plus `reason` when `status` is `no_integral_basis`. In that case `F` and `F_fnv` are `[]`.
- **Optional:** `basis_fnv`, `phi_fnv`, `saturation`, `q0_key`, `bound_basis`, `bits_F`, `gammas`, `charpoly_Z`,
  `origin`, `class_keys`, `order_ties` and `canonical` (§1b), and any writer-specific diagnostics (timings, for instance).
  - `gammas` is optional in the format but **needed** for the ℓ | |Γ_x| check of §7. Both planned writers emit it.
  - When an optional `FreeBlockZ` member is absent, a reader fills it with the defaults of §3 (`0`, `"-"`, `"cpu"`).
- **Writer obligations:**
  - `F_fnv[o]` must equal the §4 hash of `F[o]`, and readers check it.
  - `ops` is ascending and free of duplicates.
  - Every entry is a decimal string as in §4. No JSON numbers appear inside `F`, so no precision is lost above 2^53.

## 1b. v2 changes (binding; 2026-11-15)

The **only** change from v1 is a required writer rule: the **canonical class order**. It fixes the basis in which the
required field `F` is expressed, so by §1a it is a schema bump. Every other field, encoding and convention is unchanged
from v1. The v1 text below stays valid with "v1" read as "v2".

**Why.** `brandt.module(D)`'s BFS order depends on the base maximal order, and `alginit` picks that order at random. The
order therefore depended on process history: D = 17 gives `gammas` [6, 2] in a fresh process and [2, 6] after D = 2..13.
v1 records (commits f54b109e, e5911cab) are **superseded**. Their order was process-dependent.

**Writer obligation (k = 2, required).** Sort the classes c **ascending** on the tuple (K1, K2), lexicographically:
1. **K1 = |Γ_c|**, where Γ_c = O_r(I_c)^× includes ±1 (the `gammas` value).
2. **K2 = θ_c = (r_c(1), r_c(2), …, r_c(20))**, compared as an integer vector, where
   - r_c(m) = #{x ∈ O_r(I_c) : nrd(x) = m};
   - the form is the reduced norm on the **right order** O_r(I_c), as a ℤ-lattice of rank 4 (equivalently
     nrd(x)/N(I_c)² on conj(I_c)·I_c);
   - x and −x are both counted (not halved), so r_c(1) = |Γ_c|;
   - m runs over 1..20, with L = 20 fixed and independent of `ops`; r(0) is not part of the key.
3. **No third key.** Classes with equal (K1, K2) form a contiguous tied group. The writer emits them in any order and
   lists every pair of mutually tied positions in `order_ties`: sorted pairs `[a, b]` with a < b, as 0-based positions
   after sorting. `order_ties = []` means no ties. Comparators are permutation-aware within tied groups only.

The right-order form is intrinsic to the class. The form nrd/N(I_c) on I_c is not: it depends on the base left order.

Ties observed (*computed*, all k = 2 records, D ≤ 43): only D = 37 and D = 43, `order_ties = [[0, 1]]` each.
- The tied classes have equal θ up to L = 60 and isomorphic right orders: they are the pair I, I·P, swapped by w_D.
- The swap leaves every B_p (p < 50) unchanged (*computed*). So F and `F_fnv` do not depend on the order within the tie;
  only `class_keys` does.

**k > 2 (scope).** The k > 2 records sort their class blocks by the same key, but the lattice (§6) also depends on
`symn.py`'s class representatives. The order rule is therefore **not** required to make F reproducible there.
- Such records carry the optional field **`canonical: false`** (absent = `true`).
- Compare them by `charpoly_Z` or up to GL_d(ℤ) conjugacy, **not** by `F_fnv`.

**v1 records.** A v2 reader may accept a v1 record only as "class order unspecified", that is with permutation-aware
comparison (k = 2: up to simultaneous permutation of the basis).

## 2. Column convention (binding), with a worked 2×2 example

HACS: `LatticeModule::T` holds "per p, D x D, column convention" (`Integral/HeckeZLocal.h:167`). The free block over ℤ
satisfies T_p b_j = Σ_i F_ij b_i (`task0_inscope/results.md` §0; `docs/console/console.md:906`). `F` is stored row-major,
so F_ij = `F[i*r + j]`:
- `FreeBlockModQ` copies `G.F[o][e]` index for index into `M.T` (`DescentModuleExportZ2.cpp:260–275`);
- `full_matrix` places `F[i*r + j]` at row t+i, column t+j (`DescentModuleExportZ2.cpp:299`).

In words: **column j of F is the image of b_j**.

Brandt side (`brandt.py` l. 8): `B[c][c']` = #{ℓ-neighbours of I_c lying in class c'}.

On functions, (T_ℓ f)(c) = Σ_{c'} B[c][c'] f(c'). Then
T_ℓ 1_{c_j} = Σ_c B[c][j] 1_c, that is T b_j = Σ_i B[i][j] b_i. **So F = B, with no transpose.** This settles the
draft claim in `hacs_bridge/definite_alg.py` l. 606: it is correct.

Worked example, D = 11, T_2 (computed; §8):

```
B_2 = F = [[1, 2],      T_2 b_1 = 1·b_1 + 3·b_2   (column 1 = (1, 3))
           [3, 0]]      T_2 b_2 = 2·b_1 + 0·b_2   (column 2 = (2, 0))
```

Checks in this orientation:
- **Row sums are ℓ + 1**: F·(1, …, 1)ᵀ = (ℓ+1)·(1, …, 1)ᵀ. The constant function **1** = Σ b_j is the Eisenstein
  eigenvector, with eigenvalue λ = ℓ + 1 = 1 + ℓ^{k−1} at k = 2, which is what `ReadLocal` expects.
- **Symmetry**: |Γ_j| F_ij = |Γ_i| F_ji. Here 6·2 = 4·3, with |Γ_c| = |O_r(I_c)^×| including ±1 (`gammas`).

The divisor lattice ℤ[X_B] (basis [I_c], T[I_c] = Σ neighbours) is the dual lattice, and on it F = Bᵀ. It is **not** the
exported object. Lane B may build it by transposing, for the ℓ | |Γ_x| cross-check of §7.

## 3. The `free_block_z` record, field by field against `FreeBlockZ` (`DescentModuleExportZ.h:140–154`)

The record sits at `data.free_block_z` and carries `schema = "langlandscape_brandt/v2"`. "LB" means what Lane B does
with the field.

| JSON field | type / encoding | `FreeBlockZ` member | LB |
|---|---|---|---|
| `schema` | `"langlandscape_brandt/v2"` (required, §1a) | — | reject other values |
| `writer` (top level of `data`) | string, §1a | — | log; never branch on it |
| `tag` | `"computed"` | — | §7 item 4 |
| `status` | `"ok"` \| `"rank0"` \| `"no_integral_basis"` | — (cf. `ModuleZ::free_block` `"exact"`/`"refused"`) | build `G` only on `ok`/`rank0` |
| `reason` | string; only when `status = "no_integral_basis"` | (cf. `free_refusal`) | log |
| `D`, `M`, `k`, `n` | int; `n = k − 2` | — (`LatticeFromFreeZ` args) | §5 |
| `N` | int, `= D·M` | — (arg `N`) | §5 |
| `rank` | int r | (r = √`F[o].size()`) | assert r² = len |
| `ops` | int list, ascending primes p ∤ D·M | — (arg `G_ops`; `G.F[o]` ↔ `ops[o]`) | pass as `G_ops` |
| `F` | list over `ops` of **r lists of r decimal strings** (nested rows) | `F` : `vector<vector<nf::BigInt>>`, per op **flat** r×r row-major | flatten: `F[o][i][j]` → `G.F[o][i*r+j] = BigInt(dec)` |
| `F_fnv` | list over `ops` of `"0x"` + 16 lower-case hex digits (zero-padded, `oc_util::HexU64` style) | `F_fnv` : `vector<uint64_t>` (MatrixFnv per op) | recompute in C++ with `freez::MatrixFnv(ColsOfRowMajor(F, r), r)`, equality = load check |
| `proof` | list over `ops`; `"exact_count"` (k = 2: integer neighbour counts) or `"exact_rational_model"` (k > 2, §6); `"rank0"` at r = 0 | `proof` : `vector<string>` (HACS: `apriori`\|`apost`\|`rank0`) | copy. `LatticeFromFreeZ` does not read it, and neither does any `HeckeZLocal*` consumer (grep). We never write HACS's `apriori`/`apost`: those name HACS's CRT proof |
| `basis_rule` | string, below | `basis_rule` (HACS: `"iso_dixon/v3"`, `IsoTreeCarrierZ.h:245`) | copy |
| `basis_fnv` | hex as `F_fnv`: FNV-1a-64 of the `class_keys` text (`str(key)` of each class rep's `brandt.Lattice.key`, joined by `;`, in basis order) | `basis_fnv` (HACS: `PackedFnv(B)`) | copy. Only a fingerprint of *our* basis, not comparable to HACS's |
| `phi_fnv` | `"-"` | `phi_fnv` (`PackedFnv(Phi_cert)`) | set 0 |
| `saturation` | `"exact_basis"` (`"rank0"` at r = 0) | `saturation` (HACS `det_pm1` / `rank0`) | copy |
| `q0_key`, `bound_basis` | `"-"` | `q0_key`, `bound_basis` (HACS `"-"` at rank 0) | copy |
| `bits_F` | list over `ops`: max bit length of \|F_ij\| | `bits_F` | copy |
| — | — | `bits_B`, `bits_Phi`, `K_pairs`, `primes_used`, `primes_apriori`, timings `t_*`, `lanes`, `lane_route` | zero / `"cpu"` |
| `gammas` | int list, \|Γ_c\| including ±1, in basis order | — | §7 (ℓ \| \|Γ_x\|) |
| `d_algebra` | int: dim_ℚ ℚ[F_p : p ∈ ops] (exact, from the matrices) | — (`ReadOptions::d_target`) | §5 |
| `e_eis` | int: multiplicity of the Eisenstein system (1 at k = 2, 0 at k > 2) | — (`ReadOptions::r_eis`) | §5 |
| `charpoly_Z` | list over `ops` of decimal-string lists, **low → high** (as `symn.json`) | — | cross-check only |
| `lattice` | `"functions"` (at k > 2 the value is kept; the lattice is the Hecke-stable hull of §6, named by `basis_rule`) | — | — |
| `convention` | k = 2: `"column: T_p b_j = sum_i F[i][j] b_i; F = B_p (B[c][c'] = #neighbours of c in c'); row sums l+1"`; k > 2: `"column: T_p b_j = sum_i F[i][j] b_i; b_j = the j-th column of basis_in_Q_coords (a basis of the Hecke-stable hull Lambda); no row-sum identity (no Eisenstein system at k > 2)"` | — | — |
| `order_ties` | list of `[a, b]` (0-based canonical positions), §1b | — | permutation-aware comparison within tied groups |
| `canonical` | bool, default `true`; `false` on k > 2 records (§1b) | — | `false`: compare by `charpoly_Z`, not `F_fnv` |
| `origin` | `"jl:brandt.py"` or `"jl:symn.py+integral_basis"` | (HACS `source = "free_block_z"` is kept, §3.2) | provenance |

The `basis_rule` strings are (v2; the v1 strings `brandt_delta/v1`, `brandt_symn_int/v1` are superseded):
- k = 2: `"brandt_k2_canonical/v2: b_j = 1_{c_j}, c_j the j-th left-ideal class; classes sorted ascending by (|Gamma_c|, (r_c(1),...,r_c(20))), r_c(m) = #{x in O_r(I_c) : nrd x = m} (x, -x both counted); ties listed in order_ties, order within a tie unspecified"`;
- k > 2: `"brandt_symn_int_canonical/v2: …"` (§6; the full text is in each record).

Rank 0 (odd k, or V^{Γ_c} = 0 for all c) follows HACS's rank-0 branch (`DescentModuleExportZ2.cpp:318–333`):
- per op, `F = []`, `F_fnv = "0xcbf29ce484222325"` (= `MatrixFnv({}, 0)`, the FNV offset basis), `proof = "rank0"`;
- `saturation = "rank0"`.

## 4. `F_fnv`, byte-exact

Source chain:
- `FreeBlockCrt` sets `op.fnv = MatrixFnv(ColsOfRowMajor(op.F, r), r)` (`DescentFreeBlockCrt.cpp:1492`, `:58–63`);
- `RunFreeBlock` copies it into `G.F_fnv` (`DescentModuleExportZ2.cpp:388–395`);
- `MatrixFnv` is at `IsoTreeCarrierZ.cpp:269–281`;
- the FNV itself is `src/ModArithmetic/Fnv.h` (`FnvBytes`, offset `0xcbf29ce484222325`, prime `0x100000001b3`).

The bytes hashed are the ASCII text
`row_0 ";" row_1 ";" … ";" row_{r−1}`, where `row_i = F_i0 "," F_i1 "," … "," F_i,r−1`.

Each entry is `nf::BigInt::to_string()` (`NumberField/BigInt.cpp:110–125`):
- plain decimal, a `-` sign only when the entry is negative, no `+`, no leading zeros;
- zero is written `"0"`.

There is no separator before row 0, no trailing separator and no terminator. Hashing line by line, as the C++ does, gives
the same value as hashing the whole string. Python `str(int)` produces the same digits.

```python
def fnv1a64(s: str) -> int:
    h = 0xcbf29ce484222325
    for c in s.encode("ascii"):
        h = ((h ^ c) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h
F_fnv = "0x%016x" % fnv1a64(";".join(",".join(str(x) for x in row) for row in F))
```

**Verified against HACS's own hash (computed):**
- the source is `Console/scripts/061_s25_module_z_exact.expected` l. 5–6, which prints `F = [["-24","0","68040"],["0","-24","0"],["0","0","2049"]]`
  and `F_fnv 0xb69e2fb38c33b922` (level 1, n = 10, T_2);
- the snippet gives `0xb69e2fb38c33b922` on `"-24,0,68040;0,-24,0;0,0,2049"`.

That test includes a negative entry. Phase 2 makes it a unit test.

Lane B's load check: recompute `freez::MatrixFnv` on the flattened `G.F[o]` and require equality with the JSON `F_fnv[o]`.

## 5. `LatticeFromFreeZ` and `ReadLocal`: arguments and where each comes from

`LatticeFromFreeZ(N, n, ell, K, P, G, G_ops)` (`HeckeZLocal.h:205`, `HeckeZLocal.cpp:741–780`):

| arg | value | source |
|---|---|---|
| `N` | `D·M` (record `N`) | so that `ReadPrimes(N, ℓ, P)` appends T_ℓ exactly when ℓ ∤ DM |
| `n` | `k − 2` | record `n` |
| `ell`, `K` | the read prime and the precision; **ℓ^K < 2^63**, otherwise `refused(word_modulus)` | HJ-6 (Mazur: ℓ \| num((q−1)/12)) |
| `P` | read set ⊆ `ops`. A missing operator is an **ENGINE_CHECK** (a crash, not a refusal). Via `ReadCellLocal` the read set is `ReadPrimes(N, ℓ, P)`, so **T_ℓ must be in `ops`** for each ℓ ∤ DM that is read | `ops` (phase 2: ops = primes < 50 not dividing DM; see the coverage rule below) |
| `G` | `FreeBlockZ` from §3 | record |
| `G_ops` | record `ops` | record |

`LatticeFromFreeZ` reads only `G.F` (through `FreeBlockModQ`), the operator lookup and the squareness check. Every other
`G` field is carried along without being read.

Coverage rule: `ops` contains every prime p < 50 with p ∤ DM. For p ≥ 50 or a larger ℓ, phase 2 adds the primes on
request (`--ops`).

The result has `source = "free_block_z"`, `word = "u64"`, `K_max = 0`, `is_lattice = true` and `D = r`.

`ReadLocal(M, ReadOptions)` (`HeckeZLocal.h:220–235`, `HeckeZLocal.cpp:920 ff.`). The Mazur/Eisenstein read uses:

| option | value | why |
|---|---|---|
| `d_target` | record `d_algebra`: the ℤ-rank of ℤ[T_P]. For D prime and M = 1 this equals r (multiplicity one). | **required.** The default 0 trips `ENGINE_CHECK(dim A'_1 ≤ d_target)` at l. 943. If P ⊊ ops, d may drop, so recompute d on P or keep P = ops (**OPEN** for M > 1: old forms make d < r). |
| `r_eis` | record `e_eis` (1 at k = 2) | the multiplicity of λ in χ_L(T_p); `DivideByRoot` divides χ by (x − λ)^{r_eis} |
| `eis_rational` | `true` at k = 2 (the constant function, a single rational system); `false` at k > 2 | `false` makes the read stop at `root = "general_case"`, `p26 = "not_run"` (l. 1056–1060) |
| `k_weight` | `k` | λ_p = 1 + p^{k−1} (l. 963); at k = 2 this is p + 1 |
| `full_algebra` | `false` (the read set omits p \| D) | `ReadLocal` does not read this field (grep: only `HeckeZRecord.cpp` and `HeckeZLocalValidation.cpp` set it). Set it for the record's sake |
| `rat` | absent (`present = false`) | there is no HZ-RAT on a Brandt lattice. The θ candidate is skipped and only the T_p candidates run |
| `allow_bad_primes` | `false` | U_p (p \| D) is not exported |

`by_theory` (l. 945) needs N = 1, so it never fires at N = D ≥ 2.

## 6. k > 2: the integral basis (phase 2: option (a) implemented, changelog item 2)

`symn.py` computes the T_ℓ over K = ℚ(√a), in a K-basis of ⊕_c V^{Γ_c}. A ℚ-model V^φ exists for even k
(`q_structure_report`), but no ℤ-basis is given.

Phase 2 will do one of two things:
- **(a)** construct a Hecke-stable lattice. Start from the ℚ-model, take ℤ^d (its ℚ-coordinates, class blocks in the
  §1b order), and form the **Hecke-stable hull** Λ = ℤ[T_p : p ∈ ops]·ℤ^d (the smallest Hecke-stable lattice containing
  ℤ^d; HNF), check that every F_p is integral, and record the rule as `brandt_symn_int_canonical/v2`;
- **(b)** emit `status = "no_integral_basis"`, with `reason` and with `charpoly_Z` only.

The acceptance (char_ℤ = `symn.json`) is checked on whatever (a) covers. The report states the covered-cell count out of
66.

A lattice from (a) is **a** Hecke-stable lattice. It is not the canonical one: the integral structure of Sym^n at p | D
and at p | |Γ_x| is not fixed by it. So ReadLocal values on it are lattice-dependent at those primes (§7), and the records
say `canonical: false` (§1b).
- **ℓ = 2 reads depend on the hull choice.** For example D = 13, k = 12 has [Λ : ℤ^d] = 2^37 (*computed*). Another
  Hecke-stable lattice in the same ℚ-space gives other ℓ = 2 Smith data.

Odd k: V^{Γ_c} = 0 (−1 ∈ Γ_c acts by −1), giving `status = "rank0"`.

## 7. Caveats (binding for every consumer)

1. **Eisenstein-only `ReadLocal`.** The read is built around the Eisenstein ideal (λ_p = 1 + p^{k−1}). On Brandt
   lattices it covers the Mazur/Eisenstein reads only:
   - at k = 2, the constant function with T_p = p + 1, and the congruence module ℤ/num((q−1)/12) (HJ-6);
   - at k > 2 there is no Eisenstein system on the definite side (e = 0), so `eis_rational = false` and there is no root
     read. `ReadLocal` returns `root = general_case`, `p26 = not_run` before the annihilator is built
     (`HeckeZLocal.cpp:1056–1060`), so the L ⊕ L issue of item 7 does not arise at k > 2. Reads on k > 2 lattices are
     hull-dependent at ℓ = 2 and at ℓ | |Γ_x| (§6).
2. **η^B (cusp–cusp)** is not a `ReadLocal` output. It needs Lane B's own Smith route (`DescentSmith`, ℤ/ℓ^k with
   ℓ^k < 2^31) on the Gram matrix of the q-new module.
3. **ℓ | |Γ_x|.** The function lattice and its dual (the divisor lattice, F = Bᵀ) differ exactly at primes dividing
   some |Γ_x/±1| (the w_x-pairing is not perfect there; for D prime, ℓ ∈ {2, 3}).
   - Smith-type reads (`a`, `eta`, `C_T`) at such ℓ are lattice-dependent.
   - Lane B reports them on both lattices or flags them. The HJ-6 accept "v_p of the w_x/|Γ_x| Gram ratio = 0" is the
     check.
   - At ℓ ∤ 6·∏|Γ_x| the two reads must agree.
4. **Words.** Every value derived from these records is *computed (HACS ReadLocal on a JL lattice)*.
   - The record word `certified`, which `ReadLocal` can emit (`c3 = "certified"`, `root = "closes"`), is **not** carried
     into any JL claim.
   - Those words are [C] `sec:heckeZ` statements about HACS's H^1 lattice. A JL lattice needs a refereed [C] pre-release
     first (contract-first rule, plan §7.1, §7.3; Q3).
   - Our JSON writes `"tag": "computed"`.
5. **ℓ | D.** U_ℓ is not exported. T_ℓ is never appended at ℓ | DM (`ReadPrimes`).
6. **Word limit:** ℓ^K < 2^63 (`Zlk::Fits`); beyond that the result is `refused(word_modulus)`.
7. **Multiplicity 2: read L ⊕ L at k = 2 (binding).** `ReadLocal` assumes that each cusp eigensystem occurs twice, as in
   GL₂ H¹. The assumption sits in the `annihilator` lambda (`HeckeZLocal.cpp:1064–1078`): χ_L(T_p) is divided by
   (x − λ)^{r_eis} (`DivideByRoot`, l. 1072), and at odd ℓ the quotient must be a square (`MonicSqrt`, l. 1075).
   - **On L itself** (multiplicity 1), at odd ℓ:
     - `MonicSqrt` fails, so every candidate's annihilator is `not_exact`;
     - p26 becomes `"not_exact"` (l. 1096), so `eis_block_rank` is not computed;
     - every root read is `not_exact` and sets `inconsistent` (l. 1150–1155), giving `root = "inconsistent"` (l. 1217) and
       no C_T;
     - `v_gP_local` is never set, so `v_gP` has source `"none"` (l. 1214).
   - **Unaffected on L:** c3 / dim A′₁, mono and e. These run before the annihilator.
   - **The rule:** read **L ⊕ L** (each F_p block-diagonal diag(F_p, F_p), rank 2h) with `r_eis = 2·e_eis` (= 2), and,
     via `ReadCellLocal`, b1 = 2h (`HeckeExt/HeckeZLocalSource.cpp:141` asserts rank = b1). `d_target = d_algebra` is
     unchanged (ℚ[F_p ⊕ F_p] ≅ ℚ[F_p]).
   - **η appears twice** on L ⊕ L: each elementary divisor of the cusp-Eisenstein congruence occurs once per copy, so
     `eta` lists every L-value twice. Report the η of L as every second entry, or halve the multiplicities.
   - **ℓ = 2.** The annihilator is χ/(x − λ)^{r_eis} with no square root and is not sharp (l. 1077), so `v_gP_local` is
     never set. Without HZ-RAT, `v_gP < 0`, so `root = "open(precision)"` (l. 1224–1225), on L and on L ⊕ L alike. Lane B
     **refuses ℓ = 2 Mazur reads by name** (`refused(ell2_not_sharp)`, our word) or reads them by its own Smith route
     (item 2). Affected cells: Mazur at **q = 17** (num((q−1)/12) = 4) and **q = 41** (num = 10, ℓ = 2 of ℓ ∈ {2, 5}) among
     q ≤ 43. ℓ = 5 at q = 41 is read on L ⊕ L as usual.
   - **T_ℓ in P.** Only `ReadCellLocal` appends T_ℓ (`ReadPrimes`, `HeckeZLocalSource.cpp:138–139`). A direct
     `LatticeFromFreeZ` call does not, so the caller passes T_ℓ in P explicitly.

## 8. The B_11, k = 2 example in full (computed: `brandt.module(11)`, this session)

- h = r = 2, `gammas = [4, 6]` (the §1b order: K1 already separates the two classes), N = 11, n = 0.
- Row sums are ℓ + 1. The symmetry 6·F_12 = 4·F_21 holds on every op.
- Traces: (p + 1) + a_p(11a), with a_2 = −2, a_3 = −1, a_5 = 1.
- `d_algebra` = 2, `e_eis` = 1.

| p | F_p (rows) | canonical text | `F_fnv` | char_ℤ (low → high) |
|---|---|---|---|---|
| 2 | [[1, 2], [3, 0]] | `1,2;3,0` | `0x12097637b2c137e0` | [−6, −1, 1] = (x−3)(x+2) |
| 3 | [[2, 2], [3, 1]] | `2,2;3,1` | `0xfee36f1e9928151a` | [−4, −3, 1] = (x−4)(x+1) |
| 5 | [[4, 2], [3, 3]] | `4,2;3,3` | `0x825d45ddc0a53cba` | [6, −7, 1] = (x−6)(x−1) |

The record is shown truncated to three ops; phase 2 writes all primes < 50 except 11. It sits in `data.free_block_z`, next to
`data.schema` and `data.writer = "python:brandt_export@<commit>"`:

```json
{"schema": "langlandscape_brandt/v2", "status": "ok", "D": 11,
 "M": 1, "k": 2, "n": 0, "N": 11, "rank": 2,
 "ops": [2, 3, 5],
 "F": [[["1","2"],["3","0"]], [["2","2"],["3","1"]], [["4","2"],["3","3"]]],
 "F_fnv": ["0x12097637b2c137e0", "0xfee36f1e9928151a", "0x825d45ddc0a53cba"],
 "proof": ["exact_count", "exact_count", "exact_count"],
 "basis_rule": "brandt_k2_canonical/v2: b_j = 1_{c_j}, c_j the j-th left-ideal class; classes sorted ascending by (|Gamma_c|, (r_c(1),...,r_c(20))), r_c(m) = #{x in O_r(I_c) : nrd x = m} (x, -x both counted); ties listed in order_ties, order within a tie unspecified",
 "order_ties": [], "basis_fnv": "<FNV of class_keys>", "phi_fnv": "-", "saturation": "exact_basis", "q0_key": "-", "bound_basis": "-",
 "bits_F": [2, 2, 3], "gammas": [4, 6], "d_algebra": 2, "e_eis": 1,
 "charpoly_Z": [["-6","-1","1"], ["-4","-3","1"], ["6","-7","1"]],
 "lattice": "functions", "convention": "column: T_p b_j = sum_i F[i][j] b_i; F = B_p (B[c][c'] = #neighbours of c in c'); row sums l+1",
 "origin": "jl:brandt.py(theta,cross-checked)", "tag": "computed"}
```

For HJ-6 at D = 11 (Mazur): ℓ = 5, any K ≥ 2, read on **L ⊕ L** (rank 4, §7 item 7). Through `ReadCellLocal`: P = [2, 3],
b1 = 4, and `ReadPrimes` appends T_5, so 5 must be in `ops`. Through a direct `LatticeFromFreeZ` call: P = [2, 3, 5].
Use `ReadOptions{d_target = 2, r_eis = 2, eis_rational = true, k_weight = 2, full_algebra = false}`. Expected: C_T = 5¹,
with η = [1, 1] (5¹ twice). This is *expected*, not yet run on L ⊕ L.

> **Correction (v1 note, 2026-11-15; reported by Lane B's HJ-6-min run).** The root (C_T) read of `ReadLocal` on the
> Brandt lattice L **itself** returns `root=inconsistent`: `ReadLocal` assumes that cusp forms appear with multiplicity 2,
> as in GL₂ H¹, while the Brandt module carries each cusp eigensystem once. So "C_T = 5¹ with r_eis = 1 on L" does **not**
> hold. Lane B reads L ⊕ L (each F_p block-diagonal, rank 2h) with r_eis = 2·e_eis and b1 = 2h instead. §7 item 7 has
> the source lines, the ℓ = 2 rule and the η doubling; the example above is already stated for L ⊕ L.
> The other reads on L itself (dim A′₁, mono, e) work as specified. No required field changed for this correction, and
> `e_eis` keeps its meaning (the multiplicity of the Eisenstein system in L).

## 9. OPEN items

1. The k > 2 integral basis rule (§6): settled as (a), the Hecke-stable hull (changelog item 2). A canonical k > 2
   lattice (independent of `symn.py`'s representatives, `canonical: true`) is still open.
2. `d_target` for M > 1 (old forms) and for P ⊊ ops. Phase 2 computes `d_algebra` exactly on `ops`. A different P needs
   recomputation.
3. Whether `F` should also be emitted flat. The nested rows match the console's `module_Z().ops[].F`
   (`061_s25_module_z_exact.expected` l. 5), so one parser covers both; Lane B flattens. This is a choice, not a defect.
4. `basis_fnv`: its definition here (class-key text) is ours. HACS's `PackedFnv(B)` has no analogue on the definite side.

## 10. Changelog

- **v1, 2026-11-15 (90edfed8):** frozen.
- **v1, phase-2 notes (additive; no required field changed).**
  1. **k = 2 matrices.** The k = 2 matrices are computed by theta series:
     B_p[i][j] = #{x ∈ conj(I_i) I_j : nrd x = p·N_i N_j} / |Γ_j| (PARI `qfrep`).
     - `brandt.py`'s O(p⁴) neighbour enumeration takes about 20 s per class at p ≈ 30.
     - For every p < 14, the export asserts that the theta result equals `brandt.py`'s `T(p)`.
     - `origin` = `"jl:brandt.py(theta,cross-checked)"`.
     - The values and the convention are unchanged.
  2. **k > 2: §6 option (a) is implemented.** `basis_rule` = `brandt_symn_int/v1`: Λ = ℤ[T_p : p ∈ ops]·ℤ^d, taken in
     symn.py's rational model and written in an HNF basis.
     - It needs all of `ops`, so the lattice depends on the `ops` list.
     - `proof` = `"exact_rational_model"`.
     - New optional field `basis_in_Q_coords`: the columns of the basis in symn.py's ℚ-coordinates.
  3. **Coverage rule of §5 for k > 2 cells.** `ops` = the primes **< 20** with p ∤ D, not the primes < 50: symn.py's
     neighbour tables are O(ℓ⁴). Larger primes are added on request. The meaning of `ops` is unchanged.
  4. **New optional fields:** `class_keys` in the record, and `data.checks` (the per-record acceptance results) next to
     `data.free_block_z`.
  5. **Class order (corrected by item 8).** At D = 17 and D = 41, `definite_local.json` (HJ-A2) lists the classes in a
     different order from these records: its matrices are a permutation conjugate of ours, with `gammas` [6, 2] against
     [2, 6]. This is **not** an error of HJ-A2. `brandt.module(D)`'s BFS order is process-dependent (§1b), and HJ-A2's
     order is another valid output of it. The original text of this item called it a deviation from the rule; that was
     wrong.
  6. **Exporter location (coordinator, 2026-11-15).** The exporter moved from `code/hacs/jl/` to
     `code/python/langlandscape/hacs_bridge/brandt_export.py` (GPL, our scheme), because it uses PARI (`qfrep`), and HACS's
     rule "no external CAS in HACS" (`code/hacs/CLAUDE.md`, plan §6.3) keeps PARI out of `code/hacs/`. The format is unchanged.
  7. **§8 correction (Lane B, HJ-6-min).** ReadLocal's root read on L gives `root=inconsistent` (it assumes multiplicity-2
     cusp forms); read L ⊕ L with r_eis = 2. Lane B's independent F_fnv recomputation matches all 74 records (0 mismatches).
- **v2, 2026-11-15 (schema bump; §1b).**
  8. **Canonical class order.** The class order is now the required writer rule of §1b: ascending (|Γ_c|, θ_c), with θ_c
     the first 20 representation numbers of O_r(I_c) and ties in `order_ties`. `schema` = `langlandscape_brandt/v2`;
     `basis_rule` = `brandt_k2_canonical/v2` / `brandt_symn_int_canonical/v2`. k > 2 records carry `canonical: false`
     and their own `convention` string. All records were regenerated (new writer,
     commit and date). The `F_fnv` values of the v1 records (f54b109e, e5911cab) are **superseded** wherever the order
     changed: 7 of 74 records, the k = 2 cells D = 19, 23, 29, 31, 37, 41, 43 (*computed*; the other 67, including D = 17 and every k > 2 cell, keep their `F_fnv`). The determinism test runs D = 17, 37, 41 in two fresh processes and in a warmed process: identical `F_fnv`. The k > 2 probe D = 11, k = 12 also gave identical `F_fnv` and `charpoly_Z` in two fresh processes and a warmed one, but `canonical: false` stays: that is not guaranteed.
