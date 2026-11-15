<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# HACS checks we can run now (HACS 0.2.1, no new code)

Status: plan, written 2026-11-14 on `wip-plan`. Scope: tests and checks that need only a freshly built HACS 0.2.1 binary,
HACS console scripts (`hacs --script f.oc`), the CLI and campaign driver, and short throwaway post-processing in Python
(sympy 1.14, PARI 2.15.4 through `cypari2`). There is **no `gp` and no `sage`** on this node. PARI is used only through
`cypari2`, as `code/python/langlandscape/pari.py` already does.

Claims carry their status: *computed* (with the binary named), *cited*, *expected* (a prediction that has a source of truth),
or *exploratory* (no prediction yet).

**Probe results.** Before this file was written, every RUN-NOW script was run end to end on the earlier HACS 0.2.1 CUDA build
(`Langlandscape-wt/s03-ct/code/hacs/build/hacs`, same version string, `commit unknown`). That build directory has since been
removed. The probes ran with `ENGINE_THREADS=4` while four `--all` shards were running on the fresh binary, so the wall times
below are upper bounds. The fresh binary was **not** used for any probe. Probe results are labelled *probe (old s03-ct binary)*. They
show what to expect; they are not results of record. Results of record come only from the RUN-NOW worker's run on the fresh
binary.

## 0. Set-up (shared by every check)

```bash
export B=/home/janosch/dev/Langlandscape-wt/plan/code/hacs/build/minimal/hacs      # the fresh 0.2.1 binary (CUDA build)
export PYLL=/home/janosch/dev/Langlandscape-wt/impl/code/python                     # our langlandscape package (Brandt, symn)
export HACS_SRC=/home/janosch/dev/Langlandscape-wt/plan/code/hacs                   # the HACS tree the binary was built from
export W=<your scratchpad>/checks-now; mkdir -p "$W"; cd "$W"                       # never inside the repo
export ENGINE_THREADS=8                                                             # scripts below pin 4 for their own HACS calls
$B --version            # record this line in every result
```

**HACS limits that shape the grids.** These were checked against `docs/console/console.md` and the probes.

| verb / front end | ring | limits |
|---|---|---|
| `descent(N, n, primes)` | `Z` | N ≤ 300, n ≤ 60, ψ(N)(n+1) ≤ 300; Hecke primes 1..6, ≤ 97, ∤ N, sum ≤ 100; `U_p` for p \| N refused |
| `hecke_structure(N, n, "full"\|"anemic")` | `Z` | the same limits as `descent`; `C_T` = Eisenstein vs cuspidal congruence module |
| `level_n(N, n, ell, primes)` | `F_ell` | 5 ≤ ell ≤ 65521 prime, N ≤ 100, ψ(N)(n+1) ≤ 1000, ≤ 6 primes ≤ 97; **`U_p` for p \| N allowed** |
| `nebentypus(N, m, n, ell, primes)` | `F_ell` | the same limits, ≤ 4 primes ≤ 13, ord χ \| ell − 1 |
| `--campaign` with `coefficient_ring = Z` | `Z` | **no console limit**: descent cells (`parts = groups,hecke`) and `structure = hecke` cells at any level (dry run verified at N = 433, 1009, 2017, 4001) |
| `HeckeLevelNCurveValidation` hooks | `F_2`, `F_3` | prime levels up to 10⁵ (Calegari–Emerton grids) |

Conventions used below: `descent` charpolys `.exact` are listed high → low; `level_n` charpolys are listed low → high
(constant term first). Weight k = n + 2. For k > 2 we have H¹(Γ₀(N); Sym^n) = 2·S_k(Γ₀(N)) ⊕ E_k(Γ₀(N)) as Hecke modules
(Eichler–Shimura). For k = 2 the Eisenstein part has dimension #cusps − 1.

**Lesson from the probes** (*probe (old s03-ct binary)*). The Eisenstein factor of char(T_q) is **not** (x − 1 − q^{k−1})^e in general.
At 9 | N or 16 | N it carries twisted eigenvalues χ(q) + χ̄(q)q^{k−1}. Example: `descent(9, 0, [2])` gives
`(X + 3)(X − 3)^2`. The scripts therefore take the Eisenstein factor from PARI's Eisenstein space (`mfinit([N,k],3)`).

## 1. Overview

**RUN-NOW** marks the checks for the Sonnet worker: P1, no new code, each under 10 minutes, fully copy-pasteable (§2).

| ID | category | what | priority | est. runtime | RUN-NOW |
|---|---|---|---|---|---|
| A1 | A | acceptance battery: strict golden, Hecke gate, JL-relevant validations, device validations, CPU = GPU digests, regression diffs vs 0.2.0 | P1 | 5–8 min | **RN-1** |
| A2 | A | `--all` in 4 shards (`run_all_sharded.sh`) | P1 | ≈ 8 min (ref.), 13 min/shard alone | already being run by the build worker: read its `SHARDED_ALL` line |
| A3 | A | `--all-full` | P3 | 1 h 45 – 3 h 40 | |
| A4 | A | cross-binary identity: the RN scripts' `@@` lines and campaign `record_fnv1a64` on two builds | P1 | ≤ 15 min | |
| A5 | A | CPU-only build vs CUDA build (needs `cmake --preset cpu-only`, a separate build) | P2 | build + 10 min | |
| A6 | A | regression of the HACS-side JL answers of 2026-11-13 (`docs/jl_exchange/hacs-answers/*`, binary 0.2.0) | P2 | ≈ 5 min | part in RN-1 |
| A7 | A | regenerate `docs/latex/cli_manual_runs/*.txt` and diff, ignoring timings | P2 | ≈ 3 min | |
| A8 | A | slow descent validations (`IntegralDescent*SlowValidation`, `HeckeZLocalCensusXcheck`) | P3 | ≈ 30–60 min | |
| B1 | B | Eichler class number h(p) = rank H¹(Γ₀(p);ℤ)/2 + 1/2, mass (p−1)/24 | P1 | in RN-3 | **RN-3** |
| B2 | B | Brandt charpolys (Python) vs exact HACS char_ℤ(T_q), weight 2, p ≤ 199 | P1 | ≈ 5.5 min | **RN-3** |
| B3 | B | Mazur: C_T(Γ₀(p), wt 2, anemic) = ℤ/num((p−1)/12), p ≤ 199 | P1 | ≈ 3 min | **RN-2** |
| B4 | B | JL with Sym^{k−2}, k = 4..12, D ≤ 43: Brandt(V_k) vs HACS | P1 | ≈ 3 min | **RN-4** |
| B5 | B | level-1 Eisenstein C_T = ℤ/num(B_k/2k), k = 12..32 | P1 | ≈ 15 s | **RN-2** |
| B6 | B | C3/C5 re-run of det(Ψ\*Ψ) on a larger (M,k,q) grid (reuse `s03_h1_rerun.py`) | P2 | ≈ 5 min | |
| B7 | B | Ribet level raising: ℓ \| q^{k−2}(q+1)² − a_q² ⇒ q-new eigensystem ≡ f mod ℓ (HACS charpolys) | P2 | ≈ 5 min | |
| B8 | B | Ihara at SL₂(ℤ[1/p]): ker α = 0, torsion of coker α only Eisenstein at ℓ = k+1 (re-run task1 `cell.py` at new p) | P2 | 1–45 s/cell | |
| B9 | B | T6 ±1 diamond exponent at more (p,k) (Python `IharaCase`) | P3 | minutes | |
| B10 | B | T05-1 sign: a_q = +λ(Π_q) via HACS `level_n` U_q mod ℓ vs Python `pi_ell` | P2 | ≈ 2 min | |
| B11 | B | congruence modules at small composite levels (`hecke_structure` full/anemic, Gorenstein flags) | P2 | ≈ 5 min | |
| B12 | B | T5 / H3 inputs: η_f(q) and old/new congruence at the T5 triples from exact charpolys | P2 | ≈ 5 min | |
| B13 | B | Mazur's T/I at 2 and 3 (p ≡ 1 mod 8, mod 9): bound readings vs exact, Calegari–Emerton | P3 | — | |
| B14 | B | **T4** (q = 3, p = 17, branch through Δ): ord₁₇ c₃ at k = 12, 28, 44, 60 | P1 | ≈ 5 s | **RN-6** (bonus) |
| C1 | C | exact HACS `descent` char_ℤ(T_q) vs PARI on Γ₀(M), M ≤ 60, k ≤ 12 (232 cells) | P1 | ≈ 6 min | **RN-5** |
| C2 | C | HACS `level_n` mod ℓ (T_q **and U_p, p \| N**) vs PARI, N ≤ 100 | P1 | ≈ 10–15 min (PARI-bound) | |
| C3 | C | `nebentypus` vs PARI `mfinit([N,k,χ])`: is Conrey N.m PARI's χ or χ̄? (feeds T05-2) | P2 | ≈ 1 min | |
| C4 | C | `forms_algebra(k, ell)` / `hida_lambda` vs PARI level-1 charpolys mod ℓ / mod ℓ^W | P3 | ≈ 1 min | |
| C5 | C | `descent(...).module_Z()` exact F block vs PARI `mfheckemat` up to conjugacy (char + Smith of T − a) | P3 | ≈ 2 min | |
| D1 | D | `--bench hecke/cohom` CPU vs `ENGINE_DEVICE=gpu`, n ∈ {128, 256, 1000} | P2 | ≈ 2 min | |
| D2 | D | descent campaign Γ₀(500), n = 20 (D = 18900): CPU (16, 32 threads) vs GPU, plus digest identity | P2 | ≈ 3–5 min | |
| D3 | D | thread scaling of the RN-5 grid (`ENGINE_THREADS` = 1, 4, 16, 32) | P3 | ≈ 20 min | |
| D4 | D | `CudaImmaElimValidation` bench arm, `DescentSmithGpuValidation` timing arms | P3 | ≈ 2 min | |
| E1 | E | Mazur C_T beyond the console limit: `structure = hecke` campaign, p ∈ {211, …, 293, 433, 1009} | P2 | unknown (241, 293: ≈ 1 min each) | |
| E2 | E | descent campaigns at p ∈ {1009, 2017, 4001, 8009}: rank = 2h − 1 (Eichler) and Eisenstein congruence n \| χ_cusp(1+q) | P2 | minutes (D = p+1) | |
| E3 | E | `HeckeLevelNCurveValidation` large arms (prime N up to 10⁴ / 3·10⁴, mod 2, 3; CE theorems) | P2 | 1 s – 72 min | |
| E4 | E | B4 beyond the console bound: descent campaign at D ∈ {47, …, 101}, k ≤ 12 vs Python `symn` | P3 | ≈ 10 min | |
| E5 | E | `level_n` at N ≈ 100 with large ℓ (≤ 65521) and many weights: mod-ℓ Eisenstein congruences | P3 | ≈ 2 min | |

Counts: A 8, B 14, C 5, D 4, E 5 (36 checks). RUN-NOW: RN-1 … RN-5, plus the tiny RN-6.

---

## 2. RUN-NOW (exact instructions for the Sonnet worker)

General rules:
- Run everything in `$W` (see §0), one check after the other. Do not run them in parallel: the timings are part of the
  result.
- Save every stdout/stderr as `$W/<id>.log` and record `$B --version`, the date, and the wall time of each step
  (`/usr/bin/time -v` or `time`).
- Do not commit anything. Report per check: PASS/FAIL, the summary line, and any deviation from "expected".
- A FAIL is a finding, not something to fix. Re-run once; if it fails again, stop that check and report it.

### RN-1 = A1: acceptance battery of the fresh binary (≈ 5–8 min)

Sources of truth: the golden reference (`src/hacs/Golden/GoldenReference.inc`), the frozen console transcripts, the
validations' own oracles (`docs/validation-catalogue.md`), and the stored 0.2.0 outputs in
`docs/jl_exchange/hacs-answers/task1_v6/data/`.

```bash
cd "$W"
# (1) strict golden reference (≈ 30 s on the reference machine): exit code 0 expected
GOLDEN_STRICT=1 $B GoldenRegressionValidation > a1_golden.log 2>&1; echo "golden exit=$?"
# (2) the Hecke acceptance gate (HeckeBenchmarkSmoke is slow tier, so it is not in --all) + the four determinism checks
$B HeckeEndToEndValidation HeckeBadPrimeValidation HeckeBenchmarkSmoke EngineDeterminismValidation \
   HeckeExtDeterminismValidation ConsoleDeterminismValidation > a1_gate.log 2>&1; echo "gate failures=$?"
# (3) the validations behind the verbs this file uses (level N, nebentypus, descent at level N, Hecke structure, console)
$B ConsoleScriptValidation HeckeLevelNValidation HeckeLevelNHeilbronnValidation HeckeLevelNCurveValidation \
   HeckeNebentypusValidation IntegralDescentLevelNValidation IntegralDescentHeckeValidation HeckeZRecordValidation \
   > a1_jl.log 2>&1; echo "jl failures=$?"
# (4) device validations (a CPU-only build prints [SKIP] and passes; on this CUDA build they must RUN, not skip)
$B CudaBitIdentityValidation EngineCrossDeviceValidation DescentSmithGpuValidation > a1_gpu.log 2>&1; echo "gpu failures=$?"
grep -c '\[SKIP\]' a1_gpu.log      # expected 0 on the RTX PRO 6000 node
```

(5) CPU and GPU give the same records (digests must be identical). Expected `H^1` of (1,30), from
`docs/latex/cli_manual_runs/env_descent_gpu.txt`: `Z^5 + Z/2 + Z/2 + Z/2 + Z/2^2 + Z/2^2 + Z/2^2 + Z/3 + Z/3 + Z/3^2 + Z/5^2 + Z/29`.

```bash
cat > a1_dev.oc <<'EOF'
# RN-1 step 5: the same descent records on the CPU and on the GPU route must have the same record_fnv1a64.
set coefficient_ring = "Z";
for c in [[1, 30], [11, 10], [37, 4], [30, 2]] {
  d = descent(c[0], c[1]);
  print("@@DEV " + json([c[0], c[1], d.status, d.digest, d.groups[1]]));
}
EOF
ENGINE_THREADS=4 $B --script a1_dev.oc > a1_cpu.txt 2>&1; echo "cpu exit=$?"
ENGINE_THREADS=4 ENGINE_DEVICE=gpu ENGINE_GPU_SMITH2K_MIN=0 $B --script a1_dev.oc > a1_gpu.txt 2>&1; echo "gpu exit=$?"
grep GPU_SMITH2K a1_gpu.txt          # expected: device=<k> with k > 0 and fallbacks=0
diff <(grep '^@@DEV' a1_cpu.txt) <(grep '^@@DEV' a1_gpu.txt) && echo "DEVICE-IDENTICAL"
```

(This `.oc` was not probed: the earlier binary had already been removed. It uses only members documented in `console.md`:
`DescentRecord.digest`, `.status`, `.groups`. If it errors, report the message.)

(6) regression against the 0.2.0 answers (expected byte-identical `@@` lines; *probe (old s03-ct binary)*: identical on the earlier
0.2.1 build, 109/109 lines).

```bash
X=$HACS_SRC/docs/jl_exchange/hacs-answers/task1_v6
for s in hacs_level_n_xcheck hacs_level_n_xcheck_ext; do
  ENGINE_THREADS=4 $B --script $X/scripts/$s.oc | grep '^@@' > a1_$s.out
  diff <(grep '^@@' $X/data/$s.out) a1_$s.out > /dev/null && echo "$s IDENTICAL" || echo "$s DIFFERS"
done
```

(7) the campaign record hashes of the manual's worked example (expected: the six `record_fnv1a64` values in
`docs/latex/cli_manual_runs/campaign_z_run.txt`, e.g. `desc_N11_n2_…` → `0xa77d93e005bf411d`).

```bash
$B --campaign $HACS_SRC/docs/latex/cli_manual_runs/descent_small.spec --output a1_descent_small --quiet
diff <(grep '^desc_' $HACS_SRC/docs/latex/cli_manual_runs/campaign_z_run.txt | cut -f1-10) \
     <(tail -n +2 a1_descent_small/summary.tsv | cut -f1-10) && echo "CAMPAIGN-IDENTICAL"
```

PASS = steps 1–4 report 0 failures, step 5 prints `DEVICE-IDENTICAL`, step 6 prints two `IDENTICAL`, and step 7 prints
`CAMPAIGN-IDENTICAL`.

### RN-2 = B3 + B5: Eisenstein congruence modules over ℤ (≈ 3 min + 15 s)

**B3, the expected values.**
- C_T(Γ₀(p), weight 2, anemic Hecke algebra) = ℤ/n with n = num((p−1)/12). Sources:
  - *cited*: Mazur 1977, Ch. II (Prop. II.9.7; numbering not re-checked), T/I ≅ ℤ/n;
  - the definite side: `code/results/s03/T1.json`, |Φ^comb| = 5, 11, 3, 25, 65 for q = 11, 23, 37, 101, 131;
  - HACS's own `060_s25_hecke_structure` transcript, `(11,0) anemic: C_T certified:0x5`.
- When HACS certifies only bounds, the per-prime bounds `G3.C_T.ell=ℓ.lower_v ≤ v_ℓ(n) ≤ upper_v` must hold.
- *Probe (old s03-ct binary)*, p ≤ 199:
  - 36 of 42 primes were certified, and all 36 equal n (including n = 6, 8, 9, 16 at p = 73, 97, 109, 193);
  - p = 13 gives `C_T = "-"` (genus 0, n = 1);
  - p = 113, 157, 191, 197, 199 give `upper_bound_certified`, consistent with n prime by prime;
  - for example, at p = 113: `2:[2,2]` exact, `7:[1,1]` exact, `3:[0,3]` contains v₃ = 0.

**B5, the expected values.**
- C_T(level 1, weight k) = ℤ/num(B_k/2k). Sources:
  - *cited*: Ribet 1976 and Mazur–Wiles, the Eisenstein congruence;
  - HACS's transcript `060`, which pins k = 12 (`0x2b3` = 691) and k = 24 (`0xe16a13b` = 103·2294797).
- *Probe (old s03-ct binary)*: equal for k = 12, …, 28 and k = 32. k = 14 gives `"-"` (num = 1).

```bash
cd "$W"
cat > b3_mazur.oc <<'EOF'
# CHECK B3 (RUN-NOW 2a): Mazur's Eisenstein congruence module at prime level p, weight 2 (n = 0), anemic Hecke algebra over Z.
# Expected: C_T = Z/num((p-1)/12)  (Mazur 1977, Prop. II.9.7; definite side: our T1, |Phi^comb| = num((q-1)/12)).
set coefficient_ring = "Z";
PRIMES = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
          127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199];
for N in PRIMES {
  E = hecke_structure(N, 0, "anemic");
  print("@@HZ " + json([N, E.status, E.C_T, E.generation, E.body]));
}
EOF
cat > b3_post.py <<'EOF'
#!/usr/bin/env python3
"""Post-process CHECK B3: compare HACS C_T (anemic, n = 0, prime level p) with Mazur's num((p-1)/12), prime by prime."""
import json, re, sys
from math import gcd
import sympy as sp
ok, n_cert, n_bound = True, 0, 0
for line in open(sys.argv[1]):
    if not line.startswith("@@HZ "):
        continue
    N, status, CT, gen, body = json.loads(line[5:])
    n = (N - 1) // gcd(N - 1, 12)
    per = {}
    for b in body:
        m = re.match(r"G3\.C_T\.ell=(\d+)\.(lower_v|upper_v|status)=(.*)", b)
        if m:
            per.setdefault(int(m[1]), {})[m[2]] = m[3]
    verdicts = []
    for ell in sorted(set(per) | set(sp.primefactors(n))):
        v = sp.multiplicity(ell, n) if n > 1 else 0
        d = per.get(ell)
        if d is None:                       # ell not a candidate prime of the record: HACS says v_ell(C_T) = 0
            good = v == 0; verdicts.append(f"{ell}:absent(v={v})" + ("" if good else "!!"))
        else:
            lo, hi = int(d["lower_v"]), int(d["upper_v"])
            good = lo <= v <= hi and (d["status"] != "certified" or lo == v == hi)
            verdicts.append(f"{ell}:[{lo},{hi}]{'=' if d['status']=='certified' else '~'}v={v}" + ("" if good else "!!"))
        ok &= good
    if CT.startswith("certified:"):
        n_cert += 1; good = int(CT.split(":")[1], 16) == n; ok &= good
    elif CT == "-":
        good = n == 1                       # genus 0: no cusp forms, no congruence module
    else:
        n_bound += 1; good = None
    print(f"p={N:4d} num((p-1)/12)={n:6d} C_T={CT:24s} {'OK' if good else ('BOUNDS-CONSISTENT' if good is None else 'MISMATCH')}  {' '.join(verdicts)}")
print(f"certified={n_cert} bounded={n_bound}  ALL CONSISTENT: {ok}")
sys.exit(0 if ok else 1)
EOF
cat > b5_bernoulli.oc <<'EOF'
# CHECK B5 (RUN-NOW 2b): Eisenstein congruence module at level 1, weight k = n + 2 (full Hecke algebra over Z).
# Expected: C_T = Z/num(B_k / 2k) for 12 <= k <= 32 (Ribet / Mazur-Wiles; HACS's own 060 script pins k = 12 and k = 24).
set coefficient_ring = "Z";
for n in [10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30] {
  E = hecke_structure(1, n);
  print("@@HZ1 " + json([n + 2, E.C_T]));
}
EOF
cat > b5_post.py <<'EOF'
import json, sys
import sympy as sp
ok = True
for line in open(sys.argv[1]):
    if not line.startswith("@@HZ1 "): continue
    k, CT = json.loads(line[6:])
    want = abs(sp.numer(sp.bernoulli(k) / (2 * k)))
    got = int(CT.split(":")[1], 16) if CT.startswith("certified:") else (1 if CT == "-" else None)
    good = got == want; ok &= good
    print(f"k={k:3d} num(B_k/2k)={want} = {dict(sp.factorint(want))}  HACS C_T={CT}  {'OK' if good else 'MISMATCH'}")
print("ALL AGREE:", ok); sys.exit(0 if ok else 1)
EOF
time (ENGINE_THREADS=4 $B --script b3_mazur.oc > b3.out 2>&1); echo "exit=$?"
python3 b3_post.py b3.out | tee b3.log          # PASS = last line "ALL CONSISTENT: True", no MISMATCH line
time (ENGINE_THREADS=4 $B --script b5_bernoulli.oc > b5.out 2>&1); echo "exit=$?"
python3 b5_post.py b5.out | tee b5.log          # PASS = "ALL AGREE: True"
```

In the report, list the non-certified primes with their per-ℓ bounds. These are inputs for E1 and B13.

### RN-3 = B1 + B2: Eichler class numbers and Brandt vs Γ₀(p), weight 2 (≈ 5.5 min, mostly Python)

What is checked, for every prime 11 ≤ p ≤ 199 and q ∈ {2, 3, 5, 7}:
- rank H¹(Γ₀(p); ℤ) = 2h(p) − 1, i.e. g(X₀(p)) = h(p) − 1;
- the Eichler class number formula h(p) = (p−1)/12 + (1 − (−4/p))/4 + (1 − (−3/p))/3;
- the mass Σ 1/|Γ_x| = (p−1)/24;
- char_HACS(T_q) · (x − 1 − q) = char_Brandt(T_q)², exactly over ℤ. This is JL at the level of charpolys:
  H¹ = 2·S₂ + Eis, and the Brandt module = S₂ + Eis.

Sources of truth:
- the Eichler formula, *cited*: Eichler's class number formula (e.g. Voight 2021, the chapter on the Eichler mass and class number formulas; theorem number not re-checked);
- `code/python/langlandscape/brandt.py`, already validated against PARI in `code/results/s01/brandt_w2.json`;
- HACS `descent`.

*Probe (old s03-ct binary)*: 42 of 42 primes pass every item (e.g. p = 193: h = 16, rank 31). HACS took 13.7 s, Python 5.3 min.

```bash
cd "$W"
cat > b1_brandt_vs_hacs.py <<'EOF'
#!/usr/bin/env python3
"""CHECK B1+B2 (RUN-NOW 3): Eichler class number + Brandt charpolys (Python, definite side) vs exact char_Z(T_q) on
H^1(Gamma_0(p); Z) from HACS `descent` (GL_2 side).  JL at the level of charpolys, weight 2, prime level p:
   char_HACS(T_q) * (x - 1 - q)  ==  char_Brandt(T_q)^2       (H^1 = 2 x cusp + 1 Eisenstein;  Brandt = cusp + Eisenstein)
   rank H^1(Gamma_0(p); Z) == 2 h(p) - 1,   h(p) = (p-1)/12 + (1 - (-4/p))/4 + (1 - (-3/p))/3   (Eichler)
Usage: python3 b1_brandt_vs_hacs.py HACS_BINARY PYTHONPATH_OF_langlandscape p1 p2 ...
"""
import json, os, subprocess, sys, tempfile, time
from fractions import Fraction
import sympy as sp

hacs, pypath, primes = sys.argv[1], sys.argv[2], [int(a) for a in sys.argv[3:]]
sys.path.insert(0, pypath)
from langlandscape import brandt  # noqa: E402

X = sp.symbols("x")
QS = [2, 3, 5, 7]

def leg(a, p):
    return int(sp.jacobi_symbol(a % p, p))

def eichler_h(p):
    return Fraction(p - 1, 12) + Fraction(1 - leg(-4, p), 4) + Fraction(1 - leg(-3, p), 3)

oc = 'set coefficient_ring = "Z";\n'
for p in primes:
    oc += (f'd = descent({p}, 0, {json.dumps(QS)});\n'
           f'print("@@D " + json([{p}, d.status, d.groups_inv[1].free_rank]));\n'
           f'for c in d.charpoly {{ print("@@CP " + json([{p}, c.p, c.exact, c.determined])); }}\n')
with tempfile.NamedTemporaryFile("w", suffix=".oc", dir=".", delete=False) as f:
    f.write(oc); fn = f.name
t0 = time.time()
r = subprocess.run([hacs, "--script", fn], capture_output=True, text=True, env=dict(os.environ, ENGINE_THREADS="4"))
t_hacs = time.time() - t0
assert r.returncode == 0, r.stderr[-2000:]
rank, cp = {}, {}
for line in r.stdout.splitlines():
    if line.startswith("@@D "):
        p, st, rk = json.loads(line[4:]); assert st == "ok", (p, st); rank[p] = rk
    elif line.startswith("@@CP "):
        p, q, ex, det = json.loads(line[5:]); assert det, (p, q); cp[(p, q)] = [int(c) for c in ex]  # high -> low
ok_all, rows = True, []
for p in primes:
    t = time.time(); m = brandt.module(p, 1)
    h_e = eichler_h(p)
    row = {"p": p, "h_brandt": m.h, "h_eichler": str(h_e), "rank_H1_hacs": rank[p],
           "mass_ok": m.mass == Fraction(p - 1, 24), "h_ok": h_e == m.h, "rank_ok": rank[p] == 2 * m.h - 1}
    for q in QS:
        B = sp.Poly(list(reversed(brandt.charpoly_coeffs(m.T(q)))), X)   # charpoly_coeffs is constant-first
        H = sp.Poly(cp[(p, q)], X)
        row[f"jl_T{q}"] = (H * sp.Poly(X - 1 - q, X)) == B ** 2
    row["ok"] = row["mass_ok"] and row["h_ok"] and row["rank_ok"] and all(row[f"jl_T{q}"] for q in QS)
    row["py_s"] = round(time.time() - t, 2)
    ok_all &= row["ok"]; rows.append(row); print(json.dumps(row), flush=True)
print(json.dumps({"check": "B1+B2", "primes": primes, "all_ok": ok_all, "hacs_wall_s": round(t_hacs, 2)}))
sys.exit(0 if ok_all else 1)
EOF
P=$(python3 -c "import sympy; print(' '.join(map(str, sympy.primerange(11, 200))))")
time python3 b1_brandt_vs_hacs.py "$B" "$PYLL" $P 2>&1 | grep -v 'PARI stack' | tee b1.log
# PASS = exit 0 and last line {"check": "B1+B2", ..., "all_ok": true, ...}
```

### RN-4 = B4: JL with Sym^{k−2} coefficients (≈ 3 min)

What is checked, for D prime in {2, …, 43}, k ∈ {4, …, 12} even with (D+1)(k−1) ≤ 300, and q the first three primes
in {2, 3, 5, 7} not dividing D:

char_HACS(T_q | Γ₀(D), k) = char_Brandt(T_q | M(Ô^×; V_k))² · char_HACS(T_q | SL₂(ℤ), k)², exactly over ℤ.

Why this holds:
- For k > 2 the Brandt module is S_k(Γ₀(D))^new. This is *cited* (Eichler, JL) and was checked against PARI on D ≤ 13 in
  `code/results/s01/symn.json`, 66/66.
- H¹(Γ₀(D)) = 2·(S^new + 2·S_k(1)) + 2·Eis.
- H¹(SL₂ℤ) = 2·S_k(1) + Eis.

*Probe (old s03-ct binary)*: 61 of 61 cells pass (HACS 88 s, total 2.8 min).

```bash
cd "$W"
cat > b4_symn_jl.py <<'EOF'
#!/usr/bin/env python3
"""CHECK B4 (RUN-NOW 4): JL with Sym^{k-2} coefficients, k > 2, D prime: definite Brandt module M(O^x; V_k) of B_D (our
Python `symn`) versus exact HACS char_Z(T_q) on H^1(Gamma_0(N); Sym^{k-2} Z^2)/tors at N = D and N = 1:
   char_HACS(N=D) == char_Brandt^2 * char_HACS(N=1)^2
(H^1(Gamma_0(D)) = 2 x [S_k^new + 2 S_k(1)] + 2 Eis;  H^1(SL_2 Z) = 2 S_k(1) + Eis;  JL: Brandt(V_k) = S_k(Gamma_0(D))^new, k > 2).
Usage: python3 b4_symn_jl.py HACS_BINARY PYTHONPATH_OF_langlandscape
"""
import json, os, subprocess, sys, tempfile, time
import sympy as sp

hacs, pypath = sys.argv[1], sys.argv[2]
sys.path.insert(0, pypath)
from langlandscape import symn  # noqa: E402
X = sp.symbols("x")
DS = [int(a) for a in os.environ.get("B4_DS", "2,3,5,7,11,13,17,19,23,29,31,37,41,43").split(",")]
cells = [(D, k) for D in DS for k in range(4, 13, 2) if (D + 1) * (k - 1) <= 300]
qs_for = lambda D: [q for q in (2, 3, 5, 7) if D % q][:3]
oc = 'set coefficient_ring = "Z";\n'
need = sorted({(N, k, tuple(qs_for(D))) for D, k in cells for N in (1, D)})
for N, k, qs in need:
    oc += (f'd = descent({N}, {k-2}, {json.dumps(list(qs))});\n'
           f'for c in d.charpoly {{ print("@@CP " + json([{N}, {k}, {json.dumps(list(qs))}, c.p, c.exact, c.determined])); }}\n')
with tempfile.NamedTemporaryFile("w", suffix=".oc", dir=".", delete=False) as f:
    f.write(oc); fn = f.name
t0 = time.time()
r = subprocess.run([hacs, "--script", fn], capture_output=True, text=True, env=dict(os.environ, ENGINE_THREADS="4"))
t_hacs = time.time() - t0
assert r.returncode == 0, r.stderr[-2000:]
cp = {}
for line in r.stdout.splitlines():
    if line.startswith("@@CP "):
        N, k, qs, q, ex, det = json.loads(line[5:]); assert det; cp[(N, k, tuple(qs), q)] = sp.Poly([int(c) for c in ex], X)
ok_all, bad = True, []
for D, k in cells:
    M = symn.sym_brandt(D, k)
    qs = tuple(qs_for(D))
    for q in qs:
        cB = symn.charpoly(M.T(q), M.S.zero, M.S.one)            # constant term first, entries in Q(sqrt(-D))
        assert all(c.is_rational() for c in cB)
        B = sp.Poly([sp.Rational(c.r.numerator, c.r.denominator) for c in reversed(cB)], X)
        ok = cp[(D, k, qs, q)] == B ** 2 * cp[(1, k, qs, q)] ** 2
        if not ok: bad.append((D, k, q))
        ok_all &= ok
print(json.dumps({"check": "B4", "cells": cells, "n_cells": len(cells), "all_ok": ok_all, "bad": bad,
                  "hacs_wall_s": round(t_hacs, 1), "total_s": round(time.time() - t0, 1)}))
sys.exit(0 if ok_all else 1)
EOF
time python3 b4_symn_jl.py "$B" "$PYLL" 2>&1 | grep -v 'PARI stack' | tee b4.log
# PASS = exit 0 and "all_ok": true, "n_cells": 61
```

### RN-5 = C1: exact HACS charpolys vs PARI on Γ₀(M) (≈ 6 min)

What is checked, for all M ≤ 60 and k ∈ {2, 4, …, 12} with ψ(M)(k−1) ≤ 300 (232 cells, 696 charpolys), and q the first
three primes not dividing M:
- char_HACS(T_q) = charpoly(T_q | S_k(Γ₀(M)))² · charpoly(T_q | E_k(Γ₀(M))), exactly over ℤ;
- rank H¹ = 2 dim S_k + dim E_k;
- dim E_k = #cusps − [k = 2].

Source of truth: PARI 2.15.4 `mfinit`/`mfheckemat` (flag 1 = the full cusp space, flag 3 = the Eisenstein space), plus
Eichler–Shimura. *Probe (old s03-ct binary)*: 232/232 cells pass (HACS 363 s under load).

```bash
cd "$W"
cat > c1_hacs_vs_pari.py <<'EOF'
#!/usr/bin/env python3
"""CHECK C1 (RUN-NOW 5): exact char_Z(T_q | H^1(Gamma_0(M); Sym^{k-2} Z^2)/tors) from HACS `descent` versus PARI:
   char_HACS(T_q) == charpoly(T_q | S_k(Gamma_0(M)))^2 * charpoly(T_q | E_k(Gamma_0(M)))
(Eichler-Shimura; E_k = PARI's Eisenstein space, mfinit flag 3, of dim #cusps - [k == 2]; for 9 | M or 16 | M it carries the
twisted eigenvalues chi(q) + chi^-1(q) q^(k-1), so do NOT replace it by (x - 1 - q^(k-1))^e).  Also rank H^1 == 2 dim S_k + dim E_k.
Usage: python3 c1_hacs_vs_pari.py HACS_BINARY [MMAX] [KS comma list]
"""
import json, math, os, subprocess, sys, tempfile, time
import cypari2, sympy as sp

hacs = sys.argv[1]
MMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 40
KS = [int(k) for k in (sys.argv[3] if len(sys.argv) > 3 else "2,4,6,8,10,12").split(",")]
pari = cypari2.Pari(); pari.allocatemem(1 << 29)
X = sp.symbols("x")

def psi(M):
    return M * math.prod(sp.Rational(p + 1, p) for p in sp.primefactors(M))

def cusps(M):
    return sum(int(sp.totient(math.gcd(d, M // d))) for d in sp.divisors(M))

cells = []
for M in range(1, MMAX + 1):
    for k in KS:
        if psi(M) * (k - 1) <= 300 and not (M == 1 and k == 2):
            qs = [q for q in (2, 3, 5, 7, 11, 13) if M % q][:3]
            cells.append((M, k, qs))
oc = 'set coefficient_ring = "Z";\n'
for M, k, qs in cells:
    oc += (f'd = descent({M}, {k-2}, {json.dumps(qs)});\n'
           f'print("@@D " + json([{M}, {k}, d.status, d.groups_inv[1].free_rank]));\n'
           f'for c in d.charpoly {{ print("@@CP " + json([{M}, {k}, c.p, c.exact, c.determined])); }}\n')
with tempfile.NamedTemporaryFile("w", suffix=".oc", dir=".", delete=False) as f:
    f.write(oc); fn = f.name
t0 = time.time()
r = subprocess.run([hacs, "--script", fn], capture_output=True, text=True, env=dict(os.environ, ENGINE_THREADS="4"))
t_hacs = time.time() - t0
assert r.returncode == 0, r.stderr[-2000:]
rank, cp = {}, {}
for line in r.stdout.splitlines():
    if line.startswith("@@D "):
        M, k, st, rk = json.loads(line[4:]); assert st == "ok", (M, k, st); rank[(M, k)] = rk
    elif line.startswith("@@CP "):
        M, k, q, ex, det = json.loads(line[5:]); assert det, (M, k, q); cp[(M, k, q)] = [int(c) for c in ex]
ok_all, bad = True, []
for M, k, qs in cells:
    mf = pari.mfinit([M, k], 1)          # full cusp space S_k(Gamma_0(M))
    me = pari.mfinit([M, k], 3)          # Eisenstein space E_k(Gamma_0(M))
    dS, dE = int(pari.mfdim(mf)), int(pari.mfdim(me))
    ok = rank[(M, k)] == 2 * dS + dE and dE == cusps(M) - (1 if k == 2 else 0)
    cpq = lambda sp_, d, q: sp.Poly([int(c) for c in pari.Vec(pari.charpoly(pari.mfheckemat(sp_, q)))], X) if d else sp.Poly(1, X)
    for q in qs:
        want = cpq(mf, dS, q) ** 2 * cpq(me, dE, q)
        ok &= sp.Poly(cp[(M, k, q)], X) == want
    if not ok: bad.append((M, k))
    ok_all &= ok
print(json.dumps({"check": "C1", "cells": len(cells), "charpolys": len(cp), "all_ok": ok_all, "bad": bad,
                  "hacs_wall_s": round(t_hacs, 1), "total_s": round(time.time() - t0, 1)}))
sys.exit(0 if ok_all else 1)
EOF
time python3 c1_hacs_vs_pari.py "$B" 60 2,4,6,8,10,12 2>&1 | grep -v 'PARI stack' | tee c1.log
# PASS = exit 0, {"check": "C1", "cells": 232, "charpolys": 696, "all_ok": true, "bad": [] ...}
```

### RN-6 = B14 (bonus, ≈ 5 s): T4 at q = 3, p = 17 on the branch through Δ

The stage-06 test H1/T4 asks for ord₁₇ 𝔠₃ along the 17-adic branch through Δ. The seed predicts 1, 1, 1, 1, 2 at
k = 12, 28, 44, 60, 124. The values at k ≥ 28 lie beyond the amalgam's range and are marked \stexp in
`plan/staged/stage-06-integral-defect.tex`. k = 124 is out of reach, since `descent` allows n ≤ 60.

What the check computes (the level-1 Betti side of Prop. s06-betti):
- the 17-adic roots λ of χ_cusp(T₃) with λ ≡ τ(3) = 252 (mod 17);
- the same for T₂ with τ(2) = −24, as a consistency check of the branch;
- ord₁₇(3^{k−2}·16 − λ²) for each such root λ.

*Probe (old s03-ct binary)*:
- ord₁₇ = 1, 1, 1, 1 at k = 12, 28, 44, 60. The branch has degree 1 in every weight.
- At k = 60, T₂ alone sees two 17-adic roots ≡ τ(2), but T₃ sees only one. So a second form is congruent to Δ at T₂ only.
  Report this as a remark.

```bash
cd "$W"
cat > b14_t4.oc <<'EOF'
# CHECK B14 (RUN-NOW 6, T4 support): exact char_Z(T_3), char_Z(T_2) on H^1(SL_2(Z); Sym^{k-2} Z^2)/tors at k = 12, 28, 44, 60.
set coefficient_ring = "Z";
for n in [10, 26, 42, 58] {
  d = descent(1, n, [2, 3]);
  for c in d.charpoly { print("@@CP " + json([n + 2, c.p, c.exact, c.determined])); }
}
EOF
cat > b14_post.py <<'EOF'
#!/usr/bin/env python3
"""CHECK B14 post-processing (T4, stage 06 H1; q = 3, p = 17, branch through Delta).  Input: @@CP lines of t4.oc.
For each k: chi_cusp(T_q) = squarefree part of char_Z(T_q | H^1)/(x - 1 - q^(k-1)); its 17-adic factors h whose reduction mod 17
is a power of (x - tau(q)); for q = 3: ord_17 Norm_h( 3^(k-2) (3+1)^2 - x^2 ) = ord_17 of the Betti level-raising number c_3 on the branch."""
import json, sys
import cypari2
pari = cypari2.Pari(); pari.allocatemem(1 << 28)
P, Q, tau = 17, 3, {2: -24, 3: 252}
x = pari("x")
cp = {}
for line in open(sys.argv[1]):
    if line.startswith("@@CP "):
        k, p, ex, det = json.loads(line[5:]); assert det, (k, p); cp[(k, p)] = pari.Pol([int(c) for c in ex])
for k in sorted({k for k, _ in cp}):
    row = {"k": k}
    for p in (2, 3):
        f = cp[(k, p)] / (x - (1 + p ** (k - 1)))
        sq = pari.gcd(f, pari.deriv(f))
        cusp = f / sq                                       # chi_H1/Eis = chi_cusp^2, chi_cusp squarefree at level 1
        fac = pari.factorpadic(cusp, P, 20)
        comps = []
        for i in range(int(pari.matsize(fac)[0])):
            h = pari.Pol([pari.truncate(c) for c in pari.Vec(fac[0][i])])       # 17-adic factor, coefficients mod 17^20
            hbar = pari.Pol([pari.Mod(c, P) for c in pari.Vec(h)])
            d = int(pari.poldegree(h))
            if hbar == pari.Mod(1, P) * (x - tau[p]) ** d:
                comps.append(h)
        row[f"branch_degrees_T{p}"] = [int(pari.poldegree(h)) for h in comps]
        if p == Q:
            row["ord17_c3"] = [int(pari.valuation(pari.polresultant(h, 16 * Q ** (k - 2) - x ** 2), P)) for h in comps]
    print(json.dumps(row))
EOF
time (ENGINE_THREADS=4 $B --script b14_t4.oc > b14.out 2>&1); echo "exit=$?"
python3 b14_post.py b14.out 2>&1 | grep -v 'PARI stack' | tee b14.log
# PASS = four lines with "ord17_c3": [1] at k = 12, 28, 44, 60
```

---

## 3. Catalogue

Each entry gives: purpose · command or input · expected result · source of truth · runtime · priority.

### A. Self-tests, regressions, CPU vs CUDA

- **A1** (P1, RN-1). See §2.
- **A2** `--all`, sharded (P1).
  - Command: `bash $HACS_SRC/docs/matrix-engine/tools/run_all_sharded.sh $B 4`.
  - Expected: `SHARDED_ALL shards=4 passed=x/x failed=0 verdict=OK`.
  - Source: the suite itself (`BUILDING.md`, "Expected run times": 7 min 46 s on the reference machine, < 3 GiB/shard).
  - The build worker is running exactly this now; reuse its logs.
- **A3** `--all-full` (P3). `$B --all-full > allfull.log`, exit code = number of failures. Expected 0. About 1 h 45 min on
  the reference machine (16 cores).
- **A4** Cross-binary identity (P1, once a second 0.2.1 build exists, e.g. the next rebuild or a `Release` build).
  - Command: run RN-2's `.oc`, RN-1 steps 5–7, and `$B --campaign <spec>` for the `descent_small` spec on both binaries,
    then `diff` the `@@` lines and the `record_fnv1a64` column.
  - Expected: identical. The README states that no build switch and no `ENGINE_*` variable changes a value.
- **A5** CPU-only build (P2). The comparison is the same as A4, against a CPU-only build:
  - `cmake --preset cpu-only -B build/cpu && cmake --build build/cpu -j16`. This is a build, so it is for the build
    worker, not us.
  - In that build the device validations print `[SKIP]` and pass.
  - Expected: values identical, and `CudaBitIdentityValidation` skips.
- **A6** JL-answers regression (P2).
  - Re-run `docs/jl_exchange/hacs-answers/task0_inscope/scripts/{d3,fam,hs3b,l3}.oc` and diff the printed groups and
    charpolys against `task0_inscope/data/anchor_*.txt` and `family_charpolys.txt` (binary 0.2.0).
  - Expected: identical mathematical lines. Timing lines and `EFFECTIVE` lines are exempt.
  - The task-1 `.oc` scripts are already in RN-1 (6).
- **A7** Manual run outputs (P2).
  - For each `docs/latex/cli_manual_runs/*.txt`, run the command on its first `$ ` line with `$B` in place of `hacs`, and
    diff, ignoring `t_s=`, `seconds`, `wall`, `rss` fields and `EFFECTIVE … threads=` lines.
  - Expected: identical values (e.g. `descent_cli.txt`, `campaign_z_run.txt`, `env_descent_gpu.txt`).
- **A8** Slow descent validations (P3).
  - Command: `$B IntegralDescentGroupsSlowValidation IntegralDescentLevelNSlowValidation IntegralDescentHeckeSlowValidation IntegralDescentPairSlowValidation HeckeZLocalCensusXcheck`.
  - Expected: 0 failures.
  - Relevant because every exact charpoly we use comes from the descent.

### B. Numerical sanity checks of stage 1–3 (and 5–6) statements

- **B1, B2** (P1, RN-3). **B3, B5** (P1, RN-2). **B4** (P1, RN-4). **B14** (P1, RN-6). See §2.
- **B6** det(Ψ\*Ψ) on a larger grid (P2, stage 03, seed C3 / C5).
  - Reuse `code/hacs/jl/s03_h1_rerun.py` (impl worktree) with its grid patched in a throwaway driver:
    ```bash
    cd /home/janosch/dev/Langlandscape-wt/impl && python3 -c "
    import sys; sys.argv=['x','--hacs','$B','--out','$W/b6_C3_more.json']; sys.path.insert(0,'code/hacs/jl')
    import s03_h1_rerun as m
    m.GRID_M_K=[(1,12),(1,16),(1,18),(1,20),(1,22),(1,24),(11,2),(11,4),(11,6),(13,2),(13,4),(17,2),(17,4),(19,2),(23,2),(5,4),(5,6),(7,4),(7,6)]
    sys.exit(m.main())"
    ```
  - Expected: `all_overlapping_cases_agree: true`. Overlap with `betti_det.json` is M ∈ {1, 2, 3, 5, 7, 11}, k ≤ 12.
  - The new cells are *exploratory*. Record D_int = ∏(q^{k−2}(q+1)² − λ²), which is never 0 (Ramanujan), and its prime
    factors ℓ > k + 1, which are the level-raising primes for B7.
  - Note: T1 inside the script is hard-wired to (11, 2); keep (11, 2) in the grid.
- **B7** Ribet level raising (P2, stage 03 `prop:s03-LRdef`, seed §6.4).
  - Take each (M, k, q, ℓ) from B6 with ℓ > k + 1 and ℓ ∤ 6Mq.
  - The q-new charpoly is χ_new(T_r) = sqrt(char_HACS(Γ₀(Mq)) / char_HACS(Γ₀(M))²) for k > 2. For k = 2 there is one extra
    factor (x − 1 − r).
  - Check that χ_new(T_r) mod ℓ and χ_f(T_r) mod ℓ have a common root for r ∈ {2, 3, 5} simultaneously.
  - Expected (*cited*: Ribet 1990, Diamond–Taylor 1994): yes, at every such ℓ. Conversely there is no common root when
    ℓ ∤ D_int.
  - HACS needs ψ(Mq)(k−1) ≤ 300. Beyond that bound use a descent campaign.
- **B8** Ihara at SL₂(ℤ[1/p]) (P2, stage 03 Cor ihara).
  - Command: `python3 $HACS_SRC/docs/jl_exchange/hacs-answers/task1_v6/scripts/cell.py p k --out $W/b8_p{p}_k{k}.json`
    for p ∈ {17, 19, 23}, k ∈ {4, …, 12}. This is the independent Python re-implementation of α = dg₁ − dg_p; it does not
    call HACS.
  - Then compare its level-1 and level-p charpolys with `descent` (HACS), as `task1_v6/scripts/xcheck.py` does.
  - Expected, as on the old grid p ≤ 13 (`task1_v6/results.md` §(b)): ker α = 0, i.e. H¹(SL₂(ℤ[1/p]), V) = 0; and the
    torsion of coker α at ℓ > k, ℓ ≠ p is a single ℤ/(k+1), Eisenstein, when k+1 is a prime ≠ p.
  - Runtime 1–45 s per cell.
  - HACS has no degeneracy-map verb, so this is the only no-new-code route to the Ihara kernel.
- **B9** T6 exponents at more (p, k) (P3, stage 03 rem:s03-pm). Definite side only (Python), with the module constants
  patched in a throwaway driver:
  ```bash
  cd /home/janosch/dev/Langlandscape-wt/impl/code/python && python3 -c "
  from langlandscape.ribet import ihara as I
  for p,k in [(11,7),(11,9),(11,11),(13,9),(13,11)]:
      r = I.IharaCase(k, p, 1, 'U1p').run(ells=(5,7,13) if p!=13 else (5,7,11))
      print(p, k, r['H0'], {l: h['exponent_observed'] for l, h in r['conventions']['cohomological']['hecke'].items()})"
  ```
  - Expected: cohomological exponent +1 wherever the case is discriminating (`code/results/s03/T6.json`, acceptance after
    the M7 audit).
  - Cost is unknown for p = 11, 13 (Shapiro, dimension (p²−1)·(k−1)). Start with (11, 7).
- **B10** T05-1, the sign ε (P2, stage 05).
  - For q ∈ {11, 23, 37, 43}, k ∈ {2, 4, 6, 8}, compute `level_n(q, k−2, ℓ, [2, 3, 5, q])` with ℓ = 10007 (ψ(q)(k−1) ≤ 1000
    holds).
  - The U_q charpoly mod ℓ on H¹ is ∏_new (x − a_q)² times the Eisenstein factor (PARI `mfinit([q,k],3)`, U_q eigenvalues
    1 and q^{k−1}).
  - a_q = −w_q·q^{k/2−1} for newforms. Match each newform's a_q to its Brandt eigenline through T₂, T₃, T₅, where Π_q comes
    from Python `pi_ell` (extend `DS`, `KS` in a throwaway driver).
  - Expected: a_q = +λ(Π_q) on every line. This is *expected*, and validates Remark s05-hsieh. `code/results/s01/pi_sign.json`
    has it for D ≤ 19, k ≤ 4.
  - *Probe (old s03-ct binary)*: `level_n(11, 0, 7, [2, 11])` gives U₁₁ charpoly `[6,3,4,1]` = (x−1)³ mod 7. So a₁₁(11a) = +1 and U₁₁ = 1 on
    the Eisenstein class.
- **B11** Congruence modules at small composite levels (P2, stage 06 Gorenstein hypotheses).
  - Compute `hecke_structure(N, n, "anemic")` and `"full"` for N ∈ {2, …, 30}, n ∈ {0, 2, 4} within the limits.
  - Print `C_T`, `generation` and the body lines `G2.ell=*.m[*].local_type.{kind,gorenstein,rank}`.
  - Expected: *exploratory*. Cross-check the cells that overlap `task0_inscope/data/congruence_modules.json` (computed by
    0.2.0).
  - *Probe (old s03-ct binary)*: at prime N, `full` returns `C_T = not_run` (the record runs C_T only for the anemic algebra at N > 1), so
    use `anemic`.
- **B12** T5 / H3 inputs (P2, stage 06).
  - The T5 triples are (q, k, p) ∈ {(13, 18, 19), (5, 18, 23), (5, 16, 31), (13, 12, 31), (3, 18, 53), (3, 18, 61),
    (13, 16, 101)}. All seven satisfy the console bound ψ(q)(k−1) ≤ 300; the largest is (13, 18) with 14·17 = 238.
  - Compute `descent(q, k−2)` and `descent(1, k−2)` to get the exact old and new charpolys.
  - η_f(q)-side number: ord_p Res(χ_old,f(T_r), χ_new(T_r)) for r ∈ {2, 3}. This is an upper bound for the old/new
    congruence module at m_f.
  - ord_p 𝔠_q(f) = ord_p(q^{k−2}(q+1)² − a_q(f)²) on the p-adic factor of f, as in RN-6.
  - Expected: Thm E gives ord_p η_f(q) = ord_p 𝔠_q(f) + ord_p η^B. The definite η^B needs the Gram matrix, which is new
    Python and out of scope here. Record both GL₂-side numbers.
  - H3 (q ≡ −1 mod p: (13, k ≤ 6, 7), (19, 4, 5), (29, 4, 5)) is computed the same way. The predicted difference
    ord 𝔠_q − t_f(q) is 0.
  - Caveat: the full algebra with U_q at level q is reachable only mod ℓ (`level_n`). Use `level_n(q, k−2, p, [2, 3, q])`
    for the U_q factor.
- **B13** Mazur at 2 and 3 (P3, exploratory).
  - At p ≡ 1 mod 8 and p ≡ 1 mod 9 the 2- and 3-parts of n are the delicate ones (Mazur II.16, Calegari–Emerton).
  - Collect the RN-2 / E1 cells where a 2- or 3-part is only bounded (e.g. p = 113, 157, 241) and run
    `HECKE_LN23_STURM=1 HECKE_LEVEL_N_R3_SMALLP_CELLS="113:2,241:2,73:2,73:3,109:3" $B HeckeLevelNCurveValidation`.
    The cell list must satisfy p | num((N−1)/12); remove any cell the validation refuses.
  - Compare the dim W / Loewy readings with the C_T bounds.

### C. Cross-checks with Python and PARI

- **C1** (P1, RN-5). See §2.
- **C2** `level_n` mod ℓ incl. U_p vs PARI (P1; left out of RUN-NOW only because its PARI side is slow at N ≤ 100).
  Runtime: HACS < 1 min, PARI ≈ 10–15 min for N ≤ 100. Use `NMAX = 40` for a run under 3 min.
  - Command: `python3 c2_leveln_vs_pari.py $B 10007 100`. The script is below and has the same shape as C1.
  - What it checks:
    - char(T | H¹(Γ₀(N); Sym^n F_ℓ)) = charpoly(T | S_k)² · charpoly(T | E_k) mod ℓ, for T ∈ {T_q (q ∤ N), U_p (p | N)};
    - h1 = 2 dim S_k + dim E_k.
  - *Probe (old s03-ct binary)*: 114/114 cells pass for N ≤ 20, k ≤ 12, including U₂ at N = 4, 8, 16 and U₃ at N = 9, 18.
  - Source: PARI `mfheckemat` on flag 1 and flag 3 spaces.


```bash
cd "$W"
cat > c2_leveln_vs_pari.py <<'EOF'
#!/usr/bin/env python3
"""CHECK C2: HACS level_n(N, n, ell, primes) charpolys mod ell (T_q, and U_p for p | N) versus PARI:
   char(T | H^1(Gamma_0(N); Sym^n F_ell)) == charpoly(T | S_k)^2 * charpoly(T | E_k)  mod ell,  k = n + 2,
and h1 == 2 dim S_k + dim E_k.  (U_p on E_k: PARI's eigenvalues; for k = 2, prime N: U_N = 1 on the Eisenstein class.)
Usage: python3 c2_leveln_vs_pari.py HACS_BINARY [ELL=10007] [NMAX=100]
"""
import json, os, subprocess, sys, tempfile, time
import cypari2
hacs = sys.argv[1]; ELL = int(sys.argv[2]) if len(sys.argv) > 2 else 10007; NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 100
pari = cypari2.Pari(); pari.allocatemem(1 << 29)
cells = []
for N in range(2, NMAX + 1):
    idx = int(pari("(N)->N*prod(i=1,#factor(N)~,1+1/factor(N)[i,1])")(N))
    for k in (2, 4, 6, 8, 10, 12):
        if idx * (k - 1) <= 1000:
            good = [q for q in (2, 3, 5, 7) if N % q][:2]
            bad = [int(p) for p in pari.factor(N)[0]][:2]
            cells.append((N, k, (good + bad)[:6]))
oc = ""
for N, k, ps in cells:
    oc += f'A = level_n({N}, {k-2}, {ELL}, {json.dumps(ps)});\nprint("@@L " + json([{N}, {k}, A.h1, A.ops]));\n'
with tempfile.NamedTemporaryFile("w", suffix=".oc", dir=".", delete=False) as f:
    f.write(oc); fn = f.name
t0 = time.time()
r = subprocess.run([hacs, "--script", fn], capture_output=True, text=True, env=dict(os.environ, ENGINE_THREADS="4"))
assert r.returncode == 0, r.stderr[-2000:]
t_hacs = time.time() - t0
P = lambda coeffs_low: pari.Pol([pari.Mod(c, ELL) for c in reversed(coeffs_low)])
ok_all, bad_cells = True, []
for line in r.stdout.splitlines():
    if not line.startswith("@@L "): continue
    N, k, h1, ops = json.loads(line[4:])
    mf, me = pari.mfinit([N, k], 1), pari.mfinit([N, k], 3)
    dS, dE = int(pari.mfdim(mf)), int(pari.mfdim(me))
    ok = h1 == 2 * dS + dE
    for op in ops:
        q = op["p"]
        cS = pari.charpoly(pari.mfheckemat(mf, q)) if dS else pari.Pol(1)
        cE = pari.charpoly(pari.mfheckemat(me, q)) if dE else pari.Pol(1)
        want = pari.Mod(1, ELL) * cS ** 2 * cE
        ok &= bool(P(op["charpoly"]) == want)
    if not ok: bad_cells.append((N, k))
    ok_all &= ok
print(json.dumps({"check": "C2", "ell": ELL, "cells": len(cells), "all_ok": ok_all, "bad": bad_cells,
                  "hacs_wall_s": round(t_hacs, 1), "total_s": round(time.time() - t0, 1)}))
sys.exit(0 if ok_all else 1)
EOF
time python3 c2_leveln_vs_pari.py "$B" 10007 100 2>&1 | grep -v 'PARI stack' | tee c2.log    # PASS = "all_ok": true
```
- **C3** Nebentypus convention (P2, decides the χ ↔ χ̄ dictionary for T05-2).
  - The contract [C] `sec:nebentypus` (NB5) leaves this open: charpoly(T | H¹_par) = charpoly(T | H)², where H carries the
    eigenvalues "of a single space of forms of character χ or χ̄".
  - [C] fixes the reduction rule: χ_{N.m}(g) ↦ s, where g is the least primitive root mod N and s is the least primitive
    ord(χ)-th root of unity in [1, ℓ).
  - Cells: (N, m, n, ℓ) ∈ {(5, 2, 1, 13), (5, 4, 0, 11), (5, 4, 2, 11), (7, 2, 2, 13), (7, 2, 0, 13), (13, 8, 1, 17)}. Keep only cells with parity_ok, ord χ \| ℓ − 1 and ℓ ∤ N. Run
    `nebentypus(N, m, n, ℓ, [2, 3])` (with [2, 3] minus any prime dividing N).
  - PARI side: `G = znstar(N, 1)`, `chi = znconreychar(G, m)`; build `mfinit([N, n+2, [G, chi]], 1)` and the same for
    `charconj(G, chi)`.
  - Reduce the charpolys of `mfheckemat(·, p)` from Q(ζ_o) to F_ℓ by the embedding ζ_o ↦ ω, with ω fixed by χ(g) ↦ s:
    if `chareval(G, chi, g) = j/o`, then ω = s^{j⁻¹ mod o}.
  - Expected: for every cell, exactly one of χ, χ̄ reproduces HACS's `ops[i].charpoly` / (Eisenstein factor). Quadratic
    cells cannot discriminate and serve as controls. Record the winner as the dictionary for T05-2 (stage 05) and for
    `rem:s03-pm`.
- **C4** forms side (P3).
  - `forms_algebra(k, ℓ)` for k = 12..60, ℓ ∈ {691, 3617, 10007}: charpolys mod ℓ vs PARI `mfinit([1,k],1)` mod ℓ.
  - `hida_lambda(ℓ, k, W)` for ℓ = 5, 7: charpoly of U = T_ℓ on eS_k mod ℓ^W vs PARI, via the ordinary factor of
    charpoly(T_ℓ) mod ℓ^W.
  - Expected: equal. The source is PARI.
- **C5** Integral Hecke module structure (P3).
  - For `descent(N, n).module_Z()` at (11, 2), (3, 10), (5, 4): compare the exact F block (`ops[i].F`, decimal strings)
    with PARI `mfheckemat` on the full space.
  - Equal charpolys are expected. Equal Smith forms of F − a·1 are *exploratory*, because the lattices differ: H¹/tors vs
    the q-expansion lattice. A difference is a finding about lattices, not a failure.

### D. GPU vs CPU timings

- **D1** (P2) Hecke pipeline benches.
  - Commands: for n in 128 256: `$B --bench hecke $n 134217757 2 --repeat 4` under `ENGINE_DEVICE=cpu` and
    `ENGINE_DEVICE=gpu`. Also `$B --bench cohom 1000 134217757 --lean`.
  - Expected: identical `dims=`. The manual and `performance-reference.md` expect the CPU to be faster on these shapes.
    Reference: `hecke 128` 0.12 s, `hecke 256` 0.56 s, `cohom 1000 --lean` 14.8 s / 1157 MB on a 16-core machine.
- **D2** (P2) Descent Smith on GPU. Spec:
  ```
  name = gpu_descent
  coefficient_ring = Z
  n_sym = 20
  level = 200, 500
  parts = groups,hecke
  ```
  - Runs: (a) `ENGINE_THREADS=16 $B --campaign gpu.spec --output d2_cpu16`; (b) `ENGINE_THREADS=32 … --output d2_cpu32`;
    (c) `ENGINE_DEVICE=gpu ENGINE_THREADS=16 … --output d2_gpu`.
  - Expected: the same `record_fnv1a64` in all three `summary.tsv`. (c) prints `EFFECTIVE GPU_SMITH2K … fallbacks=0`.
  - Reference timing: Γ₀(1000), n = 20 took 142.8 s on the GPU vs 903.9 s on 16 CPU threads. Γ₀(500) has D = 18900, so
    estimate about 2 min CPU / 20 s GPU (cubic extrapolation).
- **D3** (P3) Thread scaling of RN-5's grid. Re-run `c1_hacs_vs_pari.py` with the `ENGINE_THREADS` inside the script set to
  1, 4, 16, 32 (edit the env dict) and record `hacs_wall_s`.
- **D4** (P3) `CUDA_IMMA_ELIM_BENCH=4096,4096 $B CudaImmaElimValidation`;
  `HECKE_DESCENT_SMITH_GPU_ARMS=… $B DescentSmithGpuValidation` (the arm syntax is in `validation-catalogue.md`). Timing
  only.

### E. Stress tests beyond what our Python reaches

- **E1** (P2) Mazur beyond the console bound. Spec (the dry run parses):
  ```
  name = mazur_big
  coefficient_ring = Z
  structure = hecke
  n_sym = 0
  level = 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 433, 1009
  algebra = anemic
  ```
  - Command: `$B --campaign mazur_big.spec --output e1_out`, then run `b3_post.py`-style parsing on `e1_out/cells/*.json`.
    The record is the same `integral_hecke_structure/v1`; read `C_T` and the `G3.C_T.ell=` body lines.
  - Expected: C_T = num((p−1)/12), or bounds containing it.
  - *Probe (old s03-ct binary)*: 241 and 293 return `upper_bound_certified` in about 1 min each; 241 has `2:open(sandwich)`.
  - Runtime at 433 and 1009 is unknown. Run 433 first, in its own section, and stop if a cell exceeds 15 min.
- **E2** (P2) Large prime levels by descent.
  ```
  name = desc_big
  coefficient_ring = Z
  n_sym = 0
  level = 1009, 2017, 4001, 8009
  p = 2, 3, 5
  parts = groups,hecke
  ```
  - What is checked:
    - rank H¹ = 2h(p) − 1 with h(p) from the Eichler formula (RN-3's `eichler_h`);
    - with Q = char_HACS(T_q)/(x − 1 − q) = χ_cusp², isqrt(Q(1+q)) = |χ_cusp(1+q)| is divisible by n = num((p−1)/12) for
      every q (Eisenstein congruence). Report the quotient gcd_q / n.
  - Where Python Brandt cannot go (h ≈ p/12 ≈ 670 classes at 8009), this tests the GL₂ side alone against two closed
    formulas.
  - Runtime: D = p + 1. The 2-adic Smith form has about 4/3·D rows, so seconds to a minute per cell. The CRT charpolys have
    degree about p/6.
- **E3** (P2) Calegari–Emerton grids, prime levels in the thousands, mod 2 and 3.
  - Commands:
    - `HECKE_LN23_Z1_NMAX=2000 $B HeckeLevelNCurveValidation` (≈ 1 s extra);
    - `HECKE_LN23_THM12I_NMAX=10000 $B HeckeLevelNCurveValidation` (133 cells, ≈ 3.5 min);
    - `HECKE_LN23_HEAVY=1 $B HeckeLevelNCurveValidation` (adds (21929, 2): dim W = 255, Loewy 128, ≈ 34 s);
    - P3: `HECKE_LN23_THM11_NMAX=30000` (397 cells, 72 min).
  - Expected: `… checks, 0 failing`; read the `EFFECTIVE … cells=` line.
  - Source: Calegari–Emerton, Thm 1.1 / 1.2(i), as frozen in the validation.
  - This is the mod-2/3 Eisenstein structure of T(p), which RN-2 can only bound.
- **E4** (P3) B4 beyond the console bound.
  - A descent campaign with `level = 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101`, `n_sym = 2..10 step 2`, `p = 2, 3, 5`
    (D ≤ 1122), plus level 1. Then the B4 identity against Python `symn.sym_brandt(D, k)`.
  - Python cost at D ≈ 100 is unknown (≈ 0.6 s at D = 23, k = 8).
- **E5** (P3) Mod-ℓ Eisenstein congruences at level ≤ 100.
  - Compute `level_n(N, n, ℓ, [2, 3, 5])` for prime N ≤ 97, n with ψ(N)(n+1) ≤ 1000, and ℓ ∈ prime factors of
    num(B_k/2k)·num((N−1)/12) that lie in [5, 65521].
  - Expected: the multiplicity of the root 1 + q^{k−1} in char(T_q) mod ℓ exceeds its multiplicity in E_k exactly when ℓ is
    an Eisenstein prime for (N, k).
  - *Exploratory* bookkeeping. The theory is *cited*: Mazur, Ribet, Billerey–Menares.

---

## 4. What is not reachable without new code (for the record)

- **Degeneracy maps** dg₁, dg_p : H¹(Γ₀(N)) → H¹(Γ₀(Np)) and Ψ\*Ψ as a map. HACS exposes H¹ and T_q only. The Ihara kernel
  is therefore checked through B8's independent Python and through charpolys (B6, B7).
- **U_p over ℤ at p \| N** (`descent` refuses p \| N). It is available only mod ℓ through `level_n` (B10, B12).
- **Γ₁(N) at level > 13** and Hida towers beyond ℓ ≤ 13 (`tower_edge_not_built`). T3, T05-2, T7 at Γ₁(Np^s) with U_p
  remain definite-side Python only.
- **k = 124** in T4: `descent` allows n ≤ 60 only, and the campaign has the same per-cell bound in n.
- **The definite side of anything** (Brandt, Gram matrices, η^B). That lives in `code/python`. HACS is GL₂ only (task-0
  feasibility note in `docs/jl_exchange/hacs-answers/README.md`).
