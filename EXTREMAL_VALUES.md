# Extremal values: what this method delivers at its optimum

**Written 2026-08-02.** This is the single source of truth for every constant in the
averaged mod-`2^k` spectral certificate. It supersedes the constants printed in
[THEOREM.md](THEOREM.md), [LEMMA_C_PROOF.md](LEMMA_C_PROOF.md) and
[UFULL_ASSEMBLY_PROOF.md](UFULL_ASSEMBLY_PROOF.md) wherever they disagree, and it is the
document [README.md](README.md) and `paper/syracuse_spectral_gap.tex` should be read
against.

> **Scope of this file (read-only, ES Technique 7b).** This document **re-derives no
> mathematics**. It cites every input by file and line, corrects arithmetic, and attaches an
> evidence label to each constant. Its only new content is (i) the corrected arithmetic,
> (ii) the labels, and (iii) the reproduction numbers from the script committed alongside it
> (`extremal_values_check.py`). No lemma is strengthened, weakened or restated here. Where
> this file disagrees with a proof document, the disagreement is recorded in
> [Flags](#flags-disagreements-found-with-the-existing-documents), not silently fixed in the
> proof document.

> **Scope of the theorem (unchanged).** This is a theorem about the mod-`2^k` transfer
> operator of the Syracuse map, a Markov model. It does not eliminate Collatz cycles: the
> `3x-1` operator passes the same certificate and `3x-1` has real cycles
> ([CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md)). Nothing in this document changes that.
> Sharpening a constant that cannot separate `3x+1` from `3x-1` sharpens nothing about
> Collatz.

## Label vocabulary

`PROVEN` (unconditional proof written out in this repo, all `k`) | `DATA` (machine-verified
over a finite range, no proof) | `measured` (a computed value of the object itself, not a
bound). Labels never round up: a bound that consumes a `DATA` input is `DATA`, however good
the numerics.

---

## The table

`cert(k) := max_a sum_b Q_k[a,b] 2^{a-b}`, `Q_k[a,b] := ||P_a U_k P_b||_2`, and
`|lambda_2(T_k)| <= rho(Q_k) <= cert(k)` (THEOREM.md Part I, lines 56-91). All rows bound the
same quantity; they differ only in what is fed to the defect term of the Part III row sum
(THEOREM.md lines 111-127).

| # | Statement | Exact closed form | Value | Label |
|---|---|---|---|---|
| 1 | `cert(k) <= f(3)` for all `k >= 3`, from Lemmas A + B alone | `2^{-3/2} + 2^{-1} = (2 + sqrt 2)/4` | **0.8535533906** | **PROVEN** |
| 2 | `cert(k) <= max_{e>=2}[ sum_{d=1}^{e-2} 2^{-3d/2} + (2/sqrt 3) 2^{-(e+1)/2} ]`, max at `e = 4` | `(3 + 6 sqrt 2 + 2 sqrt 6)/24` | **0.6826775358** | **PROVEN** |
| 3 | same envelope with the sharp constant `3/4`, max at `e = 4` | `(1 + 3 sqrt 2)/8` | **0.6553300859** | **DATA** (`k <= 26`) |
| 4 | same envelope fed the **measured** `v_b` profile | `sum_{d=1}^{2} 2^{-3d/2} + S_k 2^{-5/2}`, `S_k -> 0.8817` | **0.634412** (k=13) | **measured** |
| 5 | the objects themselves: `cert(k)`, `rho(Q_k)`, `|lambda_2(T_k)|` | - | **0.634412 / 0.5644 / 0.264** (k=13) | **measured** |
| 6 | the older UFULL row-sum assembly, `cert(k) < G_up + (defect at the top row)` | `1/(2 sqrt 2 - 1) + 1/sqrt 6` | **0.9551664511** | **PROVEN** |
| 6b | the same with the sharp constant `3/4` | `1/(2 sqrt 2 - 1) + 2^{-3/2}` | **0.9004715513** | **DATA** (`k <= 26`) |

`G_up := sum_{d>=1} 2^{-3d/2} = 1/(2 sqrt 2 - 1) = (1 + 2 sqrt 2)/7 = 0.5469181607`.

**Row 6 is not on the optimisation path.** It is the pre-2026-07-05 assembly, kept here only
because the number `0.9005` is still printed in several places. Row 1 already beats it, from
strictly weaker inputs. Read rows 1-5 as the method's actual ladder.

### Row-by-row provenance and what would move it down

**Row 1 - `0.8535533906`, PROVEN.**
*Where:* THEOREM.md line 21 (statement), lines 111-133 (proof), line 127 (the envelope
`f(e) = sum_{d=1}^{e-2} 2^{-3d/2} + 2^{-(e-1)/2}`), line 133 (`max f = f(3)`). Lean:
`lean/GapCertificate.lean` (`envelope_max`, `envelope_lt_one`, `assembly_row_bound`,
`certificate_lt_one`), sorry-free.
*Inputs:* Lemma A (THEOREM.md lines 100-105), Lemma B (lines 106-107), the truncation
`b <= k-2` (lines 111-113), one Cauchy-Schwarz (lines 118-124). Nothing else.
*To move down a row:* prove any uniform bound on the defect profile better than the pure
`L^2` mass, i.e. any `g_b <= C` with `C < 1`. This is exactly Lemma C, and it is done: row 2
is already unconditional. Row 1's only remaining role is as the constant the Lean core
certifies.

**Row 2 - `0.6826775358`, PROVEN.**
*Where:* the constant `sqrt(3/4)` is LEMMA_C_PROOF.md line 25 ("We prove `g_b < sqrt(3/4) =
0.8660 < 0.961` for all `k, b` ... **unconditionally**") and line 159, equation (8):
`g_b^2 <= 3/4 - 2^{-p} < 3/4`. Feeding it through THEOREM.md's truncated envelope
(lines 154-157) multiplies that envelope's defect term by `(sqrt 3/2)(4/3) = 2/sqrt 3`.
*Derivation (arithmetic only, no new mathematics):* `v_b <= (sqrt 3/2) 2^{-b} 2^{-k/2}` gives
`sum_{b=0}^{k-2} v_b 2^{-b} < (sqrt 3/2)(4/3) 2^{-k/2} = (2/sqrt 3) 2^{-k/2}`; with
`u_a 2^a = 2^{(a-1)/2}` (THEOREM.md line 124) the defect term is
`(2/sqrt 3) 2^{-(e+1)/2}`. Argmax `e = 4`, monotone decreasing for `e > 4`, verified to
`e = 60`.
*This is the headline number of the whole method.* Row 2, not row 3, is what the paper and
the README may state as proven.
*To move down a row:* prove `g_b <= 3/4` for all `k` (currently `DATA` to `k = 26`). By
LEMMA_C_PROOF.md line 119 that is equivalent to the excess bound `coll(p) - A_p <= (7/8) 2^p`;
the proof there delivers only `coll(p) - A_p <= 3*2^{p-1} - 2 < (3/2) 2^p` (line 155), a
factor `12/7` slack.

**Row 3 - `0.6553300859`, DATA.**
*Where:* the sharp constant is LEMMA_C_PROOF.md lines 16-17 (Lemma C sharp form) and
UFULL_ASSEMBLY_PROOF.md lines 53-56 (`g_b^2 <= 9/16` for `k = 6..22`, equality at `b = k-4`,
so `3/4` cannot be lowered). LEMMA_C_PROOF.md line 28 states plainly that the sharp `3/4` "is
verified exactly to `k=26` but not needed".
*The printed value `0.65597` in THEOREM.md line 157 is a misprint.* The formula printed
immediately above it evaluates to `(1 + 3 sqrt 2)/8 = 0.6553300859` at `e = 4`, verified in
exact arithmetic and in float. The same misprint appears at `paper/syracuse_spectral_gap.tex`
line ~456; the abstract's "improves the constant to 0.656" (tex lines ~52-54) is true of
`0.65533` and remains true, but is an overclaim in provenance, not in arithmetic: it is a
`DATA` constant presented as proven.
*To move down a row:* nothing. Row 3 is already the best the `g_b <= 3/4` route can give, and
`3/4` is sharp. The only movement available is upward in confidence: prove `3/4` and row 3
becomes PROVEN.

**Row 4 - `0.63448`, measured.**
This is what the assembly would give if the true `v_b` profile were proven rather than
measured. Feed the measured profile through the identical Part III row sum, defining
`S_k := 2^{k/2} sum_{b=0}^{k-2} v_b 2^{-b}`:

| k | `S_k` | row-4 bound | argmax `e` | row-5 `cert(k)` |
|---|---|---|---|---|
| 6  | 0.8863901 | 0.635247 | 4 | 0.633784 |
| 8  | 0.8835860 | 0.634751 | 4 | 0.634659 |
| 10 | 0.8823851 | 0.634539 | 4 | 0.634533 |
| 12 | 0.8820383 | 0.634477 | 4 | 0.634477 |
| 13 | 0.8816705 | 0.634412 | 4 | 0.634412 |

The three admissible values of `S_k` are the ladder in miniature: `2/sqrt 3 = 1.1547`
(PROVEN, row 2), `1` (DATA, row 3), `~0.8817` (measured, row 4). **Row 4 and row 5 agree to
six digits by `k = 12`**, which is the sharp statement of where the remaining slack lives:
after `k ~ 12` the Part III assembly is not lossy at all, and the entire gap between the
proven `0.6827` and the true `0.6344` is the gap between `2/sqrt 3` and the true `S_k`. There
is no other slack left to recover.
*To move down a row:* prove the measured profile, i.e. an asymptotic for
`sum_b v_b 2^{-b}` rather than a uniform bound on each `g_b`. That is a statement about the
`3x+1` exponential sum `S_k` of LEMMA_C_PROOF.md Step 1, not a shell-counting statement, and
nothing in this repo attempts it.

**Row 5 - `0.63441 / 0.5644 / 0.264`, measured.**
*Where:* THEOREM.md line 25 (`cert ~ 0.6345`, `rho(Q) ~ 0.566`, `|lambda_2| ~ 0.27`),
UFULL_ASSEMBLY_PROOF.md lines 152-157 (per-`k` table).
Rebuilt from the THEOREM.md Setup definition (lines 34-45) by two independent code paths:

| k | `cert(k)` | `rho(Q_k)` | `\|lambda_2(T_k)\|` | binding `e*` | `max_b g_b^2` | `\|\|c\|\| 2^{k/2}` |
|---|---|---|---|---|---|---|
| 4  | 0.611725 | 0.501992 | 0.2727 | 4 | 0.5625 | 1.6202 |
| 6  | 0.633784 | 0.553529 | 0.2767 | 4 | 0.5625 | 1.6105 |
| 8  | 0.634659 | 0.566061 | 0.2549 | 4 | 0.5625 | 1.6081 |
| 10 | 0.634533 | 0.567279 | 0.2702 | 4 | 0.5625 | 1.6075 |
| 12 | 0.634477 | 0.565553 | 0.2652 | 4 | 0.5625 | 1.6073 |
| 13 | 0.634412 | 0.564415 | 0.2637 | 4 | 0.5625 | 1.6072 |

`max_b g_b^2 = 9/16` exactly for every `k >= 4` (the sharp constant of row 3 is attained, at
`b = k-4`); `||c|| 2^{k/2}` peaks at `1.6202` at `k = 4`, below `sqrt 3 = 1.7321` (Lemma B).
`|lambda_2|` oscillates in `0.239-0.277` with no visible trend; "`~0.27`" is the top of that
band, not a limit.

**The binding row is `e* = 4`, not the envelope's `e = 3`.** For every `k >= 4` the row
attaining `cert(k)` is `a* = k-4`. THEOREM.md's Sharpness remark (lines 146-152), which says
"the row that sets the CONSTANT is `e = 3`", is a statement about the **row-1 envelope**, not
about `cert(k)`. The `e = 3` peak in row 1 is an artifact of the Cauchy-Schwarz defect bound
being 3.2x conservative there (`0.5` bound vs `0.156` measured). Rows 2, 3 and 4 all peak
correctly at `e = 4`. Source of this finding: the trivial-witness audit (private working
directory, `TRIVIAL_WITNESS_AUDIT_2026-08-02.md` Finding 1), reproduced here.
At the binding row the split is analytic-clean `2^{-3/2} + 2^{-3} = 0.478553` plus measured
defect `S_k 2^{-5/2} = 0.1559`, summing to `0.634477` at `k = 12`, which is `cert(12)` to six
digits.
*To move down a row:* nothing to prove. Row 5 is the object. Any bound below it is false.

**Row 6 / 6b - `0.9551664511` PROVEN, `0.9004715513` DATA.**
*Where:* UFULL_ASSEMBLY_PROOF.md line 79 (`< G_up + 2^{-3/2} = 0.900472`), derived at lines
101-118 by bounding the clean part by the **full** series `G_up` and the defect part by its
top-row value. LEMMA_C_PROOF.md lines 184-188 already gives the proven-constant version:
"`cert(k) < G_up + 0.408 = 0.547 + 0.408 = 0.955 < 1`". Exactly,
`(2/sqrt 3) 2^{-3/2} = 1/sqrt 6 = 0.4082482905`, so the constant is
`1/(2 sqrt 2 - 1) + 1/sqrt 6 = (6 + 12 sqrt 2 + 7 sqrt 6)/42 = 0.9551664511`.
*Status:* superseded. THEOREM.md lines 138-144 record why (UFULL Remark 2 added the full
`G_up` to the top row, where the upper cascade is empty). Both 6 and 6b are strictly worse
than row 1, which needs strictly less. They are listed so that no downstream document quotes
`0.9005` as the current proven constant, and so that if `0.9005` is quoted it is at least
labelled `DATA`.
*To move down a row:* use the truncated envelope. Done; that is row 1.

---

## The `3x-1` companion

> **Model theory only. This table separates nothing.** The `3x-1` map (`n -> oddpart(3n-1)`)
> **has** non-trivial cycles - `{5, 7}` and `{17, 25, 37, 55, 41, 61, 91}` - and it passes
> every certificate below **more strongly** than `3x+1`. No quantity in this document, at any
> provenance level, distinguishes "has cycles" from "has no cycles". Improving row 2 to row 3
> to row 4 improves a number that is already smaller for the map that has cycles. See
> [CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md).

| k | `3x+1` cert | `3x-1` cert | `3x+1` `rho(Q)` | `3x-1` `rho(Q)` | `3x+1` `\|l2\|` | `3x-1` `\|l2\|` |
|---|---|---|---|---|---|---|
| 6  | 0.633784 | 0.601817 | 0.553529 | 0.503891 | 0.2767 | 0.2966 |
| 8  | 0.634659 | 0.606053 | 0.566061 | 0.527227 | 0.2549 | 0.2933 |
| 10 | 0.634533 | 0.606140 | 0.567279 | 0.536479 | 0.2702 | 0.2915 |
| 11 | 0.634279 | 0.606035 | 0.566419 | 0.538775 | 0.2521 | 0.2833 |

*Where:* CYCLE_CLAIM_REFUTED.md lines 35-41. Every digit reproduced here by both code paths;
these columns were previously not reproducible from any script in this repo.

Three points that matter for how this table may be used:

1. **The two operators are not conjugate.** The natural guess `T_minus = Pi T_plus Pi` with
   `Pi: x -> -x mod 2^k` (from `3(-x)+1 = -(3x-1)`, `v2` preserved) is **FALSE**. The clean
   part is negation-covariant; the failure is confined 100% to the defect column, because
   every lift in the defect fiber has `v2(3n +- 1) >= k`, where the lift correspondence
   `n <-> 2^{2k} - n` no longer pins the negated target mod `2^k`. Entrywise deviation decays
   like `~5 * 2^{-k}`, but the **spectra do not converge**: `cert(+1) ~ 0.6345` versus
   `cert(-1) ~ 0.6061`, a stable `0.028-0.032` gap in `k`. Source:
   `TRIVIAL_WITNESS_AUDIT_2026-08-02.md` Finding 2 (private working directory).
2. **So `cert` is a sign-sensitive functional that still fails to certify.** It is not that
   the certificate cannot see the sign; it sees it (through the defect fiber, the unique
   model-distinguishing object in the construction) and the sign it prefers is the wrong one.
   That is a strictly stronger obstruction than sign-blindness, and it is an empirical
   observation, not a theorem.
3. **The binding row differs.** For `3x-1` the binding row is `e* = 5` for `k = 6, 8, 10, 11`,
   not `e* = 4`. The two operators do not even attain their certificates on the same row.

## Absurd-height instantiation

The 6,586,818,670-odd-step figure is the CF-convergent cycle-elimination range quoted in the
private `STATUS.md`. Instantiating `4 g^{s/2}` at `s = 6,586,818,670`:

| `g` | provenance | `4 g^{s/2}` |
|---|---|---|
| 0.8535533906 | row 1, PROVEN | `~10^{-2.26e8}` |
| 0.6826775358 | row 2, PROVEN | `~10^{-5.46e8}` |
| 0.6553300859 | row 3, DATA | `~10^{-6.04e8}` |
| 0.27 | row 5, measured `\|lambda_2\|` | `~10^{-1.87e9}` |

Every row gives a bound that is vacuously small, and the differences between rows - a factor
of `10^{3.78e8}` between row 1 and row 3 - are worth nothing. Per
[CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md), the averaging over `2^k` lifts dilutes any
genuine cycle edge to weight `2^{-k}`, so a small `|lambda_2|` is consistent with cycles
existing; the `3x-1` operator has an even smaller bound and real cycles. **The size of this
number is not evidence of anything.** It is included because the same instantiation appears
in the private status documents framed as though smallness were progress.

## Reproduction

`extremal_values_check.py` (committed with this document). It rebuilds `T_k` from the
THEOREM.md Setup definition (lines 34-45) and passes a reproduce-known-quantities gate before
computing anything new.

```
python extremal_values_check.py
```

Gate (must print PASS before any new number):

```
cert(8)   rebuilt = 0.634659   published 0.634659 (UFULL_ASSEMBLY_PROOF.md line 155)
rho(Q,8)  rebuilt = 0.566061   published 0.566061
|lambda2| rebuilt = 0.254888   published 0.255 (CYCLE_CLAIM_REFUTED.md line 38)
f(3)              = 0.8535533906  published 0.8535533906 (THEOREM.md line 133)
T_8 column-stochastic, max column-sum error 0.00e+00
```

Every constant is computed twice by different means:

- **closed-form constants**: float arithmetic versus exact `sympy` surds evaluated to 30
  digits. Worst disagreement over all of them: `7.6e-17`.
- **measured constants**: (A) enumerate all `2^k` lifts, build `T_k`, transform to the
  character basis; versus (B) build the character-basis operator directly from the
  Coset-Uniformity masked-phase formula (THEOREM.md lines 95-99) plus the single defect row,
  with no lift enumeration outside the `r*` fiber. Worst disagreement over `cert`, `rho(Q)`,
  `|lambda_2|` and the whole `v_b` profile, both signs, `k = 6, 8, 10, 11, 12`: `2.6e-14`.
  Method (B) agreeing with (A) to machine precision is also an independent numerical
  confirmation of the CU splitting of THEOREM.md Part II.
- `u_a = 2^{-(a+1)/2}` (THEOREM.md line 105) reproduced to `1.1e-16`, `k = 3..13`.

## Flags: disagreements found with the existing documents

1. **THEOREM.md line 157 prints `0.65597...`; the formula on line 157 evaluates to
   `0.6553300859`.** A misprint, not a mathematical error (`0.65533 < 0.656`, so every
   downstream sentence stays true). Same misprint at `paper/syracuse_spectral_gap.tex`
   line ~456.
2. **THEOREM.md line 25 and line 154-157 present `0.656` as the improved constant without a
   provenance qualifier.** It rests on the `k <= 26`-verified sharp constant `3/4`, which
   LEMMA_C_PROOF.md itself calls verified-not-proved (line 28). The proven constant is row 2,
   `0.6826775358`.
3. **LEMMA_C_PROOF.md line 165 is internally inconsistent.** Theorem C's own statement reads
   "`g_b < sqrt(3/4) = 0.8660` ... Hence `v_b = ||P_b c|| < (3/4) 2^{-b} 2^{-k/2}`". The
   second clause does not follow from the first; `g_b < sqrt(3/4)` gives
   `v_b < (sqrt 3/2) 2^{-b} 2^{-k/2}`, and `sqrt 3/2 = 0.866`, not `0.75`. This single line is
   where the `sqrt(3/4) -> 3/4` upgrade enters the document chain, and everything downstream
   that quotes `0.656` or `0.9005` inherits it. The rest of LEMMA_C_PROOF.md is consistent:
   equation (8) at line 159, the assembly evaluation at lines 184-188 (`0.955`), and the
   status summary at line 25 all correctly carry `sqrt(3/4)`.
4. **UFULL_ASSEMBLY_PROOF.md line 154 prints `cert(6) = 0.633782`; the rebuild gives
   `0.633784`** by both code paths. A 2e-6 discrepancy at `k = 6` only; `k = 8, 10, 12` match
   that table to all six printed digits. Below the 4-significant-figure reproduction
   threshold, so recorded, not escalated.
5. **THEOREM.md's Sharpness remark (lines 146-152) says the constant-setting row is `e = 3`.**
   True of the row-1 envelope, false of `cert(k)`, whose binding row is `e* = 4` for every
   `k >= 4`. Not an error in the bound (which holds row-wise), but the sentence is read as a
   statement about the operator and is not one.
6. **`NEXT_TECHNIQUES.md` (private working directory) states that the transfer-operator
   spectral gap is "provably blind to the `+1` vs `-1` sign".** False for the operator: `cert`
   and the spectrum are sign-sensitive (see the `3x-1` companion, point 2). Blindness holds
   for the `v2`-statistics only.

Flags 1, 2 and 6 are corrections to be applied in place in their own documents (ES Technique
7e, withdraw visibly), not here. Flag 3 is the root cause of flags 1-2 and should be fixed
first.

> **Update, same session (2026-08-02, task H0): flag 3 is FIXED.**
> [LEMMA_C_PROOF.md](LEMMA_C_PROOF.md) Theorem C now reads
> `v_b < sqrt(3/4) 2^{-b} 2^{-k/2}`, with a visible correction block recording the old
> `(3/4)` clause, why it did not follow, and the downstream consequences (proven sharpening
> `0.6827`, proven UFULL constant `0.9551`). Flags 1, 2, 5 and 6 remain OPEN, owned by tasks
> T6.1 (THEOREM.md, README.md, NEXT_TECHNIQUES.md) and T6.2 (the paper). Flag 4 stays
> recorded, not escalated.

## Sources

Public repo, cited by line: [THEOREM.md](THEOREM.md) 21, 25, 34-45, 56-91, 95-99, 100-107,
111-133, 138-144, 146-152, 154-160; [LEMMA_C_PROOF.md](LEMMA_C_PROOF.md) 16-17, 25, 28, 119,
155, 159, 164-165, 177-182, 184-188; [UFULL_ASSEMBLY_PROOF.md](UFULL_ASSEMBLY_PROOF.md) 53-56,
79, 101-118, 137-144, 152-157; [CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md) 35-41.

Private working directory (not in this repo), cited for the two findings reproduced above:
`RETRO_LABELS_2026-08-02.md` (referee corrections 1-3, 5) and
`TRIVIAL_WITNESS_AUDIT_2026-08-02.md` (Findings 1-3).
