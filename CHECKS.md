# CHECKS.md - standing checks for the Collatz spectral-certificate project

Every check below is a one-liner with a **current known-good value**. Run them mechanically;
do not re-derive them. A check with no committed script is marked **SCRIPT-WANTED** - that is
an admission of no coverage, not a soft pass.

Provenance: all values are quoted from the 2026-08-02 fourteen-agent audit digests
(`RETRO_LABELS_2026-08-02.md`, `TRIVIAL_WITNESS_AUDIT_2026-08-02.md`, private dir), both of
which were adversarially re-refereed. Where a value was reproduced twice by independent
fresh code, it is marked **[2x]**.

Origin of the habits: ES Technique 8 (`HANDOVER_ES_TECHNIQUES_2026-08-02.md` Section 6).

---

## 0. HEADER GATE - the sign test, applied before anything else

**Gate.** Any candidate lemma, bound, or barrier argument must either (a) be *run* at
`sign = -1` and produce a materially different value, or (b) be explicitly scoped
"model-theory only, says nothing about cycles". There is no third option. State which one, in
the doc, at the point of claim.

Under (a), "materially different" means **stable in `k`, not decaying**. A deviation that
shrinks with `k` is the null result, not a distinction - the entrywise operator deviation
decays (exactly `(floor(k/2)+1) * 2^-k`) while the `cert` gap does not (`0.028-0.032`, flat). Report the deviation
at two separated `k` and show it does not shrink, or the gate fails.

Why this is not optional: `3x-1` passes the certificate **more strongly** than `3x+1`
(`cert ~ 0.6018-0.6061` vs `0.6338-0.6347`; `rho(Q) ~ 0.504-0.539` vs `0.5535-0.5673`;
`|lambda_2| ~ 0.283-0.297` vs `0.252-0.277`, at `k = 6, 8, 10, 11`) and `3x-1` provably has
non-trivial cycles `{5,7}` and `{17,25,37,55,41,...}`. So "gap => no cycles" is FALSE
(`CYCLE_CLAIM_REFUTED.md`, 2026-06-02).

**Standing instance (do not re-assume the easy version).** Negation does **NOT** conjugate the
two chains. The tempting claim - `3(-x)+1 = -(3x-1)` with `v2` preserved, so
`Pi: x -> -x mod 2^k` gives `T_minus = Pi T_plus Pi` and identical spectra - is **FALSE**
[2x]:

- entrywise deviation decays as exactly `(floor(k/2)+1) * 2^-k` (task T3.1, ratio 1.0000 at
  every `k = 4..12`, two independent implementations; `max|T_minus - Pi T_plus Pi| = 0.0625` at
  `k=6`, `0.019531` at `k=8`) and is confined **100% to the defect column**; the clean part *is*
  negation-covariant;
- the **spectra do not converge**: deviation `0.03-0.06` at every `k >= 4`;
  `cert(+1) ~ 0.6345` vs `cert(-1) ~ 0.6061`, a `0.028-0.032` gap **stable in k**;
- mechanism: the lift correspondence `n <-> 2^{2k} - n` pins the negated target mod `2^k` only
  when `v2(3n+-1) <= k`. Every lift in the defect fiber has `v2 >= k`, and for `v2 = k+i`
  (`i >= 1`) the `3x-1` target differs from the negated `3x+1` target by `3*2^{k-i} mod 2^k`.
  The defect rows are exactly antipodal (`r*_minus = -r*_plus`, verified `k = 6, 8, 10`); the
  fiber distribution `c` is not negation-covariant.

**Consequences carried forward.** Any barrier/cap theorem premised on isospectrality of
`T_plus` and `T_minus` is dead on arrival. The **defect fiber is the unique
model-distinguishing object in the whole construction** - the same rank-1 object carrying
24.6% of the binding row. `cert` is a sign-**sensitive** functional; only `v2`-statistics
(drift, entropy) are sign-blind.

> Doc disagreement, unresolved: `NEXT_TECHNIQUES.md` Technique 2 asserts the transfer-operator
> spectral gap "is provably blind to the +1 vs -1 sign". That is **wrong about the operator**.
> Recorded, not edited.

**Coverage:** partial (improved 2026-08-02, task H0). `probe_cycle_link_cert.py` now emits
`cert`, `rho(Q)` and `|lambda_2|` for both signs and self-checks against the published table.
`probe_cycle_link.py` emits only `|lambda_1|, |lambda_2|`. **SCRIPT-WANTED:** the conjugacy
residual (`max|T_minus - Pi T_plus Pi|`, its defect-column concentration, and `r*_minus`) -
that result still exists only in uncommitted scratch code.

---

## 1. ABSURD-HEIGHT LINES

Instantiate every asymptotic or uniform claim at a height a human can be wrong about out loud.

| Check | Known-good value |
|---|---|
| `4*(0.29)^(s/2)` at `s = 6,586,818,670` (STATUS.md's own figure) | `10^(-1.77e9)` |
| same, under the **PROVEN** `|lambda_2|` bound `0.8536` (gap `0.1464`) | `10^(-2.26e8)` |
| same, under **measured** `|lambda_2| ~ 0.27` | `10^(-1.87e9)` |

**The check is not the numeral.** All three are vacuously small, so computing them proves
nothing on its own. The check **fails** unless the accompanying sentence also records the
*direction*: the tiny bound makes `s > 6.6e9` the axiom's **STRONGEST** regime, not a vacuous
one (`spectral_transfer`, `CycleSpectral.lean:205`, quantifies over **all** `delta > 0` with no
hypothesis tying `delta` to the actual gap). The framing "spectral_transfer is essentially
vacuous bookkeeping" is **FALSE-or-RETRACTED**; the bridge axiom is the entire unproven content.

**Standing rider.** Every smallness line of this kind is **model-theory only**. The inference
class it would bridge is refuted (Section 0). Writing one without the rider is the failure this
check exists to catch.

**Coverage:** SCRIPT-WANTED (three-line arithmetic; the missing artifact is the *rider*, which
is a doc assertion, so the wanted script is a grep-style linter that fails any absurd-height
numeral in a doc not accompanied by a scope sentence).

---

## 2. CALIBRATE BEFORE "PROVEN"

**Rule.** A constant "verified up to N" is **DATA** until you can point at the proof step that
delivers it. Recording the label is not enough: name the constant the proof *actually* yields,
and record the ratio between it and the sharp one.

**Live register (the instance that created this rule):**

| Constant | Status | Value |
|---|---|---|
| Lemma C sharp `g_b <= 3/4` (equality at `b = k-4`) | **DATA**, verified exactly to `k = 26` | `0.75` |
| Lemma C **proved** `g_b < sqrt(3/4)` | **PROVEN**, all `k`, all `b` | `0.8660` |
| ratio proven/sharp | - | `1.1547` |
| certificate sharpening, **unconditional** | **PROVEN** | `cert <= 0.683` |
| certificate sharpening, conditional on the DATA constant | conditional | `0.6553300859` |
| UFULL assembly constant, **unconditional** | **PROVEN** | `0.9551` |
| UFULL assembly constant as printed | conditional on the DATA constant | `0.9005` (`0.54692 + 0.35355 = 0.90047`) |

The headline `2^(-3/2) + 2^(-1) = 0.853553...` is **unaffected** by all of this - it comes from
Lemmas A + B alone and needs no Lemma C.

**Second half of the habit - re-derive MINIMALITY, not just the witness.** A check that
confirms "some bound holds" passes while the recorded bound is not the best the proof gives.
The check is: exhibit the proof's own worst case and show no smaller constant survives it. The
`3/4` register above is exactly the failure mode - `sqrt(3/4)` also "holds", and holding was
mistaken for being delivered.

**Other "verified to N" entries in the register** (each is DATA until a proof step is named):

- Lemma A exact to `k = 16` in rational arithmetic (zero error)
- `tril(Q)` separability `< 1e-10` to `k = 24`; rank-1 separability exact to `8e-17`
- assembly matches `build_T` to 6 digits; corrected block formula matches `build_T` to `3e-16`
- Lemma H exact to `k = 14` complex, `k = 26` in magnitude
- `coll(k) <= 3*2^k`, both parities, `k = 3..13`; sharp ratio `coll/2^k -> 31/12 = 2.583`
- `||c|| 2^{k/2}` peak `1.6202` at `k = 4` (`< sqrt(3)`)

**Coverage:** partial.
`attack1_lemmaA_proof.py` (Lemma A closed form), `adv_tril_sep_correct.py` (tril separability),
`lemmaB_fact1_rigorous.py` (FACT 1, `diag = 2^k`, `coll <= 3*2^k`, `k = 3..13`),
`probe_homometry_proof.py` / `probe_selfsimilar.py` (Lemma H).
**SCRIPT-WANTED:** the Lemma C sharp-constant reproduction to `k = 26` with equality at
`b = k-4` (no committed script produces it), and any minimality re-derivation at all.

---

## 3. NUMERICAL INDEPENDENCE BEFORE ANALYTIC ASSEMBLY

**Rule.** Before a new assembled bound is recorded anywhere, an independent fresh-code
reproduction must match. "Independent" means: **imports no module from this repo** (in
particular not `analytic_proofs.build_T`), and rebuilds the operator from the `THEOREM.md`
Setup definition.

**Standing reference row** (the number-referee's values, reproduced twice) [2x]:

| Quantity | Value |
|---|---|
| `cert(8)` | `0.634659` |
| `rho(Q, 8)` | `0.5661` |
| binding row | `e* = 4` for every `k = 4..13` |
| binding-row split (clean cascade + defect) | `0.4786 + 0.1559 = ~0.6345` |
| defect share of the binding row | `24.6%`, stable `k = 6..13` |
| defect share of total weighted mass | `43.6%` at `k=3`, declining to `15.5%` at `k=13` |
| upper-leak (triangle-inequality slack) share | `0.435%` at `k=3`, `<0.01%` for `k >= 8` |
| Lemma A dead-band, blocks zeroed by count | `54.5-57.1%` |
| ...weighted mass carried by live `a<b` blocks | `75.7-83.3%` |

**A scalar alone does not discharge this check.** `cert(8) = 0.634659` is reproducible by an
operator that is wrong elsewhere. The reproduction must also match a *discriminating*
quantity - the binding row `e* = 4` and the split `0.4786 + 0.1559` - because those are what
detect a mis-built defect fiber.

**Standing interpretive result this protects (ES Technique 4).** The ES pathology - a governing
lemma whose trivial branch is the actual witness `86.9%` of the time - is **NOT** present here.
Both pillars do real work: the clean cascade carries the constant, the rank-1 defect is a
genuine minority contributor at `24.6%`, and the dead band zeroes a thick set of blocks
(`54.5-57.1%` by count) while the live blocks still carry `75.7-83.3%` of weighted mass. If a
future reproduction pushes the defect share toward the ES figure, the method has acquired the
cap and the whole route needs re-scoping.

**Bound-vs-measurement note, not an error.** `THEOREM.md`'s Sharpness remark says the row that
sets the constant is `e = 3`. That is true of the **envelope** only. `cert(k)` itself binds at
the interior row `a* = k-4` (`e* = 4`) for every `k >= 4`. The `e = 3` peak is an artifact of
the Cauchy-Schwarz defect bound (`0.5` at `e=3` vs measured `0.156` - a `3.2x`-conservative
step); the Lemma C envelope peaks correctly at `e = 4`. The bound holds row-wise either way.

**Coverage:** partial. `fable_assembly_check.py` checks `R_a <= f(k-a)` for `k = 3..13`, `u_a`
exactness, `||c|| 2^{k/2} <= sqrt(3)`, the `R1/R2` structure, and that reported `cert(k)`,
`rho(Q)` match `~0.6345 / ~0.566`. `verify_assembly.py` checks the analytic row-sum assembly
(but **consumes the DATA-only `3/4` constant** - see Section 2 before quoting its output).
`audit_halfshift_s4.py` covers CU, the S4 dead band, and the `B*B = 2^{-d} I` isometry.
**SCRIPT-WANTED:** the binding-row identification (`e*`), the binding-row split, and all the
share percentages above - no committed script emits any of them; they exist only in
uncommitted scratch code.

---

## 4. PRINTED-CONSTANT RECOMPUTATION

**Rule.** Every displayed numeral in `THEOREM.md`, `README.md`, and `paper/` gets a recompute
line: evaluate **the formula as typeset**, with code that did not produce the printed value,
and compare **digit for digit**. A mismatch is a **fail even when the surrounding inequality
still holds** - which is precisely the live case below, and the reason "is the claim still
true?" is not an acceptable substitute for this check.

**Known-good recomputations:**

| Printed | Recomputed | Verdict |
|---|---|---|
| `f(2) = 0.7071` | `0.70711` | ok |
| `f(3) = 2^{-3/2}+2^{-1} = 0.85355` | `0.85355` | ok |
| `f(4) = 0.8321` | `0.83211` | ok |
| `f(5) = 0.7727` | `0.77275` | ok |
| `G_up = 0.5469` | `2^{-3/2}/(1-2^{-3/2}) = 0.54692` | ok |
| `0.9005` (UFULL) | `0.54692 + 0.35355 = 0.90047` | arithmetic ok; constant conditional, see Section 2 |
| **`0.65597`** | **`0.6553300859`** (max at `e = 4`) | **WRONG - open** |

### Imported OPEN items - owner: future paper-fix session, NOT fixed here

**OPEN-1. The `0.65597` misprint.** `max_{e>=2} [ sum_{d=1}^{e-2} 2^{-3d/2} + 2^{-(e+1)/2} ]`
evaluates to `0.6553300859` at `e = 4`, not `0.65597`. Appears in `THEOREM.md` line 157 and in
`paper/syracuse_spectral_gap.tex` line 456. The mathematical claim `cert <= 0.656` survives
either way (`0.65533 < 0.656`), which is exactly why it went unnoticed. Confirmed by
closed-form recomputation by the number referee.
*Traceability note for the fixer:* the paper's line 456 prints `0.6559\ldots`, not the digit
string `0.65597` that `THEOREM.md` carries. Both differ from `0.6553300859`; fix both.

**OPEN-2. The `3/4` constant boxed as a Theorem in the paper.**
`paper/syracuse_spectral_gap.tex` line 431 states `\begin{theorem}[Lemma C]` with
`v_b \le \tfrac{3}{4} 2^{-b} 2^{-k/2}`. The proof delivers only `sqrt(3/4) = 0.866`; `3/4` is
verified to `k = 26` and is **DATA**. Same overclaim sits in `THEOREM.md` and in
`CYCLE_CLAIM_REFUTED.md` line 58. Downgrade the box or prove the constant.

**OPEN-3.** See Section 5.

**Coverage:** SCRIPT-WANTED. No committed script recomputes displayed constants from the
typeset formulas. This is the cheapest missing script in the repo and would have caught
OPEN-1 on the day it was written.

---

## 5. REPRO-POINTER AUDIT

**Rule.** Every table in every doc names a script that produces **every column**. Naming is not
evidence: **run the named script, capture stdout, and require each column header of the table
to be derivable from that output.** A "Reproduce:" line that points at a script emitting a
different set of quantities is a broken pointer, and it will read as verified for years.

**OPEN-3 - CLOSED 2026-08-02 (task H0).** `CYCLE_CLAIM_REFUTED.md` used to read
`Reproduce: python probe_cycle_link.py`, a script printing **only** `|lambda_1|` and
`|lambda_2|` - so four of the six data columns of the table at lines 35-41 had no producer in
the public repo.

Resolution: `probe_cycle_link_cert.py` was added and emits all six columns for both signs,
with a built-in regression check against the published digits (run 2026-08-02: all 24 values
reproduced, worst deviation 0.99x the print tolerance). The `Reproduce:` line now names both
scripts and records what each covers. The numbers had already been **doubly reproduced** by
independent fresh code during the audit [2x]; they are now reproducible from the repo itself.

**Values the replacement script must emit** (`CYCLE_CLAIM_REFUTED.md` lines 35-41):

| k | 3x+1 cert | 3x+1 rho(Q) | 3x+1 \|l2\| | 3x-1 cert | 3x-1 rho(Q) | 3x-1 \|l2\| |
|---|---|---|---|---|---|---|
| 6  | 0.6338 | 0.5535 | 0.277 | 0.6018 | 0.5039 | 0.297 |
| 8  | 0.6347 | 0.5661 | 0.255 | 0.6061 | 0.5272 | 0.293 |
| 10 | 0.6345 | 0.5673 | 0.270 | 0.6061 | 0.5365 | 0.291 |
| 11 | 0.6343 | 0.5664 | 0.252 | 0.6060 | 0.5388 | 0.283 |

**Coverage:** SCRIPT-WANTED (the 3x-1 cert/rho script, task H0). Note that the audit of pointers
itself is mechanisable - a linter that, for each `Reproduce:` line, runs the script and diffs
column headers against its stdout - and does not exist either.

---

## 6. Other standing facts a check must not silently contradict

These are not checks; they are the current true state, listed so a check that "passes" against
a stale assumption is caught.

- `T_k` is **NOT** doubly stochastic; the stationary distribution is not exactly uniform (row
  sums deviate `~0.764 * 2^{-k/2}`). `E[v2] = 2` is exact only in the idealised geometric
  model, `O(2^{-k/2})`-approximate for the real chain.
- The Lean core (`lean/GapCertificate.lean`) is sorry-free (`0 sorry`, `0 admit`, `0 axiom`),
  but the assembly is **ABSTRACT**: Lemma A, R1 and Lemma B enter as named hypotheses
  (`hQupper`, `hQlower`, `hL2`). The Part I operator chain, the CU fiber count, SB
  surjectivity/cardinality, and Lemma B shell counting are **not** formalised.
- `best_approximation_bound` (`DiophantineCycle.lean:78`, legacy private tree) was **FALSE as
  formalised**. **Partially repaired 2026-08-02 (task H0), then repaired again the same day
  after an adversarial referee pass.** The first witness (`s = 1330`, `T = 2108`, a non-reduced
  multiple of the convergent `1054/665`) was killed by adding `Nat.Coprime T s` - but that was
  **not sufficient**: `isConvergentDenom` is a finite `Finset` literal capped at
  `6,586,818,670`, so any convergent denominator beyond the cap satisfies the hypothesis
  vacuously. Coprime counterexample: `s = 65,470,613,321`, `T = 103,768,467,013`
  (`|T/s - log2 3| = 1.0163e-22 < 1/(2s^2) = 1.1665e-22`) - convergent #22, which that file's
  own header names as "the first dangerous convergent". A range bound `s <= 6586818670` was
  added alongside the coprimality hypothesis. **Lesson for this checklist: a "not in the list"
  hypothesis is only as strong as the list is complete.**
- Legacy private Lean tree: **8** genuine axiom declarations remain - `AutomataApproach.lean` 2,
  `BoundedTrajectory.lean` 1, `Class3RunBounds.lean` 2, `CycleSpectral.lean` 2,
  `FrequencyAnalysis.lean` 1. Three of them (`Class3RunBounds.lean:131,159`,
  `FrequencyAnalysis.lean:229`) are **vacuous** - each concludes `exists b, b > 0 AND True`.
- The two repos diverged in **opposite** directions: the 2026-07-05 corrections landed only in
  the private copies, the 2026-06-02 retraction banners only in the public ones. Neither copy
  was a superset. **Reconciled 2026-08-02 (task H0)** in both directions: the boxed Lemma A in
  `STEP4_BLOCK_FORMULA_FOUNDATION.md` is now stated for `U_clean` (the `U_full` form was
  numerically false - that doc's own table shows `max|Q_up - 2^{-d/2}| = 1.4e-04` at `k=8`);
  the `HALFSHIFT` closing bullet and the `LEMMA_B` top-atom paragraph were ported here; the
  retraction banners were ported to the private copies. Two textual corruptions in this repo
  (`LEMMA_B_PROOF.md` FACT 1 step 3 - which had lost the range argument **and the QED** since
  the very first public commit - and `HALFSHIFT_S4_LEMMA_A_PROOF.md` line ~123) were restored
  from the private copies; a repo-wide sweep for the same link-rewrite signature found no
  further instances. **Re-check on any future port: the two repos are only as aligned as of
  this date.**
- **The reconciliation is PARTIAL - "content-identical" is NOT yet true** (adversarial referee,
  2026-08-02). Two known remaining divergences, deliberately left for a session with the time
  to review the mathematics rather than ported blind:
  (i) `HALFSHIFT_S4_LEMMA_A_PROOF.md` Sections 1-2 - the **private** copy is longer and carries
  the SB multiplicity-exactly-1 paragraph and the derivation of half-shift invariance as a CU
  corollary; the public copy still says "Lemma 1 of `HalfShiftInvariance_DRAFT.md` needs five
  steps". The private copy appears to be ahead here.
  (ii) `LEMMA_B_PROOF.md` Section 7 - public and private disagree on whether R1/R2/Lemma A are
  unconditional. The private copy now carries an explicit correction block recording this as an
  **open disagreement, not resolved** (see the PROVEN-label qualifier in
  [EXTREMAL_VALUES.md](EXTREMAL_VALUES.md)).
  Owner: task T6.1. Do not treat the two repos as mirrors until these close.
- **Lemma A ingredient (ii) - the within-level isometry `B*B = 2^{-(b-a)} I` - is PROVED for all
  `k`** (settled 2026-08-02, task W1-A). It is proved by `HALFSHIFT_S4_LEMMA_A_PROOF.md`
  **Sections 1 (SB) + 3 (S4) + 4 (owner count)** - **not** Sections 1-2, and **not** from CU
  (CU discharges the separate masked-phase ingredient (i), and R1/R2). That mis-citation was
  repeated in several documents; do not propagate it. Consequence: the headline
  `cert(k) <= 0.853553...` for all `k >= 3` is **PROVEN unqualified** - an earlier
  "PROVEN-modulo-(ii)" hedge was withdrawn. Still NOT rounded up alongside it: the Lemma C
  sharp `3/4` stays DATA (proven sharpening is `0.683`), `gap => no cycles` stays
  FALSE-or-RETRACTED, and the headline chain is **not** machine-checked (Lean covers the
  envelope/assembly core only).
- Audit headline count, for drift detection: **131** claims labelled - 69 PROVEN, 19 DATA,
  14 FALSE-or-RETRACTED, 11 STALE-superseded, 9 CONJECTURAL, 7 CITED, 2 COMPLETE-at-sketch-level
  (4 labels referee-corrected downward, none upward).

### Flags carried in from the audit (do not resolve silently)

- **Theorem count disagreement.** The audit's standing summary says `GapCertificate.lean` has
  **25 theorems**; the public `README.md` claim it labels says **15 theorems**. Both figures
  appear in `RETRO_LABELS_2026-08-02.md`. Unresolved.
- **Stale gap arithmetic.** One audit entry quotes "gap `>= 0.1464` (`0.344` with Lemma C)".
  The `0.344` uses the DATA-only `0.656`; the unconditional figure is `1 - 0.683 = 0.317`.
  Pre-dates referee correction 2.

---

## 7. How to run (script -> check map)

| Script | Covers |
|---|---|
| `fable_assembly_check.py` | S3 (`cert`, `rho(Q)`, `R_a <= f(k-a)`, `u_a`, `||c||` bound, R1/R2), S2 envelope |
| `verify_assembly.py` | S3 analytic row-sum assembly - **consumes the DATA-only `3/4` constant** |
| `audit_halfshift_s4.py` | S2 (CU, S4 dead band, `B*B = 2^{-d} I` isometry) |
| `attack1_lemmaA_proof.py` | S2 (Lemma A closed form, `k = 16` rational) |
| `adv_tril_sep_correct.py` | S2 (`tril(Q_D)` separability) |
| `lemmaB_fact1_rigorous.py` | S2 (FACT 1, `diag = 2^k`, `coll <= 3*2^k`, `k = 3..13`) |
| `probe_homometry_proof.py`, `probe_selfsimilar.py` | S2 (Lemma H) |
| `probe_cycle_link.py` | **partial S5 only** - emits `|l1|, |l2|`; **not** `cert` or `rho(Q)` |
| `probe_cycle_link_cert.py` | S0 + S5 - `cert`, `rho(Q)`, `|l2|` **both signs**, self-checking against the published table |

**SCRIPT-WANTED, in priority order** (item 1 closed 2026-08-02):

1. ~~3x-1 `cert`/`rho(Q)` script (OPEN-3)~~ - **DONE**, `probe_cycle_link_cert.py`.
2. Printed-constant recomputation linter (Section 4) - cheapest, catches OPEN-1-class errors.
3. Binding-row + defect-share reporter (Section 3) - `e*`, the split, the share percentages.
4. Negation-conjugacy residual reporter (Section 0) - `max|T_minus - Pi T_plus Pi|`, defect-column
   concentration, `r*_minus`.
5. Lemma C sharp-constant reproduction to `k = 26` with equality at `b = k-4` (Section 2).
6. `Reproduce:`-pointer linter (Section 5) and absurd-height rider linter (Section 1).
