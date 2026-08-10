# A uniform spectral gap for the Syracuse transfer operator

[![paper](https://img.shields.io/badge/paper-10pp%20PDF-blue)](paper/syracuse_spectral_gap.pdf)
[![Lean 4](https://img.shields.io/badge/Lean%204-chain%20complete%2C%20sorry--free-brightgreen)](THEOREM.md#lean-formalisation-complete-2026-08-03)
[![certificate](https://img.shields.io/badge/certificate-%E2%89%A4%200.8536%20%3C%201-success)](THEOREM.md)
[![reproducible](https://img.shields.io/badge/figures%20%26%20proofs-reproducible-blue)](#reproduce-everything)
![license](https://img.shields.io/badge/license-public%20domain-lightgrey)

![scope](https://img.shields.io/badge/scope-operator%20spectral%20gap%20only-orange)
[![cycle elimination retracted](https://img.shields.io/badge/cycle%20elimination-retracted-inactive)](CYCLE_CLAIM_REFUTED.md)
![not a proof of Collatz](https://img.shields.io/badge/not%20a%20proof%20of-Collatz-critical)

> **RETRACTION (2026-06-02, read first).** This repository previously claimed that the spectral-gap
> certificate **eliminates non-trivial Collatz cycles**. **That claim is withdrawn - it is false.** A
> uniform spectral gap of the transfer operator does NOT imply the absence of cycles. Decisive control:
> the `3x-1` map has known non-trivial cycles (`{5,7}`, `{17,25,...}`) yet its transfer operator passes
> the identical certificate (`cert ~ 0.606 < 1`, `|lambda_2| ~ 0.29`) even more strongly than `3x+1`.
> The averaging over `2^k` lifts that defines the operator washes out the deterministic orbit
> structure, so cycles are invisible to the spectrum (the same way the doubling map is mixing yet has
> dense periodic points). Full account: [CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md). (The other
> failure mode, divergent trajectories, was never addressed by this project either.)

## In plain terms

**The Collatz game.** Pick a whole number. If it is even, halve it. If it is odd, triple it and add
one. Repeat. The conjecture (open since the 1930s) says you always eventually reach 1. Two ways it
*could* fail: a number could **loop forever** in a cycle that never hits 1, or it could **grow to
infinity**. This project set out to attack the first failure mode (ruling out loops) - and the central
idea, it turns out, **does not work**. What survives is a clean side-result about a matrix.

**The trick that was tried.** Instead of following one number, follow the *cloud* of where numbers
land, and write that as a big table of numbers (a "transfer operator"). The hope was: if the operator's
second-largest characteristic size (eigenvalue) is **below 1** - a "spectral gap" - then the cloud
mixes and there is no room for a hidden loop. We proved that gap, with room to spare, at every scale.

**Why the idea fails.** A spectral gap measures mixing of the *averaged* cloud, and averaging throws
away the exact step-by-step orbit - which is the only thing a loop lives in.

The clean test, and you can check it by hand in ten seconds. The very similar `3x-1` map (triple and
subtract one) **does** have loops:

```
    5  ->  3(5) - 1 = 14 = 2 x 7   ->  7
    7  ->  3(7) - 1 = 20 = 4 x 5   ->  5
```

so `{5,7}` closes, and `{17, 25, 37, 55, 41, 61, 91}` is a second, longer one. Yet the `3x-1` operator
passes the **same** certificate, and passes it **more strongly** (`cert ~ 0.606` against `3x+1`'s
`0.854`). So a gap below 1 cannot be what rules out loops - if it were, it would "rule out" the
`3x-1` loops that plainly exist. (Same lesson as the doubling map `x -> 2x mod 1`, which mixes about
as well as anything can and still has infinitely many loops, dense everywhere.) The cycle claim is
**withdrawn**; details in [CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md).

![spectrum](figures/fig2_spectrum.png)

*The operator's eigenvalues. The top one is 1; the rest sit well below it. This gap is real and proved -
but it does not rule out cycles (the cyclic `3x-1` operator looks identical).*

**What we actually proved.** That spectral gap, for every scale `k`. The matrix splits into blocks by
how divisible by two a number is; the crux was showing each block is a clean, rigid rescaling
(an *isometry*). People expected deep "Gauss sum" machinery; it comes down to the single fact that
**3 is an odd number** (a unit modulo any power of two), plus bookkeeping. Three lemmas (A, B, C), their
shared foundation (coset-uniformity), and the final "below 1" assembly are all proved for every scale.
(The "below 1" number itself comes from A and B alone; C only sharpens it, and C's *sharpest* form is
machine-checked rather than proved - see the corrected constants below.)

![block structure](figures/fig3_incidence.png)

*One block, drawn as its nonzero pattern: exactly one mark per row. That single combinatorial fact is
the entire reason the block is a rigid rescaling.*

**Where it stands.** A correct, elementary, all-scales proof of a uniform spectral gap for the Syracuse
transfer operator (`<= 0.8536`, room to spare) - nothing more, nothing less.

---

## What the theorem is actually about

Worth reading even if you skip everything else, because the obvious reading of "uniform spectral
gap for the Collatz transfer operator" is **wrong**, and the correct one is more interesting.

**The honest object mixes instantly.** Build the transition matrix the *proper* way - condition
on the **full** 2-adic fibre of a residue rather than on the finite window of lifts `m < 2^k`.
Call it `K_k`. Then `K_k` is nilpotent off its top eigenvalue: `|lambda_2(K_k)| = 0`. It reaches
equilibrium in finitely many steps. So **the mixing of the averaged mod-`2^k` Collatz dynamics is
trivial**, and the certificate is not measuring it. (That nilpotence is classical, from the
Bernstein-Lagarias conjugacy - not proved here. The numerics are consistent with it: see
[`verify_truncation_reading.py`](verify_truncation_reading.py).)

**So what is `T_k`?** It is `K_k` with the full-fibre average replaced by the finite lift window
`[0, 2^k)`. That substitution touches exactly one row, so the defect has rank one - and it is
**small in norm, and shrinking**:

```
    ||T_k - K_k||_2  ~  0.75 * 2^(-k/2)
```

The nilpotency index of `K_k` is also small: each Syracuse step deletes at least one low bit, so
the index is about `k`, not `2^(k-1)`. Measured: exactly `k-1` for `k = 4..7`.

**What the naive heuristic predicts, and what the theorem actually adds.** Perturbing a nilpotent
of index `d` by `eps` generically gives eigenvalues of modulus `eps^(1/d)`. Here that is
`(2^(-k/2))^(1/k) -> 2^(-1/2) = 0.7071` - a constant, bounded away from 1. Measured, it climbs
`0.58, 0.59, 0.63, 0.64, 0.65, 0.65` for `k = 4..9`.

So the proven bound `0.853553...` is **the same order as the heuristic**, with true values near
`0.25`. **The theorem does not beat the heuristic, and this repository does not claim it does.**

Its value is that a heuristic is not a proof, and here the gap is not cosmetic: `T_k` is strongly
non-normal with eigenvector condition number growing like `10^k`, and **this project's own
earlier attempt to make a perturbative argument rigorous failed for exactly that reason** (the
March 2026 draft, withdrawn). The current proof is norm-based and never touches eigenvectors,
which is why it survives.

Read it as a **uniform spectral stability result for the finite-window approximation**: swapping
the full 2-adic fibre average for the window `[0,2^k)` - which is what every computation on this
chain actually does - cannot drive the sub-dominant spectrum to the unit circle at any scale.

**One limit, stated plainly.** This is about the *spectrum*, not about *mixing times*. `T_k` is
strongly non-normal and its eigenvector condition number grows like `10^k`, so a bound on
`|lambda_2|` does **not** convert into a total-variation mixing bound uniform in `k`. Spectrum
and mixing come apart here. Conflating them is exactly the error of this project's withdrawn
March 2026 draft; the current proof avoids it by never touching eigenvectors.

---

## What is this good for?

An honest answer, most useful first. This is pure mathematics on an open problem, so item 5 says
plainly where the usefulness stops.

**1. A ten-minute falsification test for Collatz claims - the most transferable thing here.**

Collatz attracts a very large number of claimed proofs. Most of those that argue by averaging,
density, entropy, statistics, or a Markov model share one weakness, and there is now a quick test
for it:

> **Run the argument against `3x - 1`.** If it goes through unchanged, it is wrong - because
> `3x - 1` has the loops `{5,7}` and `{17,25,37,55,41,61,91}` shown above.

The test costs nothing, needs nothing from this repository, and is decisive. It works because
almost every averaged model treats the `+1` and the `-1` identically. That is not a hunch: it is
proved here, machine-checked, for every odd shift and at every depth
([`lean/SignBlind.lean`](lean/SignBlind.lean)). If you are refereeing a Collatz manuscript, try
this first.

**2. Reusable formal mathematics.**

The Lean 4 development is public domain, sorry-free, and modular. Several pieces stand alone and
are useful to anyone formalising nearby material:

| file | what it gives you, independent of Collatz |
|---|---|
| [`lean/CountingLemmas.lean`](lean/CountingLemmas.lean) | 2-adic counting: fibres of `x -> 3x + c` mod `2^k`, valuation layers, shell decompositions |
| [`lean/CharacterBasis.lean`](lean/CharacterBasis.lean) | a genuine `OrthonormalBasis` of characters on `Z/2^k`, with level projections by 2-adic valuation |
| [`lean/GramIdentity.lean`](lean/GramIdentity.lean) | a Gram identity `B*B = 2^{-d} I`, proved without ever forming an adjoint |
| [`lean/SignBlind.lean`](lean/SignBlind.lean) | `3x + c` valuation statistics are the same for every odd `c`, at every depth - the theorem behind item 1 |
| [`lean/ShiftedOperator.lean`](lean/ShiftedOperator.lean) | the `3x+c` development: shifted operator, shells, entry theorem, clean blocks, defect split, and the certificate for every odd `c < 2^k` |
| [`lean/IntegerShift.lean`](lean/IntegerShift.lean) | the shift moved to `c : Z` - the representation in which `3x-1` can be written down at all - with the link theorem, Lemma B, the operator and the shell layer |

Formalising number theory is slow. A sorry-free block someone else already paid for is worth
having.

**3. A negative result, which saves other people's time.**

The companion analysis identifies a broad class of averaged-model arguments and shows that **no
argument in that class can settle Collatz either way** - every such argument is blind to the sign,
and the `3x-1` map answers the sign-blind question in the negative. Knowing which avenues are
closed is worth real time in a problem famous for consuming careers. Negative results are
underrated.

**4. A worked example of a verification discipline.**

Every claim here was measured numerically *before* it was stated, and every theorem was
**mutation-tested** - the statement is deliberately broken in a dozen ways to confirm that each
hypothesis is load-bearing and that the proof is not quietly proving something weaker. Constants
carry labels (`PROVEN` / `DATA`) that never round up. The repository contains a retraction of its
own headline claim. If you run a formalisation project, the method transfers - and it is why the
false claim was caught here rather than by a referee.

**5. Where the usefulness stops.**

There is no cryptographic, engineering, or commercial application, and none is claimed. Transfer
operators and 2-adic dynamics do turn up elsewhere - in symbolic dynamics, and in the analysis of
some arithmetic pseudorandom generators - but no connection to those is established here, and
asserting one would be exactly the kind of overreach this project exists to avoid.

---

## The technical statement

What remains correct and proved is a **uniform spectral gap for the Syracuse (3n+1) mod-`2^k` transfer
operator** `T_k`: the lemmas (A, B, and the sharpening C), their shared Coset-Uniformity foundation,
and the row-sum assembly are proved for every scale `k` by elementary 2-adic / finite-group arguments,
giving `cert(k) <= 0.8536 < 1` and hence `|lambda_2(T_k)| < 1` uniformly. The consolidated statement
and full proof chain - the spectral reduction written out end-to-end (with a 2026-07-05 correction:
`T_k` is not doubly stochastic, so the chain runs through `V = ker(1^T)` and the compression
`P_V U P_V`), plus a simplification showing Lemmas A + B alone suffice (Lemma C sharpens the constant
to **`0.6827` proven**, or `0.6553300859` conditional on a constant machine-verified to `k <= 26`;
corrected 2026-08-03, the earlier figure `0.656` was that conditional value printed without its
provenance and with a digit slip - see [EXTREMAL_VALUES.md](EXTREMAL_VALUES.md)) - is
**[THEOREM.md](THEOREM.md)**. This is a real result about the operator. It simply
does **not** carry the cycle-elimination corollary that was claimed, and it is not a proof of (any
part of) the Collatz conjecture.

## Status at a glance

| Component | State |
|---|---|
| Uniform spectral gap `cert(k) <= 0.853553... < 1`, every scale `k` | **PROVEN** (elementary, all-`k`, no hedge) |
| Lemmas A, B + Coset-Uniformity foundation + row-sum assembly | **PROVEN** (all-`k`) |
| Lemma C as *proved*: `g_b < sqrt(3/4) = 0.8660`, giving `cert <= 0.6826775358` | **PROVEN** (all-`k`) |
| Lemma C in its *sharp* form `g_b <= 3/4`, giving `cert <= 0.6553300859` | **DATA** - machine-verified `k <= 26`, no proof |
| Lean 4: the headline chain end-to-end, from `T_k`'s definition to `\|\|mu\|\| < 0.853554` | **Machine-checked, sorry-free, UNCONDITIONAL** (2026-08-03; 18 files, 449 decls, Mathlib v4.27.0) |
| Lean 4: Lemma C's sharpening (`0.6827` / `0.6553`); the non-degeneracy `gc != 0` | Paper-only - and neither is an input to the headline |
| Lean 4: the certificate at a general **odd** shift `3x+c` - `gap_certificate_shifted` | **Machine-checked, sorry-free** (2026-08; hypotheses are `c` odd, `k >= 3`, `c < 2^k` - no manifest or Parseval binder) |
| Lean 4: the `3x-1` line at an **integer** shift - map, defect residue, offset, link theorem, Lemma B, the operator, the shell layer | **Machine-checked, sorry-free** - but the chain is **incomplete**: Lemma A and the assembly are open |
| A certificate for `3x-1` | **Does not exist** - not proved, not claimed |
| Paper write-up, 10 pp | **Done** - [`paper/syracuse_spectral_gap.pdf`](paper/syracuse_spectral_gap.pdf) |
| Cycle elimination (`gap => no cycles`) | **Retracted, false** - [why](CYCLE_CLAIM_REFUTED.md) |
| Proof of the Collatz conjecture (any part) | Not attempted / not claimed |

*Label discipline (2026-08-03): `PROVEN` means an unconditional proof written out in this repo for
all `k`; `DATA` means machine-verified over a finite range with no proof. Labels never round up - a
bound consuming a `DATA` input stays `DATA`, however good the numerics. Every constant above is
copied from [EXTREMAL_VALUES.md](EXTREMAL_VALUES.md), the single source of truth. As of
2026-08-03 the headline chain **is** machine-checked end-to-end and unconditional -
`GramIdentity.gap_certificate_unconditional`, no hypothesis binder - superseding the note that
stood here, which said it was not. `PROVEN` labels on the headline are now backed by Lean as well
as by the prose proofs; the `DATA` label on Lemma C's sharp form is unaffected and unchanged.*

*On the shifted line (2026-08-10): `gap_certificate_shifted` covers odd `c` with **`c < 2^k`**, and
that hypothesis is why it says nothing about `3x-1`. A `c : Nat` shift cannot express `-1` at all.
The tempting substitute `c = 2^k - 1` is congruent to `-1` mod `2^k` but is a **different operator** -
`oddPart` does not factor through the residue, and the entrywise separation is measured at
`2, 12, 8, 44, 32, 172` for `k = 3..8` (`operator_not_residue_reducible`, and gate L5 of
`calibrate_lemmaA_integer_shift.py`). `IntegerShift.lean` moves the shift to `c : Z` so that `3x-1`
is expressible; it does not certify it. No declaration counts are quoted in these rows - the Lean
census in EXTREMAL_VALUES.md is still absent and four documents disagree on the number.*

## Contents

- [In plain terms](#in-plain-terms) - the whole story, no jargon
- [What the theorem is actually about](#what-the-theorem-is-actually-about) - the obvious reading is wrong
- [What is this good for?](#what-is-this-good-for) - honest uses, and where the usefulness stops
- [The technical statement](#the-technical-statement) - what is proved, in one paragraph
- [Status at a glance](#status-at-a-glance) - every claim with its label
- [The result, precisely](#the-result-precisely) - the certificate, Lemmas A / B / C, what remains
- [Reproduce everything](#reproduce-everything) - one command per claim
- [Repository map](#repository-map) - what each file is
- [References](#references)

![certificate vs k](figures/fig4_certificate.png)

*The certificate value stays flat below 1 as the scale `k` grows, giving a uniform spectral gap. (Note:
the `3x-1` operator, which has cycles, produces the same below-1 curve - so this does not forbid cycles;
see the retraction. Computed from the real operator; reproduce with `python generate_figures.py`.)*

## The result, precisely

Let `U_k` be the Syracuse transfer operator on odd residues mod `2^k`, in the character (Fourier)
basis, decomposed by 2-adic valuation level. Write `Q_k[a,b] = ||P_a U_k P_b||_2` for the operator
norm of the level-`(a,b)` block. The **certificate** is

```
    rho(U_k) restricted to the non-Perron part  <=  rho(Q_k)  <=  max_a sum_b Q_k[a,b] * 2^{a-b}  <  1 ,
```

uniform in `k`, giving a uniform spectral gap `|lambda_2(U_k)| < 1`. **This gap does not eliminate
cycles** - it holds equally for the `3x-1` map, which has cycles ([CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md)).
The certificate is a true statement about the operator; the cycle inference drawn from it was wrong.

![Q heatmap](figures/fig1_Q_heatmap.png)

*The block-norm matrix `Q` (log scale). The bright upper triangle is the cascade `Q[a,b] = 2^{-(b-a)/2}`;
the dark lower triangle is the rank-1 `r*` defect, which vanishes like `2^{-k/2}`.*

The certificate splits into three lemmas (A, B, C), all **proved for all `k`** (elementary), plus
the row-sum assembly, also proved. Lemmas A and B and the assembly are **machine-checked** as of
2026-08-03; Lemma C, which sharpens the headline rather than feeding it, is paper-only.

### Lemma A - upper cascade (within-level isometry)

For `0 <= a < b <= k-2`, `||P_a U_clean P_b||_2 = 2^{-(b-a)/2}` exactly, because the block `B` satisfies
`B*B = 2^{-(b-a)} I`. This reduces - by elementary algebra - to **two uniform-fibre lemmas sharing one
engine** ("3 is a unit mod `2^k` + a multiplication map has uniform fibres on a cyclic 2-group"):

- **CU** (coset-uniformity): also discharges Half-Shift Invariance and the rank-1 `S_odd` structure.
- **SB** (shell-bijection `r -> (3r+1)/2^j mod 2^{k-j}`): the instance the cascade uses.

plus **S4**, a one-line finite geometric series (`Sodd` vanishes iff `k-m <= v2(alpha) <= k-2`), which
was long mistaken for an analytic obstruction. Then `B*B = 2^{-d} I` follows from one nonzero per row
(disjoint column supports) + constant modulus. Verified exact to `k=16` (rational arithmetic, zero
error on and off diagonal), no parity dependence. Full proof: [HALFSHIFT_S4_LEMMA_A_PROOF.md](HALFSHIFT_S4_LEMMA_A_PROOF.md).

### Lemma B - lower back-flow (rank-1 defect)

`||tril(Q_k)||_2 <= sqrt(3) * 2^{-k/2} -> 0`. The lower triangle is entirely the rank-1 defect at the
exceptional residue `r* = -3^{-1} mod 2^k`; the bound reduces to a collision count `coll(k) <= 3*2^k`,
proved unconditionally for all `k` by a 2-adic shell decomposition (per-shell injectivity via a
`mod 3` + range argument). Sharp constant `coll/2^k -> 31/12`. Full proof: [LEMMA_B_PROOF.md](LEMMA_B_PROOF.md).

### Lemma C - per-level decay of the defect covector

`v_b := ||P_b c||_2 <= (3/4) * 2^{-b} * 2^{-k/2}` for all `0 <= b <= k-2`, all `k`. The constant `3/4`
is sharp (equality at `b = k-4`), verified exactly to `k=26`, with a `k`-independent boundary profile.

> **CORRECTION (2026-08-03, task T6.1).** The `3/4` displayed in that sentence is **DATA**, not
> proven. [LEMMA_C_PROOF.md](LEMMA_C_PROOF.md) proves `g_b^2 <= 3/4 - 2^{-p}`, i.e. the constant
> `sqrt(3/4) = 0.8660`, so what is proved for all `k` is `v_b < sqrt(3/4) 2^{-b} 2^{-k/2}`. The sharp
> form `g_b <= 3/4` is machine-verified to `k = 26` and has no proof. Downstream: the **proven**
> Lemma-C sharpening of the certificate is `0.6826775358`, and `0.6553300859` is the value the sharp
> constant would give. Neither touches the headline `0.853553...`, which uses Lemmas A + B only.
> Ladder with labels: [EXTREMAL_VALUES.md](EXTREMAL_VALUES.md). Original text left above, unedited.
It reduces to a periodization-excess bound on the defect covector `c` (the partial Gauss sum at `r*`):
with `h_j = N ||fold_{2^j}(c)||^2`, the bound is `2^b (2 h_b - h_{b+1}) <= 9/16`. (Correction
2026-07-05: the earlier claim here that the `L^2` mass alone fails at `1.25` was wrong - it ignored
the truncation of the upper cascade at the top rows. Lemmas A + B alone give `cert(k) <= 0.8536`;
Lemma C sharpens the constant to `0.6827` proven, `0.6553300859` under the `DATA` sharp constant
- corrected 2026-08-03 from `0.656`, which was the conditional value misprinted and unlabelled.
See [THEOREM.md](THEOREM.md) and the correction note in
[UFULL_ASSEMBLY_PROOF.md](UFULL_ASSEMBLY_PROOF.md).)

Lemma C is now **proved** ([LEMMA_C_PROOF.md](LEMMA_C_PROOF.md)). The covector `c` is a 3x+1
exponential sum; via Lemma B's 2-adic shell method, the assembly-strength bound
`g_b < sqrt(3/4) = 0.866 < 0.961` follows, with the cross-scale identity `S_k(2 xi) = S_{k-1}(xi)` -
once the open link - now **derived** (Lemma H, an elementary parity split: one parity gives a geometric
series that vanishes, the other is exactly the next-scale sum). Lemma C inherits only the Half-Shift
Invariance dependence that Lemmas A and B already carry, and adds no new conditional input.

### What remains

The spectral-gap mathematics is complete and all-`k` (Coset-Uniformity proved in
[HALFSHIFT_S4_LEMMA_A_PROOF.md](HALFSHIFT_S4_LEMMA_A_PROOF.md); `cert(k) <= 0.8536 < 1`, uniform,
consolidated with the full spectral reduction in [THEOREM.md](THEOREM.md)). What
does **not** follow, and is **withdrawn**, is cycle elimination: the gap `=> no cycles` inference is
false ([CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md)). Ruling out non-trivial Collatz cycles would
require an instrument sensitive to the deterministic orbit (e.g. linear-forms-in-logs / height bounds,
as in classical cycle-length results), not this transfer-operator spectral gap.

**The Lean formalisation of the gap is complete as of 2026-08-03.** Eighteen files, 449
theorem/lemma declarations, sorry-free, no `native_decide`, every `#print axioms` set a subset of
`{propext, Classical.choice, Quot.sound}`. The end of the chain is
`GramIdentity.gap_certificate_unconditional`: for every `k >= 3`, every eigenvalue `mu != 1` of
the concretely defined `TransferOperator.Tend k` has `||mu|| < 0.853554`, with no undischarged
hypothesis. See [THEOREM.md](THEOREM.md) for the file-by-file chain. The note that stood here -
"the headline chain end-to-end is **not** machine-checked" - is superseded.

**This changes nothing about scope.** A machine-checked certificate is still a certificate about
the averaged mod-`2^k` chain, and the `3x-1` control still passes the identical certificate while
having real cycles. Indeed the formalisation *sharpens* the limit rather than softening it: the
only property of `3^{-1}` used anywhere in the Lean proof of the hard step is that it is **odd**,
so every construction runs verbatim for `3x-1`. An unconditional certificate is not evidence about
`3x+1` specifically. It formalises a correct-but-not-cycle-eliminating statement.

### What this method delivers at its optimum, and why sharpening it further would not help

The ladder in [EXTREMAL_VALUES.md](EXTREMAL_VALUES.md) is the whole of what this method class - the
averaged mod-`2^k` chain - is known to emit: `0.853553...` proven from Lemmas A + B, `0.6826775358`
proven with Lemma C as actually proved, `0.6553300859` under a constant verified only to `k = 26`,
and `cert(k)`'s own measured value `0.634412`, which the assembly already matches to six digits by
`k = 12`. There is very little slack left to recover, and recovering it would sharpen a number that
is *smaller* for `3x-1` - a map with real cycles - than for `3x+1` (`0.6061` against `0.6345`,
stably in `k`). The mechanism is the same one that makes the gap provable: averaging over `2^k`
lifts dilutes any genuine cycle edge to weight `2^{-k}`, so no quantity in the table separates "has
cycles" from "has no cycles". Note the distinction that makes it worse rather than better: the
certificate is not blind to the sign - it sees it, through the defect fibre - it simply prefers the
wrong map. That much is established. Whether *every* invariant of this averaged chain is likewise
blocked is conjectured, supported by the `3x-1` control, and **not proven here**.

*Absurd-height instantiation, for calibration only.* At `s = 6,586,818,670` odd steps the proven
`0.853553...` gives `4 g^{s/2} ~ 10^{-2.26e8}`; the measured `|lambda_2| ~ 0.27` gives
`~10^{-1.87e9}`. Both are vacuously small, and neither means anything for cycles: the `3x-1`
operator produces an even smaller number and `3x-1` has cycles. This is model theory only.

---

## Reproduce everything

```bash
pip install -r requirements.txt
python generate_figures.py          # the four README figures, from the real operator
python audit_halfshift_s4.py        # coset-uniformity, S4, isometry parity-split + boundaries (0 violations)
python attack1_lemmaA_proof.py      # closed-form B*B = 2^-d I, all (a,b), to k=14
python lemmaB_fact1_rigorous.py     # collision bound coll <= 3*2^k, both parities, vs the true Syracuse fibre
python adv_tril_sep_correct.py      # ||tril(Q_D)|| matches the dense operator (<1e-10); chain to k=24
python verify_assembly.py           # the older Lemma A+C route (cert < 0.9551 proven / 0.9005 under the DATA
                                    #   sharp constant); matches build_T to 6 digits. Superseded by the A+B route.
python fable_assembly_check.py      # THEOREM.md envelope: R_a <= f(k-a), cert <= 0.8536, k=3..13 vs build_T
python explore_vb_profile.py        # the v_b profile and per-row S_a (Lemma C ground truth)
python probe_periodization.py       # g_b^2 = 2^b(2 h_b - h_{b+1}); sup = 9/16 (the Lemma C reduction)
python probe_gb_collision.py        # g_b^2 = E_p/4^p (single index, p=k-b); sum|S|^2 = 2^p coll(p)
python probe_autocorr.py            # E_p = 2^{p-1}(coll-A); Lemma C <=> coll(p)-A_p <= (9/8)2^p
python probe_shell_halfshift.py     # shell proof: j=0 cancels, diag=2^{p-1}, coll-A <= (3/2)2^p
python probe_homometry_proof.py     # Lemma H: parity split proving S_k(2 xi) = S_{k-1}(xi)
python verify_lemma_h.py            # independent integer-exact check of Lemma H (0 failures)
python probe_cycle_link.py          # the 3x+1 vs 3x-1 control: same gap, but 3x-1 HAS cycles (retraction)
python probe_cycle_recovery.py      # cycle-detector tests: spectrum/traces are cycle-blind
```

## Repository map

| File | Role |
|------|------|
| `HALFSHIFT_S4_LEMMA_A_PROOF.md` | Lemma A: within-level isometry + Half-Shift coset-uniformity (proof) |
| `LEMMA_B_PROOF.md` | Lemma B: the collision bound `coll <= 3*2^k` (proof) |
| `STEP4_BLOCK_FORMULA_FOUNDATION.md` | the operator split `U = U_clean + D` and block formula |
| `HalfShiftInvariance_DRAFT.md` | Half-Shift Invariance / rank-1 `S_odd` (Lean draft) |
| `CYCLE_CLAIM_REFUTED.md` | **the retraction**: why the spectral gap does not eliminate cycles (3x-1 control) |
| `CYCLE_STRUCTURE_RECOVERY.md` | follow-up: no cycle structure is recoverable from the spectral side; where it lives |
| `probe_cycle_link.py`, `probe_cycle_recovery.py` | the 3x+1 vs 3x-1 control + cycle-detector tests |
| `paper/syracuse_spectral_gap.pdf` | **the paper** (10 pp): the theorem, all proofs, the Lean section, and the scope/retraction statement |
| `THEOREM.md` | **the consolidated theorem**: full spectral reduction + assembly, `cert(k) <= 0.8536` from A + B alone |
| `lean/` | **Lean 4 formalisation, complete and unconditional** - 18 files, 449 theorem/lemma declarations, sorry-free on Mathlib v4.27.0. `lake build` from `lean/`. Chain and file-by-file breakdown in [THEOREM.md](THEOREM.md). |
| `lean/GramIdentity.lean` | the end of the chain: the upper-block entry theorem, the Gram identity `B*B = 2^{-d} I`, (CLEAN), and `gap_certificate_unconditional` |
| `lean/TransferOperator.lean` | `T_k` itself, defined from the lift window by `Tcount` - what the certificate is *about* |
| `lean/GapCertificate.lean` | the elementary core (FACT 1, SB, CU, envelope, Cauchy-Schwarz assembly) |
| `lean/OperatorChain.lean` | THEOREM.md Part I.1-I.2 (Perron split, compression, Gelfand) |
| `lean/CountingLemmas.lean` | the CU fibre count, SB surjectivity, shell cardinality |
| `EXTREMAL_VALUES.md` | **the constants source of truth**: every certificate constant with its evidence label |
| `UFULL_ASSEMBLY_PROOF.md` | the earlier row-sum assembly from Lemma A + Lemma C: `cert(k) < 0.9551` proven, `< 0.9005` under the `DATA` sharp constant (Remark 2 corrected; superseded by THEOREM.md) |
| `LEMMA_C_PROOF.md` | Lemma C proved (shell method + Lemma H homometry); assembly-strength bound |
| `UFULL_ASSEMBLY_PLAN.md` | the prior cold-start brief for the assembly (now actioned) |
| `verify_assembly.py`, `explore_vb_profile.py`, `verify_lemma_h.py`, `probe_*.py` | assembly + Lemma C / H verification |
| `analytic_proofs.py` | `build_T(k)`: the transfer operator (the numerical oracle) |
| `audit_halfshift_s4.py`, `attack1_lemmaA_proof.py`, `attack1_Sodd.py` | Lemma A / CU / S4 verification |
| `lemmaB_fact1_rigorous.py`, `attack3_*.py` | Lemma B verification |
| `adv_tril_sep_correct.py`, `step4_*.py`, `diagnose_block_formula.py` | block / defect numerics |
| `generate_figures.py` | regenerates the figures |

## References

- L. Mori (2024), *C\*(T_1,T_2) irreducible on l^2(N) iff Collatz*, arXiv:2411.08084.
- T. Tao (2019), *Almost all Collatz orbits attain almost bounded values*, arXiv:1909.03562.
- A. Kontorovich, J. Lagarias (2009-2010), transfer operators for 3x+1.

## License

Public domain. The detailed exploratory history (many dead ends) lives in a separate private
repository; this repo is the curated, reproducible result.
