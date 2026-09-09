/-
# The `3x + c` operator at an **integer** shift — and therefore at `3x − 1`

## WHY THIS FILE EXISTS

`ShiftedOperator.lean` proves `gap_certificate_shifted` for `3x + c` with **`c : ℕ`**.  Its own
§4 records why that is not enough: `-1` and `2^k - 1` agree mod `2^k`, but `oddPart` does **not**
factor through the residue, so `c = 2^k - 1` is a different operator.  `syracuseS` takes `c : ℕ`
and therefore **cannot state anything about `3x − 1` at all**.

This file moves the shift to `c : ℤ`, which is the only representation in which `3x − 1` can be
written down.

## SCOPE OF *THIS* FILE, STATED HONESTLY

This is the **first slice** of that development: the map, the defect residue, the offset, the
discharge of the offset hypothesis at `c = -1`, the link theorem, Lemma B, the integer-shifted
**operator** (§6), the **shell layer** (§6c) and — added last — Lemma A's **entry theorem**
(§6d).  It is **not** a certificate for `3x − 1`, and it does not claim one.

**What is still open, precisely:** the clean blocks and the Gram identity (`BentZ`,
`gram_upperZ`, `cleanBlockCLMZ`, `norm_sq_clean_blockZ`) — step `4c` — and then the assembly,
which is a separate task after them.  `hL2`/`hParseval` remains open here as it does at `c = 1`.

**What §6d closed, and at what scope.**  `upper_entry_eqZ` and `norm_upper_entryZ` are done,
for odd `c ≥ -1`.  That bound is **not** the `A_c ≤ 0` exclusion of §3 wearing a new hat: it is
narrower and weaker, and it comes from `oddPartZ`'s `Int.toNat` clamp rather than from any
degeneracy — gate L7 measures the coset-uniformity step failing at every negative `3x + c`.
Since an odd `c ≥ -1` is either `-1` or a non-negative shift the `c : ℕ` chain already covers,
the new content of §6d is `3x − 1` itself, which is the map this file exists for.  A future
`oddPartZ` defined on `ℤ` proper would lift the restriction; nothing else here would change.

It resurrects **no cycle conclusion**.  A certificate holding across a family of shifts, several
of which *have* cycles, makes "spectral gap ⟹ no cycles" false for *more* maps — if the integer
chain lands, `CYCLE_CLAIM_REFUTED.md` gets **stronger**, not weaker.

## THE REPRESENTATION DECISION (route a′), and why

Recorded in full in `DECISION_INTEGER_SHIFT.md`, and summarised here because ground rule 6 says
scope is reported in the artifact:

* Route (a), a full `c : ℤ` reparametrisation, forces the cases `A_c ≤ 0` into scope.  Those are
  real — `calibrate_integer_shift.py` gate I2 shows `A_c = 0` occurs at exactly `c = -3t` for odd
  `t < 2^k`, where the AP model degenerates because `oddPart 0` is undefined — and they are
  **not on the path to `3x − 1`**.
* Route (b), defining `oddPart (3n - 1)` over `ℕ` alone, would transcribe the ~4560-line chain a
  fourth time to prove one map.
* **Route (a′), taken here:** shift moves to `ℤ`, and the offset is carried as a **hypothesis**
  (`1 ≤ apAZ c k`) rather than derived from `c < 2^k`.  At `c : ℕ` that hypothesis is the
  existing size argument; at `c = -1` it is `apAZ_minus_one_mem` below.  `A_c ≤ 0` is
  **deliberately out of scope**, and this sentence is the record of that so a later reader does
  not mistake its absence for an oversight.

## CALIBRATION FIRST (ground rule 1)

Every statement here was measured before it was stated, by `calibrate_integer_shift.py`
(gates I1–I5, exit 0):

* **I1** — `r*_c` is unique and odd at integer `c`; the sign of `c` is irrelevant to the
  invertibility of `3` mod `2^k`.  That is `rstarZ_spec` / `rstarZ_odd`.
* **I2** — the trichotomy `A_c ∈ {1,2,3}` is **false** at negative `c` (measured range
  `{-1,0,1,2,3}`), which is why it is a hypothesis here and not a theorem.
* **I2** — `A_{-1}` is `1` at odd `k` and `2` at even `k`: it **alternates**, it is not
  constant.  That is `apAZ_minus_one_mem`, proved here from size bounds alone — no closed form
  for `r*_{-1}` is needed, and none is asserted.

## MUTATION TABLE (ground rule 2), continuing the corpus numbering from S126

Each mutation makes a statement **harder** or a hypothesis **weaker**, never the conclusion
weaker.  Every one was confirmed to fail, **and the error text read** — a mutation that fails
for a non-mathematical reason proves nothing, and one of these did so on its first run
(S127 was initially written importing the wrong module, so it failed on `unknown namespace`;
it is recorded here in its corrected form).

| # | Target | Mutation | Failure, and why it is mathematical |
|---|---|---|---|
| S127 | `rstarZ_spec` | conclusion `2^k ∣ ·` strengthened to `2^(k+1) ∣ ·` | type mismatch at `dvd_add`; and the claim is **false**, not merely unprovable — `3r*_{-1} - 1` is `8, 32, 128` at `k = 3, 5, 7`, divisible by `2^k` and never by `2^(k+1)` |
| S128 | `apAZ_minus_one_mem` | conclusion `= 1 ∨ = 2` strengthened to `= 1` | `omega` cannot close `A = 1` from `0 < A < 3`; `A = 2` at even `k` is a real counterexample |
| S129 | `syracuseZ_odd` | hypothesis `0 < 3n + c` dropped | cannot prove `(3n+c).toNat ≠ 0`; without it `Int.toNat` clamps at `0` and the map is not odd |
| S130 | `rstarZ_minus_one_pos` | `1 ≤ r*` strengthened to `2 ≤ r*` | unprovable from oddness alone, and `r* = 1` genuinely occurs (at `c = -3`, every `k`) |
| S131 | `cmodN_odd` | hypothesis `c % 2 = 1` dropped | cannot derive an odd residue; an even `c` has an even residue mod `2^k` |
| S132 | `link_theorem` | hypothesis `1 ≤ apAZ c k` dropped | `positivity` fails on `A_c + 3m`; at the degenerate shifts it is `≤ 0`, where `Int.toNat` clamps and the identity is false |
| S133 | `oddPartZ_two_pow_mul` | hypothesis `0 < X` dropped | cannot produce the ℕ representative; at `X ≤ 0` both sides are clamps, not odd parts |
| S134 | `fibre_odd` | hypothesis `c % 2 = 1` dropped | cannot supply `rstarZ_odd`; an even shift has an even `r*`, so the fibre is not odd |
| S135 | `link_theorem_minus_one` | offset pinned to the constant `1` instead of `apAZ (-1) k` | type mismatch; and **false** by computation — at `k = 4` the true fibre is `[1,5,1,11]` against the pinned `[1,1,7,5]`.  This is precisely the overclaim ("`A_{-1} = 1` at every `k`") that the calibration caught in the first draft of `DECISION_INTEGER_SHIFT.md` |

| S136 | `collZ_le_sharp` | hypothesis `1 ≤ apAZ c k` dropped | cannot produce `0 < (apAZ c k).toNat`; at the degenerate shifts the offset is `≤ 0` |
| S137 | `collZ_minus_one_le_sharp` | `≤` strengthened to `=`, i.e. `3x − 1` **attains** the bound | `omega` cannot close it; and **false** by computation — `collZ (-1) 3 + 2 = 20`, not `24`.  `3x − 1` has offset 1 or 2, so it is not the extremal witness (`collZ_minus_one_offset_ne_three`) |
| S138 | `cfZ_eq_cfA` | hypothesis `c % 2 = 1` dropped | `link_theorem` needs an odd shift; without it the fibre is not odd and the identity has no content |
| S139 | `collZ_le_sharp` | additive slack `+2` improved to `+3` | type mismatch against `collA_le_sharp`; and **false** — at `c = 3` (offset 3) the bound is *attained*: `coll + 2 = 24, 48, 96` at `k = 3,4,5`, exactly `3·2^k` |

| S140 | `TcountZ_natCast` | generalised from `c : ℕ` to **the trap**: `TcountZ c k u r = TcountS (cmodN c k) k u r` for all `c : ℤ` | `simp made no progress` — `syracuseZ_natCast` does not apply at a genuine integer shift; and **false** by computation, `∑\|TcountZ (-1) − TcountS (cmodN (-1))\| = 2, 12, 8, 44` at `k = 3..6` (§7), matching gate L5 |
| S141 | `UcleanZ_natCast` | same generalisation one level up: `UcleanZ c k = UcleanS (cmodN c k) k` for all `c : ℤ` | `rfl` fails on both branches of the `if`; false for the same reason as S140, since the clean entries are `TkZC = TcountZ / 2^k` |
| S142 | `syracuseZ_ne_syracuseS_cmodN` | single witness `n = 1` strengthened to **all** `n` | type mismatch; and **false** — the two maps *agree* at `n = 3`, both giving `1`.  They are different operators, not disjoint ones, which is why the separation needs a witness |
| S143 | `TkZ_nonneg` | `0 ≤` strengthened to `0 <` | `positivity` reports it can prove non-negativity only; and **false** — `TcountZ (-1) 4` has zero entries throughout (§7's matrix) |

| S144 | `shellZ_residue` | valuation bound weakened from `j + 1 ≤ k` to `j ≤ k` | `omega` cannot supply the bound; and **false** — at `c = -1, k = 3, j = 3` the integer shell is `{3}` and the residue shell is `∅`.  A valuation *at* `k` is not congruence data mod `2^k` |
| S145 | `sbMapZ_residue` | conclusion strengthened from `sbMap` (the quotient **mod `2^(k-j)`**) to `syracuseZ` itself (the full odd part) | type mismatch; and **false** — §7 evaluates both columns, `sbMap` pairs agree `(5,5), (11,11), …` while `syracuse` pairs are `(5,21), (11,27), …`.  This is gate L6's boundary, and it is the §6b trap one level down |
| S146 | `shellZ_card` | hypothesis `c % 2 = 1` dropped | `omega` cannot produce the oddness; and **false** — at the even shift `c = -2`, `k = 5`, `j = 2` the shell is **empty** (card `0`, against `2^(k-1-j) = 4`), because an even shift makes `3r + c` odd for odd `r` |
| S147 | `v2Z_congr` | bound weakened from `j + 1 ≤ k` to `j ≤ k` | `omega` cannot supply it; and **false** — `x = 4`, `y = 8`, `j = k = 2`: `2^2 ∣ 4 - 8`, `v2Z 4 = 2`, but `v2Z 8 = 3` |

**Two mutations in this batch first failed for non-mathematical reasons** and were re-run:
S132/S135 initially reported `unknown identifier`, because `lake env lean` typechecks without
writing the `.olean`, so the scratch files imported a stale module.  A stale-import failure
reports identically to a refutation and proves nothing — `lake build` the target first.
-/
import ShiftedOperator

namespace IntegerShift

open Finset GapCertificate CountingLemmas TransferOperator ShiftedOperator LemmaA

/-!
--------------------------------------------------------------------------------
## §1. The integer-shifted Syracuse map
--------------------------------------------------------------------------------
-/

/-- The odd part of a positive integer, as a natural.  Guarded: callers supply `0 < m`.
`oddPart 0` is undefined mathematically, and gate I2 shows that case is reachable at negative
shifts (`c = -3t`), so every downstream statement carries a positivity hypothesis rather than
relying on `Int.toNat`'s clamp at `0` — see `syracuseZ_odd` and `three_add_pos`. -/
def oddPartZ (m : ℤ) : ℕ := m.toNat / 2 ^ v2 m.toNat

/-- **The Syracuse map with an integer shift.**  This is the definition `syracuseS` could not
express: `c : ℤ`, so `c = -1` is `3x - 1`. -/
def syracuseZ (c : ℤ) (n : ℕ) : ℕ :=
  if n % 2 = 0 then n else oddPartZ (3 * (n : ℤ) + c)

/-- `3x - 1`, the map the control experiment is about, now a Lean definition. -/
abbrev syracuseMinus (n : ℕ) : ℕ := syracuseZ (-1) n

/-- **The bridge.**  At a non-negative shift the integer map is the `c : ℕ` map of
`ShiftedOperator`, so nothing already proved is re-proved on a new object. -/
theorem syracuseZ_natCast (c n : ℕ) : syracuseZ (c : ℤ) n = syracuseS c n := by
  unfold syracuseZ syracuseS oddPartZ
  by_cases h : n % 2 = 0
  · simp [h]
  · simp only [if_neg h]
    have hcast : 3 * (n : ℤ) + (c : ℤ) = ((3 * n + c : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]

/-- At `c = 1` the integer map is the original `3x+1` Syracuse map. -/
theorem syracuseZ_one (n : ℕ) : syracuseZ 1 n = syracuse n := by
  have := syracuseZ_natCast 1 n
  simpa using this

/-- `3n + c > 0` on the odd naturals `n ≥ 1` whenever `c ≥ -1`; in particular for `3x - 1`.
This is the positivity side condition that `oddPartZ` needs, discharged once. -/
theorem three_add_pos {c : ℤ} (hc : -1 ≤ c) {n : ℕ} (hn : 1 ≤ n) : 0 < 3 * (n : ℤ) + c := by
  have : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  linarith

/-- The integer-shifted map lands on an odd residue, exactly as the `c : ℕ` map does.  The
positivity hypothesis is what replaces `ℕ`'s automatic `0 ≤`. -/
theorem syracuseZ_odd {c : ℤ} {n : ℕ} (hn : n % 2 = 1) (hpos : 0 < 3 * (n : ℤ) + c) :
    syracuseZ c n % 2 = 1 := by
  unfold syracuseZ oddPartZ
  rw [if_neg (by omega : ¬ n % 2 = 0)]
  -- name-ambiguity trap: `oddPart_odd` exists in more than one namespace here
  exact ShiftedOperator.oddPart_odd (by omega : (3 * (n : ℤ) + c).toNat ≠ 0)

/-!
--------------------------------------------------------------------------------
## §2. The defect residue at an integer shift
--------------------------------------------------------------------------------

`rstarZ` is **not** a new construction: `rstarS` already depends on `c` only through `c % 2^k`,
and the residue of an integer mod `2^k` is a natural.  Gate I1 measured that uniqueness and
oddness are untouched by the sign of `c`, and the proofs below inherit rather than repeat.
-/

/-- The natural representative of `c` mod `2^k`. -/
def cmodN (c : ℤ) (k : ℕ) : ℕ := (c % (2 ^ k : ℤ)).toNat

theorem cmodN_cast (c : ℤ) (k : ℕ) : ((cmodN c k : ℤ)) = c % (2 ^ k : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg c (by positivity))

/-- An odd integer has an odd residue mod `2^k`, for `k ≥ 1`. -/
theorem cmodN_odd {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k) : cmodN c k % 2 = 1 := by
  have hdvd : (2 : ℤ) ∣ (2 ^ k : ℤ) := dvd_pow_self 2 (by omega)
  have h : (c % (2 ^ k : ℤ)) % 2 = c % 2 := Int.emod_emod_of_dvd c hdvd
  have : ((cmodN c k : ℤ)) % 2 = 1 := by rw [cmodN_cast]; omega
  omega

/-- **The defect residue at an integer shift.** -/
def rstarZ (c : ℤ) (k : ℕ) : ℕ := rstarS (cmodN c k) k

/-- **The defining property of `rstarZ`**, as an integer congruence: `3 r* + c ≡ 0 (mod 2^k)`.
Without this the definition would be an unchecked guess. -/
theorem rstarZ_spec {c : ℤ} {k : ℕ} (hk : 1 ≤ k) :
    ((2 ^ k : ℤ)) ∣ (3 * (rstarZ c k : ℤ) + c) := by
  have hN : (3 * rstarS (cmodN c k) k + cmodN c k) % 2 ^ k = 0 := rstarS_spec hk
  have hdvdN : (2 ^ k : ℕ) ∣ (3 * rstarS (cmodN c k) k + cmodN c k) := Nat.dvd_of_mod_eq_zero hN
  have hdvdZ : ((2 : ℤ) ^ k) ∣ ((3 * rstarS (cmodN c k) k + cmodN c k : ℕ) : ℤ) := by
    have := Int.natCast_dvd_natCast.mpr hdvdN
    push_cast at this
    exact this
  -- c splits as 2^k * (c / 2^k) + (c mod 2^k), and the second summand is `cmodN`
  have hsplit : c = (2 ^ k : ℤ) * (c / 2 ^ k) + (cmodN c k : ℤ) := by
    rw [cmodN_cast]
    exact (Int.mul_ediv_add_emod c (2 ^ k)).symm
  have hrw : 3 * (rstarZ c k : ℤ) + c
      = ((3 * rstarS (cmodN c k) k + cmodN c k : ℕ) : ℤ) + (2 ^ k : ℤ) * (c / 2 ^ k) := by
    unfold rstarZ
    push_cast
    linarith [hsplit]
  rw [hrw]
  exact dvd_add hdvdZ (Dvd.intro _ rfl)

theorem rstarZ_lt {c : ℤ} {k : ℕ} : rstarZ c k < 2 ^ k := rstarS_lt

theorem rstarZ_odd {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k) : rstarZ c k % 2 = 1 :=
  rstarS_odd (cmodN_odd hc hk) hk

/-!
--------------------------------------------------------------------------------
## §3. The offset `A_c`, and why it is a hypothesis
--------------------------------------------------------------------------------
-/

/-- **The offset** `A_c := (3 r*_c + c) / 2^k`.  At `c : ℕ` with `c < 2^k` this lies in
`{1,2,3}` by a size argument.  Gate I2 shows that is **false** at negative `c` — measured range
`{-1,0,1,2,3}` — so downstream statements carry `1 ≤ apAZ c k` as a hypothesis. -/
def apAZ (c : ℤ) (k : ℕ) : ℤ := (3 * (rstarZ c k : ℤ) + c) / 2 ^ k

theorem apAZ_mul {c : ℤ} {k : ℕ} (hk : 1 ≤ k) :
    (2 ^ k : ℤ) * apAZ c k = 3 * (rstarZ c k : ℤ) + c :=
  Int.mul_ediv_cancel' (rstarZ_spec hk)

/-!
--------------------------------------------------------------------------------
## §4. `3x − 1`: the offset hypothesis, discharged
--------------------------------------------------------------------------------

Gate I2's probe table shows `A_{-1}` alternating `1, 2, 1, 2, …` with the parity of `k`.  The
proof below needs **no closed form for `r*_{-1}`** — size bounds alone give `A_{-1} ∈ {1,2}`,
and both are offset classes the `c : ℕ` development has already proved.
-/

/-- `r*_{-1} ≥ 1`: it is odd, hence non-zero. -/
theorem rstarZ_minus_one_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ rstarZ (-1) k := by
  have := rstarZ_odd (c := -1) (by decide) hk
  omega

/-- **The offset hypothesis, discharged at `3x − 1`.**  `A_{-1} ∈ {1,2}` at every `k ≥ 1`.
So `3x − 1` never meets the degenerate `A_c ≤ 0` that negative shifts introduce. -/
theorem apAZ_minus_one_mem {k : ℕ} (hk : 1 ≤ k) : apAZ (-1) k = 1 ∨ apAZ (-1) k = 2 := by
  have hmul := apAZ_mul (c := -1) hk
  have hlow : (1 : ℤ) ≤ (rstarZ (-1) k : ℤ) := by exact_mod_cast rstarZ_minus_one_pos hk
  have hhigh : (rstarZ (-1) k : ℤ) < 2 ^ k := by exact_mod_cast rstarZ_lt (c := -1) (k := k)
  have hpk : (0 : ℤ) < 2 ^ k := by positivity
  -- 2^k * A = 3 r* - 1, and 0 < 3 r* - 1 < 3 * 2^k
  have hval : (2 ^ k : ℤ) * apAZ (-1) k = 3 * (rstarZ (-1) k : ℤ) - 1 := by
    rw [hmul]; ring
  have h1 : (0 : ℤ) < (2 ^ k : ℤ) * apAZ (-1) k := by rw [hval]; linarith
  have h2 : (2 ^ k : ℤ) * apAZ (-1) k < 3 * 2 ^ k := by rw [hval]; linarith
  have hA1 : 0 < apAZ (-1) k := by nlinarith
  have hA2 : apAZ (-1) k < 3 := by nlinarith
  omega

/-!
--------------------------------------------------------------------------------
## §5. The link theorem at an integer shift
--------------------------------------------------------------------------------

The defect fibre over `r*_c` **is** the arithmetic progression `A_c + 3m`.  This is the
integer-shift analogue of `CollisionBound.syracuse_defect_fibre` and of gate B3, and it is what
Lemma B consumes.

Gate I3 measured it first: **0 mismatches over 523,917 compared pairs**, `k = 3..9`, every odd
`c` with `-2·2^k < c < 2^k`.  The measurement also fixed the shape of the statement — entries
where a side is genuinely undefined (`A_c + 3m = 0`, equivalently `3n + c = 0`) were *counted*,
not skipped, and there were exactly as many as the `A_c = 0` shifts predict.  Here `1 ≤ A_c`
excludes them, which is the route-(a′) hypothesis doing its job.

Note what is **not** needed: nothing below is sensitive to the sign of `c`.  The shift enters
only through `apAZ_mul`, and `oddPart (2^k · X) = oddPart X` is what does the work — which is
why gate I3 found the identity holding verbatim at negative `A_c` too.
-/

/-- `oddPartZ` on a natural is `CollisionBound.oddPart`.  A bridge, so the ℕ development's
odd-part lemmas apply unchanged. -/
theorem oddPartZ_natCast (n : ℕ) : oddPartZ (n : ℤ) = CollisionBound.oddPart n := by
  unfold oddPartZ CollisionBound.oddPart
  rw [Int.toNat_natCast]

/-- **Powers of two are invisible to the odd part**, at integer argument.  This is the whole
mechanism of the link theorem, and the reason it is sign-agnostic. -/
theorem oddPartZ_two_pow_mul {X : ℤ} (hX : 0 < X) (j : ℕ) :
    oddPartZ ((2 ^ j : ℤ) * X) = oddPartZ X := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, X = (t : ℤ) := ⟨X.toNat, (Int.toNat_of_nonneg hX.le).symm⟩
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht; omega
  have hcast : ((2 ^ j : ℤ) * X).toNat = 2 ^ j * X.toNat := by
    subst ht
    rw [show ((2 ^ j : ℤ) * (t : ℤ)) = ((2 ^ j * t : ℕ) : ℤ) by push_cast; ring]
    rw [Int.toNat_natCast, Int.toNat_natCast]
  unfold oddPartZ
  rw [hcast]
  exact CollisionBound.oddPart_two_pow_mul (by omega : X.toNat ≠ 0)

/-- The fibre entries over `r*_c` are odd, so the map does not fall through its parity guard. -/
theorem fibre_odd {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    (rstarZ c k + m * 2 ^ k) % 2 = 1 := by
  have hr : rstarZ c k % 2 = 1 := rstarZ_odd hc hk
  -- omega treats `m * 2^k` as an atom, so hand it the divisibility explicitly
  have hdvd : 2 ∣ m * 2 ^ k := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) m
  omega

/-- **THE LINK THEOREM at an integer shift.**  The shifted-Syracuse image of the `m`-th lift of
the defect residue is the odd part of `A_c + 3m` — the defect fibre *is* the AP model.

The hypothesis `1 ≤ apAZ c k` is route (a′)'s offset hypothesis; it is exactly what excludes the
degenerate `A_c ≤ 0` shifts, and `apAZ_minus_one_mem` discharges it for `3x − 1`. -/
theorem link_theorem {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k)
    (hA : 1 ≤ apAZ c k) (m : ℕ) :
    syracuseZ c (rstarZ c k + m * 2 ^ k) = oddPartZ (apAZ c k + 3 * m) := by
  have hodd := fibre_odd hc hk m
  unfold syracuseZ
  rw [if_neg (by omega : ¬ (rstarZ c k + m * 2 ^ k) % 2 = 0)]
  -- 3n + c = 2^k * (A_c + 3m), by the defining property of the offset
  have hfac : 3 * ((rstarZ c k + m * 2 ^ k : ℕ) : ℤ) + c
      = (2 ^ k : ℤ) * (apAZ c k + 3 * m) := by
    have := apAZ_mul (c := c) hk
    push_cast
    linarith [this]
  rw [hfac]
  exact oddPartZ_two_pow_mul (by positivity) k

/-- The link theorem in the form gate I3 measured it: mod `2^k`. -/
theorem link_theorem_mod {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k)
    (hA : 1 ≤ apAZ c k) (m : ℕ) :
    syracuseZ c (rstarZ c k + m * 2 ^ k) % 2 ^ k = oddPartZ (apAZ c k + 3 * m) % 2 ^ k := by
  rw [link_theorem hc hk hA m]

/-- **The link theorem for `3x − 1`**, with no hypothesis left to discharge: the offset one is
supplied by `apAZ_minus_one_mem`.  This is the first statement in the corpus that is about the
`3x − 1` defect fibre and is *proved* rather than measured. -/
theorem link_theorem_minus_one {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    syracuseMinus (rstarZ (-1) k + m * 2 ^ k) = oddPartZ (apAZ (-1) k + 3 * m) := by
  have hA : 1 ≤ apAZ (-1) k := by
    rcases apAZ_minus_one_mem hk with h | h <;> omega
  exact link_theorem (by decide) hk hA m

/-!
--------------------------------------------------------------------------------
## §6. Lemma B at an integer shift
--------------------------------------------------------------------------------

`collZ c k` is the collision count of the **genuine** integer-shifted defect fibre: it is
defined from `syracuseZ` and `rstarZ`, with no AP model anywhere in the statement.  §5's link
theorem is what turns it into `collA`, and `ShiftedOperator.collA_le_sharp` — already proved,
at an arbitrary positive offset — bounds it.

**No new collision mathematics is written here, and gate I4 is why.**  I4 measured that
`coll_c ≤ 3·2^k` still holds at negative `c` and still depends on `c` only through `A_c`.  So
Lemma B at an integer shift is a routing problem, not a proof problem.

**Note what replaced the size hypothesis.**  `ShiftedOperator.collS_le_sharp` needs `c < 2^k`,
because that is what its trichotomy `apAS_mem` needs to know the offset is positive.  Here the
offset hypothesis `1 ≤ apAZ c k` is carried directly, so **no bound on `c` appears** — a shift
of any magnitude is in scope provided its offset is positive.  That is route (a′) paying for
itself, and it is why `collZ_minus_one_le` needs no side condition at all. -/

/-- The AP term as an integer, bridged to `ShiftedOperator.apTermA`. -/
theorem oddPartZ_ap {A : ℤ} (hA : 1 ≤ A) (m : ℕ) :
    oddPartZ (A + 3 * m) = CollisionBound.oddPart (apTermA A.toNat m) := by
  have hcast : A + 3 * (m : ℤ) = ((apTermA A.toNat m : ℕ) : ℤ) := by
    unfold apTermA
    push_cast
    omega
  rw [hcast, oddPartZ_natCast]

/-- The fibre-value multiplicity of the genuine integer-shifted defect fibre. -/
def cfZ (c : ℤ) (k t : ℕ) : ℕ :=
  ((range (2 ^ k)).filter
    (fun m => syracuseZ c (rstarZ c k + m * 2 ^ k) % 2 ^ k = t)).card

/-- **`coll` for the genuine integer-shifted defect fibre.**  Defined from `syracuseZ` and
`rstarZ` alone. -/
def collZ (c : ℤ) (k : ℕ) : ℕ := ∑ t ∈ range (2 ^ k), (cfZ c k t) ^ 2

/-- The genuine fibre count IS the AP-model count, at the offset `apAZ c k`.  This is §5's link
theorem, applied under the filter. -/
theorem cfZ_eq_cfA {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k)
    (hA : 1 ≤ apAZ c k) (t : ℕ) :
    cfZ c k t = cfA (apAZ c k).toNat k t := by
  unfold cfZ cfA
  congr 1
  apply filter_congr
  intro m _
  rw [link_theorem hc hk hA m, oddPartZ_ap hA m]
  rfl

theorem collZ_eq_collA {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k)
    (hA : 1 ≤ apAZ c k) :
    collZ c k = collA (apAZ c k).toNat k := by
  unfold collZ collA
  exact Finset.sum_congr rfl fun t _ => by rw [cfZ_eq_cfA hc hk hA t]

/-- **LEMMA B AT AN INTEGER SHIFT.**  `collZ c k + 2 ≤ 3·2^k`, for every odd integer `c` whose
offset is positive — including negative `c`, and with **no bound on `|c|`**.

The statement is about the genuine integer-shifted Syracuse map over its genuine defect
residue.  The route is §5's link theorem, then `collA_le_sharp`. -/
theorem collZ_le_sharp {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k)
    (hA : 1 ≤ apAZ c k) : collZ c k + 2 ≤ 3 * 2 ^ k := by
  have hpos : 0 < (apAZ c k).toNat := by omega
  rw [collZ_eq_collA hc hk hA]
  exact collA_le_sharp hpos hk

/-- **LEMMA B AT AN INTEGER SHIFT**, in the form `CollisionBound.coll_le` states it. -/
theorem collZ_le {c : ℤ} (hc : c % 2 = 1) {k : ℕ} (hk : 1 ≤ k)
    (hA : 1 ≤ apAZ c k) : collZ c k ≤ 3 * 2 ^ k := by
  have := collZ_le_sharp hc hk hA
  omega

/-- **LEMMA B FOR `3x − 1`**, with every hypothesis discharged but `k ≥ 1`.

This is Lemma B for the actual map the control experiment is about.  It is **not** a
certificate: Lemma A and the assembly are still open, and this file claims neither. -/
theorem collZ_minus_one_le_sharp {k : ℕ} (hk : 1 ≤ k) :
    collZ (-1) k + 2 ≤ 3 * 2 ^ k := by
  have hA : 1 ≤ apAZ (-1) k := by
    rcases apAZ_minus_one_mem hk with h | h <;> omega
  exact collZ_le_sharp (by decide) hk hA

theorem collZ_minus_one_le {k : ℕ} (hk : 1 ≤ k) : collZ (-1) k ≤ 3 * 2 ^ k := by
  have := collZ_minus_one_le_sharp hk
  omega

/-- **The bound is NOT attained at `3x − 1`**, and saying so is the honest form of the
sharpness claim.  `collS_sharp_at_offset_three` shows `3·2^k` is attained at offset `3`; gate
I2 shows `A_{-1} ∈ {1,2}`, never `3`.  So `3x − 1` sits strictly inside a bound that is sharp
for the family — the bound cannot be lowered for the family, but `3x − 1` is not the witness. -/
theorem collZ_minus_one_offset_ne_three {k : ℕ} (hk : 1 ≤ k) : apAZ (-1) k ≠ 3 := by
  rcases apAZ_minus_one_mem hk with h | h <;> omega

/-!
--------------------------------------------------------------------------------
## §6. The integer-shifted **operator** — the first spectral object
--------------------------------------------------------------------------------

Everything above is arithmetic.  Lemma A is the first spectral step, and every spectral object
in `ShiftedOperator.lean` (`TcountS`, `TkS`, `TkSC`, `UcleanS`, `UendS`) takes `c : ℕ`.  This
section builds the `ℤ` analogues.  It is **step 4a of three**: the entry theorem (`4b`) and the
clean blocks and Gram identity (`4c`) are not here, and Lemma A is therefore **not proved**.

### THE TRAP THIS SECTION IS BUILT TO AVOID

**`TkZ c k` is NOT `TkS (cmodN c k) k`.**  `rstarZ` legitimately reduces through the residue —
§3 defines it that way — because it is fixed by a **congruence** (`2^k ∣ 3r + c`).  That success
is exactly what makes the same move look safe here.  It is not: the operator is built from
`oddPart`, which does **not** factor through the residue mod `2^k`, and the lift window is the
whole point.  `ShiftedOperator.lean` §4 records the corpus's own two-handover failure on this.

`TkZ_ne_TkZ_of_cmodN` below **refutes the shortcut inside Lean**, at `k = 3`, rather than
leaving it as a warning in prose.  `calibrate_lemmaA_integer_shift.py` gate L5 measures the
entrywise separation independently: `2, 12, 8, 44, 32, 172` at `k = 3..8`.

### CALIBRATION FIRST (ground rule 1)

`calibrate_lemmaA_integer_shift.py`, exit 0, at `c = -1, -5, -7, -11, -13`:

* **L1** — H1 (support) and H2 (modulus) hold verbatim at negative `c`, to `1e-16`.  The shift
  is still only a **per-entry phase**, so everything above the entry theorem transfers.
* **L2** — the clean upper-cascade block norms are still **exactly** `2^{-(b-a)/2}`.
* **L3** — the `shell`/`sbMap` bijection **survives** at negative `c`.  This was the gate: those
  objects are `ℕ`-valued and use `(3r + c)/2^j`, which at negative `c` goes negative before it
  goes anywhere.  Had it failed, Lemma A at an integer shift needed re-scoping rather than
  mirroring, and this section would not exist in this shape.
* **L4** — the defect is still rank `1` and still under `√3·2^{-k/2}`.

`H3` remains **FALSE** (`calibrate_lemmaA_shift_structure.py`): the phase is *not* a column
phase, there is no diagonal-unitary shortcut, and the norm invariance comes from **disjoint
support**.  Do not attempt a conjugation argument here.

### SCOPING CORRECTION FOR STEP 4b, found by tracing the dependency and recorded here so the
### next session does not re-discover it

`BRIEF_LEMMA_A_GENERAL_SHIFT.md` scopes `4b` as "mirror §12–§13", i.e. `upper_entry_eqS` and
`norm_upper_entryS`.  That is **too shallow**.  `upper_entry_eqS`'s proof consumes
`cleanEntryS_eq_masked`, `maskedOddsS`, `shellS_disjoint` and `shell_character_sumS`, and
`shell_character_sumS` in turn consumes `shellS_reindex`, `shellS_oddpart`,
`syracuseS_on_shellS` and `sbMapS` — the whole §2b **shell layer**, all of it at `c : ℕ`.

So `4b` is really **two** slices: the shell layer at `ℤ` (`shellZ`, `sbMapZ`, and their
reindex / oddpart / on-shell lemmas) and only then the entry theorem.  `norm_shift_phase` is
the cheap half and is essentially free at `ℤ` — `wz` already takes an integer argument, so
`‖wz k (ξ * u * c)‖ = 1` is `norm_wz` verbatim with no `ℕ`-cast in the way.

Gate **L3** is the reason this is a mirror rather than a re-scope: the `shell`/`sbMap`
bijection onto the odd residues mod `2^(k-j)` **survives** at negative `c`, where
`(3r + c)/2^j` goes negative before it goes anywhere.  L3 passing says the objects exist; it
does **not** say they have been built.  They have not.
-/

/-- **The integer-shifted transition count.**  Mirror of `ShiftedOperator.TcountS`, with the
lift window over the genuine integer-shifted map.  Target-first, as everywhere in this corpus. -/
def TcountZ (c : ℤ) (k u r : ℕ) : ℕ :=
  ((range (2 ^ k)).filter (fun m => syracuseZ c (r + m * 2 ^ k) % 2 ^ k = u)).card

/-- **The bridge**, and the reason this section is not a re-derivation: at a non-negative shift
the integer count *is* the `c : ℕ` count, so every theorem `ShiftedOperator` proves about
`TcountS` applies to `TcountZ` at `c ≥ 0` without restatement. -/
theorem TcountZ_natCast (c : ℕ) (k u r : ℕ) : TcountZ (c : ℤ) k u r = TcountS c k u r := by
  unfold TcountZ TcountS
  simp only [syracuseZ_natCast]

/-- **The integer-shifted operator `T_k^{(c)}`**, on the `2^{k-1}` odd residues mod `2^k`. -/
noncomputable def TkZ (c : ℤ) (k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℝ :=
  fun u r => (TcountZ c k (od u) (od r) : ℝ) / 2 ^ k

theorem TkZ_natCast (c k : ℕ) : TkZ (c : ℤ) k = TkS c k := by
  funext u r; unfold TkZ TkS; rw [TcountZ_natCast]

theorem TkZ_nonneg (c : ℤ) (k : ℕ) (u r : Fin (2 ^ (k - 1))) : 0 ≤ TkZ c k u r := by
  unfold TkZ; positivity

/-- `T_k^{(c)}` complexified, mirroring `TkSC`. -/
noncomputable def TkZC (c : ℤ) (k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℂ :=
  fun u r => (TcountZ c k (od u) (od r) : ℂ) / 2 ^ k

theorem TkZC_natCast (c k : ℕ) : TkZC (c : ℤ) k = TkSC c k := by
  funext u r; unfold TkZC TkSC; rw [TcountZ_natCast]

/-- **The integer-shifted `U_clean`**: the transpose of `T_k^{(c)}` with the defect row removed.
The orientation — transpose, and the `r*` row rather than the `r*` column — is inherited from
`ShiftedOperator.UcleanS`, which inherits it from `OperatorBlock` §0.1's numerical check at
`c = 1`.  It is not re-derived here. -/
noncomputable def UcleanZ (c : ℤ) (k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℂ :=
  fun r u => if (r : ℕ) = idx (rstarZ c k) then 0 else Matrix.transpose (TkZC c k) r u

theorem UcleanZ_apply (c : ℤ) (k : ℕ) (r u : Fin (2 ^ (k - 1))) :
    UcleanZ c k r u = if (r : ℕ) = idx (rstarZ c k) then 0 else TkZC c k u r := rfl

/-- The zeroed row is exactly the row `rstarZ_spec` identifies. -/
theorem UcleanZ_defect_row (c : ℤ) (k : ℕ) {r : Fin (2 ^ (k - 1))}
    (hr : (r : ℕ) = idx (rstarZ c k)) (u : Fin (2 ^ (k - 1))) : UcleanZ c k r u = 0 := by
  rw [UcleanZ_apply, if_pos hr]

/-- Off the defect row, the integer-shifted `U_clean` is the transpose of `T_k^{(c)}`. -/
theorem UcleanZ_clean_row (c : ℤ) (k : ℕ) {r : Fin (2 ^ (k - 1))}
    (hr : (r : ℕ) ≠ idx (rstarZ c k)) (u : Fin (2 ^ (k - 1))) :
    UcleanZ c k r u = TkZC c k u r := by
  rw [UcleanZ_apply, if_neg hr]

/-- `rstarS` sees `c` only through `c % 2^k`, because it is fixed by a congruence.  This is the
*correct* half of the residue reduction, and it is the half that makes the bridge below work —
the operator half is refuted by `TkZ_ne_TkZ_of_cmodN`. -/
theorem rstarS_mod (c k : ℕ) : rstarS (c % 2 ^ k) k = rstarS c k := by
  unfold rstarS; rw [Nat.mod_mod]

/-- At a non-negative shift the integer defect row is the `c : ℕ` defect row. -/
theorem rstarZ_natCast (c k : ℕ) : rstarZ (c : ℤ) k = rstarS c k := by
  unfold rstarZ cmodN
  have h : ((c : ℤ) % (2 ^ k : ℤ)) = ((c % 2 ^ k : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast, rstarS_mod]

/-- **The full bridge for the clean operator.**  Nothing above `c ≥ 0` is a new object. -/
theorem UcleanZ_natCast (c k : ℕ) : UcleanZ (c : ℤ) k = UcleanS c k := by
  funext r u
  rw [UcleanZ_apply, UcleanS_apply, rstarZ_natCast, TkZC_natCast]

/-- The integer-shifted `U_clean` as an endomorphism of `ℓ²`. -/
noncomputable def UendZ (c : ℤ) (k : ℕ) : Module.End ℂ (EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :=
  Matrix.toEuclideanLin (UcleanZ c k)

@[simp] theorem UendZ_apply (c : ℤ) (k : ℕ) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1))))
    (r : Fin (2 ^ (k - 1))) : (UendZ c k x) r = ∑ u, UcleanZ c k r u * x u := rfl

theorem UendZ_natCast (c k : ℕ) : UendZ (c : ℤ) k = UendS c k := by
  unfold UendZ UendS; rw [UcleanZ_natCast]

/-!
### §6b. The trap, refuted inside Lean

The shortcut `TkZ c k = TkS (cmodN c k) k` is **false**, and this is the machine-checked
statement of that, at `k = 3`, `c = -1` (`cmodN (-1) 3 = 7`).  It is stated on `TcountZ` rather
than on `TkZ` because the counts are naturals and the separation is exact; the matrices differ
by the same entry, divided by `2^k`.

The witness is the one-line check from the brief: the lift window is what separates them.
`oddPart (3·1 − 1) = 1` but `oddPart (3·1 + 8 − 1) = 5`, so the source residue `r = 1` sends a
lift to a different target under the two maps, and the counts at that target differ.

`decide` is unavailable here — `syracuseZ` contains `v2 = padicValNat`, which the kernel does
not reduce — so the separation is exhibited by `#eval` in §7 and by gate L5 in the Python, and
the theorem below is proved from the map values rather than by computation on the counts.
-/

/-- `3x − 1` and `3x + 7` disagree on the lift `1` of the residue `1`: the first sends it to
`1`, the second to `5`.  This is the whole of §4's correction in one line. -/
theorem syracuseZ_ne_syracuseS_cmodN : syracuseZ (-1) 1 ≠ syracuseS 7 1 := by
  -- `v2` is `padicValNat`, which the kernel does not reduce; both values go through
  -- `v2_two_pow_mul_odd`, never through `decide`.
  have hv2 : v2 2 = 1 := by
    have := GapCertificate.v2_two_pow_mul_odd 1 1 (by norm_num); norm_num at this; exact this
  have hv10 : v2 10 = 1 := by
    have := GapCertificate.v2_two_pow_mul_odd 1 5 (by norm_num); norm_num at this; exact this
  have h1 : syracuseZ (-1) 1 = 1 := by
    unfold syracuseZ oddPartZ
    norm_num
    show (2 : ℕ) / 2 ^ v2 2 = 1
    rw [hv2]; norm_num
  have h2 : syracuseS 7 1 = 5 := by
    unfold syracuseS
    norm_num [hv10]
  rw [h1, h2]; omega

/-- **The residue shortcut is FALSE.**  `TkZ c k` is not `TkS (cmodN c k) k`, and this exhibits
a shift at which the two `syracuse` maps that generate them already differ, on a lift inside the
window.  Do not define the integer operator through the residue. -/
theorem operator_not_residue_reducible :
    ∃ (c : ℤ) (n : ℕ), syracuseZ c n ≠ syracuseS (cmodN c 3) n :=
  ⟨-1, 1, by
    have : cmodN (-1 : ℤ) 3 = 7 := by decide
    rw [this]; exact syracuseZ_ne_syracuseS_cmodN⟩

/-!
--------------------------------------------------------------------------------
## §6c. The **shell layer** at an integer shift  (step 4b, first half)
--------------------------------------------------------------------------------

`upper_entry_eqS`'s proof reaches down through `cleanEntryS_eq_masked`, `maskedOddsS`,
`shellS_disjoint` and `shell_character_sumS` into `shellS`, `sbMapS`, `shellS_oddpart`,
`syracuseS_on_shellS` and `shellS_reindex` — the whole §2b shell layer, at `c : ℕ`.  This
section is that layer at `c : ℤ`.

### WHERE THE RESIDUE REDUCTION IS LEGITIMATE, AND WHERE IT IS NOT

§6b refuted the residue shortcut **for the operator**.  It is natural — and, this time,
correct — to ask whether the *shell* reduces, and the answer decides how big this section is.
It does, and here is the reason, which is also the reason it does not contradict §6b:

* the shell is cut out by `v2 (3r + c) = j` with `j ≤ k - 1`, and a valuation below `k` is
  determined by `3r + c` **mod `2^k`**;
* `sbMap` takes `(3r + c) / 2^j` **mod `2^(k-j)`**, and replacing `c` by `c + 2^k t` moves that
  quotient by `2^(k-j) t`, i.e. not at all mod `2^(k-j)`;
* and, decisively, **`r` ranges over `[0, 2^k)` here — this is not the lift window.**  §6b's
  operator takes `oddPart (3n + c)` for `n = r + m·2^k`, an *unbounded* odd part that no
  congruence mod `2^k` can pin down.  That is the whole difference.

`syracuseZ` itself is **not** residue-reducible even on the shell — it returns the full odd
part `(3r + c)/2^j`, which moves by `2^(k-j) t`.  Only its value *mod `2^(k-j)`*, which is
exactly `sbMapZ`, is stable.  Gate **L6** measures all three: shell identical `True`, sbMap
identical `True`, `syracuse` identical **`False`**, at `c = -1,-5,-7,-11,-13`, `k = 4..7`.

So the reduction below is **proved, never assumed**, and it is stated as its own theorem
(`shellZ_residue`, `sbMapZ_residue`) precisely so that the boundary against §6b is legible.
-/

/-- The 2-adic valuation of a **non-zero integer**, sign-agnostically: `v₂(-10) = v₂(10) = 1`.
`Int.toNat` would clamp a negative argument to `0` and report valuation `0`, which is wrong at
exactly the shifts this file exists for — `3r + c` is genuinely negative for small `r` at
`c = -13`.  `natAbs` is the honest choice, and matches the Python's `v2(abs(n))`. -/
def v2Z (m : ℤ) : ℕ := v2 m.natAbs

theorem v2Z_natCast (n : ℕ) : v2Z (n : ℤ) = v2 n := by
  unfold v2Z; rw [Int.natAbs_natCast]

/-- The `ℤ` form of `CountingLemmas.v2_eq_iff_dvd`, with divisibility taken over `ℤ`. -/
theorem v2Z_eq_iff_dvd {m : ℤ} {j : ℕ} (hm : m ≠ 0) :
    v2Z m = j ↔ ((2 : ℤ) ^ j ∣ m ∧ ¬ ((2 : ℤ) ^ (j + 1) ∣ m)) := by
  have habs : m.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hm
  have hd : ∀ i : ℕ, ((2 : ℤ) ^ i ∣ m) ↔ (2 ^ i ∣ m.natAbs) := by
    intro i
    rw [← Int.natAbs_dvd_natAbs]
    simp [Int.natAbs_pow]
  rw [v2Z, v2_eq_iff_dvd habs, hd, hd]

/-- **A valuation below `k` is congruence data mod `2^k`.**  This is the whole reason the shell
layer reduces through the residue while the operator (§6b) does not. -/
theorem v2Z_congr {x y : ℤ} {j k : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hjk : j + 1 ≤ k) (hcong : (2 : ℤ) ^ k ∣ x - y) (hv : v2Z x = j) : v2Z y = j := by
  rw [v2Z_eq_iff_dvd hx] at hv
  rw [v2Z_eq_iff_dvd hy]
  have hdvd : ∀ i : ℕ, i ≤ k → ((2 : ℤ) ^ i ∣ x ↔ (2 : ℤ) ^ i ∣ y) := by
    intro i hi
    have hsub : (2 : ℤ) ^ i ∣ x - y := dvd_trans (pow_dvd_pow 2 hi) hcong
    constructor
    · intro h; simpa using h.sub hsub
    · intro h
      have : (2 : ℤ) ^ i ∣ y + (x - y) := h.add hsub
      simpa using this
  exact ⟨(hdvd j (by omega)).1 hv.1, fun h => hv.2 ((hdvd (j + 1) (by omega)).2 h)⟩

/-- **The integer-shifted valuation shell.**  Defined at `c : ℤ` directly — *not* through the
residue — so that `shellZ_residue` below is a theorem about it rather than its definition. -/
def shellZ (c : ℤ) (k j : ℕ) : Finset ℕ :=
  (range (2 ^ k)).filter (fun r => 0 < r ∧ r % 2 = 1 ∧ v2Z (3 * (r : ℤ) + c) = j)

/-- **The integer-shifted SB map.**  `Int.emod` by a positive modulus is non-negative, so the
`toNat` is faithful and not a clamp. -/
def sbMapZ (c : ℤ) (k j r : ℕ) : ℕ := (((3 * (r : ℤ) + c) / 2 ^ j) % 2 ^ (k - j)).toNat

theorem shellZ_natCast (c k j : ℕ) : shellZ (c : ℤ) k j = shellS c k j := by
  unfold shellZ shellS
  apply filter_congr
  intro r _
  have hc : 3 * (r : ℤ) + (c : ℤ) = ((3 * r + c : ℕ) : ℤ) := by push_cast; ring
  rw [hc, v2Z_natCast]

/-- `3r + c` never vanishes at the shifts this file is about: `c ≥ -1` gives `3r + c ≥ -1`, and
it is `0` only if `3 ∣ c`, which is the `c = -3t` case held out of scope throughout. -/
theorem three_mul_add_ne_zero {c : ℤ} (hc : ¬ (3 : ℤ) ∣ c) (r : ℕ) : 3 * (r : ℤ) + c ≠ 0 := by
  intro h
  exact hc ⟨-(r : ℤ), by linarith⟩

/-- **THE REDUCTION, PROVED.**  On the shell — but *not* on the operator (§6b) — the integer
shift may be replaced by its residue.  The hypothesis `j + 1 ≤ k` is what makes the valuation
congruence data, and `¬ 3 ∣ c` is the standing `A_c ≤ 0` exclusion. -/
theorem shellZ_residue {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) {k j : ℕ} (hjk : j + 1 ≤ k) :
    shellZ c k j = shellS (cmodN c k) k j := by
  rw [← shellZ_natCast]
  unfold shellZ
  apply filter_congr
  intro r _
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · simp
  have hres : ((cmodN c k : ℕ) : ℤ) = c % (2 ^ k : ℤ) := cmodN_cast c k
  have hcong : (2 : ℤ) ^ k ∣ (3 * (r : ℤ) + c) - (3 * (r : ℤ) + ((cmodN c k : ℕ) : ℤ)) := by
    refine ⟨c / 2 ^ k, ?_⟩
    rw [hres]
    linarith [Int.emod_add_ediv c ((2 : ℤ) ^ k)]
  have hx : 3 * (r : ℤ) + c ≠ 0 := three_mul_add_ne_zero hc3 r
  have hy : 3 * (r : ℤ) + ((cmodN c k : ℕ) : ℤ) ≠ 0 := by
    have h1 : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hrpos
    have h2 : (0 : ℤ) ≤ ((cmodN c k : ℕ) : ℤ) := Int.natCast_nonneg _
    intro h; linarith
  constructor
  · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h1, v2Z_congr hx hy hjk hcong h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1, v2Z_congr hy hx hjk (by simpa using (dvd_neg.2 hcong)) h2⟩

/-- On the shell the integer `2^j` genuinely divides `3r + c` — the fact every quotient
statement below rests on. -/
theorem shellZ_dvd {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) {k j r : ℕ} (hr : r ∈ shellZ c k j) :
    (2 : ℤ) ^ j ∣ 3 * (r : ℤ) + c := by
  unfold shellZ at hr
  rw [mem_filter] at hr
  exact ((v2Z_eq_iff_dvd (three_mul_add_ne_zero hc3 r)).1 hr.2.2.2).1

theorem sbMapZ_natCast (c k j r : ℕ) : sbMapZ (c : ℤ) k j r = sbMapS c k j r := by
  unfold sbMapZ sbMapS
  have h : 3 * (r : ℤ) + (c : ℤ) = ((3 * r + c : ℕ) : ℤ) := by push_cast; ring
  rw [h, show ((2 : ℤ) ^ j) = ((2 ^ j : ℕ) : ℤ) by push_cast; ring,
    show ((2 : ℤ) ^ (k - j)) = ((2 ^ (k - j) : ℕ) : ℤ) by push_cast; ring,
    ]
  norm_cast

/-- **THE REDUCTION FOR `sbMap`.**  Companion to `shellZ_residue`: replacing `c` by its residue
moves the quotient `(3r + c)/2^j` by `2^(k-j) t`, i.e. not at all mod `2^(k-j)`.  Gate L6
measures this as `sbMap identical: True` at every shift and `k` tested. -/
theorem sbMapZ_residue {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) {k j r : ℕ} (hjk : j + 1 ≤ k)
    (hr : r ∈ shellZ c k j) : sbMapZ c k j r = sbMapS (cmodN c k) k j r := by
  rw [← sbMapZ_natCast]
  unfold sbMapZ
  congr 1
  obtain ⟨q, hq⟩ := shellZ_dvd hc3 hr
  have hres : ((cmodN c k : ℕ) : ℤ) = c % (2 ^ k : ℤ) := cmodN_cast c k
  have hsplit : (2 : ℤ) ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← pow_add]; congr 1; omega
  -- `3r + c'` is `2^j (q − 2^{k−j} t)`, with `t = c / 2^k`
  have hq' : 3 * (r : ℤ) + ((cmodN c k : ℕ) : ℤ)
      = 2 ^ j * (q - 2 ^ (k - j) * (c / 2 ^ k)) := by
    rw [hres]
    have hd := Int.emod_add_ediv c ((2 : ℤ) ^ k)
    have : c % (2 : ℤ) ^ k = c - 2 ^ k * (c / 2 ^ k) := by linarith
    rw [this, hsplit]
    linarith [hq]
  rw [hq, hq', Int.mul_ediv_cancel_left _ (by positivity : (2 : ℤ) ^ j ≠ 0),
    Int.mul_ediv_cancel_left _ (by positivity : (2 : ℤ) ^ j ≠ 0), Int.sub_emod,
    Int.mul_emod_right, sub_zero, Int.emod_emod_of_dvd _ dvd_rfl]

/-!
### The corollaries, inherited rather than re-proved

With the two reductions in hand, every shell fact `4b(ii)` consumes transfers from the `c : ℕ`
development by rewriting.  **This is the payoff of proving the reduction instead of assuming
it:** nothing below is a new argument, and nothing below touches the operator, where the same
move is false.
-/

/-- Shell cardinality at an integer shift: `2^{k-1-j}`, shift-independent. -/
theorem shellZ_card {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) (hc : c % 2 = 1) {k j : ℕ}
    (hj : 1 ≤ j) (hjk : j + 1 ≤ k) : (shellZ c k j).card = 2 ^ (k - 1 - j) := by
  rw [shellZ_residue hc3 hjk]
  exact shellS_card (cmodN_odd hc (by omega)) hj hjk

/-- Distinct shells are disjoint at an integer shift. -/
theorem shellZ_disjoint {c : ℤ} {k j j' : ℕ} (h : j ≠ j') :
    Disjoint (shellZ c k j) (shellZ c k j') := by
  apply Finset.disjoint_left.2
  intro r hr hr'
  unfold shellZ at hr hr'
  rw [mem_filter] at hr hr'
  exact h (hr.2.2.2 ▸ hr'.2.2.2 ▸ rfl)

/-- **Lemma SB at an integer shift**, as the change of summation variable `4b(ii)` consumes. -/
theorem shellZ_reindex {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) (hc : c % 2 = 1) {k j : ℕ}
    (hj : 1 ≤ j) (hjk : j + 1 ≤ k) (α : ℕ) :
    ∑ r ∈ shellZ c k j, w k ^ (α * sbMapZ c k j r) = Sodd k α (k - j) := by
  rw [← shellS_reindex (c := cmodN c k) (cmodN_odd hc (by omega)) hj hjk α]
  refine Finset.sum_congr (shellZ_residue hc3 hjk) ?_
  intro r hr
  rw [sbMapZ_residue hc3 hjk ((shellZ_residue hc3 hjk).symm ▸ hr)]

/-!
--------------------------------------------------------------------------------
## §6d. Lemma A's **entry theorem** at an integer shift  (step 4b, second half)
--------------------------------------------------------------------------------

§6c built the shell layer.  This section is the entry theorem standing on it:
`upper_entry_eqZ` and `norm_upper_entryZ`, mirroring `ShiftedOperator` §7 and the first
theorem of its §8.  With these, **Lemma A's entry theorem is closed at an integer shift.**
The clean blocks and the Gram identity (`BentZ`, `gram_upperZ`, `cleanBlockCLMZ`,
`norm_sq_clean_blockZ`) are step `4c` and are **not** here; the assembly is a separate task
after them.  `hL2`/`hParseval` is untouched and remains open exactly as at `c = 1`.

### THE ONE NEW HYPOTHESIS, AND IT WAS MEASURED BEFORE IT WAS WRITTEN

Everything in §6c is sign-agnostic, because a valuation reads `natAbs` (`v2Z`).  The
operator is not: `oddPartZ` is `m.toNat / 2 ^ v2 m.toNat`, and **`Int.toNat` clamps a
non-positive argument to `0`**.  So the coset-uniformity step — `Syr_c(x + m2^K)` is affine
in `m`, which is the whole engine of the Gauss collapse — is **false** wherever `3x + c < 0`,
and the clamp makes it fail silently rather than loudly.

Gate **L7** in `calibrate_lemmaA_integer_shift.py` measures exactly this, and its last column
is the point:

```
   k | c    | 0<3x+c cases | A holds | B holds | B on the 3x+c<0 cases
   6 | -1   | 31           | True    | True    | n/a
   6 | -5   | 30           | True    | True    | False      <- the clamp
   6 | -13  | 29           | True    | True    | False
```

The **valuation** is frozen under the lift at every shift tested (claim A, `v2Z_congr` does
it here); the **affine step** holds on every positive `3x + c` and fails on every negative
one.  So `cu_syracuse_affineZ` carries `0 < 3x + c`, in the packaged form `-1 ≤ c` — which
is `three_add_pos`, already in §1, and which is satisfied by `3x − 1`.

**This narrows the section's scope, and the narrowing is stated rather than hidden.**  At an
odd `c ≥ -1` the shift is either `-1` or a non-negative one the `c : ℕ` chain already covers,
so the new content of §6d is `3x − 1` itself.  That is the map this file exists for; it is
not a general integer-shift entry theorem, and nothing below claims to be one.  The shifts
`c ≤ -3` are out of scope here for a *different and weaker* reason than `A_c ≤ 0` is out of
scope in §3 — this one is a clamp in a definition, not a degeneracy in the mathematics, and
a future `oddPartZ` on `ℤ` proper would lift it.

### CALIBRATION FIRST (ground rule 1) — gates L7, L8, L9, exit 0

* **L7** — CU at an integer shift, above.
* **L8** — the Gauss collapse holds at `c = -1`: the column sum against `w^{η·}` still
  collapses to one phase gated by `2^v ∣ η`, to `1e-12` at `k = 4, 5`.  That is
  `gauss_collapseZ`.
* **L9** — the entry theorem itself, at `c = -1`, `k = 5, 6`: `cleanEntryZ` equals
  `w^{ξuc} · Sodd(resJ …)` to `1e-12` over 40 `(a,b,η',ξ')` cases, and the modulus on the
  27 sharp points is exactly `2^{k-d-1}`.  **The `Sodd` factor carries no `c`** — measured,
  at a shift where `syracuseZ` is a genuinely different map from any `c : ℕ` one (L5).

### MUTATION TABLE, continuing from S147

| # | Target | Mutation | Failure, and why it is mathematical |
|---|---|---|---|
| S148 | `cu_syracuse_affineZ` | hypothesis `-1 ≤ c` **weakened** to `-5 ≤ c` | *Application type mismatch* at `three_add_pos`, twice — the positivity `oddPartZ_two_pow_mul` needs is exactly what `-1 ≤ c` supplies; and **false** by computation, gate L7's last column at `c = -5, k = 6` reads `False`, because the clamp sends a lift to `0` where the affine value is negative.  Weakened rather than dropped on purpose: dropping the binder would fail on `unknown identifier`, which proves nothing |
| S149 | `cu_valuation_frozenZ` | hypothesis `v2Z (3x+c) < K` weakened to `≤ K` | `omega could not prove the goal` at the `j + 1 ≤ k` argument of `v2Z_congr`; and **false** — at `v = K` the lift moves the valuation.  Same content as S147 one level up |
| S150 | `gauss_collapseZ` | gate `2 ^ v2Z (3r+c) ∣ η` weakened to `2 ∣ η` | three `rewrite failed` — `ratio_one_iff` produces the gate `2^v ∣ η` and no longer matches either branch; and **false**, since L8 measures the column at `2 ∣ η` with `2^v ∤ η` as `0`, not `2^k w^{ησ}` |
| S151 | `upper_entry_eqZ` | phase `wz k (ξ*u*c)` → `wz k (ξ*u)` (the `c = 1` phase) | *Type mismatch* against what `shell_character_sumZ` returns; and **false** by computation — at `c = -1` the two phases are separated by up to `1.85` in modulus over the `k = 5, 6` cases, so they are not the same number |
| S152 | `upper_entry_eqZ` | regime weakened `a < b` → `a ≤ b` | `omega` fails on `1 ≤ b - a`, and `shell_dvd_upper` / `shell_sum_vanishes` both mismatch — every one needs `a < b`.  At `a = b` the dead band is empty; that is the LOWER regime, a different theorem |
| S153 | `norm_upper_entryZ` | modulus `2^{k-d-1}` → `2^{k-d}` | `unsolved goals` after `norm_Sodd_full`, which delivers the half; and **false** — L9's sharp-point column measures `2^{k-d-1}` to `8.5e-13` |

All six were run under `lake build` on the real target and their error text read, per the note
below the previous batch.  None failed on a stale import.
-/

section EntryInteger

open LemmaA CharacterBasis BlockVanishing OperatorBlock CollisionBound GramIdentity

/-- An **odd positive** integer is its own odd part — the base case `oddPartZ_two_pow_mul`
strips down to.  Positivity is load-bearing: at `X ≤ 0` the `toNat` clamp makes this `0`. -/
theorem oddPartZ_odd {X : ℤ} (hX : 0 < X) (hodd : X % 2 = 1) : oddPartZ X = X.toNat := by
  unfold oddPartZ
  rw [v2_odd_mod _ (by omega : X.toNat % 2 = 1)]
  simp

/-- **The `2`-adic split of a positive integer**, with the quotient odd *and positive*.  The
`ℤ` analogue of `shellS_oddpart`'s content, stated on a bare positive integer so both the
shell version and the lift-window version below can consume it. -/
theorem v2Z_split {X : ℤ} (hX : 0 < X) :
    X = 2 ^ v2Z X * (X / 2 ^ v2Z X) ∧ (X / 2 ^ v2Z X) % 2 = 1 ∧ 0 < X / 2 ^ v2Z X := by
  obtain ⟨hdvd, hndvd⟩ := (v2Z_eq_iff_dvd (ne_of_gt hX)).1 rfl
  -- abstract the exponent BEFORE rewriting `X`, or `rw [hq]` recurses into `v2Z X` itself
  set v := v2Z X with hv
  obtain ⟨q, hq⟩ := hdvd
  have h2 : (0 : ℤ) < 2 ^ v := by positivity
  have hqv : X / 2 ^ v = q := by
    rw [hq, Int.mul_ediv_cancel_left _ (by positivity : (2 : ℤ) ^ v ≠ 0)]
  have hqpos : 0 < q := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  refine ⟨by rw [hqv]; exact hq, ?_, by rw [hqv]; exact hqpos⟩
  rw [hqv]
  rcases Int.even_or_odd q with he | ho
  · exfalso
    obtain ⟨t, ht⟩ := he
    exact hndvd ⟨t, by rw [hq, ht, pow_succ]; ring⟩
  · obtain ⟨t, ht⟩ := ho
    omega

/-- **The valuation is frozen under the lift**, at an integer shift.  This is `v2Z_congr` doing
its job one level up: `3(x + m2^K) + c` differs from `3x + c` by `3m·2^K`, and a valuation
strictly below `K` is congruence data mod `2^K`.

Sign-agnostic, exactly as §6c is — no positivity is needed here, only non-vanishing. -/
theorem cu_valuation_frozenZ {c : ℤ} (hc1 : -1 ≤ c) {x m K : ℕ} (hx : x % 2 = 1)
    (hK : v2Z (3 * (x : ℤ) + c) < K) :
    v2Z (3 * ((x + m * 2 ^ K : ℕ) : ℤ) + c) = v2Z (3 * (x : ℤ) + c) := by
  have hXpos : 0 < 3 * (x : ℤ) + c := three_add_pos hc1 (by omega)
  have hlift : 3 * ((x + m * 2 ^ K : ℕ) : ℤ) + c
      = (3 * (x : ℤ) + c) + 3 * (m : ℤ) * 2 ^ K := by push_cast; ring
  have hYpos : 0 < 3 * ((x + m * 2 ^ K : ℕ) : ℤ) + c := by
    have : (0 : ℤ) ≤ 3 * (m : ℤ) * 2 ^ K := by positivity
    rw [hlift]; linarith
  -- `k := K` must be pinned: nothing else in the application determines it
  refine v2Z_congr (k := K) (ne_of_gt hXpos) (ne_of_gt hYpos) (by omega) ?_ rfl
  exact ⟨-(3 * (m : ℤ)), by rw [hlift]; ring⟩

/-- **CU AT AN INTEGER SHIFT.**  For odd `x` with `v := v₂(3x + c) < K`,
`Syr_c(x + m2^K) = (3x+c)/2^v + 3m·2^{K−v}`.

This is `ShiftedOperator.cu_syracuse_affineS` at `c : ℤ`, and it is the only genuinely new
mathematics in step `4b(ii)`.  The hypothesis `-1 ≤ c` is gate L7's measurement, not a
defensive addition: at a negative `3x + c` the identity is **false**, because `oddPartZ`
clamps. -/
theorem cu_syracuse_affineZ {c : ℤ} (hc1 : -1 ≤ c) (x m K : ℕ) (hx : x % 2 = 1)
    (hK : v2Z (3 * (x : ℤ) + c) < K) :
    syracuseZ c (x + m * 2 ^ K)
      = ((3 * (x : ℤ) + c) / 2 ^ v2Z (3 * (x : ℤ) + c)).toNat
        + 3 * m * 2 ^ (K - v2Z (3 * (x : ℤ) + c)) := by
  have hXpos : 0 < 3 * (x : ℤ) + c := three_add_pos hc1 (by omega)
  obtain ⟨hsplit, hqodd, hqpos⟩ := v2Z_split hXpos
  set v := v2Z (3 * (x : ℤ) + c) with hvdef
  set q := (3 * (x : ℤ) + c) / 2 ^ v with hqdef
  have hlift_odd : (x + m * 2 ^ K) % 2 = 1 := by
    have h2 : (2 : ℕ) ∣ m * 2 ^ K := (dvd_pow_self 2 (by omega : K ≠ 0)).mul_left m
    omega
  have hpow : (2 : ℤ) ^ v * 2 ^ (K - v) = 2 ^ K := by
    rw [← pow_add]; congr 1; omega
  have hfac : 3 * ((x + m * 2 ^ K : ℕ) : ℤ) + c
      = (2 : ℤ) ^ v * (q + 3 * (m : ℤ) * 2 ^ (K - v)) := by
    push_cast
    linear_combination hsplit - 3 * (m : ℤ) * hpow
  have hmnn : (0 : ℤ) ≤ 3 * (m : ℤ) * 2 ^ (K - v) := by positivity
  have hqm_pos : 0 < q + 3 * (m : ℤ) * 2 ^ (K - v) := by linarith
  have hqm_odd : (q + 3 * (m : ℤ) * 2 ^ (K - v)) % 2 = 1 := by
    have h2 : (2 : ℤ) ∣ 3 * (m : ℤ) * 2 ^ (K - v) :=
      Dvd.dvd.mul_left (dvd_pow_self 2 (by omega : K - v ≠ 0)) _
    omega
  unfold syracuseZ
  rw [if_neg (by omega : ¬ (x + m * 2 ^ K) % 2 = 0), hfac,
    oddPartZ_two_pow_mul hqm_pos v, oddPartZ_odd hqm_pos hqm_odd]
  have hcast : q + 3 * (m : ℤ) * 2 ^ (K - v)
      = ((q.toNat + 3 * m * 2 ^ (K - v) : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg hqpos.le]
  rw [hcast, Int.toNat_natCast]

/-- The integer-shifted map as an exact quotient, on any odd source.  Mirror of
`ShiftedOperator.syracuseS_eq_quot`. -/
theorem syracuseZ_eq_quotZ {c : ℤ} (hc1 : -1 ≤ c) {r : ℕ} (hr : r % 2 = 1) :
    syracuseZ c r = ((3 * (r : ℤ) + c) / 2 ^ v2Z (3 * (r : ℤ) + c)).toNat := by
  have hpos : 0 < 3 * (r : ℤ) + c := three_add_pos hc1 (by omega)
  obtain ⟨hsplit, hqodd, hqpos⟩ := v2Z_split hpos
  unfold syracuseZ
  rw [if_neg (by omega : ¬ r % 2 = 0)]
  conv_lhs => rw [hsplit]
  rw [oddPartZ_two_pow_mul hqpos, oddPartZ_odd hqpos hqodd]

/-- On a shell, `3r + c = 2^j q` with `q` odd and **positive**.  `ShiftedOperator`'s
`shellS_oddpart` at `c : ℤ`; positivity is the extra conjunct the clamp forces. -/
theorem shellZ_oddpart {c : ℤ} (hc1 : -1 ≤ c) {k j r : ℕ} (hr : r ∈ shellZ c k j) :
    3 * (r : ℤ) + c = 2 ^ j * ((3 * (r : ℤ) + c) / 2 ^ j)
      ∧ ((3 * (r : ℤ) + c) / 2 ^ j) % 2 = 1
      ∧ 0 < (3 * (r : ℤ) + c) / 2 ^ j := by
  unfold shellZ at hr
  rw [mem_filter] at hr
  have hpos : 0 < 3 * (r : ℤ) + c := three_add_pos hc1 (by omega : 1 ≤ r)
  have hsp := v2Z_split hpos
  rw [hr.2.2.2] at hsp
  exact hsp

/-- On a shell the integer-shifted map is the exact quotient `(3r + c)/2^j`. -/
theorem syracuseZ_on_shellZ {c : ℤ} (hc1 : -1 ≤ c) {k j r : ℕ} (hr : r ∈ shellZ c k j) :
    syracuseZ c r = ((3 * (r : ℤ) + c) / 2 ^ j).toNat := by
  have hmem := hr
  unfold shellZ at hmem
  rw [mem_filter] at hmem
  rw [syracuseZ_eq_quotZ hc1 hmem.2.2.1, hmem.2.2.2]

/-- The character column of `TcountZ` **is** the lift-window sum.  `TcountZ`'s definition read
backwards; no arithmetic and no shift is involved.  Mirror of `char_col_as_liftS`. -/
theorem char_col_as_liftZ (c : ℤ) (k r η : ℕ) :
    ∑ u ∈ range (2 ^ k), (TcountZ c k u r : ℂ) * w k ^ (η * u)
      = ∑ m ∈ range (2 ^ k), w k ^ (η * syracuseZ c (r + m * 2 ^ k)) := by
  have hmaps : ∀ m ∈ range (2 ^ k), syracuseZ c (r + m * 2 ^ k) % 2 ^ k ∈ range (2 ^ k) :=
    fun m _ => mem_range.2 (Nat.mod_lt _ (Nat.two_pow_pos k))
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun m => w k ^ (η * (syracuseZ c (r + m * 2 ^ k) % 2 ^ k)))
  have hstep : ∀ u ∈ range (2 ^ k),
      (TcountZ c k u r : ℂ) * w k ^ (η * u)
        = ∑ m ∈ (range (2 ^ k)).filter
              (fun m => syracuseZ c (r + m * 2 ^ k) % 2 ^ k = u),
            w k ^ (η * (syracuseZ c (r + m * 2 ^ k) % 2 ^ k)) := by
    intro u _
    have hcong : ∀ m ∈ (range (2 ^ k)).filter
        (fun m => syracuseZ c (r + m * 2 ^ k) % 2 ^ k = u),
        w k ^ (η * (syracuseZ c (r + m * 2 ^ k) % 2 ^ k)) = w k ^ (η * u) :=
      fun m hm => by rw [(mem_filter.1 hm).2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul, TcountZ]
  rw [Finset.sum_congr rfl hstep, hfib]
  exact Finset.sum_congr rfl fun m _ => w_pow_mod k η _

/-- **THE GAUSS COLLAPSE AT AN INTEGER SHIFT.**  For a clean source `r`
(`v := v₂(3r + c) < k`), the integer-shifted operator's column sum against `w^{η·}` collapses
to a single phase, gated by `2^v ∣ η`.

Gate L8 measured it at `c = -1` before it was written.  `ratio_one_iff` is shift-free and is
imported unchanged; the only shifted input is `cu_syracuse_affineZ`. -/
theorem gauss_collapseZ {c : ℤ} (hc1 : -1 ≤ c) {k r : ℕ} (hr : r % 2 = 1)
    (hK : v2Z (3 * (r : ℤ) + c) < k) (η : ℕ) :
    ∑ u ∈ range (2 ^ k), (TcountZ c k u r : ℂ) * w k ^ (η * u)
      = if 2 ^ v2Z (3 * (r : ℤ) + c) ∣ η then
          ((2 ^ k : ℕ) : ℂ) * w k ^ (η * syracuseZ c r) else 0 := by
  rw [char_col_as_liftZ c k r η]
  have hstep : ∀ m ∈ range (2 ^ k),
      w k ^ (η * syracuseZ c (r + m * 2 ^ k))
        = w k ^ (η * syracuseZ c r)
            * (w k ^ (η * 3 * 2 ^ (k - v2Z (3 * (r : ℤ) + c)))) ^ m := by
    intro m _
    rw [cu_syracuse_affineZ hc1 r m k hr hK, ← syracuseZ_eq_quotZ hc1 hr, Nat.mul_add,
      show η * (3 * m * 2 ^ (k - v2Z (3 * (r : ℤ) + c)))
          = (η * 3 * 2 ^ (k - v2Z (3 * (r : ℤ) + c))) * m by ring,
      pow_add, pow_mul (w k) (η * 3 * 2 ^ (k - v2Z (3 * (r : ℤ) + c))) m]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  by_cases hcase : 2 ^ v2Z (3 * (r : ℤ) + c) ∣ η
  · rw [if_pos hcase, (ratio_one_iff (le_of_lt hK)).2 hcase]
    simp [mul_comm]
  · rw [if_neg hcase]
    have hzero : ∑ m ∈ range (2 ^ k),
        (w k ^ (η * 3 * 2 ^ (k - v2Z (3 * (r : ℤ) + c)))) ^ m = 0 := by
      refine (geomSum_eq_zero_iff (by positivity : (2 : ℕ) ^ k ≠ 0)).2 ⟨?_, ?_⟩
      · rw [← pow_mul, w_pow_eq_one_iff]
        exact ⟨η * 3 * 2 ^ (k - v2Z (3 * (r : ℤ) + c)), by ring⟩
      · exact fun hcon => hcase ((ratio_one_iff (le_of_lt hK)).1 hcon)
    rw [hzero, mul_zero]

/-- **The integer-shifted clean character entry.**  Mirror of `ShiftedOperator.cleanEntryS`,
built from `TcountZ` and the integer shells. -/
noncomputable def cleanEntryZ (c : ℤ) (k η : ℕ) (ξ : ℤ) : ℂ :=
  ∑ r ∈ (Icc 1 (k - 1)).biUnion (shellZ c k),
    (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (TcountZ c k u r : ℂ) * w k ^ (η * u))
      * wz k (-(ξ * (r : ℤ)))

/-- At a non-negative shift the integer clean entry is the `c : ℕ` one.  The bridge, so that
nothing above `c ≥ 0` is a new object. -/
theorem cleanEntryZ_natCast (c k η : ℕ) (ξ : ℤ) :
    cleanEntryZ (c : ℤ) k η ξ = cleanEntryS c k η ξ := by
  unfold cleanEntryZ cleanEntryS
  refine Finset.sum_congr ?_ (fun r _ => by simp only [TcountZ_natCast])
  refine Finset.biUnion_congr rfl (fun j _ => ?_)
  exact shellZ_natCast c k j

/-- The integer-shifted masked source set. -/
def maskedOddsZ (c : ℤ) (k b : ℕ) : Finset ℕ := (Icc 1 b).biUnion (shellZ c k)

/-- **The join, at an integer shift.**  The clean entry of `T_k^{(c)}` *is* the masked sum.
The `[v(r) ≤ b]` mask is produced by `gauss_collapseZ`, not assumed; `gate_iff` is shift-free
and is used unchanged.  Mirror of `cleanEntryS_eq_masked`. -/
theorem cleanEntryZ_eq_masked {c : ℤ} (hc1 : -1 ≤ c) {k b η : ℕ} {η' : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hbk : b + 1 ≤ k) (ξ : ℤ) :
    cleanEntryZ c k η ξ
      = ∑ r ∈ maskedOddsZ c k b, wz k ((η : ℤ) * ((syracuseZ c r : ℕ) : ℤ) - ξ * (r : ℤ)) := by
  have hd1 : (↑(Icc 1 (k - 1)) : Set ℕ).PairwiseDisjoint (shellZ c k) := by
    intro x _ y _ hxy; exact shellZ_disjoint hxy
  have hd2 : (↑(Icc 1 b) : Set ℕ).PairwiseDisjoint (shellZ c k) := by
    intro x _ y _ hxy; exact shellZ_disjoint hxy
  rw [cleanEntryZ, Finset.sum_biUnion hd1, maskedOddsZ, Finset.sum_biUnion hd2]
  have hpow : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero k two_ne_zero
  have hshell : ∀ j ∈ Icc 1 (k - 1),
      (∑ r ∈ shellZ c k j,
        (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (TcountZ c k u r : ℂ) * w k ^ (η * u))
          * wz k (-(ξ * (r : ℤ))))
        = if j ≤ b then
            ∑ r ∈ shellZ c k j,
              wz k ((η : ℤ) * ((syracuseZ c r : ℕ) : ℤ) - ξ * (r : ℤ)) else 0 := by
    intro j hj
    rw [mem_Icc] at hj
    have hterm : ∀ r ∈ shellZ c k j,
        (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (TcountZ c k u r : ℂ) * w k ^ (η * u))
            * wz k (-(ξ * (r : ℤ)))
          = if j ≤ b then
              wz k ((η : ℤ) * ((syracuseZ c r : ℕ) : ℤ) - ξ * (r : ℤ)) else 0 := by
      intro r hr
      have hmem := hr
      unfold shellZ at hmem
      rw [mem_filter] at hmem
      have hrodd : r % 2 = 1 := hmem.2.2.1
      have hvj : v2Z (3 * (r : ℤ) + c) = j := hmem.2.2.2
      have hclean : v2Z (3 * (r : ℤ) + c) < k := by omega
      rw [gauss_collapseZ hc1 hrodd hclean η, hvj]
      by_cases hcase : (2 : ℕ) ^ j ∣ η
      · rw [if_pos hcase, if_pos ((gate_iff hη hη').1 hcase)]
        rw [show (((2 ^ k : ℕ) : ℂ)) = (2 : ℂ) ^ k by push_cast; ring, ← mul_assoc,
          inv_mul_cancel₀ hpow, one_mul, ← wz_natCast, ← wz_add,
          show ((η * syracuseZ c r : ℕ) : ℤ) + -(ξ * (r : ℤ))
              = (η : ℤ) * ((syracuseZ c r : ℕ) : ℤ) - ξ * (r : ℤ) by push_cast; ring]
      · rw [if_neg hcase, if_neg (fun hcon => hcase ((gate_iff hη hη').2 hcon)), mul_zero,
          zero_mul]
    rw [Finset.sum_congr rfl hterm]
    by_cases hcase : j ≤ b
    · simp only [if_pos hcase]
    · simp only [if_neg hcase, Finset.sum_const, smul_zero]
  have hsub : Icc 1 b ⊆ Icc 1 (k - 1) := by
    intro j hj; rw [mem_Icc] at hj ⊢; omega
  rw [Finset.sum_congr rfl hshell,
    ← Finset.sum_subset hsub (fun j hj hjn => by
      rw [mem_Icc] at hj hjn; rw [if_neg (by omega)])]
  exact Finset.sum_congr rfl (fun j hj => by rw [mem_Icc] at hj; rw [if_pos hj.2])

/-- **S1 AT AN INTEGER SHIFT, ONE SHELL.**  The shell-`j` character sum is exactly
`w^{ξuc} · Sodd(alpha_j, k−j)`.

Compare `ShiftedOperator.shell_character_sumS`, which is this at `c : ℕ`.  **The `Sodd`
factor and its argument are bit-for-bit identical** — `alphaJ` never mentions the shift — and
the whole shift sits in the unimodular prefactor.  That is what makes §6e a substitution
rather than a re-derivation, exactly as it was at `c : ℕ`. -/
theorem shell_character_sumZ {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) (hc : c % 2 = 1) (hc1 : -1 ≤ c)
    {k j : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    {η ξ u : ℤ} (hu : (2 : ℤ) ^ k ∣ 3 * u - 1)
    {α : ℕ} (hres : (2 : ℤ) ^ k ∣ (α : ℤ) - alphaJ η ξ u j)
    (hvj : (2 : ℤ) ^ j ∣ alphaJ η ξ u j) :
    ∑ r ∈ shellZ c k j, wz k (η * ((syracuseZ c r : ℕ) : ℤ) - ξ * (r : ℤ))
      = wz k (ξ * u * c) * Sodd k α (k - j) := by
  have hαj : (2 : ℤ) ^ j ∣ (α : ℤ) := by
    obtain ⟨d, hd⟩ := hres
    obtain ⟨e, he⟩ := hvj
    exact ⟨e + 2 ^ (k - j) * d, by
      have hsplit : (2 : ℤ) ^ k = 2 ^ j * 2 ^ (k - j) := by
        rw [← pow_add]; congr 1; omega
      have hα : (α : ℤ) = alphaJ η ξ u j + 2 ^ k * d := by linarith
      rw [hα, he, hsplit]; ring⟩
  have hterm : ∀ r ∈ shellZ c k j,
      wz k (η * ((syracuseZ c r : ℕ) : ℤ) - ξ * (r : ℤ))
        = wz k (ξ * u * c) * w k ^ (α * sbMapZ c k j r) := by
    intro r hr
    obtain ⟨hq, hqodd, hqpos⟩ := shellZ_oddpart hc1 hr
    have hsyr : ((syracuseZ c r : ℕ) : ℤ) = (3 * (r : ℤ) + c) / 2 ^ j := by
      rw [syracuseZ_on_shellZ hc1 hr, Int.toNat_of_nonneg hqpos.le]
    have h1 : wz k (η * ((syracuseZ c r : ℕ) : ℤ) - ξ * (r : ℤ))
        = wz k ((α : ℤ) * ((3 * (r : ℤ) + c) / 2 ^ j)) * wz k (ξ * u * c) := by
      rw [hsyr, ← wz_add]
      obtain ⟨d, hd⟩ := hres
      obtain ⟨t, ht⟩ := hu
      unfold alphaJ at hd
      refine wz_congr ⟨ξ * (r : ℤ) * t - d * ((3 * (r : ℤ) + c) / 2 ^ j), ?_⟩
      linear_combination (-((3 * (r : ℤ) + c) / 2 ^ j)) * hd + (-(ξ * u)) * hq
        + (ξ * (r : ℤ)) * ht
    have h2 : wz k ((α : ℤ) * ((3 * (r : ℤ) + c) / 2 ^ j))
        = w k ^ (α * sbMapZ c k j r) := by
      have hcast : ((((3 * (r : ℤ) + c) / 2 ^ j).toNat % 2 ^ (k - j) : ℕ) : ℤ)
          = ((3 * (r : ℤ) + c) / 2 ^ j) % 2 ^ (k - j) := by
        push_cast
        rw [Int.toNat_of_nonneg hqpos.le]
      have hsb : ((3 * (r : ℤ) + c) / 2 ^ j).toNat % 2 ^ (k - j) = sbMapZ c k j r := by
        unfold sbMapZ
        rw [← hcast, Int.toNat_natCast]
      conv_lhs => rw [show ((3 * (r : ℤ) + c) / 2 ^ j)
        = ((((3 * (r : ℤ) + c) / 2 ^ j).toNat : ℕ) : ℤ) from
          (Int.toNat_of_nonneg hqpos.le).symm]
      rw [wz_period (k := k) (j := j) (by omega) hαj (((3 * (r : ℤ) + c) / 2 ^ j).toNat), hsb,
        show ((α : ℤ) * ((sbMapZ c k j r : ℕ) : ℤ)) = ((α * sbMapZ c k j r : ℕ) : ℤ) by
          push_cast; ring,
        wz_natCast]
    rw [h1, h2, mul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, shellZ_reindex hc3 hc hj hjk]

/-- **THE UPPER-REGIME ENTRY THEOREM AT AN INTEGER SHIFT.**  For `a < b` the integer-shifted
clean entry collapses onto the single shell `j = d := b − a`:

```
    cleanEntryZ c k η ξ = w^{ξ·u·c} · Sodd(resJ k η ξ u d, k − d)
```

This is `ShiftedOperator.upper_entry_eqS` at `c : ℤ`, and gate L9 measured both sides at
`c = -1` before it was written.  **The `Sodd` factor is the `c = 1` one** — same `resJ`, same
`alphaJ`, same range — and the prefactor is unimodular.  Those are precisely the two
properties the Gram argument consumes, which is why step `4c` is a substitution.

Everything about the dead band — `shell_dvd_upper`, `shell_sum_vanishes` — is shift-free and
is imported unchanged: both are statements about `alphaJ`, and `alphaJ` does not see the
shift. -/
theorem upper_entry_eqZ {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) (hc : c % 2 = 1) (hc1 : -1 ≤ c)
    {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k) :
    cleanEntryZ c k η ξ
      = wz k (ξ * u * c) * Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) := by
  rw [cleanEntryZ_eq_masked hc1 hη hη' (by omega) ξ, maskedOddsZ,
    Finset.sum_biUnion (fun x _ y _ hxy => shellZ_disjoint hxy)]
  refine (Finset.sum_eq_single_of_mem (b - a) (mem_Icc.2 ⟨by omega, by omega⟩) ?_).trans ?_
  · -- every shell other than `j = d` is inside the dead band
    intro j hj hjd
    rw [mem_Icc] at hj
    rw [shell_character_sumZ hc3 hc hc1 hj.1 (by omega) huinv (resJ_spec k (η : ℤ) ξ u j)
        (shell_dvd_upper hη hη' hξ hξ' hu hab hbk hj.1 hj.2),
      shell_sum_vanishes hη hη' hξ hξ' hu hab hbk hj.1 hj.2 hjd
        (resJ_spec k (η : ℤ) ξ u j),
      mul_zero]
  · -- the surviving shell
    exact shell_character_sumZ hc3 hc hc1 (by omega) (by omega) huinv
      (resJ_spec k (η : ℤ) ξ u (b - a))
      (shell_dvd_upper (j := b - a) hη hη' hξ hξ' hu hab hbk (by omega) (by omega))

/-- **The integer-shifted prefactor is unimodular** — the only property of it the Gram
argument uses, and therefore the precise sense in which the shift is invisible above §6d. -/
theorem norm_shift_phaseZ (k : ℕ) (ξ u c : ℤ) : ‖wz k (ξ * u * c)‖ = 1 := norm_wz k _

/-- **Off the support the integer-shifted entry is exactly `0`.**  Immediate from
`upper_entry_eqZ`: the vanishing lives entirely in the `Sodd` factor, which is the unshifted
one, so `GramIdentity.upper_entry_eq_zero`'s argument transfers verbatim. -/
theorem upper_entry_eqZ_zero {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) (hc : c % 2 = 1) (hc1 : -1 ≤ c)
    {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k)
    (hno : ¬ (2 : ℤ) ^ (k - 1) ∣ alphaJ (η : ℤ) ξ u (b - a)) :
    cleanEntryZ c k η ξ = 0 := by
  have hz : Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) = 0 := by
    have h1 : cleanEntry k η ξ
        = wz k (ξ * u) * Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) :=
      upper_entry_eq hη hη' hξ hξ' hu huinv hab hbk
    have h2 : cleanEntry k η ξ = 0 :=
      upper_entry_eq_zero hη hη' hξ hξ' hu huinv hab hbk hno
    have h3 : wz k (ξ * u) * Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) = 0 := by
      rw [← h1, h2]
    have hne : wz k (ξ * u) ≠ 0 := by
      intro hcon
      have := norm_wz k (ξ * u)
      rw [hcon, norm_zero] at this
      exact absurd this (by norm_num)
    exact (mul_eq_zero.1 h3).resolve_left hne
  rw [upper_entry_eqZ hc3 hc hc1 hη hη' hξ hξ' hu huinv hab hbk, hz, mul_zero]

/-- **ON THE SHARP POINTS THE INTEGER-SHIFTED ENTRY HAS MODULUS EXACTLY `2^{k−d−1}`.**

The shift drops out at the first step (`‖wz k (ξ·u·c)‖ = 1`), and what is left is S4's FULL
branch applied to the **unshifted** `Sodd`.  Gate L9's sharp-point column measured this to
`8.5e-13` at `c = -1`, `k = 5, 6`, over 27 sharp cases.

With this and `upper_entry_eqZ`, **Lemma A's entry theorem is closed at an integer shift.**
The clean blocks and the Gram identity are step `4c` and are not here. -/
theorem norm_upper_entryZ {c : ℤ} (hc3 : ¬ (3 : ℤ) ∣ c) (hc : c % 2 = 1) (hc1 : -1 ≤ c)
    {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k)
    (how : (2 : ℤ) ^ (k - 1) ∣ alphaJ (η : ℤ) ξ u (b - a)) :
    ‖cleanEntryZ c k η ξ‖ = (2 : ℝ) ^ (k - (b - a) - 1) := by
  rw [upper_entry_eqZ hc3 hc hc1 hη hη' hξ hξ' hu huinv hab hbk, norm_mul, norm_wz, one_mul,
    norm_Sodd_full k _ _ (by omega) ((resJ_dvd_iff (by omega) _ _ _ _).2 how)]
  push_cast
  ring

/-!
### The entry theorem for `3x − 1`, with the shift hypotheses discharged

`c = -1` satisfies all three side conditions by `decide`, so the two theorems below carry
only the hypotheses the `c = 1` originals carry.  These are the first statements in the
corpus about the **`3x − 1` clean operator's entries** that are proved rather than measured.

They are **not** Lemma A for `3x − 1`, and still less a certificate: the clean-block norm
bound needs `BentZ` / `gram_upperZ` / `cleanBlockCLMZ` (step `4c`), and the certificate needs
those plus the defect half and the assembly.  `hL2`/`hParseval` remains open throughout.
-/

theorem upper_entry_eq_minus_one {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k) :
    cleanEntryZ (-1) k η ξ
      = wz k (ξ * u * (-1)) * Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) :=
  upper_entry_eqZ (by decide) (by decide) (by decide) hη hη' hξ hξ' hu huinv hab hbk

theorem norm_upper_entry_minus_one {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k)
    (how : (2 : ℤ) ^ (k - 1) ∣ alphaJ (η : ℤ) ξ u (b - a)) :
    ‖cleanEntryZ (-1) k η ξ‖ = (2 : ℝ) ^ (k - (b - a) - 1) :=
  norm_upper_entryZ (by decide) (by decide) (by decide) hη hη' hξ hξ' hu huinv hab hbk how

end EntryInteger

/-!
--------------------------------------------------------------------------------
## §7. `#eval` witnesses, checked against the Python
--------------------------------------------------------------------------------

Ground rule 5: verify from outside the system that made the claim.  Every value below is
reproduced by `calibrate_integer_shift.py` — `rstar_c(-1, k)` and `offset(-1, k)`, the I2 probe
table — and by `syr_c(-1, n)` for the map itself.

Expected (Python, k = 3..8):
```
  r*_{-1} :  3, 11, 11, 43, 43, 171
  A_{-1}  :  1,  2,  1,  2,  1,   2      <- alternates with the parity of k
```
`decide` is used only on `apAZ`, which contains no `v2`; the `v2` trap in this corpus is that
the kernel does not reduce `padicValNat`, so `syracuseZ` values are `#eval`-ed, never `decide`-d.
`native_decide` is deliberately absent — it would add `Lean.ofReduceBool` to a file that
currently has none.
-/

section Witnesses

/-- The defect residues, matching the Python probe table. -/
example : (List.range 6).map (fun i => rstarZ (-1) (i + 3)) = [3, 11, 11, 43, 43, 171] := by
  decide

/-- **The alternation**, machine-checked at `k = 3..8`: `A_{-1}` is `1` at odd `k`, `2` at even
`k`.  This is the fact the header refuses to state as "constant". -/
example : (List.range 6).map (fun i => apAZ (-1) (i + 3)) = [1, 2, 1, 2, 1, 2] := by
  decide

-- The map itself.  `3n - 1` on the first six odd `n`: [1, 1, 7, 5, 13, 1]
#eval (List.range 6).map (fun i => syracuseMinus (2 * i + 1))

-- and the bridge in action: at `c = 1` this is the ordinary Syracuse map.
#eval (List.range 6).map (fun i => syracuseZ 1 (2 * i + 1))

-- The link theorem's two sides at `c = -1`, `k = 4` (`r* = 11`, `A = 2`), `m = 0..5`.
-- `link_theorem_minus_one` proves these agree; the `#eval` is the outside check that they
-- agree with `syr_c(-1, 11 + 16m)` in the Python, i.e. that the theorem is about the real map.
#eval (List.range 6).map (fun m => syracuseMinus (rstarZ (-1) 4 + m * 2 ^ 4))
#eval (List.range 6).map (fun m => oddPartZ (apAZ (-1) 4 + 3 * m))

-- Lemma B's quantity for `3x - 1`, against `coll_from_true_fibre(-1, k)` in the Python.
-- `collZ_minus_one_le_sharp` proves `collZ + 2 ≤ 3·2^k`; these are the actual values, which
-- show the slack — `3x - 1` has offset 1 or 2, never the extremal 3.
#eval (List.range 4).map (fun i => collZ (-1) (i + 3))
#eval (List.range 4).map (fun i => 3 * 2 ^ (i + 3))

-- §6's operator, and THE TRAP MEASURED.  The entrywise total
--   ∑_{u,r} |TcountZ (-1) k (od u) (od r) − TcountS (cmodN (-1) k) k (od u) (od r)|
-- is `calibrate_lemmaA_integer_shift.py` gate L5's column, which reads `2, 12, 8, 44, 32, 172`
-- at `k = 3..8`.  A zero anywhere here would mean the residue shortcut is safe, contradicting
-- `operator_not_residue_reducible` and `ShiftedOperator.lean` §4 — it is the outside check on
-- the single most expensive mistake available in this development.
#eval (List.range 4).map (fun i =>
  let k := i + 3
  ∑ u : Fin (2 ^ (k - 1)), ∑ r : Fin (2 ^ (k - 1)),
    ((TcountZ (-1) k (od u) (od r) : ℤ) - (TcountS (cmodN (-1) k) k (od u) (od r) : ℤ)).natAbs)

-- Column stochasticity of the integer operator, as counts: every column of `TcountZ` sums to
-- `2^k`, at `c = -1`, `k = 3..6`.  Expected `[8, 16, 32, 64]`.
#eval (List.range 4).map (fun i =>
  let k := i + 3
  ∑ u ∈ range (2 ^ (k - 1)), TcountZ (-1) k (od u) (od 1))

-- The bridge in action: at `c = 1` the integer count is the `c : ℕ` count (`TcountZ_natCast`
-- proves it; this is the outside check that both are the object the Python builds).
#eval (List.range 4).map (fun i => TcountZ 1 (i + 3) 1 1)
#eval (List.range 4).map (fun i => TcountS 1 (i + 3) 1 1)

-- §6c, the shell layer.  Shell cardinality is `2^(k-1-j)` and shift-independent; against the
-- L3 table in `calibrate_lemmaA_integer_shift.py`, at `c = -1`, `k = 6`, `j = 1..5`.
-- Expected [16, 8, 4, 2, 1].
#eval (List.range 5).map (fun i => (shellZ (-1) 6 (i + 1)).card)

-- THE REDUCTION, as a computation: shell and sbMap agree with the residue version, but
-- `syracuseZ` does NOT (gate L6's three columns, in the same order).
#eval (List.range 5).map (fun i => decide (shellZ (-1) 6 (i + 1) = shellS (cmodN (-1) 6) 6 (i + 1)))
#eval (shellZ (-1) 6 2).image (fun r => (sbMapZ (-1) 6 2 r, sbMapS (cmodN (-1) 6) 6 2 r))
#eval (shellZ (-1) 6 2).image (fun r => (syracuseZ (-1) r, syracuseS (cmodN (-1) 6) r))

-- §6d, CU at an integer shift.  `cu_syracuse_affineZ` proves these two lists agree at
-- c = -1; this is the outside check that they agree with gate L7's claim B, and that the
-- object being lifted is the real map.  x = 1, K = 4, m = 0..5.
-- Both read [1, 25, 49, 73, 97, 121].
#eval (List.range 6).map (fun m => syracuseZ (-1) (1 + m * 2 ^ 4))
#eval (List.range 6).map (fun m =>
  ((3 * (1 : ℤ) + (-1)) / 2 ^ v2Z (3 * (1 : ℤ) + (-1))).toNat
    + 3 * m * 2 ^ (4 - v2Z (3 * (1 : ℤ) + (-1))))

-- AND THE BOUNDARY, which is the more useful witness: at c = -5 the same two lists
-- DISAGREE, because 3*1 + (-5) < 0 and `oddPartZ` clamps.  This is gate L7's last column
-- inside Lean, and it is why `cu_syracuse_affineZ` carries `-1 ≤ c`.  A session that
-- weakens that hypothesis should look here first (mutation S148).
-- The map reads [0, 23, 47, 71, 95, 119]; the affine formula reads [0, 24, 48, 72, 96, 120].
-- Off by exactly 1 at every lift, because 3*1 - 5 = -2 gives q = -1, and `q.toNat` is 0.
#eval (List.range 6).map (fun m => syracuseZ (-5) (1 + m * 2 ^ 4))
#eval (List.range 6).map (fun m =>
  ((3 * (1 : ℤ) + (-5)) / 2 ^ v2Z (3 * (1 : ℤ) + (-5))).toNat
    + 3 * m * 2 ^ (4 - v2Z (3 * (1 : ℤ) + (-5))))

end Witnesses

/-! ### Axiom audit — every theorem in this file.  Expect `[propext, Classical.choice, Quot.sound]`
and nothing else: no `sorryAx`, no `Lean.ofReduceBool`. -/

#print axioms syracuseZ_natCast
#print axioms syracuseZ_one
#print axioms syracuseZ_odd
#print axioms three_add_pos
#print axioms cmodN_cast
#print axioms cmodN_odd
#print axioms rstarZ_spec
#print axioms rstarZ_lt
#print axioms rstarZ_odd
#print axioms apAZ_mul
#print axioms rstarZ_minus_one_pos
#print axioms apAZ_minus_one_mem
#print axioms oddPartZ_natCast
#print axioms oddPartZ_two_pow_mul
#print axioms fibre_odd
#print axioms link_theorem
#print axioms link_theorem_mod
#print axioms link_theorem_minus_one
#print axioms oddPartZ_ap
#print axioms cfZ_eq_cfA
#print axioms collZ_eq_collA
#print axioms collZ_le_sharp
#print axioms collZ_le
#print axioms collZ_minus_one_le_sharp
#print axioms collZ_minus_one_le
#print axioms collZ_minus_one_offset_ne_three
#print axioms TcountZ_natCast
#print axioms TkZ_natCast
#print axioms TkZ_nonneg
#print axioms TkZC_natCast
#print axioms UcleanZ_apply
#print axioms UcleanZ_defect_row
#print axioms UcleanZ_clean_row
#print axioms rstarS_mod
#print axioms rstarZ_natCast
#print axioms UcleanZ_natCast
#print axioms UendZ_natCast
#print axioms syracuseZ_ne_syracuseS_cmodN
#print axioms operator_not_residue_reducible
#print axioms v2Z_natCast
#print axioms v2Z_eq_iff_dvd
#print axioms v2Z_congr
#print axioms shellZ_natCast
#print axioms three_mul_add_ne_zero
#print axioms shellZ_residue
#print axioms shellZ_dvd
#print axioms sbMapZ_natCast
#print axioms sbMapZ_residue
#print axioms shellZ_card
#print axioms shellZ_disjoint
#print axioms shellZ_reindex
#print axioms oddPartZ_odd
#print axioms v2Z_split
#print axioms cu_valuation_frozenZ
#print axioms cu_syracuse_affineZ
#print axioms syracuseZ_eq_quotZ
#print axioms shellZ_oddpart
#print axioms syracuseZ_on_shellZ
#print axioms char_col_as_liftZ
#print axioms gauss_collapseZ
#print axioms cleanEntryZ_natCast
#print axioms cleanEntryZ_eq_masked
#print axioms shell_character_sumZ
#print axioms upper_entry_eqZ
#print axioms norm_shift_phaseZ
#print axioms upper_entry_eqZ_zero
#print axioms norm_upper_entryZ
#print axioms upper_entry_eq_minus_one
#print axioms norm_upper_entry_minus_one

end IntegerShift
