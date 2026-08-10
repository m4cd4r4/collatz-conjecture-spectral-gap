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
discharge of the offset hypothesis at `c = -1`, the link theorem, Lemma B, and — §6, added
last — the integer-shifted **operator**.  It is **not** a certificate for `3x − 1`, and it does
not claim one.

**What is still open, precisely:** Lemma A needs the entry theorem (`upper_entry_eqZ`,
`norm_upper_entryZ`) and the clean blocks and Gram identity (`BentZ`, `gram_upperZ`,
`cleanBlockCLMZ`, `norm_sq_clean_blockZ`).  §6 is step `4a` of those three, and the assembly is
a separate task after all of them.  `hL2`/`hParseval` remains open here as it does at `c = 1`.

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

**Two mutations in this batch first failed for non-mathematical reasons** and were re-run:
S132/S135 initially reported `unknown identifier`, because `lake env lean` typechecks without
writing the `.olean`, so the scratch files imported a stale module.  A stale-import failure
reports identically to a refutation and proves nothing — `lake build` the target first.
-/
import ShiftedOperator

namespace IntegerShift

open Finset GapCertificate CountingLemmas TransferOperator ShiftedOperator

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

end IntegerShift
