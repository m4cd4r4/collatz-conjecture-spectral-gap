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

This is the **first slice** of that development: the map, the defect residue, the offset, and
the discharge of the offset hypothesis at `c = -1`.  It is **not** a certificate for `3x − 1`,
and it does not claim one.  The spectral chain (link theorem, Lemma B, Lemma A, assembly) is
open work.

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
## §5. `#eval` witnesses, checked against the Python
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

end IntegerShift
