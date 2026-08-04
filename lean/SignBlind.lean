/-
# Sign-blindness at finite level: the one-step valuation law does not see the shift

## SCOPE DECLARATION (read this first)

This file proves the finite-level, elementary core of the barrier argument's input I1, in two
stages.

**Stage A (§2–§3b), one step.**

> For every **odd** `c`, the map `r ↦ (3r + c) mod 2^k` carries the odd residues mod `2^k`
> **bijectively onto the even residues**.  Consequently the distribution of `v₂(3r + c)` over
> odd `r` is **the same for every odd `c`** — in particular for `c = 1` (the `3x+1` Syracuse
> step) and `c = 2^k − 1` (the `3x−1` step).

**Stage B (§3c), every depth.**

> For every odd `c` and every valuation pattern `(j₁, …, jₜ)` with each `jᵢ ≥ 1` and
> `Σjᵢ + 1 ≤ k`, the number of odd `r < 2^k` realising that pattern is `2^{k−1−Σjᵢ}` —
> again independent of `c` (`pattern_count`, `pattern_count_sign_blind`).

Stage B is the stronger statement and the one the barrier actually consumes: the two
valuation processes agree not merely in their one-step marginals but on **every cylinder set**
inside the clean band.  It rests on a step bijection (`step_image`) — a step of valuation `j`
carries its fibre bijectively onto the odd residues one level down — so depth-`t` counting at
level `k` is depth-`(t−1)` counting at level `k − j`.

It does **NOT**:

* say anything about Collatz cycles, or about the conjecture in either direction;
* prove the process-level statement `L₊ = L₋` on `ℤ₂` outright.  Stage B gives every cylinder
  count *within the clean band* `Σjᵢ + 1 ≤ k`; passing to `ℤ₂` needs the band to be removed by
  a limit `k → ∞` and the counts turned into a measure.  **That step is not here, and calling
  Stage B the process-level law would be an overclaim;**
* touch the certificate.  `GramIdentity.gap_certificate_unconditional` neither uses nor needs
  anything below.

## Why this file exists

The corpus's barrier documents (`BARRIER_THEOREM.md`, `PHASE_T3_1_CONJUGACY.md`) had **zero
machine-checked content**: every sign-blindness claim was prose plus a Python sweep, with
input I1 carrying the label CITED.  This is the first Lean statement anywhere in the
development that mentions the `3x−1` map at all.

## The strengthening the calibration forced

The intended statement was "the `3x+1` and `3x−1` valuation counts agree".  Measuring first
(§3) showed something better and cheaper: the count is `2^{k−j−1}` **regardless of the
shift**, so there is nothing special about the two signs.  The theorem below is therefore
stated for an arbitrary odd `c`, which is also the generality Bernstein-Lagarias 1996 works
in (*"the results generalize to the ax + b map, where ab is odd"*).  Sign-blindness is the
corollary `valuation_count_sign_blind`.

## Provenance of the hard step

Injectivity of `r ↦ (3r + c) mod 2^k` is **not** proved here — it is
`CountingLemmas.three_mul_add_inj`, which routes through
`GapCertificate.eq_of_two_pow_dvd_three_mul_sub` and constructs no inverse of `3`.  This file
supplies only the parity bookkeeping and the counting.

Sorry-free, no `native_decide`.  Calibration §3 and §3c, explicit count §3b, depth-`t` count
§3c, mutation table §5 (18 mutations, all fail), axiom audit §6.
-/

import CountingLemmas

set_option autoImplicit false

namespace SignBlind

open Finset GapCertificate CountingLemmas

/-!
--------------------------------------------------------------------------------
## §1. The even residues
--------------------------------------------------------------------------------
-/

/-- The even residues mod `2^m`, the counterpart of `CountingLemmas.oddResidues`. -/
def evenResidues (m : ℕ) : Finset ℕ := (range (2 ^ m)).filter (fun q => q % 2 = 0)

theorem mem_evenResidues {m q : ℕ} : q ∈ evenResidues m ↔ q < 2 ^ m ∧ q % 2 = 0 := by
  simp [evenResidues, mem_filter, mem_range]

/-- Half the residues are even.  Proved by complementing `oddResidues_card` rather than by a
second bijection, so the two counts cannot drift apart. -/
theorem evenResidues_card {m : ℕ} (hm : 1 ≤ m) : (evenResidues m).card = 2 ^ (m - 1) := by
  classical
  have hpow : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have himg : evenResidues m = (range (2 ^ (m - 1))).image (fun t => 2 * t) := by
    ext q
    rw [mem_evenResidues, mem_image]
    constructor
    · rintro ⟨hlt, hpar⟩
      exact ⟨q / 2, mem_range.2 (by omega), by omega⟩
    · rintro ⟨t, ht, rfl⟩
      rw [mem_range] at ht
      exact ⟨by omega, by omega⟩
  rw [himg, card_image_of_injective _ (fun x y h => by omega), card_range]

/-!
--------------------------------------------------------------------------------
## §2. The shift map, and the bijection
--------------------------------------------------------------------------------

The only arithmetic input is `CountingLemmas.three_mul_add_inj`.  Everything else is parity
and a cardinality count.
-/

/-- One Syracuse numerator step, reduced mod `2^k`: `r ↦ (3r + c) mod 2^k`. -/
def shiftMap (k c r : ℕ) : ℕ := (3 * r + c) % 2 ^ k

/-- **An odd shift sends odds to evens.**  This is the only place the parity of `c` is used,
and it is the whole reason the sign cannot be seen. -/
theorem shiftMap_mem_even {k c r : ℕ} (hk : 1 ≤ k) (hc : c % 2 = 1)
    (hr : r ∈ oddResidues k) : shiftMap k c r ∈ evenResidues k := by
  rw [oddResidues, mem_filter, mem_range] at hr
  rw [mem_evenResidues]
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos k), ?_⟩
  have hdvd : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  show ((3 * r + c) % 2 ^ k) % 2 = 0
  rw [Nat.mod_mod_of_dvd _ hdvd]
  omega

/-- `shiftMap` is injective on the odd residues (a restriction of `three_mul_add_inj`). -/
theorem shiftMap_injOn {k c : ℕ} :
    Set.InjOn (shiftMap k c) (↑(oddResidues k) : Set ℕ) := by
  intro x hx y hy hxy
  simp only [oddResidues, coe_filter, Set.mem_setOf_eq, mem_range] at hx hy
  exact three_mul_add_inj hx.1 hy.1 hxy

/-- **THE BIJECTION.**  For every odd `c`, `r ↦ (3r + c) mod 2^k` maps the odd residues
*onto* the even residues.

`c` appears nowhere in the conclusion.  That is the content: the image is the same set for
every odd shift, so no statistic computed from it can depend on the shift. -/
theorem shiftMap_image {k c : ℕ} (hk : 1 ≤ k) (hc : c % 2 = 1) :
    (oddResidues k).image (shiftMap k c) = evenResidues k := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro s hs
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hs
    exact shiftMap_mem_even hk hc hr
  · rw [card_image_of_injOn shiftMap_injOn, oddResidues_card hk, evenResidues_card hk]

/-!
--------------------------------------------------------------------------------
## §3. Sign-blindness
--------------------------------------------------------------------------------

### Calibration, run BEFORE proving

Brute force over `k = 3 … 14`, both signs, every `j`: the count of odd `r < 2^k` with
`v₂((3r ± 1) mod 2^k) = j` is `2^{k−j−1}` for `1 ≤ j ≤ k−1`, with **0 mismatches**, plus
exactly one exceptional residue per sign (`3r ± 1 ≡ 0`).  That measurement is what prompted
stating the theorem for an arbitrary odd `c` rather than for the two signs.
-/

/-- **Any statistic of the shifted value has a shift-independent sum.**  Stated for an
arbitrary `f` because the valuation is not special: nothing about `v₂` is used. -/
theorem sum_comp_shiftMap_indep {k c : ℕ} (hk : 1 ≤ k) (hc : c % 2 = 1)
    {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∑ r ∈ oddResidues k, f (shiftMap k c r) = ∑ s ∈ evenResidues k, f s := by
  classical
  rw [← shiftMap_image hk hc, Finset.sum_image]
  intro x hx y hy hxy
  exact shiftMap_injOn hx hy hxy

/-- **The counting form.**  The number of odd `r` whose shifted value satisfies any predicate
`p` equals the number of even residues satisfying `p` — for every odd shift `c`. -/
theorem count_comp_shiftMap_indep {k c : ℕ} (hk : 1 ≤ k) (hc : c % 2 = 1)
    (p : ℕ → Prop) [DecidablePred p] :
    ((oddResidues k).filter (fun r => p (shiftMap k c r))).card
      = ((evenResidues k).filter p).card := by
  classical
  have h := sum_comp_shiftMap_indep (M := ℕ) hk hc (fun s => if p s then 1 else 0)
  rw [Finset.card_filter, Finset.card_filter]
  exact h

/-- **SIGN-BLINDNESS, finite level.**  The `3x+1` step and the `3x−1` step induce the *same*
distribution of `v₂` on the odd residues mod `2^k` — and so does `3x + c` for every odd `c`.

This is input I1 of `BARRIER_THEOREM.md` at one step and finite `k`.  It is **not** the
process-level `L₊ = L₋`; see the scope declaration. -/
theorem valuation_count_sign_blind {k c c' : ℕ} (hk : 1 ≤ k)
    (hc : c % 2 = 1) (hc' : c' % 2 = 1) (j : ℕ) :
    ((oddResidues k).filter (fun r => v2 (shiftMap k c r) = j)).card
      = ((oddResidues k).filter (fun r => v2 (shiftMap k c' r) = j)).card := by
  rw [count_comp_shiftMap_indep hk hc (fun s => v2 s = j),
    count_comp_shiftMap_indep hk hc' (fun s => v2 s = j)]

/-!
--------------------------------------------------------------------------------
## §3b. The explicit count
--------------------------------------------------------------------------------

`valuation_count_sign_blind` says the two counts *agree*.  This says what they **are**.
The bridge is `CountingLemmas.v2_eq_iff_mod`: valuation exactly `j` is the single residue
class `2^j` mod `2^(j+1)`, so `residue_class_card` finishes it.
-/

/-- Valuation exactly `j` (for `j ≥ 1`) is the residue class `2^j` mod `2^(j+1)`.

`j ≥ 1` is load-bearing and not cosmetic: Mathlib's `padicValNat 2 0 = 0`, so at `j = 0` the
left-hand side would also collect `s = 0`, which is even and in range. -/
theorem evenResidues_v2_eq {k j : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
    (evenResidues k).filter (fun s => v2 s = j)
      = (range (2 ^ k)).filter (fun s => s % 2 ^ (j + 1) = 2 ^ j) := by
  classical
  have hj1 : (0 : ℕ) < 2 ^ j := Nat.two_pow_pos j
  ext s
  rw [mem_filter, mem_filter, mem_evenResidues, mem_range]
  constructor
  · rintro ⟨⟨hlt, _⟩, hv⟩
    have hs0 : s ≠ 0 := by
      intro hc; rw [hc] at hv; simp [v2] at hv; omega
    exact ⟨hlt, (v2_eq_iff_mod hs0).1 hv⟩
  · rintro ⟨hlt, hmod⟩
    have hs0 : s ≠ 0 := by
      intro hc; rw [hc, Nat.zero_mod] at hmod; omega
    refine ⟨⟨hlt, ?_⟩, (v2_eq_iff_mod hs0).2 hmod⟩
    -- `s ≡ 2^j (mod 2^(j+1))` with `j ≥ 1` forces `s` even
    have hdvd : (2 : ℕ) ∣ 2 ^ (j + 1) := dvd_pow_self 2 (by omega)
    have h2 : s % 2 = (2 ^ j) % 2 := by
      rw [← Nat.mod_mod_of_dvd s hdvd, hmod]
    have : (2 : ℕ) ^ j % 2 = 0 := by
      have : (2 : ℕ) ^ j = 2 * 2 ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    omega

/-- **The explicit one-step count.**  For every odd shift `c`, exactly `2^(k-j-1)` of the odd
residues mod `2^k` have `v₂(3r + c) = j`.

This strictly strengthens `valuation_count_sign_blind`, which only said two such counts are
equal to each other. -/
theorem valuation_count_explicit {k c j : ℕ} (hk : 1 ≤ k) (hc : c % 2 = 1)
    (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
    ((oddResidues k).filter (fun r => v2 (shiftMap k c r) = j)).card = 2 ^ (k - j - 1) := by
  classical
  rw [count_comp_shiftMap_indep hk hc (fun s => v2 s = j), evenResidues_v2_eq hj hjk,
    residue_class_card hjk (Nat.pow_lt_pow_right (by norm_num) (by omega))]
  congr 1

/-!
--------------------------------------------------------------------------------
## §3c. Stage B — the t-step clean-pattern count
--------------------------------------------------------------------------------

### Calibration, run BEFORE proving

Two sweeps, both with **0 mismatches**:

* the *step bijection* (`step_image` below) — 308 cases over `k = 3…13`, `j = 1…k−1`, and
  shifts `c ∈ {1, 2^k−1, 3, 2^(k+1)+7}`, including one larger than the modulus;
* the *pattern count* — 770 clean patterns over `k = 5…12`, `t = 1…3`, both signs, count
  exactly `2^{k−1−Σj}`.

### The structure that makes the induction work

A step of valuation `j` does not merely land somewhere; it lands on **the same problem one
level down**.  `r ↦ (3r + c) / 2^j` carries the level-`j` fibre *bijectively* onto
`oddResidues (k − j)`.  So depth-`t` counting at level `k` reduces to depth-`(t−1)` counting
at level `k − j`, and the induction is structural on the pattern list.
-/

/-- Counting through an injective reindexing.  Proved by the same sum trick as
`count_comp_shiftMap_indep`, so the two stay in step. -/
theorem card_filter_of_image {S : Finset ℕ} {φ : ℕ → ℕ} (hinj : Set.InjOn φ (↑S : Set ℕ))
    (Q : ℕ → Prop) [DecidablePred Q] :
    (S.filter (fun r => Q (φ r))).card = ((S.image φ).filter Q).card := by
  classical
  rw [Finset.card_filter, Finset.card_filter,
    Finset.sum_image (fun x hx y hy h => hinj hx hy h)]

/-- A step of valuation `j` divides out exactly `2^j`, leaving an odd residue one level down. -/
theorem shiftMap_div_odd {k c r j : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    (hr : r ∈ oddResidues k) (hv : v2 (shiftMap k c r) = j) :
    shiftMap k c r / 2 ^ j ∈ oddResidues (k - j) := by
  classical
  have hs0 : shiftMap k c r ≠ 0 := by
    intro hc0; rw [hc0] at hv; simp [v2] at hv; omega
  have hmod := (v2_eq_iff_mod hs0).1 hv
  have hlt : shiftMap k c r < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hpow : (2 : ℕ) ^ k = 2 ^ j * 2 ^ (k - j) := by rw [← pow_add]; congr 1; omega
  have hjp : (0 : ℕ) < 2 ^ j := Nat.two_pow_pos j
  obtain ⟨q, hq⟩ : ∃ q, shiftMap k c r / 2 ^ (j + 1) = q := ⟨_, rfl⟩
  have h := Nat.div_add_mod (shiftMap k c r) (2 ^ (j + 1))
  rw [hmod, hq] at h
  have hval : shiftMap k c r = 2 ^ j * (2 * q + 1) := by rw [← h, pow_succ]; ring
  have hdiv : shiftMap k c r / 2 ^ j = 2 * q + 1 := by
    rw [hval]; exact Nat.mul_div_cancel_left _ hjp
  rw [oddResidues, mem_filter, mem_range, hdiv]
  refine ⟨?_, by omega⟩
  have : shiftMap k c r / 2 ^ j < 2 ^ (k - j) :=
    Nat.div_lt_of_lt_mul (by rw [← hpow]; exact hlt)
  omega

/-- Injectivity of `r ↦ (3r + c)/2^j` on the level-`j` fibre: `2^j` can be multiplied back,
after which `shiftMap_injOn` applies. -/
theorem step_injOn {k c j : ℕ} :
    Set.InjOn (fun r => shiftMap k c r / 2 ^ j)
      (↑((oddResidues k).filter (fun r => v2 (shiftMap k c r) = j)) : Set ℕ) := by
  classical
  intro x hx y hy hxy
  simp only [coe_filter, Set.mem_setOf_eq] at hx hy
  have hdx : (2 : ℕ) ^ j ∣ shiftMap k c x := by rw [← hx.2]; exact pow_padicValNat_dvd
  have hdy : (2 : ℕ) ^ j ∣ shiftMap k c y := by rw [← hy.2]; exact pow_padicValNat_dvd
  have hs : shiftMap k c x = shiftMap k c y := by
    rw [← Nat.div_mul_cancel hdx, ← Nat.div_mul_cancel hdy]
    exact congrArg (· * 2 ^ j) hxy
  exact shiftMap_injOn (by simpa using hx.1) (by simpa using hy.1) hs

/-- **THE STEP BIJECTION.**  `r ↦ (3r + c)/2^j` maps the level-`j` fibre *onto* the odd
residues one level down.  `c` again appears nowhere in the conclusion. -/
theorem step_image {k c j : ℕ} (hk : 1 ≤ k) (hc : c % 2 = 1) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
    ((oddResidues k).filter (fun r => v2 (shiftMap k c r) = j)).image
        (fun r => shiftMap k c r / 2 ^ j)
      = oddResidues (k - j) := by
  classical
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hx
    rw [mem_filter] at hr
    exact shiftMap_div_odd hj hjk hr.1 hr.2
  · rw [oddResidues_card (by omega : 1 ≤ k - j), card_image_of_injOn step_injOn,
      valuation_count_explicit hk hc hj hjk]

/-- The depth-`t` valuation pattern, as a decidable predicate.  Structural on the pattern
list; the level drops by `j` at each step, which is exactly `step_image`'s content. -/
def patternB (c : ℕ) : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | (j :: js), k, r =>
      (v2 (shiftMap k c r) == j) && patternB c js (k - j) (shiftMap k c r / 2 ^ j)

/-- **STAGE B.**  For every odd shift `c` and every clean pattern, the count is
`2^(k-1-Σj)` — independent of `c`.

"Clean" is `js.sum + 1 ≤ k`: the pattern must not consume more bits than the modulus has. -/
theorem pattern_count {c : ℕ} (hc : c % 2 = 1) :
    ∀ (js : List ℕ) (k : ℕ), (∀ j ∈ js, 1 ≤ j) → js.sum + 1 ≤ k →
      ((oddResidues k).filter (fun r => patternB c js k r = true)).card
        = 2 ^ (k - 1 - js.sum) := by
  classical
  intro js
  induction js with
  | nil =>
    intro k _ hk
    simp only [patternB, List.sum_nil, Nat.sub_zero, Finset.filter_True]
    exact oddResidues_card (by omega)
  | cons j js ih =>
    intro k hjs hsum
    have hj : 1 ≤ j := hjs j (by simp)
    simp only [List.sum_cons] at hsum
    have hsum' : js.sum + 1 ≤ k - j := by omega
    have hjk : j + 1 ≤ k := by omega
    have hk : 1 ≤ k := by omega
    have hsplit : (oddResidues k).filter (fun r => patternB c (j :: js) k r = true)
        = ((oddResidues k).filter (fun r => v2 (shiftMap k c r) = j)).filter
            (fun r => patternB c js (k - j) (shiftMap k c r / 2 ^ j) = true) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro r _
      simp only [patternB, Bool.and_eq_true, beq_iff_eq]
    rw [hsplit,
      card_filter_of_image (Q := fun x => patternB c js (k - j) x = true) step_injOn,
      step_image hk hc hj hjk,
      ih (k - j) (fun x hx => hjs x (by simp [hx])) hsum']
    simp only [List.sum_cons]
    congr 1
    omega

/-- **THE PROCESS-LEVEL SIGN-BLINDNESS, at finite `k`.**  Any two odd shifts induce the same
depth-`t` pattern counts; `3x+1` and `3x−1` in particular.

This is barrier input I1 in the form the barrier actually uses it — the mod-`2^k` chain's
valuation process, at every finite depth. -/
theorem pattern_count_sign_blind {c c' : ℕ} (hc : c % 2 = 1) (hc' : c' % 2 = 1)
    (js : List ℕ) (k : ℕ) (hjs : ∀ j ∈ js, 1 ≤ j) (hsum : js.sum + 1 ≤ k) :
    ((oddResidues k).filter (fun r => patternB c js k r = true)).card
      = ((oddResidues k).filter (fun r => patternB c' js k r = true)).card := by
  rw [pattern_count hc js k hjs hsum, pattern_count hc' js k hjs hsum]

/-!
--------------------------------------------------------------------------------
## §4. Non-vacuity
--------------------------------------------------------------------------------

`c = 1` is the `3x+1` step and `c = 2^k − 1` is the `3x−1` step, both odd for `k ≥ 1`, so the
theorem above is about the two maps the barrier is about.
-/

/-- `2^k − 1` is odd for `k ≥ 1`: the `3x−1` shift really is in scope. -/
theorem sub_one_odd {k : ℕ} (hk : 1 ≤ k) : (2 ^ k - 1) % 2 = 1 := by
  have h : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hp : 0 < 2 ^ (k - 1) := Nat.two_pow_pos _
  omega

/-- The two maps the barrier compares, instantiated with no hypothesis left open. -/
theorem plus_minus_agree {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    ((oddResidues k).filter (fun r => v2 (shiftMap k 1 r) = j)).card
      = ((oddResidues k).filter (fun r => v2 (shiftMap k (2 ^ k - 1) r) = j)).card :=
  valuation_count_sign_blind hk (by omega) (sub_one_odd hk) j

/-- The sets involved are not empty, so the equality is not vacuous: at `k = 6` there are
`2^5 = 32` odd residues and `32` even ones. -/
example : (oddResidues 6).card = 32 := by
  rw [oddResidues_card (by norm_num : (1:ℕ) ≤ 6)]; norm_num

example : (evenResidues 6).card = 32 := by
  rw [evenResidues_card (by norm_num : (1:ℕ) ≤ 6)]; norm_num

/-- The `3x−1` shift at `k = 6` is `63`, which is odd. -/
example : (2 ^ 6 - 1) % 2 = 1 := sub_one_odd (by norm_num)

/-- Stage B is non-vacuous too: at `k = 6` the depth-2 pattern `(2, 1)` is realised by
`2^(6-1-3) = 4` odd residues, for the `3x+1` step. -/
example : ((oddResidues 6).filter (fun r => patternB 1 [2, 1] 6 r = true)).card = 4 := by
  rw [pattern_count (by norm_num) [2, 1] 6 (by decide) (by norm_num)]
  decide

/-- And by the same 4 for the `3x−1` step — a depth-2 instance of the barrier's input I1. -/
example : ((oddResidues 6).filter (fun r => patternB 1 [2, 1] 6 r = true)).card
    = ((oddResidues 6).filter (fun r => patternB 63 [2, 1] 6 r = true)).card :=
  pattern_count_sign_blind (by norm_num) (by norm_num) [2, 1] 6 (by decide) (by norm_num)

/-!
--------------------------------------------------------------------------------
## §5. Mutation tests
--------------------------------------------------------------------------------

| # | mutation | result |
|---|---|---|
| N1 | `shiftMap_mem_even`: neuter `hc : c % 2 = 1` to `c % 2 = c % 2` | fails |
| N2 | `shiftMap_image`: conclusion `= evenResidues k` → `= oddResidues k` | fails |
| N3 | `evenResidues_card`: `2 ^ (m - 1)` → `2 ^ m` | fails |
| N4 | `sub_one_odd`: `(2 ^ k - 1) % 2 = 1` → `= 0` | fails |
| N5 | `valuation_count_explicit`: `2 ^ (k-j-1)` → `2 ^ (k-j)` | fails |
| N6 | `evenResidues_v2_eq`: neuter `hj : 1 ≤ j` to `1 ≤ 1` (the `padicValNat 2 0 = 0` trap) | fails |

N1 is the one that matters: it is the check that the **parity of the shift** is what makes
the image shift-independent, rather than some accident of `3`.

Stage B (§3c) was mutated separately, 12 mutations, all fail:

| # | mutation | result |
|---|---|---|
| B1 | `pattern_count`: `2 ^ (k - 1 - js.sum)` → `2 ^ (k - js.sum)` | fails |
| B2 | `pattern_count`: `2 ^ (k - 1 - js.sum)` → `2 ^ (k - 2 - js.sum)` | fails |
| B3 | `pattern_count`: `hc : c % 2 = 1` → `c % 2 = 0` | fails |
| B4 | `pattern_count`: drop the clean band, `js.sum + 1 ≤ k` → `js.sum ≤ k` | fails |
| B5 | `pattern_count`: drop positivity of each step, `1 ≤ j` → `0 ≤ j` | fails |
| B6 | `step_image`: target level `k - j` → `k - j + 1` | fails |
| B7 | `step_image`: target `oddResidues` → `evenResidues` | fails |
| B8 | `shiftMap_div_odd`: lands in `oddResidues k` rather than `oddResidues (k - j)` | fails |
| B9 | `shiftMap_div_odd`: drop `1 ≤ j` | fails |
| B10 | `card_filter_of_image`: drop the injectivity hypothesis | fails |
| B11 | `patternB`: recursion keeps level `k` instead of dropping to `k - j` | fails |
| B12 | `patternB`: recursion forgets the `/ 2 ^ j` | fails |

B4 and B11 are the two that matter.  B4 is the clean band: `2^{k−1−Σj}` is only the count
while the pattern has not consumed the modulus, and the theorem must say so.  B11 is the
structural claim — that a step of valuation `j` lands on *the same problem one level down*,
which is what makes the induction work at all rather than merely typecheck.

--------------------------------------------------------------------------------
## §6. Axiom audit
--------------------------------------------------------------------------------
-/

#print axioms mem_evenResidues
#print axioms evenResidues_card
#print axioms shiftMap_mem_even
#print axioms shiftMap_injOn
#print axioms shiftMap_image
#print axioms sum_comp_shiftMap_indep
#print axioms count_comp_shiftMap_indep
#print axioms evenResidues_v2_eq
#print axioms valuation_count_explicit
#print axioms valuation_count_sign_blind
#print axioms card_filter_of_image
#print axioms shiftMap_div_odd
#print axioms step_injOn
#print axioms step_image
#print axioms pattern_count
#print axioms pattern_count_sign_blind
#print axioms sub_one_odd
#print axioms plus_minus_agree

end SignBlind
