/-
# Sign-blindness at finite level: the one-step valuation law does not see the shift

## SCOPE DECLARATION (read this first)

This file proves **one** thing, and it is the finite-level, elementary core of the barrier
argument's input I1:

> For every **odd** `c`, the map `r ↦ (3r + c) mod 2^k` carries the odd residues mod `2^k`
> **bijectively onto the even residues**.  Consequently the distribution of `v₂(3r + c)` over
> odd `r` is **the same for every odd `c`** — in particular for `c = 1` (the `3x+1` Syracuse
> step) and `c = 2^k − 1` (the `3x−1` step).

It does **NOT**:

* say anything about Collatz cycles, or about the conjecture in either direction;
* prove the process-level statement `L₊ = L₋` (equality of the two *valuation-process* laws
  on `ℤ₂`).  That needs Haar measure, the conjugacy map `Q_∞` and a Bernoulli property;
  Mathlib has no `IsBernoulli`, and this file constructs no measure at all.  **What is here is
  the one-step, finite-`k` statement, and calling it more than that would be an overclaim;**
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

Sorry-free, no `native_decide`.  Calibration §3, mutation table §5, axiom audit §6.
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

N1 is the one that matters: it is the check that the **parity of the shift** is what makes
the image shift-independent, rather than some accident of `3`.

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
#print axioms valuation_count_sign_blind
#print axioms sub_one_odd
#print axioms plus_minus_agree

end SignBlind
