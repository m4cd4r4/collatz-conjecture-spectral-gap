/-
# Lemma A: the S4 dead band, the valuation table, and the survivor rule

Formalises the *arithmetic and analytic core* of Lemma A as written out in
`HALFSHIFT_S4_LEMMA_A_PROOF.md` (2026-06-01), §3 and §4.

## SCOPE DECISION (option A) - read this first

Task L6 offered three scopes. This file takes **(A)**: formalise S4 (the dead-band
vanishing) as a standalone finite-geometric-series theorem, and formalise the
valuation table and the survivor argument as statements about `alpha_j`. It does
**not** build a concrete `T_k`, does not construct the character-basis block
operator `B`, and therefore does **not** state `B*B = 2^{-d} I`.

Concretely, this file proves, for all `k`:

* `Sodd_eq_zero_iff` - **S4**, the exact vanishing criterion for the odd character
  sum, unconditional, no `k`-dependent error term (§3 of HALFSHIFT).
* `Sodd_full`, `norm_Sodd_full` - S4's FULL branch and its modulus `2^{m-1}`.
* `valuation_below/above/at` - the **valuation table** of §4, exactly as printed.
* `survivor_dead_band`, `survivor_at_d` - **(S5)**: every shell `j ≠ d` lands
  inside S4's dead band (hence contributes `0`), and at `j = d` only the two sharp
  points can survive.
* `shell_sum_vanishes` - the two joined: `Sodd(alpha_j, k-j) = 0` for `j ≠ d`.

## Sign scope (STANDING GATE, inherited from `Assembly.lean` §GATE 1)

**Nothing here says anything about Collatz cycles.** Every statement below is about
2-adic valuations, roots of unity and finite geometric series. All of it is equally
true of the `3x-1` operator, which passes the identical certificate and *has* real
cycles (`CYCLE_CLAIM_REFUTED.md`). Nothing in this file is evidence about `3x+1`
that is not also evidence about `3x-1`. In particular `3` never appears in any
statement of this file: the modular inverse enters only as an abstract **odd** unit
`u`, which is exactly the property the proof uses (see `Odd u` in every hypothesis).
That is the honest strength of the argument, and its honest limit.

## What is discharged, and what is not (do not overstate)

`Assembly.LemmaAFacts` has two residue fields. Against them:

* `hQlower` (`P_a U_clean P_b = 0` for `a ≥ b`) - **NOT touched, at all.** It is R1
  of `STEP4_BLOCK_FORMULA_FOUNDATION.md`, a different argument from the one here.
* `hQupper` (`Q a b ≤ s^(b-a) + ...` for `a < b`) - **NOT discharged as a Lean
  statement either.** What is now formal is a set of *inputs to its paper proof*:
  the whole of §3 (S4), and the §4 steps S1-valuations and S5-survivor. Still on
  paper only: the passage from `Sodd` to the block entry `hat(eta,xi)` (needs the
  shell decomposition of a concrete `U_clean`), the owner count (S6/S7), the
  disjointness (S8), and hence `B*B = 2^{-d} I` and the numeric bound itself.
  Those need a concrete `T_k`, which no file in this development defines.

**Read that precisely: 0 of the 2 residue fields are closed.** Neither can be, in
Lean, without a concrete `T_k`. The claim this file supports is narrower and true:
the *analytic* heart of `hQupper`'s paper proof - the only step prior notes called
non-elementary - is now machine-checked, and what remains of that proof is
combinatorial bookkeeping over a concrete operator, not analysis.

## Load-bearing vs retained hypotheses (the `unused variable` warnings are real)

Five hypotheses below are deliberately retained for fidelity to HALFSHIFT's setting
and are *not* used by their proofs. This makes the theorems weaker than they could
be, never stronger, and is recorded here rather than silenced:

* `valuation_below`: `Odd η'` unused - row 1 needs only `ξ'`, `u` odd.
* `valuation_above`: `Odd ξ'`, `Odd u` unused - row 2 needs only `η'` odd.
* `survivor_dead_band`: `1 ≤ j` unused - the conclusion also holds at `j = 0`.
* `survivor_at_d`: `b + 2 ≤ k` unused - `2^d ∣ alpha_d` needs no top truncation.

Sorry-free. Axioms: subset of `{propext, Classical.choice, Quot.sound}` - verified
by the `#print axioms` block at the bottom.
-/

import CountingLemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Ring.GeomSum

namespace LemmaA

open Finset

/-!
--------------------------------------------------------------------------------
## Section 0. Divisibility primitives (ℕ and ℤ)
--------------------------------------------------------------------------------
-/

/-- `2^k ∣ α·2^m ↔ 2^(k-m) ∣ α`. Note the **truncated** subtraction is correct on
both sides: for `m ≥ k` the left side is automatic and `2^0 = 1` divides everything.
This single lemma supplies both dead-band edges (`m` and `1`). -/
theorem two_pow_dvd_mul_two_pow (k m α : ℕ) : 2 ^ k ∣ α * 2 ^ m ↔ 2 ^ (k - m) ∣ α := by
  rcases le_or_gt k m with h | h
  · simp only [Nat.sub_eq_zero_of_le h, pow_zero, one_dvd, iff_true]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 h) α
  · have hsplit : (2 : ℕ) ^ k = 2 ^ (k - m) * 2 ^ m := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, Nat.mul_dvd_mul_iff_right (by positivity : 0 < (2 : ℕ) ^ m)]

/-- The exact 2-adic valuation of `2^t * z` for **odd** `z`, in the dvd form used
throughout `CountingLemmas` (`v2_eq_iff_dvd`). This is the only parity fact the
valuation table needs. -/
theorem v2_of_odd_mul {t : ℕ} {z : ℤ} (hz : Odd z) :
    (2 : ℤ) ^ t ∣ 2 ^ t * z ∧ ¬ (2 : ℤ) ^ (t + 1) ∣ 2 ^ t * z := by
  refine ⟨Dvd.intro z rfl, fun h => ?_⟩
  rw [pow_succ] at h
  have hne : (2 : ℤ) ^ t ≠ 0 := by positivity
  have h2 : (2 : ℤ) ∣ z := (mul_dvd_mul_iff_left hne).1 h
  obtain ⟨c, rfl⟩ := hz
  omega

/-- `2^t * x` is even whenever `t ≥ 1`. -/
theorem even_two_pow_mul {t : ℕ} (ht : 1 ≤ t) (x : ℤ) : Even ((2 : ℤ) ^ t * x) := by
  refine ⟨2 ^ (t - 1) * x, ?_⟩
  have : (2 : ℤ) ^ t = 2 ^ (t - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [this]; ring

/-- `v2 n = t` (dvd form) is the same as "`n` is `2^t` times an odd number".
Stated so the odd-part hypotheses of §2 are visibly **equivalent** to the
`v2(η) = b`, `v2(ξ) = a` of `HALFSHIFT` §4 - not a stronger, possibly vacuous,
substitute. -/
theorem two_pow_exact_iff_odd_part (t : ℕ) (n : ℤ) :
    ((2 : ℤ) ^ t ∣ n ∧ ¬ (2 : ℤ) ^ (t + 1) ∣ n) ↔ ∃ n', Odd n' ∧ n = 2 ^ t * n' := by
  constructor
  · rintro ⟨⟨c, rfl⟩, hnd⟩
    refine ⟨c, ?_, rfl⟩
    rcases Int.even_or_odd c with he | ho
    · exact absurd (by obtain ⟨d, rfl⟩ := he; exact ⟨d, by rw [pow_succ]; ring⟩) hnd
    · exact ho
  · rintro ⟨n', hn', rfl⟩
    exact v2_of_odd_mul hn'

/-!
--------------------------------------------------------------------------------
## Section 1. S4 - the dead band
--------------------------------------------------------------------------------

### STATEMENT FIDELITY (`HALFSHIFT_S4_LEMMA_A_PROOF.md` §3, quoted verbatim)

> Define `Sodd(alpha, m) := sum_{q odd, 0 <= q < 2^m} w^{alpha*q}`. With `q = 2l+1`:
> `Sodd(alpha, m) = w^alpha * sum_{l=0}^{2^{m-1}-1} (w^{2*alpha})^l`
>
> **Lemma S4.** For `m >= 1`:
> - if `2*alpha ≡ 0 (mod 2^k)` (i.e. `alpha in {0, 2^{k-1}}`): `Sodd = 2^{m-1} * w^alpha`,
>   modulus `2^{m-1}` (FULL);
> - else `Sodd = w^alpha (w^{2^m alpha} - 1)/(w^{2 alpha} - 1)`, which **vanishes iff**
>   `k - m <= v2(alpha) <= k - 2`;
> - else (`v2(alpha) < k - m`) it is a nonzero partial sum.

The Lean statement uses the **divisibility form** `2^(k-m) ∣ α ∧ ¬ 2^(k-1) ∣ α`
rather than `k-m ≤ v2 α ≤ k-2`. The two agree for `α ≠ 0` (`v2_dead_band_iff`
below), and the dvd form is additionally **correct at `α = 0`**, where Mathlib's
`padicValNat 2 0 = 0` would make the `v2` form assert vanishing at `α = 0` for
`m ≥ k` - which is false (`Sodd(0,m) = 2^{m-1}`). Calibrated against a direct
complex enumeration; see §4.
-/

/-- `w = exp(2πi / 2^k)`, the primitive `2^k`-th root of unity of `HALFSHIFT`. -/
noncomputable def w (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2 ^ k : ℕ) : ℂ))

theorem w_isPrimitiveRoot (k : ℕ) : IsPrimitiveRoot (w k) (2 ^ k) :=
  Complex.isPrimitiveRoot_exp (2 ^ k) (by positivity)

/-- The only property of `w` used anywhere below. -/
theorem w_pow_eq_one_iff (k n : ℕ) : w k ^ n = 1 ↔ 2 ^ k ∣ n :=
  (w_isPrimitiveRoot k).pow_eq_one_iff_dvd n

theorem w_ne_zero (k : ℕ) : w k ≠ 0 := Complex.exp_ne_zero _

theorem norm_w (k : ℕ) : ‖w k‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one ((w_pow_eq_one_iff k (2 ^ k)).2 dvd_rfl) (by positivity)

/-- `Sodd(α, m) = Σ_{q odd, 0 ≤ q < 2^m} w^{α q}`. -/
noncomputable def Sodd (k α m : ℕ) : ℂ :=
  ∑ q ∈ (range (2 ^ m)).filter (fun q => q % 2 = 1), w k ^ (α * q)

/-- The odd residues below `2^m` are exactly `{2l+1 : l < 2^(m-1)}`. -/
theorem oddRange_eq_image {m : ℕ} (hm : 1 ≤ m) :
    (range (2 ^ m)).filter (fun q => q % 2 = 1)
      = (range (2 ^ (m - 1))).image (fun l => 2 * l + 1) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  ext q
  simp only [mem_filter, mem_range, mem_image, Nat.add_sub_cancel, pow_succ]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨q / 2, by omega, by omega⟩
  · rintro ⟨l, hl, rfl⟩; omega

/-- The `q = 2l+1` substitution of §3, verbatim: `Sodd = w^α · Σ_l (w^{2α})^l`. -/
theorem Sodd_eq_geom (k α m : ℕ) (hm : 1 ≤ m) :
    Sodd k α m = w k ^ α * ∑ l ∈ range (2 ^ (m - 1)), (w k ^ (2 * α)) ^ l := by
  unfold Sodd
  rw [oddRange_eq_image hm, sum_image (by intro x _ y _ h; dsimp only at h; omega), mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

/-- A finite geometric sum of length `L > 0` vanishes exactly when the ratio is a
nontrivial `L`-th root of unity. (`geom_sum_mul` does all the work; the `ζ = 1`
branch is where `L ≠ 0` is used.) -/
theorem geomSum_eq_zero_iff {ζ : ℂ} {L : ℕ} (hL : L ≠ 0) :
    (∑ i ∈ range L, ζ ^ i) = 0 ↔ ζ ^ L = 1 ∧ ζ ≠ 1 := by
  constructor
  · intro h
    have hζ : ζ ≠ 1 := by
      rintro rfl
      simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
      exact hL (by exact_mod_cast h)
    refine ⟨?_, hζ⟩
    have hg := geom_sum_mul ζ L
    rw [h, zero_mul] at hg
    exact eq_of_sub_eq_zero hg.symm
  · rintro ⟨h1, h2⟩
    have hg := geom_sum_mul ζ L
    rw [h1, sub_self] at hg
    exact (mul_eq_zero.1 hg).resolve_right (sub_ne_zero.2 h2)

/-- **LEMMA S4 (the dead band).** For `m ≥ 1` and every `k`, `α`:
`Sodd(α, m) = 0` **iff** `2^(k-m) ∣ α` and `2^(k-1) ∤ α`.

Unconditional, exact, no `k`-dependent error term. `m ≥ 1` is the only side
condition, exactly the boundary HALFSHIFT §3 flags ("The only boundary to guard in
Lean is `m >= 1`"). In the cascade `m = k-j ≥ 2` since `j ≤ b ≤ k-2`, so the guard
is never binding there. -/
theorem Sodd_eq_zero_iff (k α m : ℕ) (hm : 1 ≤ m) :
    Sodd k α m = 0 ↔ (2 ^ (k - m) ∣ α ∧ ¬ (2 ^ (k - 1) ∣ α)) := by
  have hsplit : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ, Nat.add_sub_cancel]; ring
  have hexp : 2 * α * 2 ^ (m - 1) = α * 2 ^ m := by rw [hsplit]; ring
  rw [Sodd_eq_geom k α m hm, mul_eq_zero]
  have hw : ¬ (w k ^ α = 0) := pow_ne_zero _ (w_ne_zero k)
  rw [or_iff_right hw, geomSum_eq_zero_iff (by positivity : (2 : ℕ) ^ (m - 1) ≠ 0)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · -- ζ^L = 1  ⇒  2^k ∣ α·2^m  ⇒  2^(k-m) ∣ α
      rw [← pow_mul, w_pow_eq_one_iff, hexp] at h1
      exact (two_pow_dvd_mul_two_pow k m α).1 h1
    · -- ζ ≠ 1  ⇒  ¬ 2^k ∣ 2α  ⇒  ¬ 2^(k-1) ∣ α
      intro hd
      refine h2 ?_
      rw [w_pow_eq_one_iff]
      have hx := (two_pow_dvd_mul_two_pow k 1 α).2 hd
      rwa [pow_one, mul_comm] at hx
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← pow_mul, w_pow_eq_one_iff, hexp]
      exact (two_pow_dvd_mul_two_pow k m α).2 h1
    · intro hone
      rw [w_pow_eq_one_iff] at hone
      exact h2 ((two_pow_dvd_mul_two_pow k 1 α).1 (by rwa [pow_one, mul_comm]))

/-- **LEMMA S4, FULL branch.** When `2^(k-1) ∣ α` (i.e. `α ∈ {0, 2^{k-1}}` in
range), the ratio is `1` and the sum is the full count. -/
theorem Sodd_full (k α m : ℕ) (hm : 1 ≤ m) (h : 2 ^ (k - 1) ∣ α) :
    Sodd k α m = (2 ^ (m - 1) : ℕ) * w k ^ α := by
  rw [Sodd_eq_geom k α m hm]
  have hz : w k ^ (2 * α) = 1 := by
    rw [w_pow_eq_one_iff]
    have hx := (two_pow_dvd_mul_two_pow k 1 α).2 h
    rwa [pow_one, mul_comm] at hx
  rw [hz]
  simp [mul_comm]

/-- The modulus of the FULL branch is exactly `2^{m-1}`, as §3 states. -/
theorem norm_Sodd_full (k α m : ℕ) (hm : 1 ≤ m) (h : 2 ^ (k - 1) ∣ α) :
    ‖Sodd k α m‖ = (2 ^ (m - 1) : ℕ) := by
  rw [Sodd_full k α m hm h, norm_mul, norm_pow, norm_w, one_pow, mul_one]
  simp

/-- The `v2` form of the dead band, for `α ≠ 0`, matching §3's printed
`k - m <= v2(alpha) <= k - 2`. Kept separate because it is **false at `α = 0`**
under Mathlib's `padicValNat 2 0 = 0` convention. -/
theorem v2_dead_band_iff {k m α : ℕ} (hα : α ≠ 0) (hk : 2 ≤ k) :
    (2 ^ (k - m) ∣ α ∧ ¬ (2 ^ (k - 1) ∣ α)) ↔ (k - m ≤ GapCertificate.v2 α ∧ GapCertificate.v2 α ≤ k - 2) := by
  unfold GapCertificate.v2
  rw [padicValNat_dvd_iff_le hα]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hc
    exact h2 ((padicValNat_dvd_iff_le hα).2 (by omega))
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hd => by have := (padicValNat_dvd_iff_le hα).1 hd; omega⟩

/-!
--------------------------------------------------------------------------------
## Section 2. The valuation table
--------------------------------------------------------------------------------

### STATEMENT FIDELITY (`HALFSHIFT_S4_LEMMA_A_PROOF.md` §4, quoted verbatim)

> `eta*q(r) - xi*r = eta*q - xi*(2^j q - 1)/3 = q*alpha_j + xi*3^{-1}  (mod 2^k)`,
> `alpha_j := eta - xi*2^j*3^{-1}`.
>
> **Valuations, computed once (the prerequisite for the reduction AND the survivor
> rule).** With `v2(eta) = b` and `v2(xi*2^j*3^{-1}) = a+j`:
>
> `v2(alpha_j) = a+j   (j < d);     v2(alpha_j) = b   (j > d);     v2(alpha_j) >= b   (j = d).`
>
> In every case `v2(alpha_j) >= j` (using `a >= 0` for `j < d`, and `j <= b` for `j >= d`).

`3^{-1}` is carried as an abstract **odd** `u : ℤ` (§Sign scope): the proof uses
only `Odd u`, never `3 * u ≡ 1`. Valuations are in the dvd form of
`GapCertificate.v2_eq_iff_dvd`; the hypotheses `η = 2^b·η'`, `ξ = 2^a·ξ'` with
`η'`, `ξ'` odd are *equivalent* to `v2 η = b`, `v2 ξ = a` by
`two_pow_exact_iff_odd_part` above.
-/

/-- `alpha_j := eta - xi * 2^j * u`, with `u` standing for `3^{-1}`. -/
def alphaJ (η ξ u : ℤ) (j : ℕ) : ℤ := η - ξ * 2 ^ j * u

/-- **Valuation table, row 1: `j < d`.** `v2(alpha_j) = a + j`, exactly. -/
theorem valuation_below {a b j : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (hj : j < b - a) (hab : a ≤ b) :
    (2 : ℤ) ^ (a + j) ∣ alphaJ η ξ u j ∧ ¬ (2 : ℤ) ^ (a + j + 1) ∣ alphaJ η ξ u j := by
  have hkey : alphaJ η ξ u j = 2 ^ (a + j) * (2 ^ (b - a - j) * η' - ξ' * u) := by
    unfold alphaJ
    subst hη; subst hξ
    have e1 : (2 : ℤ) ^ b = 2 ^ (a + j) * 2 ^ (b - a - j) := by
      rw [← pow_add]; congr 1; omega
    rw [e1, pow_add]; ring
  rw [hkey]
  exact v2_of_odd_mul ((even_two_pow_mul (by omega) η').sub_odd (hξ'.mul hu))

/-- **Valuation table, row 2: `j > d`.** `v2(alpha_j) = b`, exactly. -/
theorem valuation_above {a b j : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (hj : b - a < j) (hab : a ≤ b) :
    (2 : ℤ) ^ b ∣ alphaJ η ξ u j ∧ ¬ (2 : ℤ) ^ (b + 1) ∣ alphaJ η ξ u j := by
  have hkey : alphaJ η ξ u j = 2 ^ b * (η' - 2 ^ (j - (b - a)) * (ξ' * u)) := by
    unfold alphaJ
    subst hη; subst hξ
    have e1 : (2 : ℤ) ^ a * ξ' * 2 ^ j * u = 2 ^ b * (2 ^ (j - (b - a)) * (ξ' * u)) := by
      have e2 : (2 : ℤ) ^ b * 2 ^ (j - (b - a)) = 2 ^ a * 2 ^ j := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      calc (2 : ℤ) ^ a * ξ' * 2 ^ j * u = (2 ^ a * 2 ^ j) * (ξ' * u) := by ring
        _ = 2 ^ b * (2 ^ (j - (b - a)) * (ξ' * u)) := by rw [← e2]; ring
    rw [e1]; ring
  rw [hkey]
  exact v2_of_odd_mul (hη'.sub_even (even_two_pow_mul (by omega) (ξ' * u)))

/-- **Valuation table, row 3: `j = d`.** `v2(alpha_d) ≥ b`. This row is an
inequality in HALFSHIFT too - it is exactly the slack the two sharp points
`alpha_d ∈ {0, 2^{k-1}}` live in. -/
theorem valuation_at {a b : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hξ : ξ = 2 ^ a * ξ') (hab : a ≤ b) :
    (2 : ℤ) ^ b ∣ alphaJ η ξ u (b - a) := by
  refine ⟨η' - ξ' * u, ?_⟩
  unfold alphaJ
  subst hη; subst hξ
  have e1 : (2 : ℤ) ^ a * ξ' * 2 ^ (b - a) * u = 2 ^ b * (ξ' * u) := by
    have e2 : (2 : ℤ) ^ a * 2 ^ (b - a) = 2 ^ b := by rw [← pow_add]; congr 1; omega
    calc (2 : ℤ) ^ a * ξ' * 2 ^ (b - a) * u = (2 ^ a * 2 ^ (b - a)) * (ξ' * u) := by ring
      _ = 2 ^ b * (ξ' * u) := by rw [e2]
  rw [e1]; ring

/-!
--------------------------------------------------------------------------------
## Section 3. (S5) The survivor rule - only `j = d` escapes the dead band
--------------------------------------------------------------------------------

### STATEMENT FIDELITY (`HALFSHIFT_S4_LEMMA_A_PROOF.md` §4, quoted verbatim)

> **(S5) only `j = d` survives.** Place the valuations above against S4's dead-band
> `[j, k-2]`:
> - `j < d`: `v2(alpha_j) = a+j`, and `j <= a+j <= b-1 <= k-3`, in `[j, k-2]` => `A_j = 0`.
> - `j > d`: `v2(alpha_j) = b`, and `j <= b <= k-2`, in `[j, k-2]` => `A_j = 0`.
> - `j = d`: `v2(alpha_d) >= b`; in the band (=> `A_d = 0`) unless `v2(alpha_d) >= k-1`,
>   i.e. `alpha_d in {0, 2^{k-1}}`, where S4 gives the FULL value
>   `|Sodd(alpha_d, k-d)| = 2^{k-d-1}`.

At shell `j` the character sum is `Sodd(alpha_j, k-j)`, so S4's dead band
`2^(k-m) ∣ α ∧ ¬2^(k-1) ∣ α` reads, with `m = k-j` and `j ≤ k`, as
`2^j ∣ alpha_j ∧ ¬2^(k-1) ∣ alpha_j` - i.e. exactly `j ≤ v2 ≤ k-2`.
-/

/-- **(S5) for `j ≠ d`.** Every shell other than `j = d` lands strictly inside the
dead band: `2^j ∣ alpha_j` and `2^(k-1) ∤ alpha_j`.

The hypothesis `b + 2 ≤ k` is HALFSHIFT's `b ≤ k-2` (the truncated level range,
`THEOREM.md` Part III); `1 ≤ j ≤ b` is the shell range of (S1). -/
theorem survivor_dead_band {k a b j : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (hab : a < b) (hbk : b + 2 ≤ k) (hj1 : 1 ≤ j) (hjb : j ≤ b)
    (hjd : j ≠ b - a) :
    (2 : ℤ) ^ j ∣ alphaJ η ξ u j ∧ ¬ (2 : ℤ) ^ (k - 1) ∣ alphaJ η ξ u j := by
  rcases lt_or_gt_of_ne hjd with hlt | hgt
  · -- j < d : v2 = a + j, and j ≤ a+j ≤ b-1 ≤ k-3
    obtain ⟨hd, hnd⟩ := valuation_below hη hη' hξ hξ' hu hlt (by omega)
    refine ⟨dvd_trans (pow_dvd_pow 2 (by omega)) hd, fun hc => hnd ?_⟩
    exact dvd_trans (pow_dvd_pow 2 (by omega)) hc
  · -- j > d : v2 = b, and j ≤ b ≤ k-2
    obtain ⟨hd, hnd⟩ := valuation_above hη hη' hξ hξ' hu hgt (by omega)
    refine ⟨dvd_trans (pow_dvd_pow 2 (by omega)) hd, fun hc => hnd ?_⟩
    exact dvd_trans (pow_dvd_pow 2 (by omega)) hc

/-- **(S5) at `j = d`.** The surviving shell still satisfies the *lower* dead-band
condition `2^d ∣ alpha_d`; only the *upper* one can fail, and it fails exactly at
the two sharp points `2^(k-1) ∣ alpha_d`. So `j = d` is the unique candidate
survivor, and it survives iff `2^(k-1) ∣ alpha_d`. -/
theorem survivor_at_d {k a b : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hξ : ξ = 2 ^ a * ξ') (hab : a < b) (hbk : b + 2 ≤ k) :
    (2 : ℤ) ^ (b - a) ∣ alphaJ η ξ u (b - a) :=
  dvd_trans (pow_dvd_pow 2 (by omega)) (valuation_at hη hξ (by omega))

/-!
### Bridge to S4

S4 is a statement about `α : ℕ` (a residue); the valuation table is about
`alphaJ : ℤ`. Both dead-band exponents (`j` and `k-1`) are `≤ k`, so both
conditions only see `alphaJ mod 2^k` - which is what lets a residue representative
be substituted.
-/

/-- Divisibility by `2^t` with `t ≤ k` is a mod-`2^k` invariant. -/
theorem dvd_congr_mod {t k : ℕ} {x y : ℤ} (ht : t ≤ k) (h : (2 : ℤ) ^ k ∣ x - y) :
    ((2 : ℤ) ^ t ∣ x ↔ (2 : ℤ) ^ t ∣ y) := by
  have hk : (2 : ℤ) ^ t ∣ x - y := dvd_trans (pow_dvd_pow 2 ht) h
  constructor
  · intro hx
    have hxy : (2 : ℤ) ^ t ∣ x - (x - y) := dvd_sub hx hk
    simpa using hxy
  · intro hy
    have hxy : (2 : ℤ) ^ t ∣ y + (x - y) := dvd_add hy hk
    simpa using hxy

/-- **(S5) + S4 joined.** For every shell `j ≠ d` in range, the shell's character
sum `Sodd(alpha_j, k-j)` is **exactly zero**.

`α : ℕ` is any residue representative of `alpha_j` mod `2^k`. -/
theorem shell_sum_vanishes {k a b j α : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (hab : a < b) (hbk : b + 2 ≤ k) (hj1 : 1 ≤ j) (hjb : j ≤ b)
    (hjd : j ≠ b - a) (hres : (2 : ℤ) ^ k ∣ (α : ℤ) - alphaJ η ξ u j) :
    Sodd k α (k - j) = 0 := by
  obtain ⟨hlow, hhigh⟩ := survivor_dead_band hη hη' hξ hξ' hu hab hbk hj1 hjb hjd
  have hjk : j ≤ k := by omega
  refine (Sodd_eq_zero_iff k α (k - j) (by omega)).2 ⟨?_, ?_⟩
  · -- 2^(k - (k-j)) = 2^j divides α
    have hkj : k - (k - j) = j := by omega
    rw [hkj, ← Int.natCast_dvd_natCast]
    push_cast
    exact (dvd_congr_mod hjk hres).2 hlow
  · intro hc
    refine hhigh ?_
    have : ((2 : ℤ) ^ (k - 1) ∣ (α : ℤ)) := by
      rw [← Int.natCast_dvd_natCast] at hc; push_cast at hc; exact hc
    exact (dvd_congr_mod (by omega) hres).1 this

/-!
--------------------------------------------------------------------------------
## Section 4. Calibration (graded: EVIDENCE, not witness)
--------------------------------------------------------------------------------

`Sodd` is not computable (it is a sum of `Complex.exp` values), so Lean cannot
`#eval` the analytic side. The calibration is therefore split, and graded honestly:

* **Python side (the analytic half).** A session-side enumeration (task L6, not
  committed; regenerate with the four lines below) computes `Sodd(α, m)` directly
  as a complex sum for `k = 5, 6`, `m = 1 .. k+1`, all `α ∈ [0, 2^k)` - 640 cases -
  and compares the numerically-zero set against **both** predicate forms (the dvd
  form and the `v2` form). Result: **0 failures**, and 0 failures on the FULL-branch
  modulus `|Sodd| = 2^{m-1}`. This exercises the `m > k` truncated-subtraction edge.
* **Lean side (the predicate half).** `#guard` below recomputes the dvd predicate
  *from the theorem's own right-hand side* (via `deadBandDec_iff`, proved, not
  asserted) and pins it to the literal vanishing sets Python measured.

Regeneration recipe (exact, 4 lines):
```python
import cmath, math
def sodd(k, a, m):
    w = cmath.exp(2j*math.pi/(2**k))
    return sum(w**(a*q) for q in range(2**m) if q % 2 == 1)
# vanishing set:  [a for a in range(2**k) if abs(sodd(k,a,m)) < 1e-9]
```

**Grade: EVIDENCE, not witness.** Neither half alone certifies `Sodd_eq_zero_iff`;
the theorem is proved above, and this only guards against the statement being about
the wrong object. The `#guard`s WOULD fail the build if the predicate drifted.
-/

/-- Decidable form of S4's dead band. Built by `decide` from the theorem's own
right-hand side, so `deadBandDec_iff` is true **by construction** - there is no
hand-transcribed predicate that could drift away from the statement. -/
def deadBandDec (k m α : ℕ) : Bool := decide (2 ^ (k - m) ∣ α ∧ ¬ (2 ^ (k - 1) ∣ α))

/-- `deadBandDec` is the right-hand side of `Sodd_eq_zero_iff`, not a lookalike. -/
theorem deadBandDec_iff (k m α : ℕ) :
    deadBandDec k m α = true ↔ (2 ^ (k - m) ∣ α ∧ ¬ (2 ^ (k - 1) ∣ α)) := by
  unfold deadBandDec; exact decide_eq_true_iff

/-- The set S4 predicts vanishes, at level `k`, block length `m`. -/
def vanishingSet (k m : ℕ) : List ℕ := (List.range (2 ^ k)).filter (deadBandDec k m)

-- Literal lists measured by the direct complex enumeration in `s4_calib.py`.
#guard vanishingSet 5 2 = [8, 24]
#guard vanishingSet 5 3 = [4, 8, 12, 20, 24, 28]
#guard vanishingSet 5 4 = [2, 4, 6, 8, 10, 12, 14, 18, 20, 22, 24, 26, 28, 30]
#guard vanishingSet 6 3 = [8, 16, 24, 40, 48, 56]
#guard vanishingSet 6 4 = [4, 8, 12, 16, 20, 24, 28, 36, 40, 44, 48, 52, 56, 60]
-- `m = 1`: the sum is the single term `w^α`, never zero.
#guard vanishingSet 5 1 = []
#guard vanishingSet 6 1 = []
-- `α = 0` is never in a vanishing set: the dvd form gets this right where the
-- `v2` form (with `padicValNat 2 0 = 0`) would not.
#guard (vanishingSet 5 4).all (· != 0)

/-!
### Satisfiability of the §2/§3 hypotheses (failure mode 3: vacuity)

`survivor_dead_band`'s hypothesis block is nonempty. A concrete witness, checked
by the kernel: `k = 6, a = 1, b = 3, d = 2, j = 1, η' = ξ' = u = 1`, so
`η = 8, ξ = 2, alpha_1 = 8 - 2·2·1 = 4`. Then `2^j = 2 ∣ 4` and `2^{k-1} = 32 ∤ 4`,
so the conclusion is a genuine (true, non-trivial) assertion at this point. -/
theorem hyp_satisfiable :
    (Odd (1 : ℤ)) ∧ alphaJ (2 ^ 3 * 1) (2 ^ 1 * 1) 1 1 = 4 ∧
      (2 : ℤ) ^ 1 ∣ (4 : ℤ) ∧ ¬ (2 : ℤ) ^ (6 - 1) ∣ (4 : ℤ) := by
  refine ⟨⟨0, by ring⟩, by unfold alphaJ; norm_num, ⟨2, by norm_num⟩, ?_⟩
  intro h
  norm_num at h

/-- The witness above is literally an instance of `survivor_dead_band`: this
`example` type-checks only if every hypothesis is satisfiable simultaneously. -/
example : (2 : ℤ) ^ 1 ∣ alphaJ (2 ^ 3 * 1) (2 ^ 1 * 1) 1 1 ∧
    ¬ (2 : ℤ) ^ (6 - 1) ∣ alphaJ (2 ^ 3 * 1) (2 ^ 1 * 1) 1 1 :=
  survivor_dead_band (k := 6) (a := 1) (b := 3) (j := 1)
    rfl ⟨0, by ring⟩ rfl ⟨0, by ring⟩ ⟨0, by ring⟩
    (by omega) (by omega) (by omega) (by omega) (by omega)

/-!
--------------------------------------------------------------------------------
## Section 5. Axiom audit
--------------------------------------------------------------------------------

Every exported declaration must use a SUBSET of `{propext, Classical.choice,
Quot.sound}`. Several use strictly fewer; that is fine and expected.
-/

#print axioms two_pow_dvd_mul_two_pow
#print axioms v2_of_odd_mul
#print axioms even_two_pow_mul
#print axioms two_pow_exact_iff_odd_part
#print axioms w_isPrimitiveRoot
#print axioms w_pow_eq_one_iff
#print axioms norm_w
#print axioms oddRange_eq_image
#print axioms Sodd_eq_geom
#print axioms geomSum_eq_zero_iff
#print axioms Sodd_eq_zero_iff
#print axioms Sodd_full
#print axioms norm_Sodd_full
#print axioms v2_dead_band_iff
#print axioms valuation_below
#print axioms valuation_above
#print axioms valuation_at
#print axioms survivor_dead_band
#print axioms survivor_at_d
#print axioms dvd_congr_mod
#print axioms shell_sum_vanishes
#print axioms deadBandDec_iff
#print axioms hyp_satisfiable

end LemmaA
