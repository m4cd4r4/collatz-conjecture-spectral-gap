/-
# The owner count (S6/S7 step (2) of the Lemma A block formula)

## SCOPE DECLARATION (read this first)

Task L14 offered three scopes. **This file takes (F1), and only (F1)**: the owner
count as a standalone counting theorem about `CharacterBasis.levelSet` and
`LemmaA.alphaJ`.

It does **NOT**:

* prove disjoint ownership (F2),
* prove the Gram identity `B* B = 2^{-d} I` (F3),
* discharge **(CLEAN)**, and in particular it does **not** touch
  `CleanBlock.gap_certificate_of_clean`, whose hypothesis is untouched and still
  stands. Nothing in this file may be read as closing (CLEAN).

## What is proved

For `a ≤ b` with `b + 2 ≤ k`, any odd `u : ℤ`, and any `η ∈ levelSet k b`:

    #{ ξ ∈ levelSet k a : 2^(k-1) ∣ alphaJ η ξ u (b-a) } = 2^(b-a)

(`owner_count`).  Here `alphaJ η ξ u j = η - ξ * 2^j * u` (`LemmaA.alphaJ`), and
`u` is the abstract odd integer standing for `3⁻¹ mod 2^k`; the theorem needs
nothing about `u` beyond oddness.  The S6/S7 regime is `a < b`; the proof needs
only `a ≤ b`, so that is what is assumed (see the hypothesis note on
`owner_count`).

## The proof

1. `η ∈ levelSet k b` gives `η = 2^b * η'` with `η'` odd
   (via `DefectSplit.mem_levelSet_mod`), and likewise every `ξ ∈ levelSet k a`
   is `ξ = 2^(a+1) t + 2^a` for a unique `t < 2^(k-2-a)`.
2. Since `a + (b-a) = b`,
   `alphaJ η ξ u (b-a) = 2^b * (η' - u - 2 t u) = 2^(b+1) * (w - t u)`,
   where `η' - u = 2w` (both are odd).  So, cancelling `2^(b+1)` out of
   `2^(k-1) = 2^(b+1) * 2^(k-2-b)`, the condition is exactly

       2^(k-2-b) ∣ (t u - w).                         (`cond_iff`)

3. `u` odd is a unit mod `2^M`, so that congruence pins `t` to a single residue
   class mod `2^M` (`odd_unit_class`), and a residue class mod `2^M` meets
   `[0, 2^K)` in `2^(K-M)` points (`CountingLemmas.residue_class_card`) — here
   `K = k-2-a`, `M = k-2-b`, `K - M = b - a`.

Note the oddness constraint of step 1 costs nothing precisely because it is
absorbed into the parametrisation `ξ = 2^(a+1) t + 2^a` **before** the counting;
the count is then over `t` with no parity side condition.

## Calibration

`sweep` (§4) enumerates every `(a, b, η)` triple for a given `k` with a concrete
`u = 3⁻¹ mod 2^k` and returns the mismatches.  `#guard sweep 6 43 = []` and
`#guard sweep 7 43 = []` (43 is `3⁻¹` mod both 64 and 128).  An independent
Python sweep over `k = 6,7,8,9` — 450 `(a,b,η)` triples — found 0 mismatches.

## Non-vacuity

`hyp_satisfiable_owner` plus the concrete `example`s in §4 exhibit the hypothesis
block being met and the conclusion being a non-trivial number (`2^(b-a) = 4`, not
`0` and not `1`).
-/

import DefectSplit

namespace OwnerCount

open Finset GapCertificate CountingLemmas CharacterBasis

/-!
--------------------------------------------------------------------------------
## §1. An odd `u` is a unit mod `2^M`: the congruence `t u ≡ w` is one class
--------------------------------------------------------------------------------

`CountingLemmas` has this for the specific multiplier `3` (`three_mul_add_inj` /
`three_mul_add_surj`, by pigeonhole, deliberately avoiding any inverse).  Here the
multiplier is an abstract odd `u`, and the Bezout identity coming from
`IsCoprime u (2^M)` is the cheapest route, so we take it.
-/

/-- An odd integer is coprime to `2`. -/
theorem isCoprime_two_of_odd {u : ℤ} (hu : Odd u) : IsCoprime u 2 := by
  obtain ⟨m, hm⟩ := hu
  exact ⟨1, -m, by rw [hm]; ring⟩

/-- **The unit step.** For odd `u`, `M : ℕ` and any `w : ℤ`, the set of naturals `t`
with `2^M ∣ (t u - w)` is exactly one residue class mod `2^M`. -/
theorem odd_unit_class {M : ℕ} {u w : ℤ} (hu : Odd u) :
    ∃ c : ℕ, c < 2 ^ M ∧ ∀ t : ℕ, ((2 : ℤ) ^ M ∣ ((t : ℤ) * u - w) ↔ t % 2 ^ M = c) := by
  obtain ⟨p, q, hpq⟩ : IsCoprime u ((2 : ℤ) ^ M) := (isCoprime_two_of_odd hu).pow_right
  -- `hpq : p * u + q * 2 ^ M = 1`
  have hMpos : (0 : ℤ) < 2 ^ M := by positivity
  have hnn : 0 ≤ (w * p) % (2 : ℤ) ^ M := Int.emod_nonneg _ (ne_of_gt hMpos)
  have hlt : (w * p) % (2 : ℤ) ^ M < 2 ^ M := Int.emod_lt_of_pos _ hMpos
  refine ⟨((w * p) % (2 : ℤ) ^ M).toNat, ?_, ?_⟩
  · have h : (((((w * p) % (2 : ℤ) ^ M).toNat : ℕ)) : ℤ) < 2 ^ M := by
      rwa [Int.toNat_of_nonneg hnn]
    exact_mod_cast h
  intro t
  -- (i) divisibility of `t u - w` is divisibility of `t - w p`
  have key : (2 : ℤ) ^ M ∣ ((t : ℤ) * u - w) ↔ (2 : ℤ) ^ M ∣ ((t : ℤ) - w * p) := by
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨(t : ℤ) * q + p * z, by linear_combination p * hz - (t : ℤ) * hpq⟩
    · rintro ⟨z, hz⟩
      exact ⟨-(w * q) + u * z, by linear_combination u * hz + w * hpq⟩
  -- (ii) divisibility of `t - w p` is the residue-class condition over ℤ
  have hmod : (2 : ℤ) ^ M ∣ ((t : ℤ) - w * p) ↔ (t : ℤ) % 2 ^ M = (w * p) % 2 ^ M := by
    constructor
    · intro h; exact Int.modEq_iff_dvd.2 (dvd_sub_comm.1 h)
    · intro h; exact dvd_sub_comm.1 (Int.modEq_iff_dvd.1 h)
  -- (iii) transport to ℕ
  have hcast : ((t % 2 ^ M : ℕ) : ℤ) = (t : ℤ) % (2 : ℤ) ^ M := by push_cast; ring
  rw [key, hmod]
  constructor
  · intro h
    have h2 : ((t % 2 ^ M : ℕ) : ℤ) = (w * p) % (2 : ℤ) ^ M := by rw [hcast]; exact h
    have h3 := congrArg Int.toNat h2
    simpa using h3
  · intro h
    have h2 : ((t % 2 ^ M : ℕ) : ℤ) = (w * p) % (2 : ℤ) ^ M := by
      rw [h, Int.toNat_of_nonneg hnn]
    rw [← hcast]; exact h2

/-- **The count.** For odd `u` and `M ≤ K`, the naturals `t < 2^K` with
`2^M ∣ (t u - w)` number exactly `2^(K-M)`. -/
theorem odd_class_card {K M : ℕ} {u w : ℤ} (hu : Odd u) (hMK : M ≤ K) :
    ((range (2 ^ K)).filter (fun (t : ℕ) => (2 : ℤ) ^ M ∣ ((t : ℤ) * u - w))).card
      = 2 ^ (K - M) := by
  obtain ⟨c, hc, hiff⟩ := odd_unit_class (M := M) (u := u) (w := w) hu
  have hset : (range (2 ^ K)).filter (fun (t : ℕ) => (2 : ℤ) ^ M ∣ ((t : ℤ) * u - w))
      = (range (2 ^ K)).filter (fun (t : ℕ) => t % 2 ^ M = c) := by
    apply filter_congr
    intro t _
    exact hiff t
  rw [hset, residue_class_card hMK hc]

/-!
--------------------------------------------------------------------------------
## §2. The condition on `alphaJ`, rewritten as a congruence on the level parameter
--------------------------------------------------------------------------------
-/

/-- **The rewriting step.**  With `η = 2^b η'`, `ξ = 2^(a+1) t + 2^a` and
`η' - u = 2 w`, the dead-band-survivor condition `2^(k-1) ∣ alphaJ η ξ u (b-a)`
is exactly `2^(k-2-b) ∣ (t u - w)`.

Only `a ≤ b` and `b + 2 ≤ k` are used; oddness of `η'` and `u` enters solely
through the hypothesis `hw` (which is where the halving happens). -/
theorem cond_iff {k a b t : ℕ} {u η' w : ℤ} (hw : η' - u = 2 * w)
    (hab : a ≤ b) (hbk : b + 2 ≤ k) :
    ((2 : ℤ) ^ (k - 1) ∣ LemmaA.alphaJ (2 ^ b * η') ((2 ^ (a + 1) * t + 2 ^ a : ℕ) : ℤ) u (b - a))
      ↔ (2 : ℤ) ^ (k - 2 - b) ∣ ((t : ℤ) * u - w) := by
  have hexp : a + (b - a) = b := by omega
  have hval : (((2 ^ (a + 1) * t + 2 ^ a : ℕ) : ℤ)) = 2 ^ (a + 1) * (t : ℤ) + 2 ^ a := by
    push_cast; ring
  -- the algebraic identity
  have halpha : LemmaA.alphaJ (2 ^ b * η') ((2 ^ (a + 1) * t + 2 ^ a : ℕ) : ℤ) u (b - a)
      = 2 ^ (b + 1) * (w - (t : ℤ) * u) := by
    unfold LemmaA.alphaJ
    rw [hval]
    have e1 : (2 : ℤ) ^ (a + 1) * 2 ^ (b - a) = 2 ^ (b + 1) := by
      rw [← pow_add]; congr 1; omega
    have e2 : (2 : ℤ) ^ a * 2 ^ (b - a) = 2 ^ b := by
      rw [← pow_add, hexp]
    have e3 : (2 : ℤ) ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ]; ring
    have hηw : η' = 2 * w + u := by linarith
    rw [hηw]
    linear_combination (-(t : ℤ) * u) * e1 + (-u) * e2 + (-w) * e3
  rw [halpha]
  have hsplit : (2 : ℤ) ^ (k - 1) = 2 ^ (b + 1) * 2 ^ (k - 2 - b) := by
    rw [← pow_add]; congr 1; omega
  have hne : (2 : ℤ) ^ (b + 1) ≠ 0 := by positivity
  rw [hsplit, mul_dvd_mul_iff_left hne]
  constructor
  · intro h; simpa using h.neg_right
  · intro h; simpa using h.neg_right

/-!
--------------------------------------------------------------------------------
## §3. **(F1)** The owner count
--------------------------------------------------------------------------------
-/

/-- **The owner count (F1).**  For `a < b`, `b + 2 ≤ k`, odd `u`, and any
`η ∈ levelSet k b`, exactly `2^(b-a)` elements of `levelSet k a` satisfy the
survivor condition `2^(k-1) ∣ alphaJ η ξ u (b-a)`.

This is step (2) of the S6/S7 block-formula argument.  It is a counting statement
only: it says nothing about which `ξ` those are, and nothing about the operator
norm.

**Hypothesis note (honest disclosure).**  The S6/S7 regime, and the regime of
`LemmaA.survivor_dead_band`, is `a < b`; but the proof only ever needs `a ≤ b`,
and the statement is true on the diagonal too (`a = b` gives the count `1`,
checked numerically at `k = 6,7,8`: 221 diagonal cases, all `1`).  So the
hypothesis is stated as `a ≤ b` rather than the tighter `a < b`, and `a < b` is
**not** load-bearing here.  What *is* load-bearing is `b + 2 ≤ k` (mutation M2)
and the oddness of `u` (M3). -/
theorem owner_count {k a b : ℕ} {u : ℤ} (hu : Odd u) (hab : a ≤ b) (hbk : b + 2 ≤ k)
    {η : Fin (2 ^ (k - 1))} (hη : η ∈ levelSet k b) :
    ((levelSet k a).filter
        (fun (ξ : Fin (2 ^ (k - 1))) =>
          (2 : ℤ) ^ (k - 1) ∣ LemmaA.alphaJ (η.val : ℤ) (ξ.val : ℤ) u (b - a))).card
      = 2 ^ (b - a) := by
  classical
  -- (1) split `η = 2^b * η'` with `η'` odd
  have hηmod : (η : ℕ) % 2 ^ (b + 1) = 2 ^ b := DefectSplit.mem_levelSet_mod.1 hη
  have hdm := Nat.div_add_mod (η : ℕ) (2 ^ (b + 1))
  set s : ℕ := (η : ℕ) / 2 ^ (b + 1) with hs
  have hηval : (η : ℕ) = 2 ^ (b + 1) * s + 2 ^ b := by omega
  set η' : ℤ := 2 * (s : ℤ) + 1 with hη'
  have hηZ : ((η : ℕ) : ℤ) = 2 ^ b * η' := by
    rw [hηval, hη']; push_cast; rw [pow_succ]; ring
  -- (2) halve `η' - u`
  obtain ⟨m, hm⟩ := hu
  set w : ℤ := (s : ℤ) - m with hwdef
  have hw : η' - u = 2 * w := by rw [hη', hm, hwdef]; ring
  -- (3) the level-`a` parametrisation, and the target count
  have haK : a + 2 ≤ k := by omega
  set K : ℕ := k - 2 - a with hK
  set M : ℕ := k - 2 - b with hM
  have hMK : M ≤ K := by omega
  have hKM : K - M = b - a := by omega
  have hpowK : (2 : ℕ) ^ (k - 1) = 2 ^ (a + 1) * 2 ^ K := by
    rw [← pow_add]; congr 1; omega
  -- (4) the bijection `ξ ↦ ξ / 2^(a+1)`
  have hbij : ((levelSet k a).filter
      (fun (ξ : Fin (2 ^ (k - 1))) =>
        (2 : ℤ) ^ (k - 1) ∣ LemmaA.alphaJ (η.val : ℤ) (ξ.val : ℤ) u (b - a))).card
      = ((range (2 ^ K)).filter (fun (t : ℕ) => (2 : ℤ) ^ M ∣ ((t : ℤ) * u - w))).card := by
    refine Finset.card_bij (fun ξ _ => (ξ : ℕ) / 2 ^ (a + 1)) ?_ ?_ ?_
    · -- lands in the target
      intro ξ hξ
      rw [mem_filter] at hξ
      obtain ⟨hξL, hξD⟩ := hξ
      have hξmod : (ξ : ℕ) % 2 ^ (a + 1) = 2 ^ a := DefectSplit.mem_levelSet_mod.1 hξL
      have hdmx := Nat.div_add_mod (ξ : ℕ) (2 ^ (a + 1))
      set t : ℕ := (ξ : ℕ) / 2 ^ (a + 1) with ht
      have hξval : (ξ : ℕ) = 2 ^ (a + 1) * t + 2 ^ a := by omega
      have hlt : (ξ : ℕ) < 2 ^ (k - 1) := ξ.isLt
      have htlt : t < 2 ^ K := by
        by_contra hcon
        push_neg at hcon
        have h1 : 2 ^ (a + 1) * 2 ^ K ≤ 2 ^ (a + 1) * t := Nat.mul_le_mul_left _ hcon
        have h2 : (ξ : ℕ) < 2 ^ (a + 1) * 2 ^ K := by rw [← hpowK]; exact ξ.isLt
        have h3 : 2 ^ (a + 1) * t ≤ (ξ : ℕ) := by rw [hξval]; exact Nat.le_add_right _ _
        omega
      rw [mem_filter, mem_range]
      refine ⟨htlt, ?_⟩
      rw [← cond_iff (k := k) (a := a) (b := b) (t := t) (u := u) (η' := η') (w := w)
        hw hab hbk]
      rw [← hηZ, ← hξval]
      exact hξD
    · -- injective
      intro ξ₁ h₁ ξ₂ h₂ heq
      rw [mem_filter] at h₁ h₂
      have hm₁ : (ξ₁ : ℕ) % 2 ^ (a + 1) = 2 ^ a := DefectSplit.mem_levelSet_mod.1 h₁.1
      have hm₂ : (ξ₂ : ℕ) % 2 ^ (a + 1) = 2 ^ a := DefectSplit.mem_levelSet_mod.1 h₂.1
      have e₁ := Nat.div_add_mod (ξ₁ : ℕ) (2 ^ (a + 1))
      have e₂ := Nat.div_add_mod (ξ₂ : ℕ) (2 ^ (a + 1))
      have heq' : (ξ₁ : ℕ) / 2 ^ (a + 1) = (ξ₂ : ℕ) / 2 ^ (a + 1) := heq
      rw [heq'] at e₁
      exact Fin.ext (by omega)
    · -- surjective
      intro t ht
      rw [mem_filter, mem_range] at ht
      obtain ⟨htlt, htD⟩ := ht
      have hA : 0 < 2 ^ a := Nat.two_pow_pos a
      have hvlt : 2 ^ (a + 1) * t + 2 ^ a < 2 ^ (k - 1) := by
        have h1 : t + 1 ≤ 2 ^ K := htlt
        have h2 : 2 ^ (a + 1) * (t + 1) ≤ 2 ^ (a + 1) * 2 ^ K := Nat.mul_le_mul_left _ h1
        have h3 : 2 ^ (a + 1) * (t + 1) = 2 ^ (a + 1) * t + 2 ^ (a + 1) := by ring
        have h4 : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
        rw [hpowK]
        omega
      refine ⟨⟨2 ^ (a + 1) * t + 2 ^ a, hvlt⟩, ?_, ?_⟩
      · rw [mem_filter]
        constructor
        · rw [DefectSplit.mem_levelSet_mod]
          show (2 ^ (a + 1) * t + 2 ^ a) % 2 ^ (a + 1) = 2 ^ a
          rw [Nat.mul_add_mod]
          exact Nat.mod_eq_of_lt (by rw [pow_succ]; omega)
        · show (2 : ℤ) ^ (k - 1) ∣ LemmaA.alphaJ ((η : ℕ) : ℤ)
            (((2 ^ (a + 1) * t + 2 ^ a : ℕ)) : ℤ) u (b - a)
          rw [hηZ]
          exact (cond_iff (k := k) (a := a) (b := b) (t := t) (u := u) (η' := η') (w := w)
            hw hab hbk).2 htD
      · show (2 ^ (a + 1) * t + 2 ^ a) / 2 ^ (a + 1) = t
        rw [Nat.mul_add_div (Nat.two_pow_pos (a + 1)),
          Nat.div_eq_of_lt (by rw [pow_succ]; omega)]
        omega
    -- (5) the count
  rw [hbij, odd_class_card ⟨m, hm⟩ hMK, hKM]

/-!
--------------------------------------------------------------------------------
## §4. Calibration, non-vacuity, and mutation guards
--------------------------------------------------------------------------------

`sweep k u` recomputes the owner count by brute-force enumeration, exactly the
way the external Python check did, and lists every `(a, b, η, count)` where the
count is not `2^(b-a)`.  Membership of `levelSet k a` is tested in its decidable
form `ξ % 2^(a+1) = 2^a` (`DefectSplit.mem_levelSet_mod`), which is also what
forces `ξ ≠ 0`.
-/

/-- Brute-force owner count for concrete `k, a, b, u, η`. -/
def ownerCountEval (k a b u η : ℕ) : ℕ :=
  ((List.range (2 ^ (k - 1))).filter (fun ξ =>
      decide (ξ % 2 ^ (a + 1) = 2 ^ a) &&
      decide ((2 : ℤ) ^ (k - 1) ∣ ((η : ℤ) - (ξ : ℤ) * 2 ^ (b - a) * (u : ℤ))))).length

/-- Every `(a, b, η)` triple with `a < b < k-1` whose owner count is not `2^(b-a)`. -/
def sweep (k u : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range (k - 1)).flatMap (fun a =>
    (List.range (k - 1)).flatMap (fun b =>
      if a < b then
        ((List.range (2 ^ (k - 1))).filter (fun η => decide (η % 2 ^ (b + 1) = 2 ^ b))).filterMap
          (fun η =>
            let c := ownerCountEval k a b u η
            if c = 2 ^ (b - a) then none else some (a, b, η, c))
      else []))

-- `43 = 3⁻¹` mod `2^6` and mod `2^7` (`3 * 43 = 129`).
#guard sweep 6 43 = []
#guard sweep 7 43 = []
-- and the theorem asks only for oddness of `u`, so an unrelated odd multiplier too:
#guard sweep 6 11 = []
#guard sweep 7 11 = []

/-- How many `(a, b, η)` triples `sweep` actually visits. A sweep that visits
nothing would report `[]` for the wrong reason. -/
def sweepCount (k : ℕ) : ℕ :=
  ((List.range (k - 1)).flatMap (fun a =>
    (List.range (k - 1)).flatMap (fun b =>
      if a < b then
        ((List.range (2 ^ (k - 1))).filter (fun η => decide (η % 2 ^ (b + 1) = 2 ^ b))).map
          (fun η => (a, b, η))
      else []))).length

-- The sweep is live: 26 triples at `k = 6`, 57 at `k = 7`. The external Python
-- sweep visited the same triples (26 + 57 + 120 + 247 = 450 over `k = 6..9`).
#guard sweepCount 6 = 26
#guard sweepCount 7 = 57

-- NEGATIVE CONTROLS. The sweep can report a mismatch, so `[] ` above is a result,
-- not a vacuity. An even multiplier is not a unit mod `2^M` and the count breaks.
#guard sweep 6 44 ≠ []
#guard sweep 7 2 ≠ []

-- The count is genuinely non-trivial: not `0`, not `1`.
-- `k = 6, a = 1, b = 3, η = 8` gives `2^(3-1) = 4`.
#guard ownerCountEval 6 1 3 43 8 = 4

/-- **Non-vacuity of the hypothesis block of `owner_count`.**  The three numeric
hypotheses are simultaneously satisfiable, and `levelSet 6 3` is inhabited by the
`η = 8` used in the `#guard` above. -/
theorem hyp_satisfiable_owner : Odd (43 : ℤ) ∧ 1 < 3 ∧ 3 + 2 ≤ 6 ∧
    (8 : ℕ) % 2 ^ (3 + 1) = 2 ^ 3 := by
  refine ⟨⟨21, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩

/-- The witness above really is an element of `levelSet 6 3`, i.e. the last
conjunct of `hyp_satisfiable_owner` is `owner_count`'s actual hypothesis `hη`. -/
example : (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 3 :=
  DefectSplit.mem_levelSet_mod.2 (by norm_num)

/-- `owner_count` instantiated at those concrete values — the conclusion is the
number `4` that the `#guard` measured, with no hypothesis left open. -/
example :
    ((levelSet 6 1).filter
      (fun (ξ : Fin (2 ^ (6 - 1))) => (2 : ℤ) ^ (6 - 1) ∣
        LemmaA.alphaJ (((⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))).val : ℤ)) (ξ.val : ℤ) 43
          (3 - 1))).card = 4 := by
  have := owner_count (k := 6) (a := 1) (b := 3) (u := 43)
    (η := (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1)))) ⟨21, by norm_num⟩ (by norm_num) (by norm_num)
    (DefectSplit.mem_levelSet_mod.2 (by norm_num))
  simpa using this

/-- The two auxiliary counting facts, at concrete values, as a second calibration
of `odd_class_card`: `K = 4`, `M = 2` gives `2^2 = 4`. -/
example : ((range (2 ^ 4)).filter
    (fun (t : ℕ) => (2 : ℤ) ^ 2 ∣ ((t : ℤ) * 43 - 5))).card = 2 ^ (4 - 2) :=
  odd_class_card ⟨21, by norm_num⟩ (by norm_num)

/-!
### What remains before (CLEAN)

This file supplies **step (2)** of the S6/S7 argument only.  Still open:

* **(F2)** disjoint ownership — that the owner sets for distinct `η ∈ levelSet k b`
  are pairwise disjoint, hence partition `levelSet k a`.  (A count of `2^(b-a)`
  each, times `|levelSet k b| = 2^(k-2-b)` owners, is `2^(k-2-a) = |levelSet k a|`,
  so the partition is *consistent* with the count — but consistency is not a proof.)
* **(F3)** the Gram identity `B* B = 2^{-(b-a)} I` for the upper block `B`, which
  is what turns the combinatorics into the operator bound.
* **(CLEAN)** itself, i.e. `‖P_a U_clean P_b‖ ≤ s^(b-a)`, the hypothesis of
  `CleanBlock.gap_certificate_of_clean`.  **That hypothesis is unchanged by this
  file.**  (STATUS 2026-08-03: closed by `GramIdentity.clean_bound` (F3), which
  consumes this file's `owner_count` directly.)
-/

#print axioms isCoprime_two_of_odd
#print axioms odd_unit_class
#print axioms odd_class_card
#print axioms cond_iff
#print axioms owner_count
#print axioms hyp_satisfiable_owner

end OwnerCount
