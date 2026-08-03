/-
# S1: the shell-bijection character step, and the vanishing of the lower block

Task L9. `TransferOperator.lean` (L7) and `CharacterBasis.lean` (L8) converged on the same
named blocker. In L8's words:

> **The S1 character step**: prove `∑_{r odd, v(r) ≤ b} w^{ηq(r) − ξr} = ∑_{j=1}^{b}
> w^{ξ·3⁻¹}·Sodd(alpha_j, k−j)` in Lean, using `CountingLemmas.sb_bijective` +
> `odds_partition` plus a `w^{qα}` periodicity lemma from `v₂(alpha_j) ≥ j`. That one step
> converts `lower_block_entry_vanishes` from a statement about a *shape* into
> `P_a U_clean P_b = 0`.

This file proves that step, and then one more: the **Gauss collapse**, which is the identity
that connects the character sum to the operator `T_k` actually defined in `TransferOperator`.

## SCOPE DECISION - read this before reading anything else

Four things are proved here, for all `k`:

* `wz`, `wz_congr`, `wz_period` (§1-§2) - integer powers of `w`, and the **periodicity
  lemma**: if `2^j ∣ α` then `w^{αq}` depends only on `q mod 2^{k-j}`. This is the
  prerequisite HALFSHIFT §4 flags ("`v2(alpha_j) >= j` is exactly what makes the shell sum
  land in `Sodd`'s canonical range").
* `shell_reindex`, `shell_character_sum` (§3-§4) - **the S1 step itself.** Over the shell
  `S_j`, `∑_r w^{ηq(r) − ξr} = w^{ξu}·Sodd(alpha_j, k−j)` exactly, with `u` an abstract
  inverse of `3` mod `2^k`. Multiplicity `1`, no constant carried: that is `sb_bijective`.
* `masked_entry_vanishes` (§5) - composing S1 with L8's `shell_sum_vanishes_lower`: for
  `b ≤ a`, the **masked character-basis entry**
  `hat(η,ξ) = ∑_{r odd, 1 ≤ v(r) ≤ b} w^{ηq(r) − ξr}` is exactly `0`. This is R1's statement
  at the level of a character-basis entry, no longer at the level of a *shape*.
* `gauss_collapse` (§6) - **the bridge to the operator.** For a clean source `r`
  (`v := v₂(3r+1) < k`), the actual transfer operator of `TransferOperator.lean` satisfies
  `∑_u Tcount(k,u,r)·w^{ηu} = [2^v ∣ η]·2^k·w^{η·Syr(r)}`. This is STEP4 §0's masking
  `[v(r) ≤ b]`, derived - not assumed - from `cu_syracuse_affine` and a geometric series.
* `cleanEntry`, `cleanEntry_eq_masked`, `clean_entry_vanishes` (§6b) - **the join.**
  `cleanEntry` is defined from `TransferOperator.Tcount` alone, with no mask in its statement;
  `cleanEntry_eq_masked` proves it equals the masked sum (the mask is *produced* by §6), and
  `clean_entry_vanishes` concludes `cleanEntry k η ξ = 0` for `b ≤ a`. That is R1 for the
  operator this development actually defines, one character-basis entry at a time.

## What is NOT discharged (do not soften this)

**`Assembly.LemmaAFacts.hQupper` and `hQlower` both remain OPEN _as of this file_. This file
closes 0 of the 2 residue fields.** (STATUS 2026-08-03: both since closed - `hQlower` at L12,
`hQupper` at F3.) Concretely, and in plain words:

1. **`P_a U_clean P_b = 0` is NOT proved as an operator identity.** §6b gets to *entries*:
   for every `η` of level `b` and `ξ` of level `a ≥ b`, the clean character-basis entry of
   `T_k` is `0`. Three things still stand between that and the operator statement, and none
   is a formality: `U_clean` is never packaged as a matrix or a `Module.End` (the defect row
   `r*` is *identified* by `defect_col_eq_cf` but never removed from an operator);
   `cleanEntry` drops the `1/N` of `chiVec`'s normalisation and never mentions `P_a`, `P_b`,
   so it is an unnormalised bilinear pairing rather than a block entry; and the implication
   "every entry in an orthonormal basis vanishes ⇒ the operator vanishes" is not applied -
   `CharacterBasis.chiBasis` and `P_apply` are not used anywhere in this file.
2. **No operator norm is bounded anywhere in this file.** `Q[a,b] = ‖P_a U P_b‖₂` is still
   not defined in this development. `hQupper` additionally needs the `a < b` isometry
   `B*B = 2^{-d} I`, whose S6/S7 owner-counting (HALFSHIFT §4) is not formalised at all.
   **STALE 2026-08-03:** `Q` is `ManifestInstance.Qmat` (L12); the owner-counting is L14/L15;
   the isometry is `GramIdentity.gram_upper` (F3).
3. **The defect is still not decomposed.** `hQlower`'s bound is a bound on the rank-one
   defect, and §6/§6b explicitly *exclude* `r*` - by the hypothesis `v₂(3r+1) < k` and by
   summing only over `(Icc 1 (k-1)).biUnion (shell k)` respectively.

So: L9 removes the blocker L7 and L8 both named, adds the operator bridge neither had, and
reaches R1 entrywise for the real `T_k`. It does not close either residue field.

## Orientation (pinned by L7; an orientation drift nearly shipped in L2)

`T_k` is target-first `T[u,r]`, `U = T_kᵀ`, `Q[a,b] = ‖P_a U P_b‖₂` with `a` the **target**
level and `b` the **source** level. §6 sums over the target index `u` with the source `r`
fixed - that is a **column** of `T_k`, i.e. a **row** of `U`, i.e. `(U χ_η)(r)`. This is the
direction the character sum needs, and it is the non-trivial one only because the weights
`w^{ηu}` are not constant; the unweighted version is `Tcount_col_sum`.

`CU` direction, again: **image size `2^v`, fibre size `2^{k-v}`** (inverted in an earlier
plan, caught by L3 and L7). §6 does not use the fibre count at all - it re-indexes the target
sum back to the lift window `m ∈ [0,2^k)` via `sum_fiberwise_of_maps_to`, so the only CU input
is the affine identity `cu_syracuse_affine`.

## Sign scope (STANDING GATE, inherited from `Assembly.lean` §GATE 1)

§1-§5 carry `3⁻¹` as an abstract `u : ℤ` with only `2^k ∣ 3u − 1` assumed, so they are literally
true of any odd multiplier. §6 does mention `3` (it routes through `syracuse`), and is a
counting fact about lifts and valuations; the `3x−1` operator satisfies the same shape
(`CYCLE_CLAIM_REFUTED.md`). Nothing here is an obstruction to cycles of anything.

## Calibration (session-side, `l9_calib.py`; scripts not committed)

Everything below was built numerically first, from `TransferOperator`'s own target-first
`Tcount` (not from a re-derived matrix), and reproduces the corpus's published values:

```
k    ‖F*F − I‖    max|P_a U_clean P_b|, a≥b    ρ(Q_k)      cert(k)     a*    |λ₂(T_k)|
6     3.6e-15              2.3e-16             0.553529    0.633784    2      0.2767
8     1.1e-15              8.4e-17             0.566061    0.634659    4      0.2549
10       -                    -                   -        0.634533    6         -
```

matching `EXTREMAL_VALUES.md` row 5 to all six printed digits including `a* = k − 4`. The
lower block is **exactly** zero, not merely small. Two checks specific to this file:

* the **S1 identity of §4**, checked entry-by-entry as
  `|∑_{r: 1≤v(r)≤b} w^{ηq(r)−ξr} − ∑_{j=1}^{b} w^{ξ·3⁻¹}Sodd(alpha_j,k−j)|`, is
  `4.6e-14` at `k=6` and `1.7e-13` at `k=8` over all levels and sampled `(η,ξ)`;
* the **Gauss collapse of §6**, checked as `max_r |(Uχ_η)(r) − [v(r)≤b]w^{ηq(r)}|` over every
  clean `r` and every `η`, is `1.4e-15` at `k=6` and `8.0e-16` at `k=8`.

One calibration number did **not** reproduce on the first try and is recorded rather than
buried: `cert(k)` is the row-max of `Q` weighted by `u_a = 2^{-a}` (i.e. `Q[a,b]·2^{a-b}`).
Confirmed: this weighting reproduces the published `0.634659` at `k=8` and `0.634412` at
`k=13`, with `a* = 4, 9` (so `e* = k - a* = 4` at both), in an independent rebuild.

> **WITHDRAWN 2026-08-03 (orchestrator check): the "conflicting weighting" half of this note
> was wrong, and there is nothing to reconcile.**
>
> The draft continued *"not by the `2^{-(a+1)/2}` of `Assembly`'s `uvec` ... the two
> weightings coexist in the corpus and are not interchangeable"*, and asked for someone to
> reconcile them. Two errors:
>
> 1. **`Assembly` has no `uvec`.** The identifier appears nowhere in this development -
>    `grep -rn uvec *.lean` matches only this comment. The claim cited an object that does
>    not exist.
> 2. **The two constants are not competing conventions; they play different roles.**
>    `2^{-(a+1)/2} = s^{a+1}` (with `s = 2^{-1/2}`, `Assembly.s`) is the **bound on**
>    `Q[a,b]` - it is literally what `hQupper` / `hQlower` assert. `2^{a-b}` is the
>    **weight applied to** `Q[a,b]` inside the `cert` row-sum. A bound on a quantity and a
>    weight on that same quantity are not alternative definitions of one thing, and
>    `Assembly.envelope s 3 = s^3 + s^2 = 0.853553...` is exactly the two composed.
>
> Left in place per this corpus's withdraw-in-place discipline. The reproduction claim in
> the paragraph above is correct and independently re-verified; only the comparison was
> wrong. Recorded because an invented discrepancy costs a future session more than a
> missing one - it sends them looking for a conflict that is not there.

## Hypotheses that are declared and not used (recorded, not silenced)

Following the convention of `LemmaA.lean` and `CharacterBasis.lean`. These make the theorems
*weaker* than they could be, never stronger:

* `syracuse_on_shell`: `hj : 1 ≤ j` unused - membership in `shell k j` already pins
  `v₂(3r+1) = j` and oddness, which is all the unfolding needs. Kept because every other
  shell lemma in the corpus carries it and dropping it would make the signatures inconsistent.
* `shell_character_sum`: `hj : 1 ≤ j` is used only through `shell_oddpart` and
  `sb_image_eq`; the `hjk : j + 1 ≤ k` bound is what forces `k - j ≥ 1`.
* `masked_entry_vanishes`: `hη' : Odd η'` is needed only by `valuation_lower`; `ξ'` is never
  required to be odd on the lower side (the same asymmetry L8 recorded).
* `clean_entry_vanishes`: `ξ'` appears only as the odd part of `ξ`; nothing needs it odd.
* `phase_congr` is stated and proved but not *used* - `shell_character_sum` inlines the same
  congruence combined with the `alpha_j → α` step in one witness. It is kept because it is the
  statement HALFSHIFT §4 quotes verbatim, and a reader checking fidelity wants it separately.

## Mutation tests (failure mode 1: a theorem a tactic closes on its own)

Seven single-token mutations were applied to the load-bearing statements and the build was run
on each. **All seven failed to compile**, i.e. none of these theorems is true for a trivial
reason and each named constant is doing work.

| # | mutation | result |
|---|---|---|
| N1 | `wz_period`: hypothesis `2^j ∣ α` → `2^0 ∣ α` (kill the valuation input) | fails |
| N2 | `shell_character_sum`: `Sodd k α (k - j)` → `Sodd k α (k - j - 1)` (shell width) | fails |
| N3 | `shell_character_sum`: prefactor `wz k (ξ*u)` → `wz k (ξ*u + 1)` | fails |
| N4 | `masked_entry_vanishes`: `hab : b ≤ a` → `a ≤ b` (the orientation) | fails |
| N5 | `gauss_collapse`: normalisation `2^k` → `2^(k-1)` | fails |
| N6 | `gauss_collapse`: gate `2^v ∣ η` → `2^(v+1) ∣ η` | fails |
| N7 | `cleanEntry_eq_masked`: `maskedOdds k b` → `maskedOdds k (b+1)` (mask width) | fails |

N4 is the orientation trap that shipped a defect in L2; N7 is the check that the mask the
Gauss collapse *produces* is the same mask §5 consumes, rather than an adjacent one.

Sorry-free. Axioms audited in §8.
-/

import CharacterBasis

namespace BlockVanishing

open Finset GapCertificate LemmaA CountingLemmas TransferOperator CharacterBasis

/-!
--------------------------------------------------------------------------------
## §1. `w` at integer exponents
--------------------------------------------------------------------------------

The phase `η·q(r) − ξ·r` is an *integer* (`ξ·r` is subtracted), and `alpha_j` is an integer,
so the whole of §4 lives at integer exponents. `w k ≠ 0`, so `zpow` is available and
`wz k` is a homomorphism `(ℤ,+) → (ℂ*, ·)`.
-/

/-- `w` at an integer exponent. -/
noncomputable def wz (k : ℕ) (n : ℤ) : ℂ := w k ^ n

theorem wz_natCast (k n : ℕ) : wz k (n : ℤ) = w k ^ n := by
  simp [wz]

theorem wz_add (k : ℕ) (m n : ℤ) : wz k (m + n) = wz k m * wz k n :=
  zpow_add₀ (w_ne_zero k) m n

theorem wz_two_pow (k : ℕ) : wz k ((2 : ℤ) ^ k) = 1 := by
  rw [show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, wz_natCast]
  exact (w_pow_eq_one_iff k (2 ^ k)).2 dvd_rfl

/-- **The only property of `wz` used below**: it factors through `ℤ / 2^k`. -/
theorem wz_congr {k : ℕ} {m n : ℤ} (h : (2 : ℤ) ^ k ∣ m - n) : wz k m = wz k n := by
  obtain ⟨t, ht⟩ := h
  have hm : m = n + 2 ^ k * t := by linarith
  rw [hm, wz_add]
  have : wz k ((2 : ℤ) ^ k * t) = 1 := by
    rw [wz, zpow_mul, ← wz, wz_two_pow, one_zpow]
  rw [this, mul_one]

/-!
--------------------------------------------------------------------------------
## §2. The periodicity lemma (`v₂(α) ≥ j ⇒ w^{αq}` sees only `q mod 2^{k-j}`)
--------------------------------------------------------------------------------

### STATEMENT FIDELITY (`HALFSHIFT_S4_LEMMA_A_PROOF.md` §4, quoted verbatim)

> In every case `v2(alpha_j) >= j` (using `a >= 0` for `j < d`, and `j <= b` for `j >= d`).
> Therefore `w^{q*alpha_j}` is invariant under `q -> q + 2^{k-j}`, i.e. depends only on
> `q mod 2^{k-j}`.

This is the step that lets the shell sum be *re-indexed* by SB: without it, `q mod 2^{k-j}`
would not determine the summand and the bijection would be useless.
-/

/-- **Periodicity.** If `2^j ∣ α` and `j ≤ k`, then `w^{α q}` depends only on `q mod 2^{k-j}`. -/
theorem wz_period {k j : ℕ} (hjk : j ≤ k) {α : ℤ} (hα : (2 : ℤ) ^ j ∣ α) (q : ℕ) :
    wz k (α * (q : ℤ)) = wz k (α * ((q % 2 ^ (k - j) : ℕ) : ℤ)) := by
  obtain ⟨s, hs⟩ := hα
  refine wz_congr ⟨s * (q / 2 ^ (k - j) : ℕ), ?_⟩
  have hq : (q : ℤ) = 2 ^ (k - j) * ((q / 2 ^ (k - j) : ℕ) : ℤ) + ((q % 2 ^ (k - j) : ℕ) : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.div_add_mod q (2 ^ (k - j))).symm
  have hsplit : (2 : ℤ) ^ k = 2 ^ j * 2 ^ (k - j) := by
    rw [← pow_add]; congr 1; omega
  rw [hs, hq, hsplit]; ring

/-!
--------------------------------------------------------------------------------
## §3. Re-indexing a shell sum by SB
--------------------------------------------------------------------------------

`CountingLemmas.sb_image_eq` says `S_j.image (sbMap k j) = oddResidues (k-j)`, and
`sb_injOn` says the map is injective there. So a sum over the shell of anything depending only
on `sbMap k j r` is literally a sum over the odd residues mod `2^{k-j}` - which is the index
set of `Sodd`. Multiplicity exactly `1`: no constant is carried.
-/

/-- `Sodd` is a sum over `oddResidues`; the two `Finset`s are the same by definition. -/
theorem Sodd_eq_oddResidues (k α m : ℕ) :
    Sodd k α m = ∑ q ∈ oddResidues m, w k ^ (α * q) := rfl

/-- **SB, as a change of summation variable.** -/
theorem shell_reindex {k j : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k) (α : ℕ) :
    ∑ r ∈ shell k j, w k ^ (α * sbMap k j r) = Sodd k α (k - j) := by
  rw [Sodd_eq_oddResidues, ← sb_image_eq hj hjk, Finset.sum_image (sb_injOn hj hjk)]

/-!
--------------------------------------------------------------------------------
## §4. **S1**: the shell character sum
--------------------------------------------------------------------------------

### STATEMENT FIDELITY (`HALFSHIFT_S4_LEMMA_A_PROOF.md` §4, quoted verbatim)

> **(S1=SB) group by `j := v(r)`, `j = 1..b`.** For fixed `j`, `3r+1 = 2^j*q` with
> `q = Syr(r)` odd, so `r = (2^j q - 1)/3` and
> `eta*q(r) - xi*r = eta*q - xi*(2^j q - 1)/3 = q*alpha_j + xi*3^{-1}  (mod 2^k)`,
> `alpha_j := eta - xi*2^j*3^{-1}`.
> [...] Hence the `j`-shell contributes exactly `A_j = w^{xi*3^{-1}} * Sodd(alpha_j, k-j)`.

`3⁻¹` is the abstract `u : ℤ` with `2^k ∣ 3u − 1` (§Sign scope). Note what is *not* assumed:
no relation between `η`, `ξ` and their valuations is used in §4 at all - S1 is unconditional
given `2^j ∣ alpha_j`. The valuation hypotheses enter only in §5, where `valuation_lower`
supplies exactly that divisibility.
-/

/-- On a shell, `Syr(r)` is the exact quotient `(3r+1)/2^j`. -/
theorem syracuse_on_shell {k j r : ℕ} (hj : 1 ≤ j) (hr : r ∈ shell k j) :
    syracuse r = (3 * r + 1) / 2 ^ j := by
  simp only [shell, mem_filter] at hr
  have hodd : r % 2 = 1 := hr.2.2.1
  unfold syracuse
  rw [if_neg (by omega)]
  simp only [hr.2.2.2]

/-- **The phase identity**, `mod 2^k`: `η·q − ξ·r ≡ alpha_j·q + ξ·u`. The only input is
`2^j·q = 3r+1` (`shell_oddpart`) and `3u ≡ 1`. -/
theorem phase_congr {k j r : ℕ} (hj : 1 ≤ j) (hr : r ∈ shell k j) {η ξ u : ℤ}
    (hu : (2 : ℤ) ^ k ∣ 3 * u - 1) :
    (2 : ℤ) ^ k ∣
      (alphaJ η ξ u j * (((3 * r + 1) / 2 ^ j : ℕ) : ℤ) + ξ * u)
        - (η * (((3 * r + 1) / 2 ^ j : ℕ) : ℤ) - ξ * (r : ℤ)) := by
  obtain ⟨hq, _⟩ := shell_oddpart hj hr
  obtain ⟨t, ht⟩ := hu
  have hqz : (2 : ℤ) ^ j * (((3 * r + 1) / 2 ^ j : ℕ) : ℤ) = 3 * (r : ℤ) + 1 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hq.symm
  refine ⟨-(ξ * (r : ℤ) * t), ?_⟩
  unfold alphaJ
  linear_combination (-(ξ * u)) * hqz + (-(ξ * (r : ℤ))) * ht

/-- **S1, one shell.** The shell-`j` character sum is exactly `w^{ξu}·Sodd(alpha_j, k−j)`.

`α : ℕ` is any representative of `alpha_j` mod `2^k` (`Sodd`'s index is a natural number);
`hvj` is the `v₂(alpha_j) ≥ j` prerequisite that HALFSHIFT §4 flags as the thing making the
shell sum land in `Sodd`'s canonical range. -/
theorem shell_character_sum {k j : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    {η ξ u : ℤ} (hu : (2 : ℤ) ^ k ∣ 3 * u - 1)
    {α : ℕ} (hres : (2 : ℤ) ^ k ∣ (α : ℤ) - alphaJ η ξ u j)
    (hvj : (2 : ℤ) ^ j ∣ alphaJ η ξ u j) :
    ∑ r ∈ shell k j, wz k (η * ((syracuse r : ℕ) : ℤ) - ξ * (r : ℤ))
      = wz k (ξ * u) * Sodd k α (k - j) := by
  have hαj : (2 : ℤ) ^ j ∣ (α : ℤ) := by
    obtain ⟨c, hc⟩ := hres
    obtain ⟨d, hd⟩ := hvj
    exact ⟨d + 2 ^ (k - j) * c, by
      have hsplit : (2 : ℤ) ^ k = 2 ^ j * 2 ^ (k - j) := by
        rw [← pow_add]; congr 1; omega
      have : (α : ℤ) = alphaJ η ξ u j + 2 ^ k * c := by linarith
      rw [this, hd, hsplit]; ring⟩
  have hterm : ∀ r ∈ shell k j,
      wz k (η * ((syracuse r : ℕ) : ℤ) - ξ * (r : ℤ))
        = wz k (ξ * u) * w k ^ (α * sbMap k j r) := by
    intro r hr
    have h1 : wz k (η * ((syracuse r : ℕ) : ℤ) - ξ * (r : ℤ))
        = wz k ((α : ℤ) * (((3 * r + 1) / 2 ^ j : ℕ) : ℤ)) * wz k (ξ * u) := by
      rw [syracuse_on_shell hj hr, ← wz_add]
      obtain ⟨c, hc⟩ := hres
      obtain ⟨t, ht⟩ := hu
      obtain ⟨hq, _⟩ := shell_oddpart hj hr
      have hqz : (2 : ℤ) ^ j * (((3 * r + 1) / 2 ^ j : ℕ) : ℤ) = 3 * (r : ℤ) + 1 := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hq.symm
      unfold alphaJ at hc
      refine wz_congr ⟨ξ * (r : ℤ) * t - c * (((3 * r + 1) / 2 ^ j : ℕ) : ℤ), ?_⟩
      linear_combination (-(((3 * r + 1) / 2 ^ j : ℕ) : ℤ)) * hc + (ξ * u) * hqz
        + (ξ * (r : ℤ)) * ht
    have h2 : wz k ((α : ℤ) * (((3 * r + 1) / 2 ^ j : ℕ) : ℤ))
        = w k ^ (α * sbMap k j r) := by
      rw [wz_period (k := k) (j := j) (by omega) hαj ((3 * r + 1) / 2 ^ j),
        show ((α : ℤ) * ((((3 * r + 1) / 2 ^ j) % 2 ^ (k - j) : ℕ) : ℤ))
            = ((α * (((3 * r + 1) / 2 ^ j) % 2 ^ (k - j)) : ℕ) : ℤ) by push_cast; ring,
        wz_natCast]
      rfl
    rw [h1, h2, mul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, shell_reindex hj hjk]

/-!
--------------------------------------------------------------------------------
## §5. R1 at the level of a character-basis entry
--------------------------------------------------------------------------------

`CharacterBasis.lower_block_entry_vanishes` proves that *a weighted sum of `Sodd` values over
the shell range vanishes* - a statement about a shape. §4 proves the masked character sum
**has** that shape. Composing them gives the entry itself.

The mask `1 ≤ v(r) ≤ b` is not cosmetic. For `b ≤ a` and `j > b`, `v₂(alpha_j) = b < j`, so
S4's dead band `[j, k-2]` is *missed* and the shell does not vanish - and the periodicity
prerequisite `2^j ∣ alpha_j` of §4 fails too, so the reduction to `Sodd` is not even
available. STEP4 §0 derives the mask from the Gauss-sum collapse; §6 below proves that
collapse, so the mask is earned rather than posited.
-/

/-- The masked source set: odd `r < 2^k` with `1 ≤ v₂(3r+1) ≤ b`. `odds_partition` says this
is all the odd residues except `r*` once `b = k-1`. -/
def maskedOdds (k b : ℕ) : Finset ℕ := (Icc 1 b).biUnion (shell k)

theorem shell_disjoint {k j j' : ℕ} (h : j ≠ j') : Disjoint (shell k j) (shell k j') := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  simp only [shell, mem_filter] at hr hr'
  exact h (by rw [← hr.2.2.2, hr'.2.2.2])

/-- A natural-number representative of `alpha_j` mod `2^k`. -/
def resJ (k : ℕ) (η ξ u : ℤ) (j : ℕ) : ℕ := (alphaJ η ξ u j % 2 ^ k).toNat

theorem resJ_spec (k : ℕ) (η ξ u : ℤ) (j : ℕ) :
    (2 : ℤ) ^ k ∣ ((resJ k η ξ u j : ℕ) : ℤ) - alphaJ η ξ u j := by
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  have hnn := Int.emod_nonneg (alphaJ η ξ u j) (ne_of_gt hpos)
  rw [resJ, Int.toNat_of_nonneg hnn]
  exact ⟨-(alphaJ η ξ u j / 2 ^ k), by rw [Int.emod_def]; ring⟩

/-- **R1, the character-basis entry.** For `b ≤ a` the masked entry
`hat(η,ξ) = ∑_{r odd, 1 ≤ v(r) ≤ b} w^{η·Syr(r) − ξ·r}` is exactly `0`.

This is `CharacterBasis.lower_block_entry_vanishes` with the shape supplied rather than
assumed. **It is still not `P_a U_clean P_b = 0`**: see the header, item 1. -/
theorem masked_entry_vanishes {k a b : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ')
    (hab : b ≤ a) (hbk : b + 2 ≤ k) (hu : (2 : ℤ) ^ k ∣ 3 * u - 1) :
    ∑ r ∈ maskedOdds k b, wz k (η * ((syracuse r : ℕ) : ℤ) - ξ * (r : ℤ)) = 0 := by
  rw [maskedOdds, Finset.sum_biUnion]
  · refine Finset.sum_eq_zero fun j hj => ?_
    rw [mem_Icc] at hj
    obtain ⟨hj1, hjb⟩ := hj
    have hjk : j + 1 ≤ k := by omega
    have hvj : (2 : ℤ) ^ j ∣ alphaJ η ξ u j :=
      dvd_trans (pow_dvd_pow 2 hjb)
        (valuation_lower (ξ' := ξ') hη hη' hξ hj1 hab).1
    rw [shell_character_sum hj1 hjk hu (resJ_spec k η ξ u j) hvj,
      shell_sum_vanishes_lower (a := a) (η' := η') (ξ' := ξ')
        hη hη' hξ hab hbk hj1 hjb (resJ_spec k η ξ u j), mul_zero]
  · intro x _ y _ hxy
    exact shell_disjoint hxy

/-!
--------------------------------------------------------------------------------
## §6. The Gauss collapse: `T_k` acting on a character
--------------------------------------------------------------------------------

### STATEMENT FIDELITY (`STEP4_BLOCK_FORMULA_FOUNDATION.md` §0, quoted verbatim)

> The inner geometric sum is `2^v` if `2^v | eta` (i.e. `v2(eta) = b >= v`) and `0` otherwise
> (`W^{2^v} = exp(2 pi i eta) = 1` always, so it is a clean indicator). Hence
> `(U chi_eta)(r) = [v <= b] w^{eta(3r+1)/2^v}     (v = v(r) < k)`.
> This is the masking `[v(r) <= b]` - it is the Gauss-sum annihilation of source frequencies
> coarser than the local valuation.

The derivation below does **not** go through the coset. It re-indexes the target sum back to
the lift window with `sum_fiberwise_of_maps_to` - which is the definition of `Tcount` read
backwards - and then applies `cu_syracuse_affine` pointwise. So the only CU input is the
affine identity, and the `2^v` / `2^{k-v}` direction never has to be chosen (see Orientation).
-/

/-- `w^{ηs}` depends only on `s mod 2^k`. -/
theorem w_pow_mod (k η s : ℕ) : w k ^ (η * (s % 2 ^ k)) = w k ^ (η * s) := by
  conv_rhs => rw [← Nat.div_add_mod s (2 ^ k)]
  rw [Nat.mul_add, pow_add, show η * (2 ^ k * (s / 2 ^ k)) = 2 ^ k * (η * (s / 2 ^ k)) by ring,
    pow_mul (w k) (2 ^ k) (η * (s / 2 ^ k)),
    (w_pow_eq_one_iff k (2 ^ k)).2 dvd_rfl, one_pow, one_mul]

/-- The target sum against `Tcount` is the lift-window sum. This is `Tcount`'s definition
read backwards; no arithmetic is involved. -/
theorem char_col_as_lift (k r η : ℕ) :
    ∑ u ∈ range (2 ^ k), (Tcount k u r : ℂ) * w k ^ (η * u)
      = ∑ m ∈ range (2 ^ k), w k ^ (η * syracuse (r + m * 2 ^ k)) := by
  have hmaps : ∀ m ∈ range (2 ^ k), syracuse (r + m * 2 ^ k) % 2 ^ k ∈ range (2 ^ k) :=
    fun m _ => mem_range.2 (Nat.mod_lt _ (Nat.two_pow_pos k))
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun m => w k ^ (η * (syracuse (r + m * 2 ^ k) % 2 ^ k)))
  have hstep : ∀ u ∈ range (2 ^ k),
      (Tcount k u r : ℂ) * w k ^ (η * u)
        = ∑ m ∈ (range (2 ^ k)).filter (fun m => syracuse (r + m * 2 ^ k) % 2 ^ k = u),
            w k ^ (η * (syracuse (r + m * 2 ^ k) % 2 ^ k)) := by
    intro u _
    have hcong : ∀ m ∈ (range (2 ^ k)).filter (fun m => syracuse (r + m * 2 ^ k) % 2 ^ k = u),
        w k ^ (η * (syracuse (r + m * 2 ^ k) % 2 ^ k)) = w k ^ (η * u) :=
      fun m hm => by rw [(mem_filter.1 hm).2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul, Tcount]
  rw [Finset.sum_congr rfl hstep, hfib]
  exact Finset.sum_congr rfl fun m _ => w_pow_mod k η _

/-- The exponent `η·3·2^{k-v}` is `≡ 0 mod 2^k` exactly when `2^v ∣ η`. -/
theorem ratio_one_iff {k v η : ℕ} (hv : v ≤ k) :
    w k ^ (η * 3 * 2 ^ (k - v)) = 1 ↔ 2 ^ v ∣ η := by
  rw [w_pow_eq_one_iff, two_pow_dvd_mul_two_pow k (k - v) (η * 3),
    show k - (k - v) = v by omega]
  constructor
  · intro h
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ (by norm_num)) h)
  · intro h
    exact Dvd.dvd.mul_right h 3

/-- **THE GAUSS COLLAPSE.** For a clean source `r` (`v := v₂(3r+1) < k`), the transfer
operator's column sum against the character `w^{η·}` collapses to a single phase, gated by
`2^v ∣ η`. Dividing by `2^k` (the normalisation in `Tk`) this is
`(U χ_η)(r) = [v ≤ v₂(η)] · w^{η·Syr(r)}`, i.e. STEP4 §0's masked-phase formula. -/
theorem syracuse_eq_quot {r : ℕ} (hr : r % 2 = 1) :
    syracuse r = (3 * r + 1) / 2 ^ v2 (3 * r + 1) := by
  unfold syracuse
  rw [if_neg (by omega)]

theorem gauss_collapse {k r : ℕ} (hr : r % 2 = 1) (hK : v2 (3 * r + 1) < k) (η : ℕ) :
    ∑ u ∈ range (2 ^ k), (Tcount k u r : ℂ) * w k ^ (η * u)
      = if 2 ^ v2 (3 * r + 1) ∣ η then ((2 ^ k : ℕ) : ℂ) * w k ^ (η * syracuse r) else 0 := by
  rw [char_col_as_lift k r η]
  have hstep : ∀ m ∈ range (2 ^ k),
      w k ^ (η * syracuse (r + m * 2 ^ k))
        = w k ^ (η * syracuse r) * (w k ^ (η * 3 * 2 ^ (k - v2 (3 * r + 1)))) ^ m := by
    intro m _
    rw [cu_syracuse_affine r m k hr hK, ← syracuse_eq_quot hr, Nat.mul_add,
      show η * (3 * m * 2 ^ (k - v2 (3 * r + 1)))
          = (η * 3 * 2 ^ (k - v2 (3 * r + 1))) * m by ring,
      pow_add, pow_mul (w k) (η * 3 * 2 ^ (k - v2 (3 * r + 1))) m]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  by_cases hcase : 2 ^ v2 (3 * r + 1) ∣ η
  · rw [if_pos hcase, (ratio_one_iff (le_of_lt hK)).2 hcase]
    simp [mul_comm]
  · rw [if_neg hcase]
    have hzero : ∑ m ∈ range (2 ^ k), (w k ^ (η * 3 * 2 ^ (k - v2 (3 * r + 1)))) ^ m = 0 := by
      refine (geomSum_eq_zero_iff (by positivity : (2 : ℕ) ^ k ≠ 0)).2 ⟨?_, ?_⟩
      · rw [← pow_mul, w_pow_eq_one_iff]
        exact ⟨η * 3 * 2 ^ (k - v2 (3 * r + 1)), by ring⟩
      · exact fun hc => hcase ((ratio_one_iff (le_of_lt hK)).1 hc)
    rw [hzero, mul_zero]

/-!
--------------------------------------------------------------------------------
## §6b. The join: the clean character-basis entry of `T_k` itself
--------------------------------------------------------------------------------

§5 is about a masked sum written by hand; §6 is about the operator. This section joins them:
`cleanEntry` is built from `TransferOperator.Tcount` and nothing else, and
`clean_entry_vanishes` says **that** entry is `0` for `b ≤ a`.

Two things this is, and one thing it is not.

* It **is** a statement about the operator defined in `TransferOperator.lean`: `Tcount` occurs
  in the statement, the mask does not. The `[v(r) ≤ b]` mask is *produced* by `gauss_collapse`
  rather than assumed - that is the whole point of §6.
* It **is** the sum over every clean source - `(Icc 1 (k-1)).biUnion (shell k)` is exactly the
  odd residues below `2^k` minus `r*`. But note the qualifier: that identification follows from
  `CountingLemmas.odds_partition` plus disjointness of the shells from `defectSet`, and
  **neither is invoked below**. The index set here is the shell union as written; the reading
  of it as "all odds but `r*`" is a corollary of a proved lemma, not itself proved here.
* It is **not** `P_a U_clean P_b = 0`. It is one entry of that block in the character basis,
  with the `1/N` of the `chiVec` normalisation dropped and the level projections `P_a`, `P_b`
  never mentioned. Going from "every entry vanishes" to "the operator vanishes" needs
  `CharacterBasis.chiBasis` and `P_apply`, which are not used anywhere in this file.
-/

/-- The clean character-basis entry of `T_k`, built from `Tcount` alone: the transpose action
`(U χ_η)(r) = 2^{-k} ∑_u Tcount(k,u,r)·w^{ηu}` paired against the conjugate character
`w^{-ξr}`, summed over every clean source `r`. -/
noncomputable def cleanEntry (k η : ℕ) (ξ : ℤ) : ℂ :=
  ∑ r ∈ (Icc 1 (k - 1)).biUnion (shell k),
    (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (Tcount k u r : ℂ) * w k ^ (η * u))
      * wz k (-(ξ * (r : ℤ)))

/-- The Gauss gate `2^j ∣ η` is exactly `j ≤ b` when `v₂(η) = b`. -/
theorem gate_iff {b j η : ℕ} {η' : ℤ} (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') :
    2 ^ j ∣ η ↔ j ≤ b := by
  constructor
  · intro h
    by_contra hc
    have hz : (2 : ℤ) ^ b * 2 ∣ 2 ^ b * η' := by
      rw [← pow_succ, ← hη]
      exact dvd_trans (pow_dvd_pow 2 (by omega)) (Int.natCast_dvd_natCast.2 h)
    have h2 : (2 : ℤ) ∣ η' :=
      (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ b ≠ 0)).1 hz
    obtain ⟨e, he⟩ := hη'
    obtain ⟨c, hcc⟩ := h2
    omega
  · intro h
    have hz : (2 : ℤ) ^ j ∣ (η : ℤ) := by
      rw [hη]; exact dvd_trans (pow_dvd_pow 2 h) ⟨η', rfl⟩
    exact_mod_cast hz

/-- **The join.** The clean entry of `T_k` *is* the masked sum of §5. The mask is derived. -/
theorem cleanEntry_eq_masked {k b η : ℕ} {η' : ℤ} (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η')
    (hbk : b + 1 ≤ k) (ξ : ℤ) :
    cleanEntry k η ξ
      = ∑ r ∈ maskedOdds k b, wz k ((η : ℤ) * ((syracuse r : ℕ) : ℤ) - ξ * (r : ℤ)) := by
  have hd1 : (↑(Icc 1 (k - 1)) : Set ℕ).PairwiseDisjoint (shell k) := by
    intro x _ y _ hxy; exact shell_disjoint hxy
  have hd2 : (↑(Icc 1 b) : Set ℕ).PairwiseDisjoint (shell k) := by
    intro x _ y _ hxy; exact shell_disjoint hxy
  rw [cleanEntry, Finset.sum_biUnion hd1, maskedOdds, Finset.sum_biUnion hd2]
  have hpow : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero k two_ne_zero
  -- every shell term is the masked phase, gated by `j ≤ b`
  have hshell : ∀ j ∈ Icc 1 (k - 1),
      (∑ r ∈ shell k j,
        (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (Tcount k u r : ℂ) * w k ^ (η * u))
          * wz k (-(ξ * (r : ℤ))))
        = if j ≤ b then
            ∑ r ∈ shell k j, wz k ((η : ℤ) * ((syracuse r : ℕ) : ℤ) - ξ * (r : ℤ)) else 0 := by
    intro j hj
    rw [mem_Icc] at hj
    have hterm : ∀ r ∈ shell k j,
        (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (Tcount k u r : ℂ) * w k ^ (η * u))
            * wz k (-(ξ * (r : ℤ)))
          = if j ≤ b then wz k ((η : ℤ) * ((syracuse r : ℕ) : ℤ) - ξ * (r : ℤ)) else 0 := by
      intro r hr
      have hrs : r ∈ shell k j := hr
      simp only [shell, mem_filter] at hr
      have hrodd : r % 2 = 1 := hr.2.2.1
      have hvj : v2 (3 * r + 1) = j := hr.2.2.2
      have hclean : v2 (3 * r + 1) < k := by omega
      rw [gauss_collapse hrodd hclean η, hvj]
      by_cases hcase : (2 : ℕ) ^ j ∣ η
      · rw [if_pos hcase, if_pos ((gate_iff hη hη').1 hcase)]
        rw [show (((2 ^ k : ℕ) : ℂ)) = (2 : ℂ) ^ k by push_cast; ring, ← mul_assoc,
          inv_mul_cancel₀ hpow, one_mul, ← wz_natCast, ← wz_add,
          show ((η * syracuse r : ℕ) : ℤ) + -(ξ * (r : ℤ))
              = (η : ℤ) * ((syracuse r : ℕ) : ℤ) - ξ * (r : ℤ) by push_cast; ring]
      · rw [if_neg hcase, if_neg (fun hc => hcase ((gate_iff hη hη').2 hc)), mul_zero, zero_mul]
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

/-- **The lower block, for the real operator, entrywise.** For `b ≤ a` the clean
character-basis entry of `T_k` is exactly `0`. Compare
`CharacterBasis.lower_block_entry_vanishes`, which is the same conclusion about a *shape*;
here the object is built from `TransferOperator.Tcount`. **Still not `P_a U_clean P_b = 0`** -
see the §6b preamble and the file header. -/
theorem clean_entry_vanishes {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ')
    (hab : b ≤ a) (hbk : b + 2 ≤ k) (hu : (2 : ℤ) ^ k ∣ 3 * u - 1) :
    cleanEntry k η ξ = 0 := by
  rw [cleanEntry_eq_masked hη hη' (by omega) ξ]
  exact masked_entry_vanishes (a := a) (η' := η') (ξ' := ξ') hη hη' hξ hab hbk hu

/-!
--------------------------------------------------------------------------------
## §7. Satisfiability and calibration (failure mode 3: vacuity)
--------------------------------------------------------------------------------

Every hypothesis block above is exhibited at a concrete point, and each `example` type-checks
only if the whole block is simultaneously satisfiable. The point is L8's:
`k = 6`, `a = 3`, `b = 2`, `η = 4`, `ξ = 8`; the inverse of `3` mod `2^6 = 64` is `43`
(`3·43 = 129 = 2·64 + 1`).
-/

theorem v2_four : v2 4 = 2 :=
  (v2_eq_iff_dvd (by norm_num)).2 ⟨by norm_num, by decide⟩

theorem syracuse_one : syracuse 1 = 1 := by
  rw [syracuse_eq_quot (by norm_num), show 3 * 1 + 1 = 4 from rfl, v2_four]
  norm_num

/-- `u = 43` really is `3⁻¹` mod `2^6`, and the point `(a,b) = (3,2)` really is lower. -/
theorem hyp_satisfiable_S1 :
    (2 : ℤ) ^ 6 ∣ 3 * (43 : ℤ) - 1 ∧ (2 : ℕ) ≤ 3 ∧ (2 : ℕ) + 2 ≤ 6 ∧
      (1 : ℕ) ∈ shell 6 2 ∧ syracuse 1 = 1 := by
  refine ⟨⟨2, by norm_num⟩, by omega, by omega, ?_, syracuse_one⟩
  simp only [shell, mem_filter, mem_range]
  exact ⟨by norm_num, by norm_num, by norm_num, by
    show v2 4 = 2
    exact v2_four⟩

/-- An instance of `masked_entry_vanishes` at that point: `b = 2 ≤ a = 3`, `k = 6`. This
type-checks only if every hypothesis of §5 is simultaneously satisfiable. -/
example :
    ∑ r ∈ maskedOdds 6 2, wz 6 ((4 : ℤ) * ((syracuse r : ℕ) : ℤ) - (8 : ℤ) * (r : ℤ)) = 0 :=
  masked_entry_vanishes (a := 3) (b := 2) (η' := 1) (ξ' := 1) (u := 43)
    (by norm_num) ⟨0, by ring⟩ (by norm_num) (by omega) (by omega) ⟨2, by norm_num⟩

/-- An instance of `shell_character_sum` at the same point, shell `j = 1`. -/
example :
    ∑ r ∈ shell 6 1, wz 6 ((4 : ℤ) * ((syracuse r : ℕ) : ℤ) - (8 : ℤ) * (r : ℤ))
      = wz 6 ((8 : ℤ) * 43) * Sodd 6 (resJ 6 4 8 43 1) (6 - 1) :=
  shell_character_sum (by omega) (by omega) ⟨2, by norm_num⟩ (resJ_spec 6 4 8 43 1)
    (by unfold alphaJ; exact ⟨-342, by norm_num⟩)

/-- An instance of the join `clean_entry_vanishes` at the same lower point: `k = 6`,
`b = 2 ≤ a = 3`, `η = 4`, `ξ = 8`. The object is `cleanEntry`, which mentions `Tcount` and no
mask - so this witnesses that the *derived* mask is satisfiable, not just the hand-written one. -/
example : cleanEntry 6 4 8 = 0 :=
  clean_entry_vanishes (a := 3) (b := 2) (η' := 1) (ξ' := 1) (u := 43)
    (by norm_num) ⟨0, by ring⟩ (by norm_num) (by omega) (by omega) ⟨2, by norm_num⟩

/-- An instance of `gauss_collapse`: `k = 4`, `r = 1`, `v₂(3·1+1) = 2 < 4`. -/
example (η : ℕ) :
    ∑ u ∈ range (2 ^ 4), (Tcount 4 u 1 : ℂ) * w 4 ^ (η * u)
      = if 2 ^ v2 (3 * 1 + 1) ∣ η then ((2 ^ 4 : ℕ) : ℂ) * w 4 ^ (η * syracuse 1) else 0 :=
  gauss_collapse (by norm_num) (by show v2 4 < 4; rw [v2_four]; omega) η

/-- The mask is a real restriction, not a no-op: `|maskedOdds k b| = ∑_{j=1}^{b} 2^{k-1-j}`,
which is `2^{k-1} − 1` only at `b = k−1` (all odds but `r*`) and strictly smaller below.
Recomputed decidably via `CountingLemmas.v2EqDec` (justified there by `v2_eq_iff_mod`). -/
def maskedCountEval (k b : ℕ) : ℕ :=
  ((List.range (2 ^ k)).filter
    (fun r => (List.range (b + 1)).any (fun j => 1 ≤ j && v2EqDec (3 * r + 1) j))).length

-- `k = 6`: shells 1..5 have sizes 16, 8, 4, 2, 1; the mask at `b = 2` keeps 24 of 31.
#guard maskedCountEval 6 2 = 24
#guard maskedCountEval 6 5 = 2 ^ 5 - 1
#guard maskedCountEval 8 2 = 96
#guard maskedCountEval 8 7 = 2 ^ 7 - 1

/-!
--------------------------------------------------------------------------------
## §8. Axiom audit
--------------------------------------------------------------------------------

Every exported declaration must use a SUBSET of `{propext, Classical.choice, Quot.sound}`.
Several use strictly fewer; that is expected and is not a violation.
-/

#print axioms wz_natCast
#print axioms wz_add
#print axioms wz_two_pow
#print axioms wz_congr
#print axioms wz_period
#print axioms Sodd_eq_oddResidues
#print axioms shell_reindex
#print axioms syracuse_on_shell
#print axioms phase_congr
#print axioms shell_character_sum
#print axioms shell_disjoint
#print axioms resJ_spec
#print axioms masked_entry_vanishes
#print axioms w_pow_mod
#print axioms char_col_as_lift
#print axioms ratio_one_iff
#print axioms gauss_collapse
#print axioms syracuse_eq_quot
#print axioms gate_iff
#print axioms cleanEntry_eq_masked
#print axioms clean_entry_vanishes
#print axioms v2_four
#print axioms syracuse_one
#print axioms hyp_satisfiable_S1

end BlockVanishing
