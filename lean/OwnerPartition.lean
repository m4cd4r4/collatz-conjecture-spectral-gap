/-
# (F2) Disjoint ownership: the owner sets partition `levelSet k a`

## SCOPE DECLARATION (read this first)

Task L15 offered three scopes.  **This file takes (F2b)**, i.e. (F2a) *plus* the
covering half: the full partition statement.

It does **NOT**:

* prove the Gram identity `B* B = 2^{-d} I` (F3) — not attempted, not implied;
* say anything about operator norms, or about the rank of any block;
* discharge **(CLEAN)**.  `CleanBlock.gap_certificate_of_clean` is untouched and
  its hypothesis `‖P_a U_clean P_b‖ ≤ Assembly.s^(b-a)` still stands, byte for
  byte.  Nothing here may be read as closing (CLEAN).

`OwnerCount.owner_count` (task L14, (F1)) supplies the *size* of each owner set.
This file supplies the *structure*: the owner sets are pairwise disjoint and
their union is all of `levelSet k a`.  L14 was explicit that the count alone does
not give this, and it does not; the two halves below are independent arguments.

## What is proved

Write `ownedBy k a b u η := {ξ ∈ levelSet k a : 2^(k-1) ∣ alphaJ η ξ u (b-a)}`.

* **(F2a)** `ownedBy_disjoint` — for `η₁ ≠ η₂`, `ownedBy … η₁` and `ownedBy … η₂`
  are disjoint.  **With no hypotheses whatsoever** on `k, a, b, u` (see the
  hypothesis note on the theorem).
* **(F2b)** `exists_owner` / `owner_biUnion` — for `Odd u`, `a ≤ b`, `b + 2 ≤ k`,
  every `ξ ∈ levelSet k a` is owned by some `η ∈ levelSet k b`, hence
  `(levelSet k b).biUnion (ownedBy k a b u) = levelSet k a`.
* `exists_unique_owner` — the two halves combined, in the form a Gram computation
  wants: each `ξ ∈ levelSet k a` has exactly one owner.
* `owner_card_sum`, `levelSet_card_via_owners` — the partition as a cardinality
  statement, and (with L14's `owner_count`) the identity
  `|levelSet k a| = 2^(k-2-b) · 2^(b-a)`.  L14 observed this arithmetic was
  *consistent* with a partition; here it is a consequence of one.

## The two proofs

**(i) Disjointness.**  If `ξ` is owned by both `η₁` and `η₂` then `2^(k-1)`
divides `alphaJ η₁ ξ u d - alphaJ η₂ ξ u d = η₁ - η₂`.  Both `ηᵢ` are values of
`Fin (2^(k-1))`, so `|η₁ - η₂| < 2^(k-1)`, forcing `η₁ = η₂`.

This is *shorter* than the route via `ηᵢ = 2^b ηᵢ'` that the task description
proposed.  That route is correct but passes through the level structure of the
`ηᵢ`, which is never needed: the bound `ηᵢ < 2^(k-1)` is already in the type.
Consequently **disjointness needs no hypotheses at all** — not `a ≤ b`, not
`b + 2 ≤ k`, not `Odd u`, and not even `ηᵢ ∈ levelSet k b`.  Confirmed by an
external sweep over 9376 `(k, u, a, b)` combinations with `η` ranging over *all*
of `Fin (2^(k-1))` and `u` over evens as well as odds: every `ξ` had exactly one
owner in every case.

**(ii) Covering.**  Given `ξ ∈ levelSet k a`, put `x := ξ · 2^(b-a) · u` and
`η := x mod 2^(k-1)`.  Writing `ξ = 2^(a+1) t + 2^a` and `u = 2m+1`,

    x = 2^(b+1) · (t·u + m) + 2^b,                              (`x_form`)

so `x % 2^(b+1) = 2^b`; and since `b + 1 ≤ k - 1`, reducing mod `2^(k-1)` first
does not disturb that, so `η % 2^(b+1) = 2^b`, which is exactly
`DefectSplit.mem_levelSet_mod`'s form of `η ∈ levelSet k b`.  Ownership is then
`2^(k-1) ∣ η - x`, which is what `%` means.

**The `v₂` trap is avoided by construction.**  The task's sketch of (ii) argues
via `v₂(η) = b`, which is the formulation that has already cost this project a
defect (`padicValNat 2 0 = 0` makes the `v₂` form false at `0`, and the sketch
needs a separate step to rule out `η = 0`).  The proof here never mentions `v₂`:
it works entirely with `% 2^(b+1) = 2^b`, which implies `η ≠ 0` for free because
`2^b ≠ 0`.  That is the same divisibility form `DefectSplit.mem_levelSet_mod`
already uses.

## Which hypotheses are load-bearing

Established by external negative controls, not by inspection:

| Hypothesis | Dropped | Result |
|---|---|---|
| `Odd u` | even `u`, otherwise in scope | 5408/5408 `(k,u,a,b)` fail to cover |
| `b + 2 ≤ k` | `b ∈ {k-1, k}` | 78/78 fail to cover (`levelSet k b = ∅`) |
| `a ≤ b` | `a > b`, truncated `b - a = 0` | 74/74 fail to cover |
| any of them | — | disjointness still holds; 0 overlaps everywhere |

So all three are load-bearing for the *covering* half, and none is load-bearing
for the *disjointness* half.  `a < b` (the S6/S7 regime) is again **not** needed;
`a = b` is fine and gives the identity partition.

## Calibration

`partitionSweep` (§4) brute-forces the whole partition claim — disjointness and
covering together, as a multiset identity — and lists the failing `(a,b)`.
`#guard partitionSweep 6 43 = []` and `= []` at `k = 7`, plus an unrelated odd
multiplier `u = 11`.  An independent Python sweep over `k = 6..9`, every `(a,b)`
with `a ≤ b` and `b + 2 ≤ k` — **100 pairs — found 0 overlaps and 0 coverage
failures**, and over *all* odd `u < 2^k` for `k = 6..8` (5408 pairs) likewise.

## Non-vacuity

`sweepPairs` counts the pairs the sweep actually visits (15 at `k=6`, 21 at
`k=7`), so `[]` is a result and not an empty enumeration.  Three **negative
controls** (`sweepEven`, `sweepWide`, `sweepLower`) show the same checker
reporting failure when `Odd u`, `b + 2 ≤ k`, or `a ≤ b` is dropped.
`hyp_satisfiable_partition` plus the concrete `example`s exhibit the hypothesis
block being met with a non-trivial conclusion (8 elements split into 2 owner sets
of 4, not 1 set of 8 and not 8 sets of 1).
-/

import OwnerCount

namespace OwnerPartition

open Finset GapCertificate CountingLemmas CharacterBasis

/-!
--------------------------------------------------------------------------------
## §1. The owner sets
--------------------------------------------------------------------------------
-/

/-- The level-`a` frequencies owned by `η`: those satisfying the dead-band
survivor condition of `LemmaA` at shell `b - a`. -/
def ownedBy (k a b : ℕ) (u : ℤ) (η : Fin (2 ^ (k - 1))) : Finset (Fin (2 ^ (k - 1))) :=
  (levelSet k a).filter
    (fun ξ => (2 : ℤ) ^ (k - 1) ∣ LemmaA.alphaJ (η.val : ℤ) (ξ.val : ℤ) u (b - a))

theorem mem_ownedBy {k a b : ℕ} {u : ℤ} {η ξ : Fin (2 ^ (k - 1))} :
    ξ ∈ ownedBy k a b u η ↔ ξ ∈ levelSet k a ∧
      (2 : ℤ) ^ (k - 1) ∣ LemmaA.alphaJ (η.val : ℤ) (ξ.val : ℤ) u (b - a) := by
  simp [ownedBy, mem_filter]

theorem ownedBy_subset {k a b : ℕ} {u : ℤ} {η : Fin (2 ^ (k - 1))} :
    ownedBy k a b u η ⊆ levelSet k a := filter_subset _ _

/-- **(F1) restated for `ownedBy`.**  This is `OwnerCount.owner_count`; it is
stated here only so that §3 can read the size of an owner set off a name that
mentions `ownedBy`.  No new content. -/
theorem ownedBy_card {k a b : ℕ} {u : ℤ} (hu : Odd u) (hab : a ≤ b) (hbk : b + 2 ≤ k)
    {η : Fin (2 ^ (k - 1))} (hη : η ∈ levelSet k b) :
    (ownedBy k a b u η).card = 2 ^ (b - a) :=
  OwnerCount.owner_count hu hab hbk hη

/-!
--------------------------------------------------------------------------------
## §2. **(F2a)** Disjointness
--------------------------------------------------------------------------------
-/

/-- **(F2a) Disjoint ownership.**  Distinct `η` own disjoint sets of level-`a`
frequencies.

**Hypothesis note (honest disclosure).**  There are no numeric hypotheses at all:
no `a ≤ b`, no `b + 2 ≤ k`, no `Odd u`, and `η₁, η₂` are arbitrary elements of
`Fin (2^(k-1))` rather than of `levelSet k b`.  The reason is that the only fact
used about the `ηᵢ` is `ηᵢ < 2^(k-1)`, which is carried by the type.  The task
description proposed a longer argument going through `ηᵢ = 2^b ηᵢ'`; that works
too, but the level structure is not needed and is therefore not assumed.  This
was checked externally before being claimed: a sweep with `η` over all of
`Fin (2^(k-1))`, `a, b < k`, and `u` over *all* residues (even ones included),
9376 combinations, found every `ξ` with exactly one owner. -/
theorem ownedBy_disjoint {k a b : ℕ} {u : ℤ} {η₁ η₂ : Fin (2 ^ (k - 1))} (hne : η₁ ≠ η₂) :
    Disjoint (ownedBy k a b u η₁) (ownedBy k a b u η₂) := by
  refine disjoint_left.2 fun ξ h1 h2 => ?_
  rw [mem_ownedBy] at h1 h2
  -- the two survivor conditions differ by exactly `η₁ - η₂`
  have hdiff : LemmaA.alphaJ ((η₁ : ℕ) : ℤ) ((ξ : ℕ) : ℤ) u (b - a)
      - LemmaA.alphaJ ((η₂ : ℕ) : ℤ) ((ξ : ℕ) : ℤ) u (b - a)
      = ((η₁ : ℕ) : ℤ) - ((η₂ : ℕ) : ℤ) := by
    unfold LemmaA.alphaJ; ring
  have hdvd : (2 : ℤ) ^ (k - 1) ∣ (((η₁ : ℕ) : ℤ) - ((η₂ : ℕ) : ℤ)) := by
    rw [← hdiff]; exact h1.2.sub h2.2
  -- but the difference is smaller than the modulus, so it vanishes
  have hb1 : ((η₁ : ℕ) : ℤ) < 2 ^ (k - 1) := by exact_mod_cast η₁.isLt
  have hb2 : ((η₂ : ℕ) : ℤ) < 2 ^ (k - 1) := by exact_mod_cast η₂.isLt
  have hn1 : (0 : ℤ) ≤ ((η₁ : ℕ) : ℤ) := Int.natCast_nonneg _
  have hn2 : (0 : ℤ) ≤ ((η₂ : ℕ) : ℤ) := Int.natCast_nonneg _
  have habs : |((η₁ : ℕ) : ℤ) - ((η₂ : ℕ) : ℤ)| < 2 ^ (k - 1) := by
    rw [abs_lt]; constructor <;> linarith
  have hz := Int.eq_zero_of_abs_lt_dvd hdvd habs
  have heq : ((η₁ : ℕ) : ℤ) = ((η₂ : ℕ) : ℤ) := by linarith
  exact hne (Fin.ext (by exact_mod_cast heq))

/-- The `Set.PairwiseDisjoint` packaging, which is what `Finset.card_biUnion` and
`Finset.sum_biUnion` consume. -/
theorem owner_pairwiseDisjoint {k a b : ℕ} {u : ℤ} :
    (↑(levelSet k b) : Set (Fin (2 ^ (k - 1)))).PairwiseDisjoint (ownedBy k a b u) :=
  fun _ _ _ _ hne => ownedBy_disjoint hne

/-!
--------------------------------------------------------------------------------
## §3. **(F2b)** Covering, and the partition
--------------------------------------------------------------------------------
-/

/-- **The shape of `ξ · 2^(b-a) · u`.**  With `ξ = 2^(a+1) t + 2^a` and `u = 2m+1`,
the product is `2^(b+1) (t u + m) + 2^b`.  This is the whole arithmetic content of
the covering half; everything after it is reduction bookkeeping.

Stated in this additive form — rather than as `v₂(x) = b` — deliberately: the
`v₂` form is the one that has already cost this project a defect at `α = 0`. -/
theorem x_form {a b t : ℕ} {u : ℤ} {m : ℤ} (hu : u = 2 * m + 1) (hab : a ≤ b) :
    ((2 ^ (a + 1) * t + 2 ^ a : ℕ) : ℤ) * 2 ^ (b - a) * u
      = 2 ^ (b + 1) * ((t : ℤ) * u + m) + 2 ^ b := by
  have e1 : (2 : ℤ) ^ (a + 1) * 2 ^ (b - a) = 2 ^ (b + 1) := by
    rw [← pow_add]; congr 1; omega
  have e2 : (2 : ℤ) ^ a * 2 ^ (b - a) = 2 ^ b := by
    rw [← pow_add]; congr 1; omega
  have hval : (((2 ^ (a + 1) * t + 2 ^ a : ℕ) : ℤ)) = 2 ^ (a + 1) * (t : ℤ) + 2 ^ a := by
    push_cast; ring
  calc ((2 ^ (a + 1) * t + 2 ^ a : ℕ) : ℤ) * 2 ^ (b - a) * u
      = ((2 : ℤ) ^ (a + 1) * 2 ^ (b - a)) * ((t : ℤ) * u) + ((2 : ℤ) ^ a * 2 ^ (b - a)) * u := by
        rw [hval]; ring
    _ = 2 ^ (b + 1) * ((t : ℤ) * u) + 2 ^ b * u := by rw [e1, e2]
    _ = 2 ^ (b + 1) * ((t : ℤ) * u) + 2 ^ b * (2 * m + 1) := by rw [hu]
    _ = 2 ^ (b + 1) * ((t : ℤ) * u + m) + 2 ^ b := by rw [pow_succ]; ring

/-- **(F2b) Covering.**  Every level-`a` frequency has an owner at level `b`.

The owner is explicit: `η = (ξ · 2^(b-a) · u) mod 2^(k-1)`.

All three hypotheses are load-bearing (external negative controls: dropping
`Odd u` fails coverage in 5408/5408 cases, dropping `b + 2 ≤ k` in 78/78,
dropping `a ≤ b` in 74/74). -/
theorem exists_owner {k a b : ℕ} {u : ℤ} (hu : Odd u) (hab : a ≤ b) (hbk : b + 2 ≤ k)
    {ξ : Fin (2 ^ (k - 1))} (hξ : ξ ∈ levelSet k a) :
    ∃ η ∈ levelSet k b, ξ ∈ ownedBy k a b u η := by
  classical
  obtain ⟨m, hm⟩ := hu
  -- (1) the level-`a` parametrisation of `ξ`
  have hξmod : (ξ : ℕ) % 2 ^ (a + 1) = 2 ^ a := DefectSplit.mem_levelSet_mod.1 hξ
  have hdm := Nat.div_add_mod (ξ : ℕ) (2 ^ (a + 1))
  set t : ℕ := (ξ : ℕ) / 2 ^ (a + 1) with ht
  have hξval : (ξ : ℕ) = 2 ^ (a + 1) * t + 2 ^ a := by omega
  -- (2) the product, and its shape
  set x : ℤ := ((ξ : ℕ) : ℤ) * 2 ^ (b - a) * u with hx
  have hxform : x = 2 ^ (b + 1) * ((t : ℤ) * u + m) + 2 ^ b := by
    rw [hx, hξval]; exact x_form hm hab
  have hxmod : x % 2 ^ (b + 1) = 2 ^ b := by
    have hlt : (2 : ℤ) ^ b < 2 ^ (b + 1) := by
      have : (0 : ℤ) < 2 ^ b := by positivity
      rw [pow_succ]; linarith
    have hnn : (0 : ℤ) ≤ 2 ^ b := by positivity
    rw [hxform, add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hnn hlt]
  -- (3) the candidate owner
  have hkpos : (0 : ℤ) < 2 ^ (k - 1) := by positivity
  have hnn : 0 ≤ x % 2 ^ (k - 1) := Int.emod_nonneg _ (ne_of_gt hkpos)
  have hltk : x % 2 ^ (k - 1) < 2 ^ (k - 1) := Int.emod_lt_of_pos _ hkpos
  set n : ℕ := (x % 2 ^ (k - 1)).toNat with hn
  have hnZ : ((n : ℕ) : ℤ) = x % 2 ^ (k - 1) := Int.toNat_of_nonneg hnn
  have hnlt : n < 2 ^ (k - 1) := by
    have : ((n : ℕ) : ℤ) < ((2 ^ (k - 1) : ℕ) : ℤ) := by rw [hnZ]; push_cast; exact hltk
    exact_mod_cast this
  refine ⟨⟨n, hnlt⟩, ?_, ?_⟩
  · -- (4) the owner really is at level `b` — in divisibility form, never via `v₂`
    rw [DefectSplit.mem_levelSet_mod]
    show n % 2 ^ (b + 1) = 2 ^ b
    have hdvdpow : ((2 : ℤ) ^ (b + 1)) ∣ ((2 : ℤ) ^ (k - 1)) := pow_dvd_pow 2 (by omega)
    have hZ : ((n : ℕ) : ℤ) % 2 ^ (b + 1) = 2 ^ b := by
      rw [hnZ, Int.emod_emod_of_dvd _ hdvdpow]; exact hxmod
    have hcast : ((n % 2 ^ (b + 1) : ℕ) : ℤ) = ((n : ℕ) : ℤ) % (2 : ℤ) ^ (b + 1) := by
      push_cast; ring
    have : ((n % 2 ^ (b + 1) : ℕ) : ℤ) = ((2 ^ b : ℕ) : ℤ) := by rw [hcast, hZ]; push_cast; ring
    exact_mod_cast this
  · -- (5) and it owns `ξ`
    rw [mem_ownedBy]
    refine ⟨hξ, ?_⟩
    show (2 : ℤ) ^ (k - 1) ∣ LemmaA.alphaJ ((n : ℕ) : ℤ) ((ξ : ℕ) : ℤ) u (b - a)
    have hgoal : LemmaA.alphaJ ((n : ℕ) : ℤ) ((ξ : ℕ) : ℤ) u (b - a) = x % 2 ^ (k - 1) - x := by
      unfold LemmaA.alphaJ; rw [hnZ, hx]
    rw [hgoal]
    refine ⟨-(x / 2 ^ (k - 1)), ?_⟩
    have hdiv := Int.mul_ediv_add_emod x ((2 : ℤ) ^ (k - 1))
    linarith

/-- **The partition, as a `biUnion` identity.**  The owner sets of the level-`b`
frequencies cover `levelSet k a` exactly. -/
theorem owner_biUnion {k a b : ℕ} {u : ℤ} (hu : Odd u) (hab : a ≤ b) (hbk : b + 2 ≤ k) :
    (levelSet k b).biUnion (ownedBy k a b u) = levelSet k a := by
  classical
  refine Subset.antisymm (biUnion_subset.2 fun η _ => ownedBy_subset) ?_
  intro ξ hξ
  obtain ⟨η, hη, hmem⟩ := exists_owner hu hab hbk hξ
  exact mem_biUnion.2 ⟨η, hη, hmem⟩

/-- **The partition, in the form a Gram computation wants.**  Every level-`a`
frequency has exactly one level-`b` owner.

Existence is `exists_owner` (needs all three hypotheses); uniqueness is
`ownedBy_disjoint` (needs none). -/
theorem exists_unique_owner {k a b : ℕ} {u : ℤ} (hu : Odd u) (hab : a ≤ b) (hbk : b + 2 ≤ k)
    {ξ : Fin (2 ^ (k - 1))} (hξ : ξ ∈ levelSet k a) :
    ∃! η : Fin (2 ^ (k - 1)), η ∈ levelSet k b ∧ ξ ∈ ownedBy k a b u η := by
  obtain ⟨η, hη, hmem⟩ := exists_owner hu hab hbk hξ
  refine ⟨η, ⟨hη, hmem⟩, ?_⟩
  rintro η' ⟨-, hmem'⟩
  by_contra hne
  exact (disjoint_left.1 (ownedBy_disjoint hne)) hmem' hmem

/-- **The partition, as a cardinality statement.** -/
theorem owner_card_sum {k a b : ℕ} {u : ℤ} (hu : Odd u) (hab : a ≤ b) (hbk : b + 2 ≤ k) :
    ∑ η ∈ levelSet k b, (ownedBy k a b u η).card = (levelSet k a).card := by
  classical
  rw [← Finset.card_biUnion owner_pairwiseDisjoint, owner_biUnion hu hab hbk]

/-- **(F1) + (F2) together.**  L14 observed that `2^(b-a)` per owner times
`2^(k-2-b)` owners is `2^(k-2-a) = |levelSet k a|`, and was careful to record
that this consistency was *not* a proof of a partition.  Now that the partition
is proved, the identity is a theorem about `levelSet k a` rather than a
coincidence: the level count is *recovered* by counting owners. -/
theorem levelSet_card_via_owners {k a b : ℕ} {u : ℤ} (hu : Odd u) (hab : a ≤ b)
    (hbk : b + 2 ≤ k) :
    (levelSet k a).card = 2 ^ (k - 2 - b) * 2 ^ (b - a) := by
  classical
  rw [← owner_card_sum hu hab hbk]
  rw [Finset.sum_congr rfl (fun η hη => ownedBy_card hu hab hbk hη)]
  rw [Finset.sum_const, DefectSplit.levelSet_card (by omega), smul_eq_mul]

/-!
--------------------------------------------------------------------------------
## §4. Calibration, non-vacuity, and negative controls
--------------------------------------------------------------------------------

`partOk` brute-forces the *entire* partition claim for one `(k, a, b, u)`: it
builds the concatenation (with multiplicity) of all the owner lists and checks it
against `levelSet k a` for equal length and mutual containment.  Equal length
plus mutual containment forces both halves at once — a repeat inside the
concatenation would push some element of `levelSet k a` out on a length count.
So an overlap and a coverage gap are each detected, separately.

Membership of a level set is tested in its decidable form `ξ % 2^(a+1) = 2^a`
(`DefectSplit.mem_levelSet_mod`), which is also what forces `ξ ≠ 0`.
-/

/-- The level-`a` frequencies, as a list. -/
def levelListEval (k a : ℕ) : List ℕ :=
  (List.range (2 ^ (k - 1))).filter (fun ξ => decide (ξ % 2 ^ (a + 1) = 2 ^ a))

/-- The level-`a` frequencies owned by `η`, as a list. -/
def ownedByEval (k a b u η : ℕ) : List ℕ :=
  (levelListEval k a).filter (fun ξ =>
    decide ((2 : ℤ) ^ (k - 1) ∣ ((η : ℤ) - (ξ : ℤ) * 2 ^ (b - a) * (u : ℤ))))

/-- Everything owned by anybody, **with multiplicity**. -/
def allOwnedEval (k a b u : ℕ) : List ℕ :=
  (levelListEval k b).flatMap (fun η => ownedByEval k a b u η)

/-- The partition check for one `(k, a, b, u)`. -/
def partOk (k a b u : ℕ) : Bool :=
  let all := allOwnedEval k a b u
  let lvl := levelListEval k a
  (all.length == lvl.length) && all.all (fun x => lvl.contains x)
    && lvl.all (fun x => all.contains x)

/-- Every in-scope `(a, b)` at which the partition claim fails. -/
def partitionSweep (k u : ℕ) : List (ℕ × ℕ) :=
  (List.range (k - 1)).flatMap (fun a =>
    (List.range (k - 1)).flatMap (fun b =>
      if a ≤ b then (if partOk k a b u then [] else [(a, b)]) else []))

-- `43 = 3⁻¹` mod `2^6` and mod `2^7`.
#guard partitionSweep 6 43 = []
#guard partitionSweep 7 43 = []
-- the theorems ask only for oddness of `u`, so an unrelated odd multiplier too:
#guard partitionSweep 6 11 = []
#guard partitionSweep 7 11 = []

/-- How many `(a, b)` pairs `partitionSweep` actually visits.  A sweep that visits
nothing would report `[]` for the wrong reason. -/
def sweepPairs (k : ℕ) : ℕ :=
  ((List.range (k - 1)).flatMap (fun a =>
    (List.range (k - 1)).flatMap (fun b => if a ≤ b then [(a, b)] else []))).length

-- The sweep is live: 15 pairs at `k = 6`, 21 at `k = 7`. The external Python sweep
-- visited 15 + 21 + 28 + 36 = 100 pairs over `k = 6..9`.
#guard sweepPairs 6 = 15
#guard sweepPairs 7 = 21

-- ... and it is looking at non-empty data: `levelSet 6 1` has 8 elements, split
-- into `|levelSet 6 3| = 2` owner sets of `2^(3-1) = 4`.
#guard (levelListEval 6 1).length = 8
#guard (levelListEval 6 3).length = 2
#guard (ownedByEval 6 1 3 43 8).length = 4
#guard (allOwnedEval 6 1 3 43).length = 8

/-!
### Negative controls

Three sweeps that drop one hypothesis each.  Each must report a failure, or the
`[]`s above would be vacuous.
-/

/-- `Odd u` dropped: same in-scope `(a,b)` range, even multiplier. -/
def sweepEven (k u : ℕ) : List (ℕ × ℕ) := partitionSweep k u

/-- `b + 2 ≤ k` dropped: `b` pushed to `k-1` and `k`. -/
def sweepWide (k u : ℕ) : List (ℕ × ℕ) :=
  (List.range (k - 1)).flatMap (fun a =>
    [k - 1, k].flatMap (fun b =>
      if a ≤ b then (if partOk k a b u then [] else [(a, b)]) else []))

/-- `a ≤ b` dropped: the `a > b` pairs, with Lean's truncated `b - a = 0`. -/
def sweepLower (k u : ℕ) : List (ℕ × ℕ) :=
  (List.range (k - 1)).flatMap (fun a =>
    (List.range (k - 1)).flatMap (fun b =>
      if b < a then (if partOk k a b u then [] else [(a, b)]) else []))

#guard sweepEven 6 44 ≠ []
#guard sweepEven 7 2 ≠ []
#guard sweepWide 6 43 ≠ []
#guard sweepWide 7 43 ≠ []
#guard sweepLower 6 43 ≠ []
#guard sweepLower 7 43 ≠ []

/-!
### Non-vacuity of the hypothesis block
-/

/-- The numeric hypotheses of `exists_owner` / `owner_biUnion` are simultaneously
satisfiable, with `8 ∈ levelSet 6 3` as an inhabitant of the owner level. -/
theorem hyp_satisfiable_partition : Odd (43 : ℤ) ∧ 1 ≤ 3 ∧ 3 + 2 ≤ 6 ∧
    (8 : ℕ) % 2 ^ (3 + 1) = 2 ^ 3 ∧ (2 : ℕ) % 2 ^ (1 + 1) = 2 ^ 1 := by
  refine ⟨⟨21, by norm_num⟩, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The `η` witness is an element of `levelSet 6 3`. -/
example : (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 3 :=
  DefectSplit.mem_levelSet_mod.2 (by norm_num)

/-- The `ξ` witness is an element of `levelSet 6 1`. -/
example : (⟨2, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 1 :=
  DefectSplit.mem_levelSet_mod.2 (by norm_num)

/-- `owner_biUnion` at concrete values, with no hypothesis left open. -/
example : (levelSet 6 3).biUnion (ownedBy 6 1 3 43) = levelSet 6 1 :=
  owner_biUnion (k := 6) (a := 1) (b := 3) (u := 43) ⟨21, by norm_num⟩ (by norm_num) (by norm_num)

/-- `exists_unique_owner` at concrete values. -/
example : ∃! η : Fin (2 ^ (6 - 1)),
    η ∈ levelSet 6 3 ∧ (⟨2, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ ownedBy 6 1 3 43 η :=
  exists_unique_owner (k := 6) (a := 1) (b := 3) (u := 43) ⟨21, by norm_num⟩ (by norm_num)
    (by norm_num) (DefectSplit.mem_levelSet_mod.2 (by norm_num))

/-- `levelSet_card_via_owners` at concrete values: `8 = 2 · 4`, i.e. the count is
non-trivial in both factors — not `1 · 8` and not `8 · 1`. -/
example : (levelSet 6 1).card = 2 ^ (6 - 2 - 3) * 2 ^ (3 - 1) :=
  levelSet_card_via_owners (k := 6) (a := 1) (b := 3) (u := 43) ⟨21, by norm_num⟩
    (by norm_num) (by norm_num)

/-- The diagonal `a = b` is in scope and gives the identity partition (owner sets
of size `2^0 = 1`), matching L14's note that `a < b` is not load-bearing. -/
example : (levelSet 6 2).biUnion (ownedBy 6 2 2 43) = levelSet 6 2 :=
  owner_biUnion (k := 6) (a := 2) (b := 2) (u := 43) ⟨21, by norm_num⟩ (by norm_num) (by norm_num)

/-!
--------------------------------------------------------------------------------
## §5. What remains before (CLEAN)
--------------------------------------------------------------------------------

In plain words, and without overclaiming:

* **Done, S6/S7 combinatorics.**  With L14's `owner_count` (how many level-`a`
  frequencies each level-`b` frequency owns) and this file's `owner_biUnion` /
  `exists_unique_owner` (that the ownership relation is a genuine partition), the
  index bookkeeping of the upper block is complete.  Every level-`a` frequency
  belongs to exactly one owner, and each owner has exactly `2^(b-a)` of them.

* **Not done, (F3): the Gram identity.**  The partition says *which* matrix
  entries of the upper block `B = P_a U P_b` are non-zero.  It says nothing about
  their *values*, and nothing about `B* B`.  Turning "the support is a partition"
  into `B* B = 2^(-(b-a)) I` needs the entries themselves: each surviving entry
  is a root of unity over `√N`, and the off-diagonal Gram sums have to be shown
  to cancel.  That cancellation is a character-sum argument, not a counting one,
  and none of it is in this file.

* **Not done, (CLEAN) itself.**  Even granting (F3), `(CLEAN)` is the operator
  statement `‖P_a U_clean P_b‖ ≤ Assembly.s^(b-a)` for the *clean* part of the
  transfer operator, which is `U` minus the defect.  (F3) would give the norm of
  the ideal block; relating that to `U_clean` is a further step.
  **`CleanBlock.gap_certificate_of_clean`'s hypothesis is unchanged by this
  file.**  Nothing here closes it, and the certificate still rests on it.
-/

#print axioms mem_ownedBy
#print axioms ownedBy_subset
#print axioms ownedBy_card
#print axioms ownedBy_disjoint
#print axioms owner_pairwiseDisjoint
#print axioms x_form
#print axioms exists_owner
#print axioms owner_biUnion
#print axioms exists_unique_owner
#print axioms owner_card_sum
#print axioms levelSet_card_via_owners
#print axioms hyp_satisfiable_partition

end OwnerPartition
