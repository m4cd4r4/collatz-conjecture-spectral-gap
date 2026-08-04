/-
# (F3) The Gram identity `B* B = 2^{-d} I`, and with it **(CLEAN)**

## SCOPE DECLARATION (read this first)

The brief offered three scopes.  **This file takes (G3)**: the Gram identity, the
operator norm of the clean upper block, and the discharge of **(CLEAN)** in
`CleanBlock.gap_certificate_of_clean`.

Concretely, and without overstating:

* `gram_upper` — **(F3)**, `∑_{ξ ∈ levelSet k a} conj B[ξ,η] · B[ξ,η'] = [η = η'] · 2^{-d}`,
  which is `B* B = 2^{-d} I` written entrywise;
* `clean_bound` — `‖cleanBlockCLM k a b‖ ≤ Assembly.s^(b-a)` for `a < b`, i.e. **(CLEAN)**
  itself, as a theorem;
* `gap_certificate_unconditional` — `CleanBlock.gap_certificate_of_clean` with its hypothesis
  **eliminated, not replaced**.  Every eigenvalue of the concretely defined `Tend k` other
  than `1` has `‖μ‖ ≤ envelope Assembly.s 3 < 0.853554`, for every `k ≥ 3`, with no
  undischarged hypothesis anywhere in the chain.

**What this does NOT do.**  It says nothing about Collatz cycles, and nothing here is
evidence about `3x+1` that is not equally evidence about `3x-1`: `3` enters only through
`three_inv_rstar`, and every arithmetic step below uses of `u = -r*` nothing but `Odd u`.
`Assembly.lean`'s standing gate 1 is unchanged.  It also does not claim `gc ≠ 0`.

--------------------------------------------------------------------------------
## §0. The route, and why it is not the route the previous task predicted
--------------------------------------------------------------------------------

Task L15 estimated F3 at "several times L14+L15 combined", because *"the off-diagonal
entries require showing a sum of roots of unity over a coset vanishes, and none of the
existing machinery does that"*.

**That estimate rested on a false premise, and the premise is false in the direction that
makes F3 smaller.**  The off-diagonal Gram entry does not vanish by character-sum
cancellation.  It vanishes because for a fixed `ξ` of level `a` there is exactly **one**
`η` of level `b` with `B[ξ,η] ≠ 0` — so in `∑_ξ conj B[ξ,η] · B[ξ,η']` with `η ≠ η'`, every
single term already has a zero factor.  That is `OwnerPartition.ownedBy_disjoint`, which
task L15 itself proved, and it is used verbatim in `gram_upper` below.  No cancellation
lemma is needed and none is proved here.

The support statement — `B[ξ,η] ≠ 0` **iff** `ξ ∈ ownedBy k a b u η` — is
`Bent_eq_zero_of_not_owned` + `norm_Bent_of_owned` in §5, and it was checked numerically
before it was proved (§1, gate 6).

Consequently this file is assembly, not discovery.  The one genuinely new ingredient is §4:
the *upper*-regime entry theorem, which no file in the development had (`CleanBlock` §6
item 1 names its absence).  Everything after §5 is bookkeeping over theorems that already
existed.

**One structural caveat, stated up front so §6 is not read as more than it is.**  The named
(F3) deliverable `gram_upper` and the operator bound `norm_sq_clean_block` are **siblings,
not a chain**: both are derived from §5's two support theorems plus L14's count and L15's
partition, and the certificate does *not* route through `gram_upper`.  Deleting `gram_upper`
would leave (CLEAN) and the certificate standing.  It is stated because it is the theorem
the brief asked for and because it is the invariant form of the same content — not because
anything downstream consumes it.  §9 repeats this.

--------------------------------------------------------------------------------
## §1. Numerical calibration — run BEFORE any proving, from `TransferOperator.Tcount`
--------------------------------------------------------------------------------

Rebuilt from scratch in Python out of `Tcount`'s own definition (`syracuse(r + m·2^k) mod
2^k` over the lift window), target-first `T[u,r]`, `U = Tᵀ`, the **row** `idx (rstar k)`
zeroed, `chiVec[ξ][s] = w^{ξ·(2s+1)}/√N`, and Mathlib's conjugate-first inner product.  No
corpus script was read.  Scripts live in the session scratchpad, not in either repo.

`B[ξ,η] := ⟪χ_ξ, U_clean χ_η⟫`, `d := b − a`, `N := 2^{k−1}`, `u := −r*`.

| gate | quantity | k=4 | k=6 | k=8 |
|---|---|---|---|---|
| 1 | `max ‖B*B − 2^{−d} I‖` over every `a < b` | `2.8e-16` | `3.6e-15` | `7.1e-15` |
| 2 | `max ‖ \|hat\| − 2^{k−d−1} ‖`, `hat = N·B` | `1.3e-15` | `6.4e-14` | `4.7e-13` |
| 3 | `max ‖ ‖P_a U_clean P_b‖ − 2^{−d/2} ‖` | `4.4e-16` | `5.0e-15` | `1.0e-14` |
| 4 | owner-count mismatches (`= 2^d`) | 0 | 0 | 0 |
| 5 | partition failures (disjoint **and** covering) | 0 | 0 | 0 |
| 6 | **`B[ξ,η] ≠ 0` XOR `ξ ∈ ownedBy η`** | 0 | 0 | 0 |

`k = 4, 5, 7` likewise; 55 `(a,b)` pairs in all.  Gate 6 is the one this file adds to the
brief's list: it is the exact bridge from L14/L15's combinatorics to the entries, and it is
what makes §0's claim about the off-diagonal a measurement rather than an assertion.
`idx (rstar 6) = 10`, agreeing with `OperatorBlock.defect_index_six`, so the calibrated
object and the Lean object are the same object.

Gates 1 and 3 are **equalities**, so no slack is recoverable anywhere below; only `≤` is
used, exactly as `CleanBlock` §6 warns.

--------------------------------------------------------------------------------
## §2. Orientation (unchanged, and load-bearing)
--------------------------------------------------------------------------------

Target-first `T[u,r]`, `U = Tᵀ`, `U_clean` zeroes the **row** `idx (rstar k)`.
`alphaJ η ξ u j = η − ξ·2^j·u` has `η` the level-`b` **source** frequency and `ξ` the
level-`a` **target** frequency, matching `OwnerPartition.ownedBy k a b u η ⊆ levelSet k a`
and `BlockVanishing.cleanEntry k η ξ`.  Mutations M1, M8 and M10 in §8 are three independent
shots at this.

Sorry-free, no `native_decide`.  Mutation table §8, axiom audit §10.
-/

import OwnerPartition
import CleanBlock

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GramIdentity

open Finset GapCertificate LemmaA CountingLemmas CollisionBound TransferOperator
open CharacterBasis BlockVanishing OperatorBlock DefectSplit ManifestInstance
open OwnerPartition OwnerCount CleanBlock

/-!
--------------------------------------------------------------------------------
## §3. The odd unit `u = −r*`
--------------------------------------------------------------------------------

Both hypothesis families in this file want the same `u`: `shell_character_sum` wants an
inverse of `3` mod `2^k`, and `survivor_dead_band` / `owner_count` want an **odd** integer.
`OperatorBlock.three_inv_rstar` supplies the first for `u = −r*`; `CollisionBound.rstar_odd`
supplies the second.  Nothing else about `u` is used anywhere below — which is precisely the
sign-blindness the standing gate records.
-/

/-- The concrete inverse of `3` mod `2^k` used by `OperatorBlock.inner_block_zero`, named so
that the same one can be threaded through the owner combinatorics. -/
def uinv (k : ℕ) : ℤ := -(rstar k : ℤ)

/-- `u = −r*` is odd — the only property the counting lemmas need. -/
theorem uinv_odd {k : ℕ} (hk : 1 ≤ k) : Odd (uinv k) := by
  have h := rstar_odd hk
  refine ⟨-((rstar k / 2 : ℕ) : ℤ) - 1, ?_⟩
  have hr : rstar k = 2 * (rstar k / 2) + 1 := by omega
  rw [uinv]
  calc -((rstar k : ℕ) : ℤ) = -((2 * (rstar k / 2) + 1 : ℕ) : ℤ) := by rw [← hr]
    _ = 2 * (-((rstar k / 2 : ℕ) : ℤ) - 1) + 1 := by push_cast; ring

/-- `u = −r*` inverts `3` mod `2^k` — the only property the character sums need. -/
theorem uinv_spec {k : ℕ} (hk : 1 ≤ k) : (2 : ℤ) ^ k ∣ 3 * uinv k - 1 :=
  three_inv_rstar hk

/-!
--------------------------------------------------------------------------------
## §4. The upper-regime entry theorem
--------------------------------------------------------------------------------

`CleanBlock` §6 item 1: *"No `a < b` analogue of `BlockVanishing.masked_entry_vanishes`
exists."*  This section is that analogue.

The shape is the same as the lower-regime one and the ingredients are all present; the only
difference is which shell survives.  For `b ≤ a` **every** shell is inside S4's dead band and
the entry is `0`.  For `a < b` exactly one shell, `j = d`, can escape, and it escapes exactly
at the two sharp points `alpha_d ∈ {0, 2^{k−1}}` — where S4's FULL branch supplies the
modulus `2^{k−d−1}`.
-/

/-- **`v₂(alpha_j) ≥ j` for every shell in range**, in the upper regime.  The three rows of
`LemmaA`'s valuation table, joined: `j < d` gives `v₂ = a+j ≥ j`, `j > d` gives `v₂ = b ≥ j`,
and `j = d` gives `v₂ ≥ b ≥ d`.  This is the periodicity prerequisite of
`shell_character_sum`, and without it the shell sum does not reduce to a `Sodd` at all. -/
theorem shell_dvd_upper {k a b j : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (hab : a < b) (hbk : b + 2 ≤ k) (hj1 : 1 ≤ j) (hjb : j ≤ b) :
    (2 : ℤ) ^ j ∣ alphaJ η ξ u j := by
  by_cases hjd : j = b - a
  · subst hjd
    exact dvd_trans (pow_dvd_pow 2 (by omega)) (valuation_at hη hξ (by omega))
  · exact (survivor_dead_band hη hη' hξ hξ' hu hab hbk hj1 hjb hjd).1

/-- **The upper-regime clean entry collapses onto the single shell `j = d`.**

Every other shell in `[1, b]` contributes exactly `0` by `LemmaA.shell_sum_vanishes`
(S5 + S4); the surviving one is `shell_character_sum` at `j = d`.  Note `d ∈ [1, b]` needs
both `a < b` (for `1 ≤ d`) and nothing else (`d = b - a ≤ b` always). -/
theorem upper_entry_eq {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k) :
    cleanEntry k η ξ
      = wz k (ξ * u) * Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) := by
  rw [cleanEntry_eq_masked hη hη' (by omega) ξ, maskedOdds,
    Finset.sum_biUnion (fun x _ y _ hxy => shell_disjoint hxy)]
  refine (Finset.sum_eq_single_of_mem (b - a) (mem_Icc.2 ⟨by omega, by omega⟩) ?_).trans ?_
  · -- every shell other than `j = d` is inside the dead band
    intro j hj hjd
    rw [mem_Icc] at hj
    rw [shell_character_sum hj.1 (by omega) huinv (resJ_spec k (η : ℤ) ξ u j)
        (shell_dvd_upper hη hη' hξ hξ' hu hab hbk hj.1 hj.2),
      shell_sum_vanishes hη hη' hξ hξ' hu hab hbk hj.1 hj.2 hjd
        (resJ_spec k (η : ℤ) ξ u j),
      mul_zero]
  · -- the surviving shell
    exact shell_character_sum (by omega) (by omega) huinv
      (resJ_spec k (η : ℤ) ξ u (b - a))
      (shell_dvd_upper (j := b - a) hη hη' hξ hξ' hu hab hbk (by omega) (by omega))

/-- `‖w^n‖ = 1` at integer exponents. -/
theorem norm_wz (k : ℕ) (n : ℤ) : ‖wz k n‖ = 1 := by
  rw [wz, norm_zpow, norm_w, one_zpow]

/-- Divisibility by `2^t`, `t ≤ k`, transfers between `alpha_j` and its residue
representative.  Stated in **divisibility** form throughout — the `v₂` form is the one that
has already cost this project a defect at `α = 0`. -/
theorem resJ_dvd_iff {k t : ℕ} (ht : t ≤ k) (η ξ u : ℤ) (j : ℕ) :
    (2 : ℕ) ^ t ∣ resJ k η ξ u j ↔ (2 : ℤ) ^ t ∣ alphaJ η ξ u j := by
  rw [← Int.natCast_dvd_natCast]
  push_cast
  exact dvd_congr_mod ht (resJ_spec k η ξ u j)

/-- **Off the support: the entry is exactly `0`.**  If the surviving shell misses the two
sharp points, S4's dead band swallows it too and nothing is left. -/
theorem upper_entry_eq_zero {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k)
    (hno : ¬ (2 : ℤ) ^ (k - 1) ∣ alphaJ (η : ℤ) ξ u (b - a)) :
    cleanEntry k η ξ = 0 := by
  rw [upper_entry_eq hη hη' hξ hξ' hu huinv hab hbk]
  have hz : Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) = 0 := by
    refine (Sodd_eq_zero_iff k _ _ (by omega)).2 ⟨?_, ?_⟩
    · rw [show k - (k - (b - a)) = b - a by omega]
      exact (resJ_dvd_iff (by omega) _ _ _ _).2 (survivor_at_d hη hξ hab hbk)
    · exact fun hc => hno ((resJ_dvd_iff (by omega) _ _ _ _).1 hc)
  rw [hz, mul_zero]

/-- **On the support: the entry has modulus exactly `2^{k−d−1}`.**  S4's FULL branch,
`LemmaA.norm_Sodd_full`, at `m = k − d`. -/
theorem norm_upper_entry {k a b η : ℕ} {ξ η' ξ' u : ℤ}
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k)
    (how : (2 : ℤ) ^ (k - 1) ∣ alphaJ (η : ℤ) ξ u (b - a)) :
    ‖cleanEntry k η ξ‖ = (2 : ℝ) ^ (k - (b - a) - 1) := by
  rw [upper_entry_eq hη hη' hξ hξ' hu huinv hab hbk, norm_mul, norm_wz, one_mul,
    norm_Sodd_full k _ _ (by omega) ((resJ_dvd_iff (by omega) _ _ _ _).2 how)]
  push_cast
  ring

/-!
--------------------------------------------------------------------------------
## §5. The block entries in the character basis
--------------------------------------------------------------------------------

`OperatorBlock.inner_chiVec_Uend` divides `cleanEntry` by `N = 2^{k−1}`, so §4's `2^{k−d−1}`
becomes `2^{−d}`.  `OperatorBlock.level_factor` turns membership of a `levelSet` into the
dyadic factorisation §4 demands, exactly as `inner_block_zero` does in the lower regime.

Both statements are indexed by `OwnerPartition.ownedBy`, so §6 can quote L14's count and
L15's partition without re-deriving the predicate.
-/

/-- `B[ξ,η] := ⟪χ_ξ, U_clean χ_η⟫`, the entry of the level block in the character basis. -/
noncomputable def Bent (k : ℕ) (ξ η : Fin (2 ^ (k - 1))) : ℂ :=
  (@inner ℂ _ _ (chiVec k ξ) (Uend k (chiVec k η)) : ℂ)

/-- Membership of a level set, in the factored form §4 consumes. -/
theorem level_split {k a : ℕ} {ξ : Fin (2 ^ (k - 1))} (hξ : ξ ∈ levelSet k a) :
    ∃ m : ℕ, ((ξ : ℕ) : ℤ) = 2 ^ a * (m : ℤ) ∧ Odd ((m : ℤ)) :=
  level_factor (mem_levelSet.1 hξ).1 (mem_levelSet.1 hξ).2

/-- A level-`b` frequency forces `b + 2 ≤ k` (`CharacterBasis.level_lt`). -/
theorem level_bound {k b : ℕ} (hk : 2 ≤ k) {η : Fin (2 ^ (k - 1))} (hη : η ∈ levelSet k b) :
    b + 2 ≤ k := by
  have h := level_lt (k := k) (ξ := η) hk (mem_levelSet.1 hη).1
  rw [(mem_levelSet.1 hη).2] at h
  omega

/-- **Off the support the block entry vanishes.**  `ξ ∉ ownedBy … η` is exactly the failure
of the sharp-point condition, so §4 applies. -/
theorem Bent_eq_zero_of_not_owned {k a b : ℕ} (hk : 2 ≤ k) (hab : a < b)
    {ξ η : Fin (2 ^ (k - 1))} (hξ : ξ ∈ levelSet k a) (hη : η ∈ levelSet k b)
    (hno : ξ ∉ ownedBy k a b (uinv k) η) :
    Bent k ξ η = 0 := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨m, hm, hmo⟩ := level_split hη
  obtain ⟨n, hn, hnodd⟩ := level_split hξ
  have hdvd : ¬ (2 : ℤ) ^ (k - 1) ∣
      alphaJ ((η : ℕ) : ℤ) ((ξ : ℕ) : ℤ) (uinv k) (b - a) := by
    intro hc
    exact hno (mem_ownedBy.2 ⟨hξ, hc⟩)
  rw [Bent, inner_chiVec_Uend hk1 ξ η,
    upper_entry_eq_zero (a := a) (b := b) hm hmo hn hnodd (uinv_odd hk1) (uinv_spec hk1)
      hab (level_bound hk hη) hdvd,
    mul_zero]

/-- **On the support the block entry has modulus exactly `2^{−d}`.**  This is the number the
Gram diagonal squares, and it is `1/2^d`, not `1/√(2^d)` and not `2^{−d}/√(dim)`: the block
has full column rank `2^{k−2−b}`, so no Frobenius shortcut is available (`CleanBlock` §6). -/
theorem norm_Bent_of_owned {k a b : ℕ} (hk : 2 ≤ k) (hab : a < b)
    {ξ η : Fin (2 ^ (k - 1))} (hη : η ∈ levelSet k b)
    (how : ξ ∈ ownedBy k a b (uinv k) η) :
    ‖Bent k ξ η‖ = (1 / 2 : ℝ) ^ (b - a) := by
  have hk1 : 1 ≤ k := by omega
  have hξ : ξ ∈ levelSet k a := ownedBy_subset how
  have hbk : b + 2 ≤ k := level_bound hk hη
  obtain ⟨m, hm, hmo⟩ := level_split hη
  obtain ⟨n, hn, hnodd⟩ := level_split hξ
  have hd : (2 : ℤ) ^ (k - 1) ∣ alphaJ ((η : ℕ) : ℤ) ((ξ : ℕ) : ℤ) (uinv k) (b - a) :=
    (mem_ownedBy.1 how).2
  have hN : ((2 ^ (k - 1) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Bent, inner_chiVec_Uend hk1 ξ η, norm_mul, norm_inv, Complex.norm_natCast,
    norm_upper_entry (a := a) (b := b) hm hmo hn hnodd (uinv_odd hk1) (uinv_spec hk1)
      hab hbk hd]
  -- `2^{k-d-1} / 2^{k-1} = (1/2)^d`
  have hsplit : ((2 ^ (k - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k - (b - a) - 1) * 2 ^ (b - a) := by
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, one_div, inv_pow]
  field_simp

/-!
--------------------------------------------------------------------------------
## §6. **(F3)** The Gram identity `B* B = 2^{−d} I`
--------------------------------------------------------------------------------

Both halves are one line of mathematics each, given §5:

* **off-diagonal** — for `η ≠ η'` every summand has a zero factor, because a `ξ` owned by
  `η` is owned by nobody else (`OwnerPartition.ownedBy_disjoint`).  This is §0's point: it is
  disjoint support, not a root-of-unity cancellation.
* **diagonal** — the sum restricts to `ownedBy … η`, on which every summand is `(2^{−d})²`,
  and there are `2^d` of them (`OwnerCount.owner_count`).  `2^d · 4^{−d} = 2^{−d}`.
-/

/-- **(F3) THE GRAM IDENTITY.**  `B* B = 2^{−d} · I`, written entrywise over the level-`b`
frequencies.  `d = b − a`.

The two inputs are theorems, not hypotheses: the owner count is L14
(`OwnerCount.owner_count`, via `ownedBy_card`) and the disjointness is L15
(`OwnerPartition.ownedBy_disjoint`).  The entry modulus is §5. -/
theorem gram_upper {k a b : ℕ} (hk : 2 ≤ k) (hab : a < b)
    {η η' : Fin (2 ^ (k - 1))} (hη : η ∈ levelSet k b) (hη' : η' ∈ levelSet k b) :
    ∑ ξ ∈ levelSet k a, (starRingEnd ℂ) (Bent k ξ η) * Bent k ξ η'
      = if η = η' then (((1 / 2 : ℝ) ^ (b - a) : ℝ) : ℂ) else 0 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hbk : b + 2 ≤ k := level_bound hk hη
  by_cases hne : η = η'
  · subst hne
    rw [if_pos rfl]
    -- restrict to the owner set: off it, the entry is zero
    have hrestrict : ∑ ξ ∈ levelSet k a, (starRingEnd ℂ) (Bent k ξ η) * Bent k ξ η
        = ∑ ξ ∈ ownedBy k a b (uinv k) η, (starRingEnd ℂ) (Bent k ξ η) * Bent k ξ η := by
      refine (Finset.sum_subset ownedBy_subset ?_).symm
      intro ξ hξ hno
      rw [Bent_eq_zero_of_not_owned hk hab hξ hη hno, map_zero, mul_zero]
    have hval : ∀ ξ ∈ ownedBy k a b (uinv k) η,
        (starRingEnd ℂ) (Bent k ξ η) * Bent k ξ η
          = (((1 / 4 : ℝ) ^ (b - a) : ℝ) : ℂ) := by
      intro ξ hξ
      rw [RCLike.conj_mul, norm_Bent_of_owned hk hab hη hξ]
      norm_cast
      rw [← pow_mul, mul_comm (b - a) 2, pow_mul]
      norm_num
    rw [hrestrict, Finset.sum_congr rfl hval, Finset.sum_const,
      ownedBy_card (uinv_odd hk1) (le_of_lt hab) hbk hη, nsmul_eq_mul]
    push_cast
    rw [← mul_pow]
    norm_num
  · rw [if_neg hne]
    refine Finset.sum_eq_zero fun ξ hξ => ?_
    by_cases how : ξ ∈ ownedBy k a b (uinv k) η
    · -- owned by `η`, hence — by DISJOINTNESS — not by `η'`
      have hno : ξ ∉ ownedBy k a b (uinv k) η' :=
        fun hc => (disjoint_left.1 (ownedBy_disjoint (Ne.symm hne))) hc how
      rw [Bent_eq_zero_of_not_owned hk hab hξ hη' hno, mul_zero]
    · rw [Bent_eq_zero_of_not_owned hk hab hξ hη how, map_zero, zero_mul]

/-!
--------------------------------------------------------------------------------
## §7. **(CLEAN)**: the operator norm, and the unconditional certificate
--------------------------------------------------------------------------------

`CleanBlock` §6 warns twice about this passage, and both warnings are honoured:

* **no `LinearMap.adjoint`.**  L12 exhausted a 400k `synthInstance` budget and then a 1M
  `isDefEq` budget on the adjoint over a `Submodule` of `EuclideanSpace`.  Nothing below
  forms an adjoint.  `‖A x‖²` is expanded directly in the character basis with
  `ManifestInstance.norm_sq_P`, and the Gram structure enters through the *support*
  statement of §5 rather than through an operator identity.
* **no rank-one / Frobenius shortcut.**  The bound comes out as `2^{−d}` exactly, with no
  dimension factor, because the owner count `2^d` cancels against `(2^{−d})²` and the
  partition makes each source coefficient appear exactly once.
-/

/-- `x ≤ y` from `x² ≤ y²` for nonnegative reals. -/
theorem le_of_sq_le_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  nlinarith

/-- **The clean upper block's norm, squared, exactly.**

`‖P_a U_clean P_b x‖² = 2^{−d} ‖P_b x‖²`.  Equality, not an estimate — §1 gate 3 measures
the same thing to `1.0e-14`.

The proof is the Gram computation with the sums reorganised by the owner partition: reindex
`levelSet k a` as `⋃_{η ∈ levelSet k b} ownedBy η` (L15), collapse each inner coefficient sum
to its single surviving term (L15's disjointness again), take the modulus (§5), and count
(L14). -/
theorem norm_sq_clean_block {k a b : ℕ} (hk : 2 ≤ k) (hab : a < b) (hbk : b + 2 ≤ k)
    (x : Fsp k) :
    ‖P k a (Uend k (P k b x))‖ ^ 2 = (1 / 2 : ℝ) ^ (b - a) * ‖P k b x‖ ^ 2 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hu : Odd (uinv k) := uinv_odd hk1
  -- (1) the coefficients of the image, in the character basis
  have hcoef : ∀ ξ : Fin (2 ^ (k - 1)),
      (@inner ℂ _ _ (chiVec k ξ) (Uend k (P k b x)) : ℂ)
        = ∑ η ∈ levelSet k b,
            (@inner ℂ _ _ (chiVec k η) x : ℂ) * Bent k ξ η := by
    intro ξ
    rw [P_apply, map_sum, inner_sum]
    exact Finset.sum_congr rfl fun η _ => by rw [map_smul, inner_smul_right, Bent]
  rw [norm_sq_P hk1 a, norm_sq_P hk1 b,
    ← owner_biUnion (k := k) (a := a) (b := b) (u := uinv k) hu (le_of_lt hab) hbk,
    Finset.sum_biUnion owner_pairwiseDisjoint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun η hη => ?_
  -- (2) on the owner set of `η`, only the `η` term of the coefficient sum survives
  have hterm : ∀ ξ ∈ ownedBy k a b (uinv k) η,
      ‖(@inner ℂ _ _ (chiVec k ξ) (Uend k (P k b x)) : ℂ)‖ ^ 2
        = (1 / 4 : ℝ) ^ (b - a) * ‖(@inner ℂ _ _ (chiVec k η) x : ℂ)‖ ^ 2 := by
    intro ξ hξ
    have hξa : ξ ∈ levelSet k a := ownedBy_subset hξ
    have hsingle : (@inner ℂ _ _ (chiVec k ξ) (Uend k (P k b x)) : ℂ)
        = (@inner ℂ _ _ (chiVec k η) x : ℂ) * Bent k ξ η := by
      rw [hcoef ξ]
      refine Finset.sum_eq_single_of_mem η hη ?_
      intro η' hη' hne
      have hno : ξ ∉ ownedBy k a b (uinv k) η' :=
        fun hc => (disjoint_left.1 (ownedBy_disjoint hne)) hc hξ
      rw [Bent_eq_zero_of_not_owned hk hab hξa hη' hno, mul_zero]
    rw [hsingle, norm_mul, mul_pow, norm_Bent_of_owned hk hab hη hξ, ← pow_mul,
      show (b - a) * 2 = 2 * (b - a) by ring, pow_mul]
    norm_num
    ring
  -- (3) count them
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    ownedBy_card hu (le_of_lt hab) hbk hη, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- **(CLEAN), pointwise.** -/
theorem norm_clean_block_le {k a b : ℕ} (hk : 2 ≤ k) (hab : a < b) (hbk : b + 2 ≤ k)
    (x : Fsp k) :
    ‖P k a (Uend k (P k b x))‖ ≤ Assembly.s ^ (b - a) * ‖x‖ := by
  have hk1 : 1 ≤ k := by omega
  have hsq := norm_sq_clean_block hk hab hbk x
  have hs : (Assembly.s ^ (b - a)) ^ 2 = (1 / 2 : ℝ) ^ (b - a) := by
    rw [← pow_mul, mul_comm, pow_mul, Assembly.s_sq]
  have hPb : ‖P k b x‖ ≤ ‖x‖ := norm_P_le hk1 b x
  have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (b - a) := by positivity
  refine le_of_sq_le_sq (norm_nonneg _)
    (mul_nonneg (pow_nonneg Assembly.s_pos.le _) (norm_nonneg _)) ?_
  rw [hsq, mul_pow, hs]
  exact mul_le_mul_of_nonneg_left
    (by nlinarith [norm_nonneg (P k b x), norm_nonneg x]) hpos

/-- **(CLEAN) ITSELF.**  The hypothesis of `CleanBlock.gap_certificate_of_clean`, as a
theorem.  Compare `CleanBlock.lean` §5, which states it as `hclean` and says explicitly
"it is a hypothesis". -/
theorem clean_bound {k : ℕ} (hk : 3 ≤ k) (a b : Fin (k - 1)) (hab : (a : ℕ) < (b : ℕ)) :
    ‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg Assembly.s_pos.le _) fun x => ?_
  rw [cleanBlockCLM_apply]
  have hb := b.isLt
  exact norm_clean_block_le (two_le hk) hab (by omega) x

/-- **THE CERTIFICATE, UNCONDITIONAL.**

Every eigenvalue of the concretely defined Syracuse transfer operator `Tend k` other than
`1` has modulus at most `envelope Assembly.s 3 = 2^{−3/2} + 2^{−1}`, uniformly in `k ≥ 3`.

Compare `CleanBlock.gap_certificate_of_clean`, which is the same conclusion carrying
`hclean`.  **Here that hypothesis is eliminated, not replaced**: the hypothesis binder is
gone from the statement, and `#print axioms` below shows nothing took its place. -/
theorem gap_certificate_unconditional {k : ℕ} (hk : 3 ≤ k)
    {μ : ℂ} (hμ : μ ≠ 1) {x : Fsp k} (hx0 : x ≠ 0) (hx : Tend k x = μ • x) :
    ‖μ‖ ≤ envelope Assembly.s 3 :=
  gap_certificate_of_clean hk (fun a b hab => clean_bound hk a b hab) hμ hx0 hx

/-- The same with the numeral. -/
theorem gap_certificate_unconditional_numeral {k : ℕ} (hk : 3 ≤ k)
    {μ : ℂ} (hμ : μ ≠ 1) {x : Fsp k} (hx0 : x ≠ 0) (hx : Tend k x = μ • x) :
    ‖μ‖ < 0.853554 :=
  gap_certificate_of_clean_numeral hk (fun a b hab => clean_bound hk a b hab) hμ hx0 hx

/-- **`hQupper` closed.**  `ManifestInstance.facts_of_hQupper`'s hypothesis, now derived.
Recorded separately because `CleanBlock` §6 says in terms that `hQupper` is OPEN; this is
the statement that changes that. -/
theorem hQupper_holds {k : ℕ} (hk : 3 ≤ k) :
    ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      Qmat k a b ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ))
        + Assembly.s ^ ((a : ℕ) + 1) * Assembly.levelVec (gcVec (two_le hk)) (b : ℕ) :=
  hQupper_of_clean hk (fun a b hab => clean_bound hk a b hab)

/-!
--------------------------------------------------------------------------------
## §8. Non-vacuity, satisfiability, and the mutation table
--------------------------------------------------------------------------------

### Why the statements are not vacuous

The index sets are inhabited at `k = 6, a = 1, b = 3`: `levelSet 6 1` has 8 elements,
`levelSet 6 3` has 2, and the owner sets have 4 each (`OwnerPartition` §4's `#guard`s,
reused rather than restated).  `uinv 6 = −21 ≡ 43 (mod 64)`, so the owner relation this file
threads is the *same* relation those `#guard`s measured at `u = 43` — the two differ by
`ξ·2^d·64`, which `2^{k−1} = 32` divides.  `uinv_congr_43` below proves that, so the
identification is a theorem rather than a remark.

The conclusions are non-trivial numbers, not `0` or `1`: `(1/2)^(b−a)` at `(1,3)` is `1/4`,
and the certificate's bound is strictly between `0` and `1`.
-/

/-- `uinv 6 = −21`, and it agrees with the `u = 43` of `OwnerCount` / `OwnerPartition`'s
`#guard`s modulo `2^{k−1} = 32` after scaling — so the owner relation proved here is the one
those sweeps measured.  (`43 − (−21) = 64`, and `2^{k−1} ∣ ξ·2^d·64` for every `ξ, d`.) -/
theorem uinv_congr_43 : uinv 6 = -21 ∧ ((43 : ℤ) - uinv 6) = 2 ^ 6 := by
  constructor
  · rfl
  · rfl

/-- The hypothesis block of §5-§7 is simultaneously satisfiable at `k = 6, a = 1, b = 3`,
in the `a < b` regime (CLEAN) is about. -/
theorem hyp_satisfiable_gram : 2 ≤ 6 ∧ 3 ≤ 6 ∧ (1 : ℕ) < 3 ∧ 3 + 2 ≤ 6 ∧ Odd (uinv 6) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, uinv_odd (by norm_num)⟩

/-- The two level sets in that instance are inhabited, so neither `P` is the zero
projection and `gram_upper` is not a statement about an empty sum. -/
example : (⟨2, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 1 :=
  mem_levelSet_mod.2 (by norm_num)

example : (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 3 :=
  mem_levelSet_mod.2 (by norm_num)

/-- **The Gram identity at concrete indices**, with no hypothesis left open. -/
example :
    ∑ ξ ∈ levelSet 6 1, (starRingEnd ℂ) (Bent 6 ξ ⟨8, by norm_num⟩)
        * Bent 6 ξ ⟨8, by norm_num⟩
      = (((1 / 2 : ℝ) ^ (3 - 1) : ℝ) : ℂ) := by
  have h := gram_upper (k := 6) (a := 1) (b := 3) (by norm_num) (by norm_num)
    (mem_levelSet_mod.2 (by norm_num) : (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 3)
    (mem_levelSet_mod.2 (by norm_num) : (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 3)
  rwa [if_pos rfl] at h

/-- The value that identity asserts is a genuine number strictly between `0` and `1`
(`1/4`), not `0` and not `1`. -/
example : (0 : ℝ) < (1 / 2 : ℝ) ^ (3 - 1) ∧ (1 / 2 : ℝ) ^ (3 - 1) = 1 / 4 := by
  norm_num

/-- **(CLEAN) at concrete indices.** -/
example : ‖cleanBlockCLM 6 1 3‖ ≤ Assembly.s ^ (3 - 1) :=
  clean_bound (k := 6) (by norm_num) ⟨1, by norm_num⟩ ⟨3, by norm_num⟩ (by norm_num)

/-- **The unconditional certificate at a concrete `k`** — every hypothesis discharged
except the eigenvalue data itself. -/
example {μ : ℂ} (hμ : μ ≠ 1) {x : Fsp 6} (hx0 : x ≠ 0) (hx : Tend 6 x = μ • x) :
    ‖μ‖ < 0.853554 :=
  gap_certificate_unconditional_numeral (by norm_num) hμ hx0 hx

/-!
### Mutation tests (failure mode 1: a theorem a tactic closes on its own)

Fourteen single-token mutations were applied to the load-bearing statements and the build was run
on each.  **All fourteen failed to compile.**  The build was restored and re-run green afterwards.

| # | mutation | result |
|---|---|---|
| M1 | `upper_entry_eq`: surviving shell index, `resJ … (b-a)` → `resJ … (a-b)` | fails |
| M2 | `upper_entry_eq`: `Sodd k (resJ … (b-a)) (k - (b-a))` → `… (k - (b-a) - 1)` (the width) | fails |
| M3 | `norm_upper_entry`: `2 ^ (k - (b-a) - 1)` → `2 ^ (k - (b-a))` (the FULL-branch modulus) | fails |
| M4 | `shell_dvd_upper`: conclusion `2^j ∣ alphaJ … j` → `2^(j+1) ∣ alphaJ … j` | fails |
| M5 | `norm_Bent_of_owned`: `(1/2)^(b-a)` → `(1/2)^(b-a+1)` | fails |
| M6 | `gram_upper`: off-diagonal branch `0` → `((1/2:ℝ)^(b-a) : ℂ)` (kill the disjointness) | fails |
| M7 | `gram_upper`: diagonal `(1/2)^(b-a)` → `(1/4)^(b-a)` (drop the owner count) | fails |
| M8 | `norm_sq_clean_block`: `‖P k b x‖` → `‖P k a x‖` (the orientation trap) | fails |
| M9 | `norm_sq_clean_block`: `(1/2)^(b-a)` → `(1/2)^(b-a) / 2` | fails |
| M10 | `clean_bound`: hypothesis `(a:ℕ) < (b:ℕ)` → `(b:ℕ) < (a:ℕ)` (the regime) | fails |
| M11 | `norm_cleanBlockCLM_eq`: `s^(b-a)` → `s^(b-a+1)` (§11) | fails |
| M12 | `norm_cleanBlockCLM_apply_chiVec`: `s^(b-a)` → `s^(b-a)/2` (§11) | fails |
| M13 | `P_chiVec_self`: conclusion `= chiVec k η` → `= 0` (§11) | fails |
| M14 | `levelSet_nonempty_nat`: `b + 2 ≤ k` → `b + 1 ≤ k` (the truncated level range) | fails |

M1, M8 and M10 are three independent shots at the orientation trap that has already cost
this project a defect.  M6 is the one that would matter most if it passed: it is the check
that the *disjointness* is genuinely load-bearing in the Gram identity rather than
decoration — which is exactly the claim §0 makes about L15's estimate.

--------------------------------------------------------------------------------
## §9. What is now closed, and what is NOT
--------------------------------------------------------------------------------

**Closed.**  `CleanBlock.gap_certificate_of_clean`'s hypothesis `hclean` is a theorem
(`clean_bound`), so `gap_certificate_unconditional` carries no hypothesis but `3 ≤ k` and the
eigenvalue data.  `ManifestInstance.facts_of_hQupper`'s `hQupper` is likewise a theorem
(`hQupper_holds`).  The Lean chain from `TransferOperator.Tcount` to `‖μ‖ < 0.853554` is
complete and machine-checked.

**A limit on what `gram_upper` earns.**  Repeating §0's caveat because it is exactly the
kind of thing this project has shipped wrong before: `gram_upper` is **not** on the
certificate's critical path.  `norm_sq_clean_block` proves `‖P_a U_clean P_b x‖²` directly
from the same two support theorems of §5, without quoting `gram_upper`.  So the honest
description is "(F3) is proved, and (CLEAN) is proved, from a shared base" — **not** "(F3)
was proved and (CLEAN) followed from it".  Anyone auditing the chain should trace
`clean_bound → norm_clean_block_le → norm_sq_clean_block → norm_Bent_of_owned /
Bent_eq_zero_of_not_owned → upper_entry_eq`, in which `gram_upper` never appears.

**NOT closed, and not touched by this file:**

* **`gc ≠ 0`.**  L12 declined to assert it and nothing here changes that.  It is not needed
  by the certificate, which is why the chain closes without it.
* **Anything about Collatz cycles.**  `Assembly.lean`'s standing gate 1 is unchanged and this
  file strengthens the reason for it: every construction above is available verbatim for the
  `3x−1` operator, because the only property of `u = 3^{-1}` used anywhere is `Odd u`.  The
  `3x−1` operator has real cycles and passes this identical certificate
  (`CYCLE_CLAIM_REFUTED.md`).  **The certificate being unconditional does not make it
  evidence about `3x+1` specifically.**  That limit is structural, and closing (CLEAN) does
  not move it.
* **The lower-regime norm.**  `OperatorBlock.P_Uclean_P_eq_zero` already gives `= 0` there;
  nothing here is needed and nothing here is added.
* **Sharpness beyond `≤`.**  §1 gate 3 measures the bound as an *equality*, and
  `gram_upper` proves the Gram identity as an equality, but `clean_bound` is stated as `≤`
  because that is what (CLEAN) is.  The equality of the *operator norm* is not stated: it
  would need the reverse inequality, i.e. an explicit near-maximiser, which is not built.

--------------------------------------------------------------------------------
## §10. Axiom audit
--------------------------------------------------------------------------------

Every exported declaration must use a SUBSET of `{propext, Classical.choice, Quot.sound}`.
Several use strictly fewer; that is expected and is not a violation.
-/

#print axioms uinv_odd
#print axioms uinv_spec
#print axioms shell_dvd_upper
#print axioms upper_entry_eq
#print axioms norm_wz
#print axioms resJ_dvd_iff
#print axioms upper_entry_eq_zero
#print axioms norm_upper_entry
#print axioms level_split
#print axioms level_bound
#print axioms Bent_eq_zero_of_not_owned
#print axioms norm_Bent_of_owned
#print axioms gram_upper
#print axioms le_of_sq_le_sq
#print axioms norm_sq_clean_block
#print axioms norm_clean_block_le
#print axioms clean_bound
#print axioms gap_certificate_unconditional
#print axioms gap_certificate_unconditional_numeral
#print axioms hQupper_holds
#print axioms uinv_congr_43
#print axioms hyp_satisfiable_gram

/-!
--------------------------------------------------------------------------------
## §11. Sharpness: the bound is an EQUALITY
--------------------------------------------------------------------------------

`clean_bound` gives `‖P_a U_clean P_b‖ ≤ s^d`, which is all (CLEAN) needs. §1 gate 3
*measures* the same quantity as an equality to `1.0e-14`, and `CleanBlock` §6 records that
the bound is sharp — but as a measurement, i.e. **DATA** sitting beside a **PROVEN** claim.

This section closes that gap. No new mathematics is required: `norm_sq_clean_block` is
already stated as an **equality**, so the reverse inequality needs only a witness vector,
and a level-`b` character is one.

That upgrade matters beyond tidiness. The 2025-26 literature now attaches at least four
inequivalent meanings to "a spectral gap for the Collatz transfer operator", and two of them
carry headline numbers near `0.85` that mean opposite things. A development that can say
*exactly* what its block norms are, rather than bounding them, is the one that can be
compared against the others without ambiguity.
-/

/-- A character is a unit vector. -/
theorem norm_chiVec {k : ℕ} (hk : 1 ≤ k) (η : Fin (2 ^ (k - 1))) : ‖chiVec k η‖ = 1 :=
  (chiVec_orthonormal hk).1 η

/-- A level-`b` character is fixed by `P_b`. -/
theorem P_chiVec_self {k : ℕ} (hk : 1 ≤ k) {b : ℕ} {η : Fin (2 ^ (k - 1))}
    (hη : η ∈ levelSet k b) : P k b (chiVec k η) = chiVec k η := by
  classical
  have hon := chiVec_orthonormal hk
  rw [P_apply, Finset.sum_eq_single η]
  · rw [orthonormal_iff_ite.1 hon η η, if_pos rfl, one_smul]
  · intro ξ _ hne
    rw [orthonormal_iff_ite.1 hon ξ η, if_neg hne, zero_smul]
  · intro hc; exact absurd hη hc

/-- Every level in range is inhabited, so §11's witness exists.

`ManifestInstance.levelSet_nonempty` is the same fact indexed by `Fin (k-1)`; this file's
indices are plain naturals carrying `b + 2 ≤ k` directly, so the hypothesis shape differs and
the two are stated separately rather than one derived from the other.  Named apart because
`ManifestInstance` is opened here and an unqualified clash would be unreadable. -/
theorem levelSet_nonempty_nat {k b : ℕ} (hbk : b + 2 ≤ k) : (levelSet k b).Nonempty := by
  rw [← Finset.card_pos, DefectSplit.levelSet_card hbk]
  positivity

/-- **(CLEAN) with the `Fin` wrapper removed**, so §11 can pair it with the lower bound. -/
theorem norm_cleanBlockCLM_le {k a b : ℕ} (hk : 2 ≤ k) (hab : a < b) (hbk : b + 2 ≤ k) :
    ‖cleanBlockCLM k a b‖ ≤ Assembly.s ^ (b - a) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg Assembly.s_pos.le _) fun x => ?_
  rw [cleanBlockCLM_apply]
  exact norm_clean_block_le hk hab hbk x

/-- **The block attains its bound at a single character.**  This is where the equality comes
from: `norm_sq_clean_block` is an identity, and `P_b` fixes `χ_η` for `η` of level `b`, so the
`‖P_b x‖` on its right-hand side is exactly `1`. -/
theorem norm_cleanBlockCLM_apply_chiVec {k a b : ℕ} (hk : 2 ≤ k) (hab : a < b) (hbk : b + 2 ≤ k)
    {η : Fin (2 ^ (k - 1))} (hη : η ∈ levelSet k b) :
    ‖cleanBlockCLM k a b (chiVec k η)‖ = Assembly.s ^ (b - a) := by
  have hk1 : 1 ≤ k := by omega
  have hfix : P k b (chiVec k η) = chiVec k η := P_chiVec_self hk1 hη
  have hsq := norm_sq_clean_block hk hab hbk (chiVec k η)
  rw [hfix, norm_chiVec hk1] at hsq
  have hs : (Assembly.s ^ (b - a)) ^ 2 = (1 / 2 : ℝ) ^ (b - a) := by
    rw [← pow_mul, mul_comm, pow_mul, Assembly.s_sq]
  refine DefectSplit.sq_eq_of_nonneg (norm_nonneg _) (pow_nonneg Assembly.s_pos.le _) ?_
  rw [hs, cleanBlockCLM_apply, hfix]
  simpa using hsq

/-- **SHARPNESS.**  `‖P_a U_clean P_b‖ = Assembly.s^(b-a)` exactly, for every `a < b` in
range — not merely `≤`.

So the certificate's clean factor is `2^{-(b-a)/2}` **on the nose**, and no route through this
block can recover any constant. `CleanBlock` §6 stated this as a numerical observation; here
it is a theorem. -/
theorem norm_cleanBlockCLM_eq {k a b : ℕ} (hk : 2 ≤ k) (hab : a < b) (hbk : b + 2 ≤ k) :
    ‖cleanBlockCLM k a b‖ = Assembly.s ^ (b - a) := by
  obtain ⟨η, hη⟩ := levelSet_nonempty_nat hbk
  refine le_antisymm (norm_cleanBlockCLM_le hk hab hbk) ?_
  have hle := (cleanBlockCLM k a b).le_opNorm (chiVec k η)
  rw [norm_cleanBlockCLM_apply_chiVec hk hab hbk hη, norm_chiVec (by omega : 1 ≤ k),
    mul_one] at hle
  exact hle

#print axioms norm_chiVec
#print axioms P_chiVec_self
#print axioms levelSet_nonempty_nat
#print axioms norm_cleanBlockCLM_le
#print axioms norm_cleanBlockCLM_apply_chiVec
#print axioms norm_cleanBlockCLM_eq

end GramIdentity
