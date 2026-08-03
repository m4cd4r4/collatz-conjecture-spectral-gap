/-
# `P_a U_clean P_b = 0`: the lower block, as an operator identity

Task L10. `BlockVanishing.lean` (L9) reached R1 **entrywise** and closed by naming exactly
what was left:

> `P_a U_clean P_b = 0` is NOT proved as an operator identity. [...] `U_clean` is never
> packaged as a matrix or a `Module.End` (the defect row `r*` is *identified* by
> `defect_col_eq_cf` but never removed from an operator); `cleanEntry` drops the `1/N` of
> `chiVec`'s normalisation and never mentions `P_a`, `P_b`, so it is an unnormalised bilinear
> pairing rather than a block entry; and the implication "every entry in an orthonormal basis
> vanishes ⇒ the operator vanishes" is not applied - `CharacterBasis.chiBasis` and `P_apply`
> are not used anywhere in this file.

This file does those three things, in that order.

## SCOPE DECISION - read this before reading anything else

Three things are proved here, for all `k`:

* `Uclean`, `Uend` (§1) - `U_clean` **as an operator**: the matrix `(TkC k)ᵀ` with the row
  `idx (rstar k)` zeroed, and its `Matrix.toEuclideanLin` endomorphism of
  `EuclideanSpace ℂ (Fin (2^(k-1)))`. Which row to zero is fixed by
  `TransferOperator.defect_col_eq_cf`: the defect is the `r*` **column** of `T_k`, hence the
  `r*` **row** of `U = T_kᵀ`. See §0.1 - zeroing the other index is a live, measured error.
* `inner_chiVec_Uend` (§4) - **the normalisation**, `⟪χ_ξ, U_clean χ_η⟫ = (1/N)·cleanEntry`.
  This is the statement L9 could not make: it turns L9's unnormalised pairing into a genuine
  matrix element of the operator in the orthonormal basis `CharacterBasis.chiBasis`. Its two
  halves are the index bookkeeping of §2 (`Fin (2^(k-1))` ↔ odd residues, and the clean
  sources ↔ `oddResidues k` minus `r*`) and the even-target vanishing of §3.
* `P_Uclean_P_eq_zero` (§6) - **`P_a U_clean P_b = 0` for `a ≥ b`, as an operator identity**,
  for every `x`, plus `P_Uclean_P_comp` in `∘ₗ` form.

  A draft of this header called that *"the development's first operator-level theorem"*. **That
  is false and is withdrawn.** `TransferOperator.colStoch_concrete` (`1ᵀ ∘ₗ T = 1ᵀ`) is an
  operator identity and predates this file, as are `CharacterBasis.P_idem`, `P_orthogonal`,
  `P_selfadjoint` and `P_resolution`. What is new here is narrower and should be stated
  narrowly: it is the first theorem in which the **level projections and the transfer operator
  appear together** - every earlier result is about one or the other, or about a scalar entry.

## What is NOT discharged (do not soften this - it is the same list L7, L8, L9 all carried)

**`Assembly.LemmaAFacts.hQupper` and `hQlower` both remain OPEN _as of this file_. This file
closes 0 of the 2 residue fields.** (STATUS 2026-08-03: both since closed - `hQlower` at L12,
`hQupper` at F3.) In plain words:

1. **`Q[a,b] = ‖P_a U P_b‖₂` is still not defined anywhere in this development, and no
   operator norm is bounded anywhere.** `P_Uclean_P_eq_zero` says a block is the zero
   operator; `hQlower` asserts a *numerical bound* `Q[a,b] ≤ s^{a+1}·v_b` on the norm of the
   **full** `U`, not the clean part. Zero is of course ≤ any bound - but only once the
   defect's contribution is added back, and that is item 2.
2. **The defect is still not decomposed.** `U = U_clean + D` with `D` the rank-one row
   `e_{r*}⊗c*` is not stated here; §1 *removes* the row rather than splitting it off, and
   nothing below proves `U = Uclean + D`, computes `‖P_a D P_b‖`, or proves the foundation
   `‖P_a e_{r*}‖ = 2^{-(a+1)/2}` (R3) that `hQlower`'s `s^{a+1}` comes from. So this file
   bounds nothing about the operator `hQlower` is actually about.
3. **`hQupper` is untouched.** The `a < b` half needs the isometry `B*B = 2^{-d}I` and its
   S6/S7 owner-counting (HALFSHIFT §4), which is not formalised anywhere in this development.
   **STALE 2026-08-03:** the owner-counting is `OwnerCount.owner_count` (L14) and
   `OwnerPartition.owner_biUnion` (L15); the isometry is `GramIdentity.gram_upper` (F3).
   Note `LemmaA.survivor_dead_band` has hypothesis `a < b` and is therefore not the lemma
   used below - the `a ≥ b` regime runs through `CharacterBasis.survivor_dead_band_lower`,
   which L8 proved for that regime specifically.

So: L10 closes the three gaps L9 named - `U_clean` is an operator, the pairing is normalised,
and the entrywise vanishing is discharged into an operator identity. It closes neither residue
field.

**The one sentence to be careful with.** It is tempting to write *"`hQlower` is now a norm
question about the defect rather than a structure question about the clean part"*. That is
true only **conditionally on a decomposition this file does not prove**: it needs
`U = U_clean + D` as a stated, proved identity before `P_a U P_b = P_a D P_b` follows from
§6, and item 2 above records that no such identity exists anywhere in this development. Until
it does, the honest form is the weaker one: *if* `U` splits as `U_clean + D`, then §6 removes
the `U_clean` term from the `a ≥ b` blocks and leaves a bound on `P_a D P_b`. Writing the
unconditional version would be failure mode 4 (a claim whose stated justification does not
support it), which this track has shipped twice.

## §0.1 Orientation (pinned by L7; an orientation drift nearly shipped in L2)

`T_k` is target-first `T[u,r]`; `U = T_kᵀ`; `Q[a,b] = ‖P_a U P_b‖₂` with `a` the **target**
level and `b` the **source** level. Column sums of `T_k` are the trivial ones
(`Tcount_col_sum`), row sums the hard ones (`Tk_row_sum`).

This file **transposes and zeroes a row**, which is precisely where L2's error would recur, so
it was checked numerically both ways before anything was proved:

| what was zeroed in `U = Tᵀ` | equals, in `T` | `max|P_a U_clean P_b|`, `a ≥ b` |
|---|---|---|
| **row** `idx (rstar k)` (this file) | delete the defect **column** `r*` | `5.7e-17` (k=4), `2.3e-16` (k=6), `6.9e-16` (k=8) |
| column `idx (rstar k)` (the trap) | delete the `r*` **row** | `1.23e-01` (k=4), `3.53e-02` (k=6), `7.9e-03` (k=8) - see the correction note |

> **CORRECTED 2026-08-03 (orchestrator re-measurement).** This row previously read
> `1.25e-01` at all three `k`. That is wrong: the wrong-index deviation is `~0.125` only at
> `k = 4` and **decays with `k`** - measured `0.1228 / 0.0353 / 0.0079` at `k = 4, 6, 8` in
> an independent rebuild. The qualitative conclusion is unaffected and the trap still fires
> at every `k` tested (the correct choice gives `9.5e-15 / 1.2e-13`, so the separation is
> ten-plus orders of magnitude).
>
> **But the decay is worth knowing, because it means this guard gets weaker as `k` grows.**
> Anyone re-running the orientation check should do it at **small `k`**, where a wrong index
> is off by `~10^-1`, not at large `k`, where it is off by `~10^-3` and could be mistaken
> for accumulated floating-point error by someone not looking carefully. A guard whose
> discriminating power shrinks in the parameter is a guard that will eventually stop
> guarding.

The wrong choice does not degrade gracefully; it is wrong by `0.125` at `k = 4, 6, 8` alike.
`‖U[dz,:] − T[:,dz]‖ = 0` to machine precision at all three, confirming the zeroed row of `U`
is the `cf` column of `T` that `defect_col_eq_cf` identifies, with mass exactly `1.000000`.

## Calibration (session-side `l10_calib.py`; scripts not committed)

Everything was built numerically from `TransferOperator`'s own target-first `Tcount`
(`syracuse(r + m·2^k) mod 2^k` over the lift window), not from a re-derived matrix.

```
k    ‖F*F − I‖   col sums of T      row sums of T (min..max)     max|P_a Uc P_b| a≥b
4     1.1e-15     exact 1 (0e0)     0.937500 .. 1.125000          5.7e-17
6     2.0e-14     exact 1 (0e0)     0.984375 .. 1.046875          2.3e-16
8     8.9e-14     exact 1 (0e0)     0.996094 .. 1.015625          6.9e-16
```

A draft of this header read the row-sum column as *"bracketing `1 − 2^{1−k}` from both
sides"*. **Wrong, and withdrawn**: every row sum is `≥ 1 − 2^{1−k}` (`0.875`, `0.96875`,
`0.992188`), never below. The correct - and much stronger - statement is that
`TransferOperator.Tk_row_sum`'s identity `T·1 = (1 − 2^{1−k})·1 + c` holds **exactly**:
`max_u |rowsum(u) − ((1 − 2^{1−k}) + c_u)| = 0.00e+00` at `k = 4, 6, 8`, with `∑_u c_u = 1`
and the consistency check `N·(1 − 2^{1−k}) + 1 = 2^{k−1} = ∑_u rowsum(u)` exact at all three.
So the row sums are **not** constant and **not** `1` - `THEOREM.md` I.1's boxed
non-uniform-stationarity warning, reproduced numerically in the same matrix the theorems below
are about, in the exact form L7 proved.

The normalisation of §4 was checked directly, as
`max_{ξ,η} |⟪χ_ξ, U_clean χ_η⟫ − cleanEntry(k,η,ξ)/N|`:
`4.8e-16` (k=4), `1.7e-15` (k=6), `4.8e-15` (k=8). The lower block is **exactly** zero, not
merely small.

## Sign scope (STANDING GATE, inherited from `Assembly.lean` §GATE 1)

`3` enters through `syracuse` and through `rstar` (`3·r* + 1 ≡ 0 mod 2^k`), so this file is
not literally sign-agnostic. It is still **not** evidence about Collatz cycles: everything
below is linear algebra over a counting matrix, and the `3x−1` operator has the same shape
(`CYCLE_CLAIM_REFUTED.md`). Nothing here is an obstruction to cycles of anything.

## Hypotheses that are declared and not used (recorded, not silenced)

Following `LemmaA.lean`, `CharacterBasis.lean` and `BlockVanishing.lean`:

* `Tcount_even_zero`: nothing; all three hypotheses are used.
* `inner_chiVec_Uend`: `hk : 1 ≤ k` is not decoration - it is consumed by `sum_targets` (§3)
  and `sum_fin_clean` (§2), which route it into `od_lt`/`od_idx`, `odds_partition` and
  `defect_card`.
* `inner_block_zero`: `hk : 2 ≤ k` is needed only through `level_lt`, to derive `b + 2 ≤ k`
  from `η ∈ levelSet k b`. The `a ≥ b` orientation enters only through
  `clean_entry_vanishes`. The oddness half of `level_factor`'s output is required for `η`
  (`clean_entry_vanishes` needs `Odd η'`) and discarded for `ξ` - the same asymmetry L8 and L9
  both recorded on the lower side.
* `P_Uclean_P_eq_zero`: nothing; `hk` and `hab` are both forwarded to `inner_block_zero`.

## Mutation tests (failure mode 1: a theorem a tactic closes on its own)

Nine single-token mutations were applied to the load-bearing statements and the build was run
on each. **All nine failed to compile.** The build was restored and re-run green afterwards.

| # | mutation | result |
|---|---|---|
| M1 | `Uclean`: `Tᵀ` → `T` (drop the transpose; propagated to all three `Uclean_*` lemmas) | fails |
| M2 | `Uclean`: zero row `idx (rstar k)` → `idx (rstar k) + 1` (the wrong defect row) | fails |
| M3 | `inner_chiVec_Uend`: normalisation `(2^{k-1})⁻¹` → `(2^k)⁻¹` | fails |
| M4 | `inner_chiVec_Uend`: `cleanEntry k η ξ` → `cleanEntry k ξ η` (swap the pairing) | fails |
| M5 | `inner_block_zero`: `hab : b ≤ a` → `a ≤ b` (the orientation) | fails |
| M6 | `P_Uclean_P_eq_zero`: `P_a U P_b` → `P_b U P_a` (swap the projections) | fails |
| M7 | `conj_w_pow`: `wz k (-n)` → `wz k n` (drop the conjugation) | fails |
| M8 | `cleanOdds_eq_erase`: `Icc 1 (k-1)` → `Icc 1 k` (the clean-source range) | fails |
| M9 | `Tcount_even_zero`: `u % 2 = 0` → `u % 2 = 1` (the parity gate) | fails |

M1, M2, M5 and M6 are four independent shots at the orientation trap that shipped a defect in
L2 - the transpose itself, which index is zeroed, which side of `b ≤ a` is assumed, and which
projection stands on which side of `U`. M3 is the `1/N` L9 flagged as missing; M4 checks that
the two character arguments are not interchangeable.

Sorry-free. Axioms audited in §8.
-/

import BlockVanishing

namespace OperatorBlock

open Finset GapCertificate LemmaA CountingLemmas CollisionBound TransferOperator
open CharacterBasis BlockVanishing

/-!
--------------------------------------------------------------------------------
## §1. `U_clean` as an operator
--------------------------------------------------------------------------------

`Uclean k` is `(TkC k)ᵀ` with the row `idx (rstar k)` zeroed. `TransferOperator.rstar` is the
unique odd `r < 2^k` with `2^k ∣ 3r+1` (`CollisionBound.eq_rstar` + `defect_card`), and
`TransferOperator.defect_col_eq_cf` proves `Tcount k · (rstar k) = cf k ·` - the defect is the
`r*` COLUMN of `T`. Under `U = Tᵀ` a column of `T` is a row of `U`; see §0.1 for the numerical
check that zeroing the other index is wrong by `0.125`.
-/

/-- **`U_clean`**: the transpose of `T_k` with the defect row removed. -/
noncomputable def Uclean (k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℂ :=
  fun r u => if (r : ℕ) = idx (rstar k) then 0 else Matrix.transpose (TkC k) r u

theorem Uclean_apply (k : ℕ) (r u : Fin (2 ^ (k - 1))) :
    Uclean k r u = if (r : ℕ) = idx (rstar k) then 0 else TkC k u r := rfl

open Matrix in
/-- Off the defect row, `U_clean` really is the transpose - stated with `ᵀ` so the
orientation of §0.1 is visible in a theorem, not only in the definition. -/
theorem Uclean_eq_transpose (k : ℕ) {r : Fin (2 ^ (k - 1))} (hr : (r : ℕ) ≠ idx (rstar k))
    (u : Fin (2 ^ (k - 1))) : Uclean k r u = (TkC k)ᵀ r u := by
  rw [Uclean_apply, if_neg hr]; rfl

/-- The zeroed row of `U_clean` is exactly the row `defect_col_eq_cf` identifies. -/
theorem Uclean_defect_row (k : ℕ) {r : Fin (2 ^ (k - 1))} (hr : (r : ℕ) = idx (rstar k))
    (u : Fin (2 ^ (k - 1))) : Uclean k r u = 0 := by
  rw [Uclean_apply, if_pos hr]

/-- Off the defect row, `U_clean` is the transpose of `T_k`. -/
theorem Uclean_clean_row (k : ℕ) {r : Fin (2 ^ (k - 1))} (hr : (r : ℕ) ≠ idx (rstar k))
    (u : Fin (2 ^ (k - 1))) : Uclean k r u = TkC k u r := by
  rw [Uclean_apply, if_neg hr]

/-- `U_clean` as an endomorphism of `ℓ²`. -/
noncomputable def Uend (k : ℕ) : Module.End ℂ (EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :=
  Matrix.toEuclideanLin (Uclean k)

@[simp] theorem Uend_apply (k : ℕ) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1))))
    (r : Fin (2 ^ (k - 1))) : (Uend k x) r = ∑ u, Uclean k r u * x u := rfl

/-!
--------------------------------------------------------------------------------
## §2. Index bookkeeping: `Fin (2^(k-1))` ↔ the odd residues, minus `r*`
--------------------------------------------------------------------------------

`chiVec` and `Uclean` are indexed by `Fin (2^(k-1))` through `od s = 2s+1`; `cleanEntry` is
indexed by the shell union `(Icc 1 (k-1)).biUnion (shell k)`. L9 flagged the identification of
that union as "all odds but `r*`" as *"a corollary of a proved lemma, not itself proved here"*.
It is proved here (`cleanOdds_eq_erase`), from `CountingLemmas.odds_partition` and
`CountingLemmas.defect_card`.
-/

/-- The odd residues mod `2^k` are exactly the image of `Fin (2^(k-1))` under `od`. -/
theorem oddResidues_eq_image {k : ℕ} (hk : 1 ≤ k) :
    oddResidues k
      = Finset.image (fun s : Fin (2 ^ (k - 1)) => od (s : ℕ)) univ := by
  ext r
  simp only [oddResidues, mem_filter, mem_range, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨idx r, idx_lt hk h1⟩, od_idx h2⟩
  · rintro ⟨s, rfl⟩
    exact ⟨od_lt hk s.isLt, od_odd _⟩

/-- `od` is injective. -/
theorem od_injective : Function.Injective od := by
  intro x y h; unfold od at h; omega

/-- Re-index a sum over `Fin (2^(k-1))` as a sum over the odd residues mod `2^k`. -/
theorem sum_fin_od {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℂ) :
    ∑ s : Fin (2 ^ (k - 1)), f (od (s : ℕ)) = ∑ r ∈ oddResidues k, f r := by
  rw [oddResidues_eq_image hk,
    Finset.sum_image (fun x _ y _ h => Fin.ext (od_injective h))]

/-- `defectSet k = {rstar k}`: `defect_card` says it is a singleton and
`rstar_mem_defectSet` says which one. -/
theorem defectSet_eq_singleton {k : ℕ} (hk : 1 ≤ k) : defectSet k = {rstar k} := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (defect_card hk)
  have hmem := rstar_mem_defectSet hk
  rw [ha] at hmem ⊢
  rw [Finset.mem_singleton] at hmem
  rw [hmem]

/-- **The clean sources ARE the odds minus `r*`.** This is the reading of
`(Icc 1 (k-1)).biUnion (shell k)` that L9 used informally and did not prove. -/
theorem cleanOdds_eq_erase {k : ℕ} (hk : 1 ≤ k) :
    (Icc 1 (k - 1)).biUnion (shell k) = (oddResidues k).erase (rstar k) := by
  ext r
  constructor
  · intro h
    have hmem : r ∈ oddResidues k := by
      rw [odds_partition hk]; exact mem_union_left _ h
    refine mem_erase.2 ⟨?_, hmem⟩
    rw [mem_biUnion] at h
    obtain ⟨j, hj, hrj⟩ := h
    rw [mem_Icc] at hj
    simp only [shell, mem_filter, mem_range] at hrj
    intro hc
    subst hc
    have hdvd : (2 : ℕ) ^ k ∣ 3 * rstar k + 1 := Nat.dvd_of_mod_eq_zero (rstar_defect hk)
    have hne : 3 * rstar k + 1 ≠ 0 := by omega
    exact ((v2_eq_iff_dvd hne).1 hrj.2.2.2).2
      (dvd_trans (pow_dvd_pow 2 (by omega)) hdvd)
  · intro h
    rw [mem_erase] at h
    have h2 := h.2
    rw [odds_partition hk, mem_union] at h2
    rcases h2 with h1 | h2
    · exact h1
    · rw [defectSet_eq_singleton hk, mem_singleton] at h2
      exact absurd h2 h.1

/-- `od s = rstar k` exactly when `s` is the defect index. -/
theorem od_eq_rstar_iff {k : ℕ} (hk : 1 ≤ k) (s : Fin (2 ^ (k - 1))) :
    od (s : ℕ) = rstar k ↔ (s : ℕ) = idx (rstar k) := by
  constructor
  · intro h
    have : idx (od (s : ℕ)) = idx (rstar k) := by rw [h]
    rwa [show idx (od (s : ℕ)) = (s : ℕ) by unfold od idx; omega] at this
  · intro h
    rw [h, od_idx (rstar_odd hk)]

/-- A sum over `Fin (2^(k-1))` with the defect index killed IS a sum over the clean sources. -/
theorem sum_fin_clean {k : ℕ} (hk : 1 ≤ k) (F : ℕ → ℂ) :
    ∑ s : Fin (2 ^ (k - 1)), (if (s : ℕ) = idx (rstar k) then (0 : ℂ) else F (od (s : ℕ)))
      = ∑ r ∈ (Icc 1 (k - 1)).biUnion (shell k), F r := by
  have hstep : ∀ s : Fin (2 ^ (k - 1)),
      (if (s : ℕ) = idx (rstar k) then (0 : ℂ) else F (od (s : ℕ)))
        = (if od (s : ℕ) = rstar k then (0 : ℂ) else F (od (s : ℕ))) := by
    intro s
    by_cases h : (s : ℕ) = idx (rstar k)
    · rw [if_pos h, if_pos ((od_eq_rstar_iff hk s).2 h)]
    · rw [if_neg h, if_neg (fun hc => h ((od_eq_rstar_iff hk s).1 hc))]
  have key : ∑ s : Fin (2 ^ (k - 1)),
        (if od (s : ℕ) = rstar k then (0 : ℂ) else F (od (s : ℕ)))
      = ∑ r ∈ oddResidues k, (if r = rstar k then (0 : ℂ) else F r) :=
    sum_fin_od hk (fun r => if r = rstar k then (0 : ℂ) else F r)
  rw [Finset.sum_congr rfl (fun s _ => hstep s), key, cleanOdds_eq_erase hk]
  rw [← Finset.sum_subset (Finset.erase_subset (rstar k) (oddResidues k))
    (fun x hx hnx => by
      have hxr : x = rstar k := by
        by_contra hc
        exact hnx (mem_erase.2 ⟨hc, hx⟩)
      rw [if_pos hxr])]
  exact Finset.sum_congr rfl (fun x hx => if_neg (mem_erase.1 hx).1)

/-!
--------------------------------------------------------------------------------
## §3. The target index: even targets carry no mass
--------------------------------------------------------------------------------

`cleanEntry`'s inner sum runs over `u ∈ range (2^k)`; `Uclean` runs over `u : Fin (2^(k-1))`,
i.e. over `od u`. The two agree because `Tcount k u r = 0` for even `u` and odd `r` -
`syracuse` maps odds to odds, which is `TransferOperator.syracuse_odd`. This is the arithmetic
twin of the orientation trap: if `Syr` did not preserve oddness the target index would leave
range and `Tcount_col_sum` would be false.
-/

/-- Even targets are unreachable from an odd source. -/
theorem Tcount_even_zero {k u r : ℕ} (hk : 1 ≤ k) (hr : r % 2 = 1) (hu : u % 2 = 0) :
    Tcount k u r = 0 := by
  unfold Tcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hc
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hodd : syracuse (r + m * 2 ^ k) % 2 ^ k % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ h2]
    exact syracuse_odd (lift_odd hk hr)
  rw [hc] at hodd
  omega

/-- The target sum over `range (2^k)` collapses to the odd targets. -/
theorem sum_targets {k : ℕ} (hk : 1 ≤ k) {r : ℕ} (hr : r % 2 = 1) (g : ℕ → ℂ) :
    ∑ u ∈ range (2 ^ k), (Tcount k u r : ℂ) * g u
      = ∑ s : Fin (2 ^ (k - 1)), (Tcount k (od (s : ℕ)) r : ℂ) * g (od (s : ℕ)) := by
  have key : ∑ s : Fin (2 ^ (k - 1)), (Tcount k (od (s : ℕ)) r : ℂ) * g (od (s : ℕ))
      = ∑ u ∈ oddResidues k, (Tcount k u r : ℂ) * g u :=
    sum_fin_od hk (fun u => (Tcount k u r : ℂ) * g u)
  rw [key]
  refine (Finset.sum_subset (fun x hx => by
    simp only [oddResidues, mem_filter] at hx; exact hx.1) ?_).symm
  intro x hx hnx
  have hx2 : x % 2 ≠ 1 := by
    intro h
    exact hnx (by
      simp only [oddResidues, mem_filter, mem_range]
      exact ⟨mem_range.1 hx, h⟩)
  rw [Tcount_even_zero hk hr (by omega), Nat.cast_zero, zero_mul]

/-!
--------------------------------------------------------------------------------
## §4. The normalisation: `⟪χ_ξ, U_clean χ_η⟫ = (1/N)·cleanEntry`
--------------------------------------------------------------------------------

L9's `cleanEntry` *"drops the `1/N` of `chiVec`'s normalisation"*, so it is an unnormalised
bilinear pairing. This section supplies the factor and thereby turns it into a genuine matrix
element of `Uend` in the orthonormal basis `CharacterBasis.chiBasis`.

`N = 2^{k-1}`; the two `1/√N` of `chiVec` (one from `χ_ξ`, one from `χ_η`) compose to `1/N`.
Verified numerically to `4.8e-15` at `k = 8` (§0 header).
-/

/-- Conjugation flips the sign of the exponent: `conj (w^n) = w^{-n}`. -/
theorem conj_w_pow (k n : ℕ) : (starRingEnd ℂ) (w k ^ n) = wz k (-(n : ℤ)) := by
  rw [map_pow, ← Complex.inv_eq_conj (norm_w k), wz, zpow_neg, zpow_natCast, ← inv_pow]

/-- **THE NORMALISATION.** The matrix element of `U_clean` between two characters is
L9's `cleanEntry`, divided by `N = 2^{k-1}`. -/
theorem inner_chiVec_Uend {k : ℕ} (hk : 1 ≤ k) (ξ η : Fin (2 ^ (k - 1))) :
    (@inner ℂ _ _ (chiVec k ξ) (Uend k (chiVec k η)) : ℂ)
      = (((2 ^ (k - 1) : ℕ) : ℂ))⁻¹ * cleanEntry k (η : ℕ) ((ξ : ℕ) : ℤ) := by
  have hNc : ((2 ^ (k - 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hpow : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero k two_ne_zero
  set F : ℕ → ℂ := fun r =>
    (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (Tcount k u r : ℂ) * w k ^ ((η : ℕ) * u))
      * wz k (-(((ξ : ℕ) : ℤ) * (r : ℤ))) with hF
  -- pointwise identification of the summands
  have hpt : ∀ s : Fin (2 ^ (k - 1)),
      (inner ℂ ((chiVec k ξ).ofLp s) ((Uend k (chiVec k η)).ofLp s) : ℂ)
        = (((2 ^ (k - 1) : ℕ) : ℂ))⁻¹
            * (if (s : ℕ) = idx (rstar k) then (0 : ℂ) else F (od (s : ℕ))) := by
    intro s
    rw [RCLike.inner_apply]
    show (Uend k (chiVec k η)) s * (starRingEnd ℂ) (chi k (ξ : ℕ) (s : ℕ) / (rt k : ℂ)) = _
    rw [map_div₀, Complex.conj_ofReal, chi, conj_w_pow]
    by_cases hs : (s : ℕ) = idx (rstar k)
    · rw [if_pos hs]
      have hz : (Uend k (chiVec k η)) s = 0 := by
        rw [Uend_apply]
        exact Finset.sum_eq_zero fun u _ => by rw [Uclean_defect_row k hs u, zero_mul]
      rw [hz, zero_mul, mul_zero]
    · rw [if_neg hs]
      have hval : (Uend k (chiVec k η)) s
          = (rt k : ℂ)⁻¹ * (((2 : ℂ) ^ k)⁻¹
              * ∑ u ∈ range (2 ^ k), (Tcount k u (od (s : ℕ)) : ℂ)
                  * w k ^ ((η : ℕ) * u)) := by
        rw [Uend_apply]
        rw [sum_targets hk (od_odd s) (fun u => w k ^ ((η : ℕ) * u))]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Uclean_clean_row k hs u]
        show (Tcount k (od (u : ℕ)) (od (s : ℕ)) : ℂ) / 2 ^ k
            * (chi k (η : ℕ) (u : ℕ) / (rt k : ℂ)) = _
        rw [chi]
        field_simp
      rw [hval, hF]
      have hodr : ((od (s : ℕ) : ℕ) : ℤ) = ((od (s : ℕ)) : ℤ) := rfl
      rw [show -(((ξ : ℕ) * od (s : ℕ) : ℕ) : ℤ) = -(((ξ : ℕ) : ℤ) * ((od (s : ℕ) : ℕ) : ℤ)) by
        push_cast; ring]
      have hrt : ((2 ^ (k - 1) : ℕ) : ℂ)⁻¹ = (rt k : ℂ)⁻¹ * (rt k : ℂ)⁻¹ := by
        rw [← mul_inv, rt_mul_rt]
      rw [hrt]
      ring
  rw [PiLp.inner_apply, Fintype.sum_congr _ _ hpt, ← Finset.mul_sum,
    sum_fin_clean hk F, cleanEntry, hF]

/-!
--------------------------------------------------------------------------------
## §5. Levels supply the dyadic factorisations `clean_entry_vanishes` demands
--------------------------------------------------------------------------------

`BlockVanishing.clean_entry_vanishes` takes `η = 2^b·η'` with `η'` odd, `ξ = 2^a·ξ'`,
`b + 2 ≤ k`, and an inverse `u` of `3` mod `2^k`. Membership in `levelSet` supplies the first
three; `rstar` supplies the fourth (`3·(−r*) − 1 = −(3r*+1) ≡ 0`), so no new arithmetic and no
new axiom is needed to instantiate it.
-/

/-- `v₂(n) = a` with `n ≠ 0` gives the dyadic factorisation `n = 2^a·(odd)`. -/
theorem level_factor {n a : ℕ} (hn : n ≠ 0) (hv : v2 n = a) :
    ∃ m : ℕ, (n : ℤ) = 2 ^ a * (m : ℤ) ∧ Odd ((m : ℤ)) := by
  obtain ⟨hd, hnd⟩ := (v2_eq_iff_dvd hn).1 hv
  obtain ⟨m, hm⟩ := hd
  refine ⟨m, by exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) hm, ?_⟩
  have hmo : m % 2 = 1 := by
    rcases Nat.even_or_odd m with he | ho
    · exfalso
      obtain ⟨t, ht⟩ := he
      exact hnd ⟨t, by rw [hm, ht, pow_succ]; ring⟩
    · rw [Nat.odd_iff] at ho; exact ho
  exact ⟨(m / 2 : ℕ), by omega⟩

/-- **`3⁻¹` mod `2^k` exists, concretely**: `u = −r*` works, because `2^k ∣ 3r*+1`. -/
theorem three_inv_rstar {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℤ) ^ k ∣ 3 * (-(rstar k : ℤ)) - 1 := by
  obtain ⟨t, ht⟩ : (2 : ℕ) ^ k ∣ 3 * rstar k + 1 :=
    Nat.dvd_of_mod_eq_zero (rstar_defect hk)
  have hz : (3 * (rstar k : ℤ) + 1) = 2 ^ k * (t : ℤ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) ht
  exact ⟨-(t : ℤ), by linarith⟩

/-- **The matrix element of `U_clean` between a level-`b` source and a level-`a` target with
`a ≥ b` is zero.** This is `clean_entry_vanishes`, normalised by §4 and instantiated by §5. -/
theorem inner_block_zero {k a b : ℕ} (hk : 2 ≤ k) (hab : b ≤ a)
    {ξ η : Fin (2 ^ (k - 1))} (hξ : ξ ∈ levelSet k a) (hη : η ∈ levelSet k b) :
    (@inner ℂ _ _ (chiVec k ξ) (Uend k (chiVec k η)) : ℂ) = 0 := by
  rw [mem_levelSet] at hξ hη
  obtain ⟨m, hm, hmo⟩ := level_factor hη.1 hη.2
  obtain ⟨n, hn, _⟩ := level_factor hξ.1 hξ.2
  have hbk : b + 2 ≤ k := by
    have := level_lt (k := k) (ξ := η) hk hη.1
    omega
  rw [inner_chiVec_Uend (by omega) ξ η,
    clean_entry_vanishes (a := a) (b := b) (η' := (m : ℤ)) (ξ' := (n : ℤ))
      (u := -(rstar k : ℤ)) hm hmo hn hab hbk (three_inv_rstar (by omega)),
    mul_zero]

/-!
--------------------------------------------------------------------------------
## §6. `P_a U_clean P_b = 0`
--------------------------------------------------------------------------------

The last step is the one L9 named and did not take: *"the implication 'every entry in an
orthonormal basis vanishes ⇒ the operator vanishes' is not applied - `CharacterBasis.chiBasis`
and `P_apply` are not used anywhere in this file."* Both are used below.

`P k b x` is by definition a combination of the level-`b` characters; `Uend k` is linear, so it
maps that to a combination of `Uend k (chiVec k η)`; `P k a` of anything reads off its
`⟪chiVec k ξ, ·⟫` coefficients for `ξ` of level `a`; and §5 says every one of those is `0`.
-/

/-- **THE OPERATOR IDENTITY.** For `a ≥ b`, `P_a U_clean P_b = 0`. -/
theorem P_Uclean_P_eq_zero {k a b : ℕ} (hk : 2 ≤ k) (hab : b ≤ a)
    (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    P k a (Uend k (P k b x)) = 0 := by
  rw [P_apply (k := k) (a := b), map_sum]
  simp only [map_smul]
  rw [P_apply]
  refine Finset.sum_eq_zero fun ξ hξ => ?_
  rw [inner_sum]
  have hz : ∀ η ∈ levelSet k b,
      (@inner ℂ _ _ (chiVec k ξ)
        ((@inner ℂ _ _ (chiVec k η) x : ℂ) • Uend k (chiVec k η)) : ℂ) = 0 := by
    intro η hη
    rw [inner_smul_right, inner_block_zero hk hab hξ hη, mul_zero]
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_smul]

/-- The same statement as an operator equation, with the composition written out. -/
theorem P_Uclean_P_comp {k a b : ℕ} (hk : 2 ≤ k) (hab : b ≤ a) :
    (P k a) ∘ₗ (Uend k : EuclideanSpace ℂ (Fin (2 ^ (k - 1))) →ₗ[ℂ] _) ∘ₗ (P k b) = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  exact P_Uclean_P_eq_zero hk hab x

/-!
--------------------------------------------------------------------------------
## §7. Satisfiability and calibration (failure mode 3: vacuity)
--------------------------------------------------------------------------------

Every hypothesis block above is exhibited at a concrete point. The point is L9's,
`k = 6`, `a = 3`, `b = 2`, extended with actual `levelSet` members: `η = 4` has `v₂ = 2 = b`
and `ξ = 8` has `v₂ = 3 = a`, both nonzero and both `< 2^5 = 32`. So `inner_block_zero` and
`P_Uclean_P_eq_zero` are not vacuously true at `k = 6`: their index sets are inhabited.

`defect_index_six` additionally pins the index this file zeroes at a concrete `k`: `rstar 6 =
21`, `idx 21 = 10`. That is the row the §0.1 numerics measured as correct and the row `+1`
(mutant M2) as wrong, so the Lean object and the calibrated object are the same object.

The mutation table is in the file header. All nine mutants were required to fail the build,
and did; the build was restored and re-run green afterwards.
-/

theorem v2_eight : v2 8 = 3 :=
  (v2_eq_iff_dvd (by norm_num)).2 ⟨by norm_num, by decide⟩

/-- The level sets used below are inhabited, `2 ≤ k`, and `b ≤ a` - simultaneously. -/
theorem hyp_satisfiable_block :
    (⟨4, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 2 ∧
    (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 3 ∧
    (2 : ℕ) ≤ 6 ∧ (2 : ℕ) ≤ 3 := by
  refine ⟨mem_levelSet.2 ⟨by norm_num, v2_four⟩, mem_levelSet.2 ⟨by norm_num, v2_eight⟩,
    by omega, by omega⟩

/-- An instance of `inner_block_zero` at that point: level `2` source, level `3` target. -/
example :
    (@inner ℂ _ _ (chiVec 6 ⟨8, by norm_num⟩)
      (Uend 6 (chiVec 6 ⟨4, by norm_num⟩)) : ℂ) = 0 :=
  inner_block_zero (a := 3) (b := 2) (by omega) (by omega)
    (mem_levelSet.2 ⟨by norm_num, v2_eight⟩) (mem_levelSet.2 ⟨by norm_num, v2_four⟩)

/-- An instance of the operator identity at the same point. -/
example (x : EuclideanSpace ℂ (Fin (2 ^ (6 - 1)))) : P 6 3 (Uend 6 (P 6 2 x)) = 0 :=
  P_Uclean_P_eq_zero (by omega) (by omega) x

/-- The defect index at `k = 6` really is `10`, i.e. `rstar 6 = 21` and `idx 21 = 10` -
the row this file zeroes, and the one the numerics in §0.1 confirm. -/
theorem defect_index_six : idx (rstar 6) = 10 := by
  have h : rstar 6 = 21 := by unfold rstar ek; norm_num
  rw [h]; unfold idx; norm_num

/-!
--------------------------------------------------------------------------------
## §8. Axiom audit
--------------------------------------------------------------------------------
-/

#print axioms Uclean_defect_row
#print axioms Uclean_eq_transpose
#print axioms sum_fin_clean
#print axioms cleanOdds_eq_erase
#print axioms defectSet_eq_singleton
#print axioms Tcount_even_zero
#print axioms sum_targets
#print axioms conj_w_pow
#print axioms inner_chiVec_Uend
#print axioms level_factor
#print axioms three_inv_rstar
#print axioms inner_block_zero
#print axioms P_Uclean_P_eq_zero
#print axioms P_Uclean_P_comp
#print axioms defect_index_six

end OperatorBlock
