/-
# The `3x + c` operator, for an arbitrary odd shift `c`

## WHY THIS FILE EXISTS

`CYCLE_CLAIM_REFUTED.md` carries this project's most transferable claim:

> the `3x - 1` map passes the **identical** certificate, more strongly than `3x + 1`, and
> `3x - 1` **has** non-trivial cycles.  So "spectral gap therefore no cycles" is false.

Everything else in the headline chain is machine-checked.  **That claim is not** - it is a
numerical observation in a Python script.  This file is the first step of closing that gap, by
generalising the operator from the hardcoded `3n + 1` to `3n + c` for arbitrary odd `c`.

## SCOPE OF *THIS* FILE, STATED HONESTLY

This is a **foundation layer, not the finished result.**  It provides the parametrised
definitions and proves that they specialise correctly at `c = 1`, so nothing existing changes
meaning.  It does **not** yet reach a certificate bound for general `c`; that needs the rest of
the chain (`CountingLemmas`, `CollisionBound`, `BlockVanishing`, `OperatorBlock`, `CleanBlock`,
`ManifestInstance`) generalised too, which is a larger job.  **Do not cite this file as
"the 3x-1 certificate is formalised".  It is not, yet.**

Five things ARE finished, and the boundary between them and the rest is the point of this note:

1. **Coset uniformity for a general odd shift** (§2b) — the engine Lemma A runs on, `c`-uniform.
2. **Lemma B's `a = 3` case, complete and sorry-free** (§2c, 2026-08-05):
   `coll3_closed : coll3 k + 2 = 3 * 2 ^ k`.  `a = 3` was the one offset case a general odd
   shift produces that `CollisionBound.lean` did not already cover.  **Read the caveat at the
   end of §2c before citing this**: it is a complete theorem about the `a = 3` AP model, and the
   theorem tying that model to the actual `3x+c` defect fibre — the general-`c` analogue of
   `CollisionBound.syracuse_defect_fibre` — is not proved here.

3. **Lemma SB for a general odd shift** (§2e, 2026-08-05): `sbS_bijective`.
4. **Lemma A's shifted ENTRY theorem** (§5–§7, 2026-08-05): `upper_entry_eqS`, with the shifted
   clean operator `UcleanS` and the shifted character pairing `inner_chiVec_UendS`.  In the
   upper regime the shifted clean entry is
   `w^{ξuc} · Sodd (resJ k η ξ u d) (k − d)`, `d = b − a` — the **same `Sodd`, the same
   `resJ`, the same `alphaJ`** as `c = 1`, with the shift confined to a unimodular prefactor.
5. **LEMMA A ITSELF, AT A GENERAL ODD SHIFT** (§8, 2026-08-05): `clean_boundS` —
   `‖P_a U_clean^{(c)} P_b‖ ≤ s^{b−a}`, `s = √(1/2)`, for every odd `c` and every `a < b`,
   via the exact identity `norm_sq_clean_blockS` and the shifted Gram identity `gram_upperS`.
   This is `calibrate_general_shift.py`'s gate 2 — measured to `1e-14` for every odd `c` — now
   proved.

Still open for general `c`: **Lemma B, the defect half** (only the `a = 3` AP-model case is
proved, and it is not tied to the shifted defect fibre), and the assembly.

**THE MISREADING THIS FILE MOST INVITES, NOW THAT §8 EXISTS.**  A certificate is
`clean + defect`.  §8 closes the clean half at every odd shift; the defect half is open.  So
there is deliberately **no** shifted analogue of `GramIdentity.gap_certificate_unconditional`
in this file, and none may be inferred from `clean_boundS`.  Until Lemma B lands for general
`c`, "the `3x+c` certificate" does not exist here — and the `3x−1` control experiment remains
a Python observation for the separate reason that `c : ℕ` cannot express `3x−1` at all (§4).

## THE CALIBRATION THAT JUSTIFIED STARTING

Run before writing any of this (`calibrate_general_shift.py`, public repo).  Four gates, every
odd `c` tested, `k = 4..8`, all pass:

* `cert_c(k) ≤ 0.853553...` — the same **bound**, not the same value (measured `0.604`–`0.682`);
* **Lemma A's clean block norms are exactly `2^{-(b-a)/2}` for every odd `c`, to `1e-14`.**  This
  is the structural fact the certificate rests on and it is completely shift-independent — the
  decisive evidence that the generalisation is real rather than hoped for;
* Lemma B's `‖D‖₂ ≤ √3 · 2^{-k/2}` holds throughout;
* `rank(D) = 1`, with `r*` the solution of `3r + c ≡ 0 (mod 2^k)`.

**One risk carried forward:** gate 3 is nearly saturated at `c = 2^k - 1` — at `k = 8`,
`0.108112` against a limit of `0.108253`, a margin of `0.13%`.  The `√3` constant may be sharp
there, so no later step may lean on slack that does not exist at that shift.

> **CORRECTED 2026-08-05.**  This paragraph used to read "at `c = 2^k - 1`, i.e. exactly the
> `3x-1` case ... the shift the control experiment actually cares about".  **`c = 2^k - 1` is
> not the `3x−1` shift** — `-1` and `2^k - 1` agree mod `2^k`, and `oddPart` does not factor
> through that.  Full correction, with the measurement, at the head of §4.  The saturation is
> real but belongs to the substitute: for the genuine `c = −1` the same quantity is `1.5284`
> against `√3 = 1.7321`, an `11.8%` margin.  Both `calibrate_general_shift.py` and this file
> carried the substitution, so the gates were being checked on the wrong operator.

## THE ONE STRUCTURAL DIFFERENCE FROM `c = 1`

`CollisionBound.rstar k = (2 ^ ek k - 1) / 3` solves `3r + 1 = 2^(ek k)`, and that closed form
is specific to the shift `1`.  For general `c` the defect residue is the solution of
`3r + c ≡ 0 (mod 2^k)`, given here as `rstarS c k` via the inverse of `3`.  Everything else in
this file is `c`-uniform.

Sorry-free.  Specialisation lemmas throughout, mutation table below, axiom audit `§9`.

## MUTATIONS (77, all fail)

| # | mutation | result |
|---|---|---|
| S1 | `syracuseS_odd`: `c % 2 = 1` → `c % 2 = 0` | fails |
| S2 | `oddPart_odd`: drop `n ≠ 0` (the `v2 0 = 0` trap) | fails |
| S3 | `rstarS_spec`: `3r + c` → `3r - c` | fails |
| S4 | `rstarS_spec`: drop `1 ≤ k` | fails |
| S5 | `TcountS_one`: shift `1` → shift `3` | fails |
| S6 | `three_pow_totient`: exponent `2^(k-1)` → `2^k` | fails |
| S7 | `cu_decompositionS`: `c % 2 = 1` → `c % 2 = 0` | fails |
| S8 | `cu_decompositionS`: `v₂(3x+c) < K` → `≤ K` | fails |
| S9 | `cu_valuation_frozenS`: frozen → shifted by one | fails |
| S10 | `cu_syracuse_affineS`: exponent `K - v` → `K` | fails |
| S11 | `cu_syracuse_fibre_cardS`: `2^(K-v)` → `2^K` | fails |
| S12 | `cu_syracuse_fibre_cardS`: drop oddness of `x` | fails |
| S13 | `oddPart_mul_odd`: `d % 2 = 1` → `d % 2 = 0` | fails |
| S14 | `oddPart_mul_odd`: drop `n ≠ 0` | fails |
| S15 | `oddPart_three_add`: drop the factor `3` on the right | fails |
| S16 | `oddPart_three_add`: `m + 1` → `m` (the off-by-one) | fails |
| S17 | `pair_count_closed`: base `P 1 = 4` → `5` | fails |
| S18 | `pair_count_closed`: recurrence `+ 3·2^j` → `+ 2·2^j` | fails |
| S19 | `pair_count_closed`: conclusion `P k + 2` → `P k + 1` | fails |
| S20 | `pair_count_closed`: drop `1 ≤ k` | fails |
| S21 | `oddPart_injOn_block`: block `(N, 2N]` → `(N, 3N]` | fails |
| S22 | `oddPart_injOn_block`: drop the lower bound `N < m` | fails |
| S23a | `exists_shift_into_block`: strengthen `N <` to `2N <` | fails |
| S23b | `exists_shift_into_block`: upper bound `2N` → `N` | fails |
| S23c | `exists_shift_into_block`: drop `0 < q` | fails |
| S24 | `exists_shift_into_block`: drop `q ≤ 2N` | fails |
| S25 | `oddPart_factor`: drop `n ≠ 0` | fails |

| S26 | `block_fibre_card`: singleton → `card = 2` | fails |
| S27 | `block_fibre_card`: drop `oddPart n ≤ 2N` | fails |
| S28 | `block_fibre_card`: block `Ioc N (2N)` → `Ioc N (3N)` | fails |
| S29 | `block_fibre_card_lower`: `n ≤ N` → `n ≤ 3N` | fails |
| S30 | `existsUnique_in_block`: drop `n ≠ 0` | fails |

The `a = 3` closure, added 2026-08-05:

| # | mutation | result |
|---|---|---|
| S31 | `pairCount_double`: recurrence `+ 3N` → `+ 2N` | fails |
| S32 | `pairCount_two`: base `4` → `3` | fails |
| S33 | `sameOddPartCount_lower_block`: `= N` → `= N + 1` | fails |
| S34 | `sameOddPartCount_lower_block`: block `(N,2N]` → `(N,3N]` | fails |
| S35 | `oddPart_lt_two_pow`: drop `1 ≤ k` | fails |
| S36 | `oddPart_lt_two_pow`: conclusion `< 2^k` → `< 2^(k-1)` | fails |
| S37 | `mul_three_mod_cancel`: cancel `2` instead of `3` | fails |
| S38 | `fibVal3_eq_iff`: drop both range hypotheses | fails |
| S39 | `coll3_closed`: margin `+ 2` → `+ 1` | fails |
| S40 | `coll3_eq_pairCount`: `pairCount (2^k)` → `pairCount (2^k − 1)` | fails |
| S41 | `coll3_closed`: drop `1 ≤ k` | fails — see the note |

The shifted SB bijection, added 2026-08-05 (§2e):

| # | mutation | result |
|---|---|---|
| S42 | `shellS_card`: `2^(k-1-j)` → `2^(k-j)` | fails |
| S43 | `shellS_card`: drop `c` odd | fails |
| S44 | `sbS_injOn`: drop `j + 1 ≤ k` | fails |
| S45 | `shellS_oddpart`: `q` odd → `q` even | fails |
| S46 | `shellS_eq`: drop `1 ≤ j` | fails |
| S47 | `sbS_image_eq`: target `oddResidues (k-j)` → `oddResidues (k-j-1)` | fails |

S43 and S44 are the ones that matter.  S43: at even `c` the shell is **empty** (for odd `r`,
`3r + c` is odd, so `v₂ = 0 ≠ j`), and an empty shell cannot biject onto a nonempty set of odd
residues — oddness of the shift is what makes the whole construction non-vacuous.  S44: without
`j + 1 ≤ k` the modulus `2^{k-j}` degenerates to `1` and every residue collapses to `0`, so
injectivity is lost.

S34 and S37 are the ones that matter.  S34: the dyadic block having ratio *exactly* `2` is what
makes the fibre a singleton; widening it to `(N,3N]` breaks the count at `N = 4`, `n = 3`
(partners `6` and `12`).  S37: without coprimality the `×3` does not drop out, and `decide`
refutes `Coprime 2 (2^k)` on the spot.

**S41 is recorded honestly and is weaker than it looks.**  Dropping `1 ≤ k` makes the *proof*
fail, but the *statement* happens to be true at `k = 0` as well (`coll3 0 = 1`, and
`1 + 2 = 3 = 3·2^0`).  So S41 shows only that this proof route uses `hk`; it is not evidence
that the hypothesis is necessary.  Left in the table labelled as such rather than deleted,
because a mutation table that silently drops its weak entries overstates the rest.

**A mutation-design note, recorded because it nearly passed as a result.**  The first version of
S23 *weakened* the conclusion (`N < q·2^j` → `0 < q·2^j`) and of course SURVIVED — a correct
proof of a stronger statement still proves a weaker one, so a conclusion-weakening mutation
tests nothing.  It was replaced by S23a–c, which strengthen the conclusion and tighten the
hypotheses instead.  **Mutations must make the statement harder or the hypotheses weaker, never
the conclusion weaker.**

S3 and S8 are the ones that matter.  S3: `rstarS` would otherwise be a definition with no
verified spec, and the formula came from Euler's theorem rather than being derived here — it was
checked numerically first (255 of 255 `(k, c)` pairs, `k ≤ 12`) and only then proved.  S8: the
strict inequality `v₂(3x+c) < K` is the whole content of coset uniformity; at `v = K` the
valuation is no longer frozen and the fibre count collapses.

Lemma A's shifted entry theorem, added 2026-08-05 (§5, §6, §7).  All 18 fail:

| # | mutation | result |
|---|---|---|
| S48 | `TcountS_even_zero`: parity gate `u % 2 = 0` → `u % 2 = 1` | fails |
| S49 | `sum_targetsS`: target reindex `od s` → `2s` (even targets) | fails |
| S50 | `inner_chiVec_UendS`: normalisation `(2^{k-1})⁻¹` → `(2^k)⁻¹` | fails |
| S51 | `inner_chiVec_UendS`: pairing `(η,ξ)` → `(ξ,η)` | fails |
| S52 | `shell_character_sumS`: **phase `w^{ξuc}` → `w^{ξu}`** (the `c = 1` phase) | fails |
| S53 | `shell_character_sumS`: `Sodd` range `k−j` → `k−j+1` | fails |
| S54 | `shell_character_sumS`: hypothesis weakened `1 ≤ j` → `0 ≤ j` | fails |
| S55 | `shell_character_sumS`: periodicity weakened `2^j ∣ alpha_j` → `2^0 ∣ alpha_j` | fails |
| S56 | `phase_congrS`: **constant `ξ·u·c` → `ξ·u`** | fails |
| S57 | `gauss_collapseS`: CU hypothesis weakened `v₂ < k` → `v₂ ≤ k` | fails |
| S58 | `gauss_collapseS`: Gauss gate `2^v ∣ η` → `2^{v+1} ∣ η` | fails |
| S59 | `cleanEntryS_eq_masked`: mask `maskedOddsS c k b` → `maskedOddsS c k (b+1)` | fails |
| S60 | `upper_entry_eqS`: surviving shell `d = b−a` → `b−a+1` | fails |
| S61 | `upper_entry_eqS`: **phase `w^{ξuc}` → `w^{ξu}`** | fails |
| S62 | `upper_entry_eqS`: regime weakened `a < b` → `a ≤ b` | fails |
| S63 | `cleanOddsS_eq_erase`: erase `rstarS c k` → `rstarS c (k+1)` | fails |
| S64 | `defectSetS_eq_singleton`: level weakened `1 ≤ k` → `0 ≤ k` | fails |
| S65 | `oddsS_partition`: shell range `Icc 1 (k−1)` → `Icc 1 (k−2)` | fails |
| S66 | `UcleanS`: **drop the transpose** (propagated to `UcleanS_apply`, `_clean_row`) | fails |
| S67 | `UcleanS`: zeroed row `idx (rstarS c k)` → `+ 1` (propagated to all three) | fails |

**S52, S56 and S61 are the ones that matter, and they are the reason this section is not
cosmetic.**  All three delete the shift from the phase, i.e. assert that the shifted shell sum
carries the *same* prefactor `w^{ξu}` as `c = 1`.  S52 and S56 fail inside `ring` — the phase
congruence `η·q − ξ·r ≡ alphaJ·q + ξ·u·c` genuinely does not close without the `c`.  So the
constant `ξ·u·c` is load-bearing arithmetic, not decoration, and the claim these sections rest
on ("only the constant changes; `alphaJ` does not") is checked in both directions: S52/S56/S61
show the constant *must* change, and `shell_character_sumS_one` shows it degenerates correctly
at `c = 1`.

S54, S55, S57, S62 and S64 are the hypothesis-weakening half: `1 ≤ j`, `2^j ∣ alpha_j`,
`v₂ < k`, `a < b` and `1 ≤ k` are each shown to be used, not decorative.

Lemma A's clean block norms at a general shift, added 2026-08-05 (§8).  All 10 fail:

| # | mutation | result |
|---|---|---|
| S68 | `norm_upper_entryS`: modulus `2^{k−d−1}` → `2^{k−d}` | fails |
| S69 | `norm_upper_entryS`: sharp point weakened `2^{k−1} ∣ alpha_d` → `2^{k−2} ∣` | fails |
| S70 | `BentS_eq_zero_of_not_owned`: conclusion `= 0` → `= 1` | fails |
| S71 | `norm_BentS_of_owned`: modulus `(1/2)^d` → `(1/2)^{d+1}` | fails |
| S72 | `norm_BentS_of_owned`: shift oddness weakened `c % 2 = 1` → `c % 2 = c % 2` | fails |
| S73 | `gram_upperS`: Gram diagonal `(1/2)^d` → `(1/4)^d` | fails |
| S74 | `gram_upperS`: diagonal and off-diagonal swapped (`η = η'` → `η ≠ η'`) | fails |
| S75 | `norm_sq_clean_blockS`: the equality sharpened `2^{−d}` → `2^{−(d+1)}` | fails |
| S76 | `norm_clean_block_leS`: bound sharpened `s^d` → `s^{d+1}` | fails |
| S77 | `clean_boundS`: level weakened `3 ≤ k` → `2 ≤ k` | fails |

**S72 is the one that matters for this section.**  §8 is a substitution, so the live worry is
that it might go through *without* the shift being constrained at all — that the `c`-oddness
hypothesis is inert plumbing.  It is not: replaced by a tautology, `inner_chiVec_UendS` no
longer applies.  S71, S73, S75 and S76 pin the constant at each of the four levels it passes
through (`2^{−d}` entry → `4^{−d}` squared → `2^{−d}` Gram → `s^d` operator), so a slip in the
owner count `2^d` cancelling against `(2^{−d})²` could not pass silently.

**S70 and S74 are recorded with their first, failed attempts.**  S70 was first written by
flipping `ξ ∉ ownedBy` to `ξ ∈ ownedBy`, and S74 by changing the off-diagonal `0` to `1`.
Both "failed" — and both failed at *elaboration* (a hypothesis applied as a function; a stuck
coercion), not at any mathematical claim.  They were replaced by the mutations in the table,
which fail on unsolved goals and non-matching branches.  Same lesson as S66/S67 below: **a
mutation that fails for a syntactic reason has tested nothing**, and the only way to know
which kind you have is to read the error.

**S66 and S67 are the orientation trap**, the one that shipped a defect in this corpus before:
the transpose itself, and which index is zeroed.  They cannot be tested from a scratch file —
that file imports the real definition — so they were applied to this file in place and the
whole tree rebuilt on each.

**Both had to be propagated to be worth anything.**  Applied to the definition alone, each
fails one line later at `UcleanS_apply`, which is a `rfl` restatement of the definition and
therefore detects nothing but itself.  Propagated through `UcleanS_apply`, `UcleanS_defect_row`
and `UcleanS_clean_row`, they fail where it counts: inside `inner_chiVec_UendS` (S66 at the
`show`, S67 at the application of `sum_fin_cleanS`), and at `UcleanS_one`, the `c = 1`
specialisation check.  The unpropagated runs are recorded here rather than dropped, because
"the mutation failed" was true of them too and it meant nothing.
-/

import GramIdentity

set_option autoImplicit false

namespace ShiftedOperator

open Finset GapCertificate CountingLemmas TransferOperator

/-!
--------------------------------------------------------------------------------
## §1. The shifted Syracuse map
--------------------------------------------------------------------------------
-/

/-- The Syracuse map with an arbitrary shift: `n ↦ (3n + c) / 2^{v₂(3n+c)}` on odd `n`.
For `c = 1` this is `GapCertificate.syracuse`; see `syracuseS_one`. -/
def syracuseS (c n : ℕ) : ℕ :=
  if n % 2 = 0 then n
  else
    let m := 3 * n + c
    m / (2 ^ v2 m)

/-- At `c = 1` the shifted map is definitionally the original. -/
theorem syracuseS_one (n : ℕ) : syracuseS 1 n = syracuse n := rfl

/-- The odd part of any nonzero natural is odd.  This is `GapCertificate.odd_part_odd` with
the `3x+1` specialisation removed; the original proof never used it. -/
theorem oddPart_odd {n : ℕ} (hn : n ≠ 0) : (n / 2 ^ v2 n) % 2 = 1 := by
  have hdvd : 2 ^ v2 n ∣ n := pow_v2_dvd n hn
  have hfac : n = 2 ^ v2 n * (n / 2 ^ v2 n) := (Nat.mul_div_cancel' hdvd).symm
  by_contra hodd
  have heven : 2 ∣ n / 2 ^ v2 n := by omega
  obtain ⟨t, ht⟩ := heven
  have hstep : 2 ^ (v2 n + 1) ∣ n := by
    refine ⟨t, ?_⟩
    calc n = 2 ^ v2 n * (n / 2 ^ v2 n) := hfac
      _ = 2 ^ v2 n * (2 * t) := by rw [ht]
      _ = 2 ^ (v2 n + 1) * t := by rw [pow_succ]; ring
  exact pow_succ_padicValNat_not_dvd hn hstep

/-- The shifted map lands on an odd residue, for every odd shift.  The parity of `c` enters
nowhere else, which is exactly why the construction is shift-uniform. -/
theorem syracuseS_odd {c n : ℕ} (hc : c % 2 = 1) (hn : n % 2 = 1) :
    syracuseS c n % 2 = 1 := by
  have hne : 3 * n + c ≠ 0 := by omega
  unfold syracuseS
  rw [if_neg (by omega : ¬ n % 2 = 0)]
  exact oddPart_odd hne

/-!
--------------------------------------------------------------------------------
## §2. The shifted transition count and operator
--------------------------------------------------------------------------------
-/

/-- **The shifted transition count.**  `TcountS c k u r` counts the lifts `m < 2^k` of the odd
residue `r` whose shifted-Syracuse image is `≡ u (mod 2^k)`.  Target-first, exactly as
`TransferOperator.Tcount`. -/
def TcountS (c k u r : ℕ) : ℕ :=
  ((range (2 ^ k)).filter (fun m => syracuseS c (r + m * 2 ^ k) % 2 ^ k = u)).card

/-- At `c = 1` the shifted count is the original count. -/
theorem TcountS_one (k u r : ℕ) : TcountS 1 k u r = Tcount k u r := rfl

/-- **The shifted operator `T_k^{(c)}`**, on the `2^{k-1}` odd residues mod `2^k`. -/
noncomputable def TkS (c k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℝ :=
  fun u r => (TcountS c k (od u) (od r) : ℝ) / 2 ^ k

theorem TkS_one (k : ℕ) : TkS 1 k = Tk k := rfl

theorem TkS_nonneg (c k : ℕ) (u r : Fin (2 ^ (k - 1))) : 0 ≤ TkS c k u r := by
  unfold TkS; positivity

/-!
--------------------------------------------------------------------------------
## §2b. Coset uniformity, for a general shift
--------------------------------------------------------------------------------

This is the engine `THEOREM.md` calls CU, and it is the shared foundation of Lemma A.  The
originals in `GapCertificate.lean` are stated for `3x + 1`; the proofs below are the same
arguments with `1` replaced by `c`, and they go through because the only property of the shift
that is ever used is that `3x + c` is even for odd `x`.

`CountingLemmas.cuMap` is already shift-free, which is why the counting half needs no
generalisation at all.
-/

/-- **CU decomposition, general shift.** `3(x + m2^K) + c = 2^v (q₀ + 3m2^{K-v})` with the
bracket odd, where `v = v₂(3x + c) < K`. -/
theorem cu_decompositionS {c : ℕ} (hc : c % 2 = 1) (x m K : ℕ) (hx : x % 2 = 1)
    (hK : v2 (3 * x + c) < K) :
    3 * (x + m * 2 ^ K) + c =
      2 ^ v2 (3 * x + c) *
        ((3 * x + c) / 2 ^ v2 (3 * x + c) + 3 * m * 2 ^ (K - v2 (3 * x + c))) ∧
    ((3 * x + c) / 2 ^ v2 (3 * x + c) + 3 * m * 2 ^ (K - v2 (3 * x + c))) % 2 = 1 := by
  set v := v2 (3 * x + c) with hv
  set q0 := (3 * x + c) / 2 ^ v with hq0
  have hne : 3 * x + c ≠ 0 := by omega
  have hdvd : 2 ^ v ∣ 3 * x + c := pow_v2_dvd _ hne
  have hfac : 3 * x + c = 2 ^ v * q0 := (Nat.mul_div_cancel' hdvd).symm
  have hpow : (2 : ℕ) ^ K = 2 ^ v * 2 ^ (K - v) := by
    rw [← pow_add]; congr 1; omega
  have hsplit : 3 * (x + m * 2 ^ K) + c = 2 ^ v * (q0 + 3 * m * 2 ^ (K - v)) := by
    calc 3 * (x + m * 2 ^ K) + c
        = (3 * x + c) + 3 * m * 2 ^ K := by ring
      _ = 2 ^ v * q0 + 3 * m * (2 ^ v * 2 ^ (K - v)) := by rw [hfac, hpow]
      _ = 2 ^ v * (q0 + 3 * m * 2 ^ (K - v)) := by ring
  refine ⟨hsplit, ?_⟩
  have hq0odd : q0 % 2 = 1 := oddPart_odd hne
  have heven : (2 : ℕ) ∣ 3 * m * 2 ^ (K - v) :=
    (dvd_pow_self 2 (by omega : K - v ≠ 0)).mul_left (3 * m)
  omega

/-- **CU, valuation frozen, general shift.** -/
theorem cu_valuation_frozenS {c : ℕ} (hc : c % 2 = 1) (x m K : ℕ) (hx : x % 2 = 1)
    (hK : v2 (3 * x + c) < K) :
    v2 (3 * (x + m * 2 ^ K) + c) = v2 (3 * x + c) := by
  obtain ⟨hsplit, hodd⟩ := cu_decompositionS hc x m K hx hK
  rw [hsplit]
  exact v2_two_pow_mul_odd _ _ hodd

/-- **CU, the shifted Syracuse step is affine in the lift.** For odd `x` with
`v₂(3x + c) < K`, `Syr_c(x + m2^K) = (3x+c)/2^v + 3m2^{K-v}`.

This is the statement Lemma A is built on, and `c` appears in it only through `v` and `q₀`. -/
theorem cu_syracuse_affineS {c : ℕ} (hc : c % 2 = 1) (x m K : ℕ) (hx : x % 2 = 1)
    (hK : v2 (3 * x + c) < K) :
    syracuseS c (x + m * 2 ^ K) =
      (3 * x + c) / 2 ^ v2 (3 * x + c) + 3 * m * 2 ^ (K - v2 (3 * x + c)) := by
  obtain ⟨hsplit, hodd⟩ := cu_decompositionS hc x m K hx hK
  have hK1 : 1 ≤ K := by omega
  have hlift_odd : (x + m * 2 ^ K) % 2 = 1 := by
    have h2 : (2 : ℕ) ∣ m * 2 ^ K := (dvd_pow_self 2 (by omega : K ≠ 0)).mul_left m
    omega
  unfold syracuseS
  rw [if_neg (by omega)]
  show (3 * (x + m * 2 ^ K) + c) / 2 ^ v2 (3 * (x + m * 2 ^ K) + c) = _
  rw [cu_valuation_frozenS hc x m K hx hK, hsplit,
    Nat.mul_div_cancel_left _ (by positivity : (0:ℕ) < 2 ^ v2 (3 * x + c))]

/-- **Specialisation check.**  At `c = 1` the shifted affine step is exactly
`GapCertificate.cu_syracuse_affine`, so the generalisation changes nothing at the old shift.
Stated as an equality of the two right-hand sides, discharged by `syracuseS_one`. -/
theorem cu_syracuse_affineS_one (x m K : ℕ) (hx : x % 2 = 1) (hK : v2 (3 * x + 1) < K) :
    syracuseS 1 (x + m * 2 ^ K) = syracuse (x + m * 2 ^ K) := by
  rw [syracuseS_one]

example (x m K : ℕ) (hx : x % 2 = 1) (hK : v2 (3 * x + 1) < K) :
    syracuse (x + m * 2 ^ K)
      = (3 * x + 1) / 2 ^ v2 (3 * x + 1) + 3 * m * 2 ^ (K - v2 (3 * x + 1)) := by
  rw [← cu_syracuse_affineS_one x m K hx hK]
  exact cu_syracuse_affineS (by norm_num) x m K hx hK

/-- **THE CU FIBRE COUNT, general shift.**  For odd `x` with `v = v₂(3x + c) < K`, the lifts
`m < 2^K` sharing a given shifted-Syracuse image mod `2^K` number exactly `2^{K-v}`.

This is the counting form of coset uniformity and the direct input to Lemma A.  Note that
`CountingLemmas.cu_fibre_card`, which does the actual counting, is shift-free — all the shift
does is fix `v` and `q₀`. -/
theorem cu_syracuse_fibre_cardS {c x K : ℕ} (hc : c % 2 = 1) (hx : x % 2 = 1)
    (hK : v2 (3 * x + c) < K) (m0 : ℕ) :
    ((range (2 ^ K)).filter
        (fun m => syracuseS c (x + m * 2 ^ K) % 2 ^ K
                    = syracuseS c (x + m0 * 2 ^ K) % 2 ^ K)).card
      = 2 ^ (K - v2 (3 * x + c)) := by
  set v := v2 (3 * x + c) with hv
  set q0 := (3 * x + c) / 2 ^ v with hq0
  have hcond : ∀ m, (syracuseS c (x + m * 2 ^ K) % 2 ^ K
      = syracuseS c (x + m0 * 2 ^ K) % 2 ^ K) ↔ cuMap K v m = cuMap K v m0 := by
    intro m
    rw [cu_syracuse_affineS hc x m K hx hK, cu_syracuse_affineS hc x m0 K hx hK]
    unfold cuMap
    constructor
    · intro h
      have hmod : Nat.ModEq (2 ^ K) (q0 + 3 * m * 2 ^ (K - v)) (q0 + 3 * m0 * 2 ^ (K - v)) := h
      have h2 : (3 * m * 2 ^ (K - v)) % 2 ^ K = (3 * m0 * 2 ^ (K - v)) % 2 ^ K :=
        Nat.ModEq.add_left_cancel' q0 hmod
      calc (3 * 2 ^ (K - v) * m) % 2 ^ K
          = (3 * m * 2 ^ (K - v)) % 2 ^ K := by ring_nf
        _ = (3 * m0 * 2 ^ (K - v)) % 2 ^ K := h2
        _ = (3 * 2 ^ (K - v) * m0) % 2 ^ K := by ring_nf
    · intro h
      have h2 : (3 * m * 2 ^ (K - v)) % 2 ^ K = (3 * m0 * 2 ^ (K - v)) % 2 ^ K := by
        calc (3 * m * 2 ^ (K - v)) % 2 ^ K
            = (3 * 2 ^ (K - v) * m) % 2 ^ K := by ring_nf
          _ = (3 * 2 ^ (K - v) * m0) % 2 ^ K := h
          _ = (3 * m0 * 2 ^ (K - v)) % 2 ^ K := by ring_nf
      exact Nat.ModEq.add_left q0 h2
  have hrw : (range (2 ^ K)).filter
      (fun m => syracuseS c (x + m * 2 ^ K) % 2 ^ K
                  = syracuseS c (x + m0 * 2 ^ K) % 2 ^ K)
      = (range (2 ^ K)).filter (fun m => cuMap K v m = cuMap K v m0) := by
    apply filter_congr
    intro m _
    exact hcond m
  rw [hrw]
  exact cu_fibre_card (le_of_lt hK) m0

/-!
--------------------------------------------------------------------------------
## §2c. Odd multipliers pass through the odd part — the key to Lemma B at `a = 3`
--------------------------------------------------------------------------------

Calibration (`calibrate_lemmaB_shift.py`) showed that Lemma B for a general odd shift is a
**three-case** problem, not an infinite family: the offset `a = (3r* + c)/2^k` only ever takes
the values `1, 2, 3`, and the collision count depends on `a` alone.  `CollisionBound.lean`
already covers the cases arising at `c = 1`.  The one new case is `a = 3`, and there

```
    coll(k, 3) = 3·2^k − 2      exactly, for every k
```

so the constant `3` is **sharp** — margin exactly `2` at every scale.  A proof that leans on
the *growing* margin available at `c = 1` will fail here.

### The route, in the sharpened form

`coll(k,3)` counts *ordered pairs* of lifts with equal image.  Two reductions kill the shift and
then the modulus:

1. `oddPart(3 + 3m) = 3·oddPart(m+1)`, because `3` is odd  — **`oddPart_mul_odd` below**;
2. multiplication by `3` is a bijection mod `2^k`, so it drops out of a count.

What is left, after `n = m+1`, is

```
    coll(k,3) = #{ (n, n') ∈ [1, 2^k]² : oddPart n = oddPart n' }
```

with **no modulus anywhere** — `oddPart n < 2^k` for `n ≤ 2^k`, so the reduction is vacuous.  The
shifted problem has become a shift-free one.

Counting that by odd part, with `c_q = #{ j : q·2^j ≤ 2^k }`, the induction step splits into
three pieces that are each immediate:

```
    P(k+1) = P(k) + 2·(Σ_q c_q) + #{odd q ≤ 2^k} + #{odd q ∈ (2^k, 2^{k+1})}
           = P(k) + 2·2^k + 2^{k-1} + 2^{k-1}
           = P(k) + 3·2^k
```

with `P(1) = 4`.  That telescopes straight to `P(k) + 2 = 3·2^k`.

Every line above was verified numerically (`k = 1..13`) before being written down.

**The `a = 3` case is complete as of 2026-08-05**, end to end and sorry-free:

* reduction 1 — `oddPart_mul_odd`, `oddPart_three_add`;
* reduction 2 — `mul_three_mod_cancel`, plus `oddPart_lt_two_pow` making the modulus vacuous;
  together, `fibVal3_eq_iff`;
* the pair count as a `Finset` cardinality — `sameOddPartCount`, `pairCount`;
* the dyadic-block bijection and the singleton fibre — `oddPart_injOn_block`,
  `exists_shift_into_block`, `existsUnique_in_block`, `block_fibre_card`;
* the three block counts summed into the recurrence — `pairCount_double`;
* the telescoping — `pair_count_closed`, `pairCount_pow_closed`;
* the conclusion — **`coll3_closed : coll3 k + 2 = 3 * 2 ^ k`** for `k ≥ 1`, with `coll3_le` in
  the form Lemma B consumes.

`coll3` is computable and its `#eval`s reproduce the calibration values `4, 10, 22, 46, 94, 190`
exactly, so the theorem is about the object the Python measured and not a convenient proxy.

**What this does NOT mean, and the one gap to name precisely.**  `a = 3` is *one of the three*
offset cases, and it is the only one that was open — `CollisionBound.lean` covers the cases
arising at `c = 1`.  Closing it does not give a certificate for general `c`:

* **`fibVal3` is not yet linked to the shifted Syracuse map by a theorem.**  At `c = 1`,
  `CollisionBound.syracuse_defect_fibre` *proves* that the AP model `oddPart(a + 3m) mod 2^k` is
  the true fibre of `syracuse` over the true `r*` — the model is a theorem there, not a
  definition, and that is deliberate: it is the corpus's failure mode (2), the right-looking
  theorem about the wrong object.  **The general-`c` analogue is not proved here.**  That the
  offset `a = (3r* + c)/2^k` takes only the values `1, 2, 3` is a *calibration finding*
  (`calibrate_lemmaB_shift.py`), not a Lean theorem.  Until the analogue of
  `syracuse_defect_fibre` exists for `rstarS`, `coll3_closed` is a complete theorem about the
  `a = 3` AP model, and the identification of that model with the `3x+c` defect fibre rests on
  Python.
* Lemma A's block norms for general `c` are still only calibrated (exactly `2^{-(b-a)/2}` to
  `1e-14`, every odd `c`, `k = 4..8`), not proved.
* The assembly is not done.

`rstarS_spec` gives the ingredient the first bullet needs (`3·rstarS c k + c ≡ 0 mod 2^k`); what
is missing is the valuation statement — which power of `2` exactly divides `3r* + c` — since it
is that exponent, not the residue, that pins `a`.

**This file still does not prove the `3x-1` certificate, and nothing in it should be cited as
doing so.**
-/

/-- **An odd multiplier passes through the odd part.**  For odd `d` and `n ≠ 0`,
`oddPart (d * n) = d * oddPart n`.

This is why `a = 3` reduces to a shift-free counting problem, and it is the only property of
`3` involved — the same "3 is odd" that the whole development runs on. -/
theorem oddPart_mul_odd {d n : ℕ} (hd : d % 2 = 1) (hn : n ≠ 0) :
    (d * n) / 2 ^ v2 (d * n) = d * (n / 2 ^ v2 n) := by
  have hd0 : d ≠ 0 := by omega
  have hdn : d * n ≠ 0 := Nat.mul_ne_zero hd0 hn
  have hvd : v2 d = 0 := v2_odd_mod d hd
  have hv : v2 (d * n) = v2 n := by
    unfold v2 at *
    rw [padicValNat.mul hd0 hn, hvd, zero_add]
  rw [hv, Nat.mul_div_assoc _ (pow_v2_dvd n hn)]

/-- The instance the `a = 3` case needs: `oddPart (3 + 3m) = 3 * oddPart (m + 1)`. -/
theorem oddPart_three_add {m : ℕ} :
    (3 + 3 * m) / 2 ^ v2 (3 + 3 * m) = 3 * ((m + 1) / 2 ^ v2 (m + 1)) := by
  have h : 3 + 3 * m = 3 * (m + 1) := by ring
  rw [h]
  exact oddPart_mul_odd (by norm_num) (by omega)

/-!
### The recurrence, by a dyadic-block bijection

Expanding `Σ_q c_q^2` is not the way in.  Split `[1, 2^{k+1}]` as `A ∪ B` with `A = [1, 2^k]`
and `B = (2^k, 2^{k+1}]`, and count the *new* same-odd-part pairs:

```
    A×B  =  2^k ,      B×A  =  2^k ,      B×B  =  2^k          (measured, k = 1..11)
```

all three blocks equal, giving `3·2^k` directly.  Every one of them follows from a single fact:

> **`oddPart` is a bijection from the dyadic block `(N, 2N]` onto the odd numbers `≤ 2N`.**

`B×B` is then the diagonal only, so it contributes `|B|`; and `A×B` contributes `1` per element
of `A`, so it contributes `|A|`.  No fibre-size formula appears anywhere.

The two halves of that fact are `oddPart_injOn_block` (injectivity — the block has ratio exactly
`2`, so two shifts of one odd number cannot both land in it) and `exists_shift_into_block`
(surjectivity — take the largest admissible shift).  Both are below.
-/

/-- `2 ^ v₂ n * oddPart n = n`. -/
theorem oddPart_factor {n : ℕ} (hn : n ≠ 0) : 2 ^ v2 n * (n / 2 ^ v2 n) = n :=
  Nat.mul_div_cancel' (pow_v2_dvd n hn)

/-- **Injectivity on a dyadic block.**  Two elements of `(N, 2N]` with the same odd part are
equal — the block has ratio exactly `2`, so it cannot contain both `q·2^i` and `q·2^j`. -/
theorem oddPart_injOn_block {N m n : ℕ} (hm1 : N < m) (hm2 : m ≤ 2 * N)
    (hn1 : N < n) (hn2 : n ≤ 2 * N) (h : m / 2 ^ v2 m = n / 2 ^ v2 n) : m = n := by
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  obtain ⟨q, hq⟩ : ∃ q, m / 2 ^ v2 m = q := ⟨_, rfl⟩
  have hm : 2 ^ v2 m * q = m := by rw [← hq]; exact oddPart_factor hm0
  have hn : 2 ^ v2 n * q = n := by rw [← hq, h]; exact oddPart_factor hn0
  rcases Nat.le_total (v2 m) (v2 n) with hv | hv
  · rcases Nat.eq_or_lt_of_le hv with he | hlt
    · rw [← hm, ← hn, he]
    · exfalso
      have hp : (2 : ℕ) ^ (v2 m + 1) ≤ 2 ^ v2 n := Nat.pow_le_pow_right (by norm_num) hlt
      have h2 : 2 * m ≤ n := by
        calc 2 * m = 2 * (2 ^ v2 m * q) := by rw [hm]
          _ = 2 ^ (v2 m + 1) * q := by rw [pow_succ]; ring
          _ ≤ 2 ^ v2 n * q := Nat.mul_le_mul_right _ hp
          _ = n := hn
      omega
  · rcases Nat.eq_or_lt_of_le hv with he | hlt
    · rw [← hm, ← hn, he]
    · exfalso
      have hp : (2 : ℕ) ^ (v2 n + 1) ≤ 2 ^ v2 m := Nat.pow_le_pow_right (by norm_num) hlt
      have h2 : 2 * n ≤ m := by
        calc 2 * n = 2 * (2 ^ v2 n * q) := by rw [hn]
          _ = 2 ^ (v2 n + 1) * q := by rw [pow_succ]; ring
          _ ≤ 2 ^ v2 m * q := Nat.mul_le_mul_right _ hp
          _ = m := hm
      omega

/-- **Surjectivity onto the odds below.**  Every `q` with `0 < q ≤ 2N` has a shift landing in
the block `(N, 2N]`: take the largest `j` with `q·2^j ≤ 2N`. -/
theorem exists_shift_into_block {N q : ℕ} (hN : 0 < N) (hq : 0 < q) (hqle : q ≤ 2 * N) :
    ∃ j, N < q * 2 ^ j ∧ q * 2 ^ j ≤ 2 * N := by
  classical
  set S := (Finset.range (2 * N + 1)).filter (fun j => q * 2 ^ j ≤ 2 * N) with hS
  have hne : S.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    simpa using hqle
  obtain ⟨j, hjmem, hjmax⟩ := S.exists_max_image id hne
  have hjf := Finset.mem_filter.mp hjmem
  refine ⟨j, ?_, hjf.2⟩
  by_contra hle
  push_neg at hle
  have hnext : q * 2 ^ (j + 1) ≤ 2 * N := by
    calc q * 2 ^ (j + 1) = 2 * (q * 2 ^ j) := by ring
      _ ≤ 2 * N := by omega
  have hbound : j + 1 < 2 * N + 1 := by
    have h1 : (2 : ℕ) ^ (j + 1) ≤ q * 2 ^ (j + 1) := Nat.le_mul_of_pos_left _ hq
    have h2 : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
    omega
  have hj1 : j + 1 ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbound, hnext⟩
  have := hjmax (j + 1) hj1
  simp only [id] at this
  omega

/-- The odd part of `2^j * q` is `q`, for odd `q`. -/
theorem oddPart_two_pow_mul {q j : ℕ} (hq : q % 2 = 1) :
    (2 ^ j * q) / 2 ^ v2 (2 ^ j * q) = q := by
  rw [v2_two_pow_mul_odd j q hq]
  exact Nat.mul_div_cancel_left q (Nat.two_pow_pos j)

/-- **THE BRIDGE.**  Every positive `n` whose odd part is at most `2N` has *exactly one*
partner in the dyadic block `(N, 2N]` sharing its odd part.

This single statement gives both block counts the recurrence needs: applied to `n` in `A` it says
each element of `A` has exactly one partner in `B`, so the `A×B` block has `|A|` pairs; applied
to `n \in B` it says the only partner of `n` in `B` is `n` itself, so `B×B` is the diagonal and
has `|B|` pairs. -/
theorem existsUnique_in_block {N n : ℕ} (hN : 0 < N) (hn : n ≠ 0)
    (hle : n / 2 ^ v2 n ≤ 2 * N) :
    ∃! n', (N < n' ∧ n' ≤ 2 * N) ∧ n' / 2 ^ v2 n' = n / 2 ^ v2 n := by
  have hq : (n / 2 ^ v2 n) % 2 = 1 := oddPart_odd hn
  have hqpos : 0 < n / 2 ^ v2 n :=
    Nat.pos_of_ne_zero (by intro hz; rw [hz] at hq; simp at hq)
  obtain ⟨j, hj1, hj2⟩ := exists_shift_into_block hN hqpos hle
  refine ⟨(n / 2 ^ v2 n) * 2 ^ j, ⟨⟨hj1, hj2⟩, ?_⟩, ?_⟩
  · rw [mul_comm]; exact oddPart_two_pow_mul hq
  · rintro y ⟨⟨hy1, hy2⟩, hy3⟩
    refine oddPart_injOn_block hy1 hy2 hj1 hj2 ?_
    rw [hy3, mul_comm, oddPart_two_pow_mul hq]

/-- **The block fibre is a singleton.**  The `Finset` form of `existsUnique_in_block`, and the
statement the two block counts are summed from.

For any positive `n` whose odd part is at most `2N`, exactly one element of the dyadic block
`(N, 2N]` shares its odd part. -/
theorem block_fibre_card {N n : ℕ} (hN : 0 < N) (hn : n ≠ 0)
    (hle : n / 2 ^ v2 n ≤ 2 * N) :
    ((Finset.Ioc N (2 * N)).filter
        (fun b => b / 2 ^ v2 b = n / 2 ^ v2 n)).card = 1 := by
  classical
  obtain ⟨b, hb, huniq⟩ := existsUnique_in_block hN hn hle
  rw [Finset.card_eq_one]
  refine ⟨b, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hx1, hx2⟩, hx3⟩
    exact huniq x ⟨⟨hx1, hx2⟩, hx3⟩
  · rintro rfl
    exact ⟨⟨hb.1.1, hb.1.2⟩, hb.2⟩

/-- **The `B×B` block is the diagonal.**  Specialising `block_fibre_card` to `n` already in the
block: its only partner there is itself.  Summed over the block this gives `|B|` pairs. -/
theorem block_fibre_card_self {N n : ℕ} (hN : 0 < N) (hn1 : N < n) (hn2 : n ≤ 2 * N) :
    ((Finset.Ioc N (2 * N)).filter
        (fun b => b / 2 ^ v2 b = n / 2 ^ v2 n)).card = 1 := by
  refine block_fibre_card hN (by omega) ?_
  calc n / 2 ^ v2 n ≤ n := Nat.div_le_self _ _
    _ ≤ 2 * N := hn2

/-- **The `A×B` fibre.**  Every `n` in `[1, N]` has exactly one partner in the block, because
its odd part is at most `n ≤ N ≤ 2N`.  Summed over `[1, N]` this gives `|A|` pairs. -/
theorem block_fibre_card_lower {N n : ℕ} (hN : 0 < N) (hn1 : 1 ≤ n) (hn2 : n ≤ N) :
    ((Finset.Ioc N (2 * N)).filter
        (fun b => b / 2 ^ v2 b = n / 2 ^ v2 n)).card = 1 := by
  refine block_fibre_card hN (by omega) ?_
  calc n / 2 ^ v2 n ≤ n := Nat.div_le_self _ _
    _ ≤ 2 * N := by omega

/-- **The telescoping step of the `a = 3` argument.**  Any `P` satisfying the pair-count
recurrence `P(k+1) = P(k) + 3·2^k` with `P 1 = 4` is `3·2^k − 2`.

Stated as `P k + 2 = 3 * 2 ^ k` rather than with a truncated subtraction, which is both cleaner
and avoids the `Nat` subtraction trap entirely.

This is the *last* step of the `a = 3` case; what remains is to prove that the actual collision
count satisfies this recurrence. -/
theorem pair_count_closed {P : ℕ → ℕ} (hbase : P 1 = 4)
    (hrec : ∀ j, 1 ≤ j → P (j + 1) = P j + 3 * 2 ^ j) :
    ∀ k, 1 ≤ k → P k + 2 = 3 * 2 ^ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · -- n + 1 = 1
      have hn : n = 0 := by omega
      subst hn
      rw [hbase]; norm_num
    · have hn : 1 ≤ n := by omega
      have := ih hn
      rw [hrec n hn, pow_succ]
      omega

/-- Sanity: the closed form does give the measured values `4, 10, 22, 46, 94`. -/
example : (3 : ℕ) * 2 ^ 1 - 2 = 4 := by norm_num
example : (3 : ℕ) * 2 ^ 3 - 2 = 22 := by norm_num
example : (3 : ℕ) * 2 ^ 6 - 2 = 190 := by norm_num

/-!
### The pair count itself, and the recurrence it satisfies

The three block lemmas above are pointwise fibre statements; the count they are summed into is
defined here.  `sameOddPartCount S T` is the number of *ordered* pairs in `S × T` with equal odd
part, and the whole recurrence is three applications of the block lemmas plus one commutation.

The recurrence `pairCount (2N) = pairCount N + 3N` is proved for **every** `N ≥ 1`, not only for
powers of two — the dyadic block `(N, 2N]` never needed `N` to be a power of `2`.  Calibrated for
`N = 1..399` before being stated.
-/

/-- **The ordered-pair count with equal odd parts**, over a product of two finite sets. -/
def sameOddPartCount (S T : Finset ℕ) : ℕ :=
  ((S ×ˢ T).filter (fun p => p.1 / 2 ^ v2 p.1 = p.2 / 2 ^ v2 p.2)).card

/-- The pair count as a sum of fibre cardinalities — the form the block lemmas plug into. -/
theorem sameOddPartCount_eq_sum (S T : Finset ℕ) :
    sameOddPartCount S T
      = ∑ a ∈ S, (T.filter (fun b => b / 2 ^ v2 b = a / 2 ^ v2 a)).card := by
  classical
  unfold sameOddPartCount
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun b _ => by simp [eq_comm]

/-- Equal-odd-part is symmetric, so the count is.  This is what gives `B×A` from `A×B` — there
is no pointwise fibre statement for `B×A` (an element of `B` whose odd part exceeds `N` has *no*
partner in `A`, and one whose odd part is small has several). -/
theorem sameOddPartCount_comm (S T : Finset ℕ) :
    sameOddPartCount S T = sameOddPartCount T S := by
  classical
  rw [sameOddPartCount_eq_sum, sameOddPartCount_eq_sum]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by simp [eq_comm]

/-- Splitting the *first* argument along a disjoint union.  With `sameOddPartCount_comm` this is
the only splitting lemma needed. -/
theorem sameOddPartCount_union_left {S T : Finset ℕ} (U : Finset ℕ) (h : Disjoint S T) :
    sameOddPartCount (S ∪ T) U = sameOddPartCount S U + sameOddPartCount T U := by
  simp only [sameOddPartCount_eq_sum]
  exact Finset.sum_union h

/-- **The pair count `P(N)`**: ordered pairs in `[1,N]²` with equal odd part.  At `N = 2^k` this
is exactly the `a = 3` collision count; see `coll3_eq_pairCount`. -/
def pairCount (N : ℕ) : ℕ := sameOddPartCount (Finset.Icc 1 N) (Finset.Icc 1 N)

theorem Icc_split_block (N : ℕ) :
    Finset.Icc 1 (2 * N) = Finset.Icc 1 N ∪ Finset.Ioc N (2 * N) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
  omega

theorem Icc_disjoint_block (N : ℕ) : Disjoint (Finset.Icc 1 N) (Finset.Ioc N (2 * N)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_Icc] at ha
  simp only [Finset.mem_Ioc] at hb
  omega

/-- **The `A×B` block has `|A| = N` pairs.**  Each `n ∈ [1,N]` has exactly one partner in the
block `(N, 2N]` — `block_fibre_card_lower`, summed. -/
theorem sameOddPartCount_lower_block {N : ℕ} (hN : 0 < N) :
    sameOddPartCount (Finset.Icc 1 N) (Finset.Ioc N (2 * N)) = N := by
  rw [sameOddPartCount_eq_sum,
    Finset.sum_congr rfl (fun a ha => block_fibre_card_lower hN
      (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2)]
  simp

/-- **The `B×B` block is the diagonal, `|B| = N` pairs.**  `block_fibre_card_self`, summed. -/
theorem sameOddPartCount_block_block {N : ℕ} (hN : 0 < N) :
    sameOddPartCount (Finset.Ioc N (2 * N)) (Finset.Ioc N (2 * N)) = N := by
  rw [sameOddPartCount_eq_sum,
    Finset.sum_congr rfl (fun a ha => block_fibre_card_self hN
      (Finset.mem_Ioc.mp ha).1 (Finset.mem_Ioc.mp ha).2)]
  simp
  omega

/-- **THE RECURRENCE.**  `P(2N) = P(N) + 3N` — the `A×B`, `B×A` and `B×B` blocks each contribute
exactly `N`.  Holds for every `N ≥ 1`; nothing here needs `N` to be a power of two. -/
theorem pairCount_double {N : ℕ} (hN : 0 < N) :
    pairCount (2 * N) = pairCount N + 3 * N := by
  classical
  unfold pairCount
  rw [Icc_split_block N, sameOddPartCount_union_left _ (Icc_disjoint_block N)]
  rw [sameOddPartCount_comm (Finset.Icc 1 N) (Finset.Icc 1 N ∪ Finset.Ioc N (2 * N)),
    sameOddPartCount_comm (Finset.Ioc N (2 * N)) (Finset.Icc 1 N ∪ Finset.Ioc N (2 * N)),
    sameOddPartCount_union_left _ (Icc_disjoint_block N),
    sameOddPartCount_union_left _ (Icc_disjoint_block N)]
  rw [sameOddPartCount_comm (Finset.Ioc N (2 * N)) (Finset.Icc 1 N),
    sameOddPartCount_lower_block hN, sameOddPartCount_block_block hN]
  ring

/-- The base case `P(2) = 4`: on `{1,2}` every ordered pair collides, both odd parts being `1`. -/
theorem pairCount_two : pairCount 2 = 4 := by
  classical
  have hv1 : v2 1 = 0 := v2_odd_mod 1 (by norm_num)
  have hv2 : v2 2 = 1 := by
    have h := v2_two_pow_mul_odd 1 1 (by norm_num)
    simpa using h
  unfold pairCount sameOddPartCount
  have hall : (Finset.Icc 1 2 ×ˢ Finset.Icc 1 2).filter
      (fun p => p.1 / 2 ^ v2 p.1 = p.2 / 2 ^ v2 p.2) = Finset.Icc 1 2 ×ˢ Finset.Icc 1 2 := by
    apply Finset.filter_true_of_mem
    rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hp
    interval_cases a <;> interval_cases b <;> simp [hv1, hv2]
  rw [hall, Finset.card_product]
  simp

/-- **The closed form of the pair count at powers of two**: `P(2^k) + 2 = 3·2^k`.
Base `pairCount_two`, step `pairCount_double`, telescoped by `pair_count_closed`. -/
theorem pairCount_pow_closed {k : ℕ} (hk : 1 ≤ k) : pairCount (2 ^ k) + 2 = 3 * 2 ^ k := by
  refine pair_count_closed (P := fun j => pairCount (2 ^ j)) ?_ ?_ k hk
  · simpa using pairCount_two
  · intro j _
    show pairCount (2 ^ (j + 1)) = pairCount (2 ^ j) + 3 * 2 ^ j
    have hp : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    rw [hp, pairCount_double (Nat.two_pow_pos j)]

/-!
### Reduction 2: the `×3` drops out, and the `a = 3` collision count in closed form

`fibVal3` is the `a = 3` fibre value, in exactly the shape `CollisionBound.fibVal` has at
`a ∈ {1,2}`: the odd part of `a + 3m`, reduced mod `2^k`.  Two facts collapse it:

* `oddPart (3 + 3m) = 3 · oddPart (m+1)` — `oddPart_three_add`, reduction 1;
* `×3` is injective mod `2^k` — `mul_three_mod_cancel`, reduction 2;

and then the modulus is vacuous, because the odd part of anything in `[1, 2^k]` is *strictly*
below `2^k` (`oddPart_lt_two_pow`: it is odd and at most `2^k`, and `2^k` is even for `k ≥ 1`).
So the shifted, moduled count is literally the shift-free, modulus-free `pairCount`.
-/

/-- The odd part of anything in `[1, 2^k]` is strictly below `2^k`, for `k ≥ 1` — so reducing an
odd part mod `2^k` does nothing.  This is what makes the modulus vacuous. -/
theorem oddPart_lt_two_pow {k n : ℕ} (hk : 1 ≤ k) (hn : n ≠ 0) (hle : n ≤ 2 ^ k) :
    n / 2 ^ v2 n < 2 ^ k := by
  have hq : (n / 2 ^ v2 n) % 2 = 1 := oddPart_odd hn
  have h1 : n / 2 ^ v2 n ≤ 2 ^ k := le_trans (Nat.div_le_self _ _) hle
  have h2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-- **Reduction 2.**  Multiplication by `3` is injective mod `2^k`, so it drops out of the
count.  The only arithmetic input is `gcd 3 (2^k) = 1`. -/
theorem mul_three_mod_cancel {k x y : ℕ} (h : (3 * x) % 2 ^ k = (3 * y) % 2 ^ k) :
    x % 2 ^ k = y % 2 ^ k := by
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by decide)
  exact Nat.ModEq.cancel_left_of_coprime hcop.symm h

/-- **The `a = 3` fibre value**, in the same shape `CollisionBound.fibVal` has at `a ∈ {1,2}`:
`Syr(r* + m·2^k) = oddPart (a + 3m) mod 2^k`. -/
def fibVal3 (k m : ℕ) : ℕ := ((3 + 3 * m) / 2 ^ v2 (3 + 3 * m)) % 2 ^ k

/-- **The collision pairs at `a = 3`**, in the same shape as `CollisionBound.collPairs`. -/
def collPairs3 (k : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2 ^ k)) ×ˢ (range (2 ^ k))).filter (fun p => fibVal3 k p.1 = fibVal3 k p.2)

/-- **`coll(k, 3)`** — the ordered collision count of the `a = 3` defect fibre. -/
def coll3 (k : ℕ) : ℕ := (collPairs3 k).card

/-- **Both reductions, in one step.**  Two lifts collide at `a = 3` iff `m+1` and `m'+1` have the
same odd part — no shift, no modulus. -/
theorem fibVal3_eq_iff {k m m' : ℕ} (hk : 1 ≤ k) (hm : m < 2 ^ k) (hm' : m' < 2 ^ k) :
    fibVal3 k m = fibVal3 k m'
      ↔ (m + 1) / 2 ^ v2 (m + 1) = (m' + 1) / 2 ^ v2 (m' + 1) := by
  unfold fibVal3
  rw [oddPart_three_add, oddPart_three_add]
  constructor
  · intro h
    have hc := mul_three_mod_cancel h
    rwa [Nat.mod_eq_of_lt (oddPart_lt_two_pow hk (by omega) (by omega)),
      Nat.mod_eq_of_lt (oddPart_lt_two_pow hk (by omega) (by omega))] at hc
  · intro h; rw [h]

/-- **The `a = 3` collision count IS the shift-free pair count**, via `m ↦ m + 1`. -/
theorem coll3_eq_pairCount {k : ℕ} (hk : 1 ≤ k) : coll3 k = pairCount (2 ^ k) := by
  classical
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  unfold coll3 collPairs3 pairCount sameOddPartCount
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext p
  obtain ⟨x, y⟩ := p
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_Icc, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl, rfl⟩
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, (fibVal3_eq_iff hk ha hb).mp hab⟩
  · rintro ⟨⟨⟨hx1, hx2⟩, hy1, hy2⟩, hxy⟩
    refine ⟨x - 1, y - 1, ⟨⟨by omega, by omega⟩, ?_⟩, by omega, by omega⟩
    refine (fibVal3_eq_iff hk (by omega) (by omega)).mpr ?_
    have hx : x - 1 + 1 = x := by omega
    have hy : y - 1 + 1 = y := by omega
    rw [hx, hy]
    exact hxy

/-- **THE `a = 3` CASE OF LEMMA B, CLOSED.**  `coll(k,3) + 2 = 3·2^k` — exactly, for every
`k ≥ 1`.  The constant `3` is therefore **sharp** at `a = 3`: the margin is exactly `2` at every
scale, and no later step may lean on slack that grows. -/
theorem coll3_closed {k : ℕ} (hk : 1 ≤ k) : coll3 k + 2 = 3 * 2 ^ k := by
  rw [coll3_eq_pairCount hk]
  exact pairCount_pow_closed hk

/-- The bound in the form Lemma B consumes. -/
theorem coll3_le {k : ℕ} (hk : 1 ≤ k) : coll3 k ≤ 3 * 2 ^ k := by
  have := coll3_closed hk
  omega

/-!
**Satisfiability witnesses.**  `coll3` is computable, so these evaluate the very definition the
theorem above is about — proof that it is not vacuous and not a convenient proxy.  The values are
`3·2^k − 2` and match `calibrate_lemmaB_shift.py` exactly.  Deliberately `#eval` and not
`theorem`: a `decide` on these would be a slow re-run of the same computation, not evidence.
-/

#eval coll3 1   -- 4    = 3·2 − 2
#eval coll3 2   -- 10   = 3·4 − 2
#eval coll3 3   -- 22   = 3·8 − 2
#eval coll3 4   -- 46   = 3·16 − 2
#eval coll3 5   -- 94   = 3·32 − 2
#eval coll3 6   -- 190  = 3·64 − 2

#eval pairCount 12   -- 32: the recurrence needs no power of two (P 24 = 32 + 36 = 68)
#eval pairCount 24   -- 68

/-!
--------------------------------------------------------------------------------
## §2e. The SB bijection is shift-independent
--------------------------------------------------------------------------------

Step 1 of `BRIEF_LEMMA_A_GENERAL_SHIFT.md` (private repo): the foundation the shifted shell
character sum needs.  **Lemma SB — `ψ(r) = (3r+c)/2^j mod 2^{k-j}` is a bijection from the
valuation shell onto the odd residues mod `2^{k-j}` — holds for every odd shift `c`**, with the
same two-line arithmetic as at `c = 1`.

Two things make this cheap, and both were checked before any of it was written:

* **injectivity is shift-free by cancellation.**  `3r + c = 2^j q` and `3r' + c = 2^j q'` give
  `3(r − r') = 2^j (q − q')`; the shift is gone before the argument starts.  This is why
  `GapCertificate.sb_injective`'s proof survives verbatim at a general shift.
* **`CountingLemmas.three_mul_add_surj` is already general in its additive constant** — it is
  stated for `3r + a` with `a` arbitrary, not for `3r + 1`.  So the modular solver surjectivity
  needs is shift-ready as it stands.

Surjectivity is proved **directly** here rather than through a cardinality argument, which is
what `sb_image_eq` does at `c = 1` (`shell_card` → `residue_class_card`).  The direct route
avoids needing a shifted `shell_eq_residue_class`, and it gives `shellS_card` as a corollary
instead of requiring it as an input — a strictly shorter dependency chain than the `c = 1` file
has.
-/

/-- The shifted valuation shell `S_j^{(c)} = { r < 2^k : r odd, v₂(3r+c) = j }`. -/
def shellS (c k j : ℕ) : Finset ℕ :=
  (range (2 ^ k)).filter (fun r => 0 < r ∧ r % 2 = 1 ∧ v2 (3 * r + c) = j)

/-- At `c = 1` the shifted shell is `CountingLemmas.shell`. -/
theorem shellS_one (k j : ℕ) : shellS 1 k j = shell k j := rfl

/-- For `j ≥ 1` the side conditions are automatic: an even `r` (including `0`) makes `3r + c`
odd, so its valuation is `0 ≠ j`. -/
theorem shellS_eq {c k j : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) :
    shellS c k j = (range (2 ^ k)).filter (fun r => v2 (3 * r + c) = j) := by
  unfold shellS
  apply filter_congr
  intro r _
  constructor
  · rintro ⟨_, _, h⟩; exact h
  · intro h
    have hodd : r % 2 = 1 := by
      by_contra hev
      have : (3 * r + c) % 2 = 1 := by omega
      rw [v2_odd_mod _ this] at h
      omega
    exact ⟨by omega, hodd, h⟩

/-- On a shifted shell, `3r + c = 2^j q` with `q` odd. -/
theorem shellS_oddpart {c k j r : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) (hr : r ∈ shellS c k j) :
    3 * r + c = 2 ^ j * ((3 * r + c) / 2 ^ j) ∧ ((3 * r + c) / 2 ^ j) % 2 = 1 := by
  rw [shellS_eq hc hj, mem_filter] at hr
  have hne : 3 * r + c ≠ 0 := by omega
  obtain ⟨hdvd, hndvd⟩ := (v2_eq_iff_dvd hne).1 hr.2
  obtain ⟨q, hq⟩ := hdvd
  have hqv : (3 * r + c) / 2 ^ j = q := by
    rw [hq, Nat.mul_div_cancel_left _ (Nat.two_pow_pos j)]
  refine ⟨by rw [hqv]; exact hq, ?_⟩
  rw [hqv]
  rcases Nat.even_or_odd q with he | ho
  · exfalso
    obtain ⟨t, ht⟩ := he
    exact hndvd ⟨t, by rw [hq, ht, pow_succ]; ring⟩
  · exact Nat.odd_iff.1 ho

/-- The shifted SB map. -/
def sbMapS (c k j r : ℕ) : ℕ := ((3 * r + c) / 2 ^ j) % 2 ^ (k - j)

theorem sbMapS_one (k j r : ℕ) : sbMapS 1 k j r = sbMap k j r := rfl

/-- **SB injectivity, general shift.**  The shift cancels in the difference, so this is
`GapCertificate.sb_injective`'s argument with `1` replaced by `c` and nothing else changed. -/
theorem sbS_injOn {c k j : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
    Set.InjOn (sbMapS c k j) (↑(shellS c k j) : Set ℕ) := by
  intro r hr r' hr' hEq
  simp only [mem_coe] at hr hr'
  obtain ⟨hq, _⟩ := shellS_oddpart hc hj hr
  obtain ⟨hq', _⟩ := shellS_oddpart hc hj hr'
  have hrk : r < 2 ^ k := by
    rw [shellS_eq hc hj, mem_filter, mem_range] at hr; exact hr.1
  have hr'k : r' < 2 ^ k := by
    rw [shellS_eq hc hj, mem_filter, mem_range] at hr'; exact hr'.1
  unfold sbMapS at hEq
  -- `2^{k-j} ∣ q - q'` over ℤ
  have hcong : ((2 : ℤ) ^ (k - j)) ∣
      ((((3 * r + c) / 2 ^ j : ℕ) : ℤ) - (((3 * r' + c) / 2 ^ j : ℕ) : ℤ)) := by
    have hme : Nat.ModEq (2 ^ (k - j)) ((3 * r' + c) / 2 ^ j) ((3 * r + c) / 2 ^ j) := hEq.symm
    have hd := (Nat.modEq_iff_dvd).1 hme
    push_cast at hd ⊢
    exact hd
  obtain ⟨s, hs⟩ := hcong
  have hqz : (2 : ℤ) ^ j * (((3 * r + c) / 2 ^ j : ℕ) : ℤ) = 3 * (r : ℤ) + (c : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hq.symm
  have hqz' : (2 : ℤ) ^ j * (((3 * r' + c) / 2 ^ j : ℕ) : ℤ) = 3 * (r' : ℤ) + (c : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hq'.symm
  have h2 : (2 : ℤ) ^ j * 2 ^ (k - j) = 2 ^ k := by
    rw [← pow_add]; congr 1; omega
  -- the shift cancels here, and only here does it appear at all
  have key : 3 * ((r : ℤ) - (r' : ℤ)) = 2 ^ k * s := by
    linear_combination -hqz + hqz' + (2 : ℤ) ^ j * hs + s * h2
  have hlt : |(r : ℤ) - (r' : ℤ)| < 2 ^ k := by
    have h1 : ((r : ℤ)) < 2 ^ k := by exact_mod_cast hrk
    have h1' : ((r' : ℤ)) < 2 ^ k := by exact_mod_cast hr'k
    rw [abs_lt]
    constructor <;> [linarith [Int.natCast_nonneg r]; linarith [Int.natCast_nonneg r']]
  have : (r : ℤ) = (r' : ℤ) :=
    eq_of_two_pow_dvd_three_mul_sub (N := k) ⟨s, key⟩ hlt
  exact_mod_cast this

/-- **SB surjectivity, general shift — proved directly.**  Given an odd `q < 2^{k-j}`, solve
`3r + c ≡ 2^j q (mod 2^k)` with `CountingLemmas.three_mul_add_surj` (already general in its
additive constant).  Then `3r + c = 2^j (q + 2^{k-j} M)` with the bracket odd, which pins the
valuation at exactly `j` and sends `r` to `q`.

No cardinality argument, hence no shifted `shell_eq_residue_class` — `shellS_card` comes out as
a corollary below rather than being needed as an input. -/
theorem sbS_image_eq {c k j : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
    (shellS c k j).image (sbMapS c k j) = oddResidues (k - j) := by
  apply Finset.Subset.antisymm
  · -- the image lands in the odd residues
    intro y hy
    simp only [mem_image] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    obtain ⟨_, hqodd⟩ := shellS_oddpart hc hj hr
    unfold sbMapS oddResidues
    rw [mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (Nat.two_pow_pos (k - j)), ?_⟩
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega : k - j ≠ 0))]
    exact hqodd
  · -- every odd residue is hit
    intro q hq
    rw [oddResidues, mem_filter, mem_range] at hq
    obtain ⟨hqlt, hqodd⟩ := hq
    have hsplit : (2 : ℕ) ^ k = 2 ^ j * 2 ^ (k - j) := by
      rw [← pow_add]; congr 1; omega
    have htlt : 2 ^ j * q < 2 ^ k := by
      rw [hsplit]
      exact Nat.mul_lt_mul_of_pos_left hqlt (Nat.two_pow_pos j)
    obtain ⟨r, hrlt, hrmod⟩ := three_mul_add_surj k c htlt
    -- 3r + c = 2^k * M + 2^j q, so the bracket q + 2^{k-j} M is odd
    obtain ⟨M, hdiv⟩ : ∃ M, 3 * r + c = 2 ^ k * M + 2 ^ j * q :=
      ⟨(3 * r + c) / 2 ^ k, by
        conv_lhs => rw [← Nat.div_add_mod (3 * r + c) (2 ^ k)]
        rw [hrmod]⟩
    have hfac : 3 * r + c = 2 ^ j * (q + 2 ^ (k - j) * M) := by
      rw [hdiv, hsplit]; ring
    have hbracket : (q + 2 ^ (k - j) * M) % 2 = 1 := by
      have : (2 : ℕ) ∣ 2 ^ (k - j) * M :=
        (dvd_pow_self 2 (by omega : k - j ≠ 0)).mul_right M
      omega
    have hv : v2 (3 * r + c) = j := by
      rw [hfac]; exact v2_two_pow_mul_odd j _ hbracket
    have hrodd : r % 2 = 1 := by
      have h2 : (2 : ℕ) ∣ 2 ^ j * (q + 2 ^ (k - j) * M) :=
        (dvd_pow_self 2 (by omega : j ≠ 0)).mul_right _
      omega
    have hmem : r ∈ shellS c k j := by
      unfold shellS
      rw [mem_filter, mem_range]
      exact ⟨hrlt, by omega, hrodd, hv⟩
    refine mem_image.2 ⟨r, hmem, ?_⟩
    unfold sbMapS
    rw [hfac, Nat.mul_div_cancel_left _ (Nat.two_pow_pos j),
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hqlt]

/-- **LEMMA SB AT A GENERAL ODD SHIFT.**  `ψ` is a bijection from the shell onto the odd
residues mod `2^{k-j}`. -/
theorem sbS_bijective {c k j : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
    Set.BijOn (sbMapS c k j) (↑(shellS c k j) : Set ℕ)
      (↑(oddResidues (k - j)) : Set ℕ) := by
  refine ⟨?_, sbS_injOn hc hj hjk, ?_⟩
  · intro r hr
    simp only [mem_coe] at hr ⊢
    rw [← sbS_image_eq hc hj hjk]
    exact mem_image_of_mem _ hr
  · intro y hy
    simp only [mem_coe] at hy
    rw [← sbS_image_eq hc hj hjk] at hy
    simp only [mem_image] at hy
    obtain ⟨r, hr, hrq⟩ := hy
    exact ⟨r, by simpa using hr, hrq⟩

/-- **The shifted shell count**, `|S_j^{(c)}| = 2^{k-1-j}` — shift-independent, and here a
corollary of the bijection rather than an input to it. -/
theorem shellS_card {c k j : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) :
    (shellS c k j).card = 2 ^ (k - 1 - j) := by
  rw [← card_image_of_injOn (sbS_injOn hc hj hjk), sbS_image_eq hc hj hjk,
    oddResidues_card (by omega : 1 ≤ k - j)]
  congr 1
  omega

/-!
**Satisfiability witnesses.**  `shellS` is computable, so these evaluate the definition the
theorems above are about.  Every value is `2^{k-1-j}`, independent of the shift — which is the
content of `shellS_card`, and is the reason the SB half of Lemma A needs no shift-specific work.
-/

#eval (shellS 1 6 2).card    -- 8 = 2^(6-1-2)
#eval (shellS 5 6 2).card    -- 8, same
#eval (shellS 63 6 2).card   -- 8, same
#eval (shellS 1 6 4).card    -- 2 = 2^(6-1-4)
#eval (shellS 11 6 4).card   -- 2, same

-- the shells at a given shift partition the odd residues except `r*`: 8+4+2+1 = 15 = 2^5 - 1
#eval ((Finset.Icc 1 5).sum (fun j => (shellS 7 6 j).card))   -- 31 = 2^5 - 1

-- The shifted shell is genuinely a different SET, not merely a different name: equinumerous
-- but not equal.  The bijection is shift-independent; the shell is not.
-- Deliberately `#eval` and not `by decide`: `v2` is `padicValNat`, which the kernel does not
-- reduce, so `decide` gets stuck here even though the compiler evaluates it fine.  Same trap as
-- `CollisionBound`'s `cf`.
#eval decide (shellS 1 6 2 = shellS 5 6 2)   -- false
#eval (shellS 1 6 2).card = (shellS 5 6 2).card   -- true

/-!
--------------------------------------------------------------------------------
## §3. The defect residue, for a general shift
--------------------------------------------------------------------------------

`CollisionBound.rstar` is the closed form `(2 ^ ek k - 1) / 3`, which solves `3r + 1 = 2^(ek k)`
and is therefore tied to the shift `1`.  For general `c` the defect row sits at the solution of
`3r + c ≡ 0 (mod 2^k)`.
-/

/-- The defect residue for shift `c` at level `k`: the `r` with `3r + c ≡ 0 (mod 2^k)`.
Written with an explicit inverse of `3` rather than a repunit closed form. -/
def rstarS (c k : ℕ) : ℕ := ((2 ^ k - c % 2 ^ k) * (3 ^ (2 ^ k / 2 - 1))) % 2 ^ k

/-- `3` is invertible mod `2^k`, which is the only arithmetic input the shifted construction
needs about `3` — exactly as in the unshifted case. -/
theorem three_coprime_two_pow (k : ℕ) : Nat.Coprime 3 (2 ^ k) :=
  Nat.Coprime.pow_right _ (by decide)

/-- Euler, specialised: `3 ^ 2^(k-1) ≡ 1 (mod 2^k)`. -/
theorem three_pow_totient {k : ℕ} (hk : 1 ≤ k) :
    Nat.ModEq (2 ^ k) (3 ^ 2 ^ (k - 1)) 1 := by
  have h := Nat.ModEq.pow_totient (three_coprime_two_pow k)
  have ht : (2 ^ k).totient = 2 ^ (k - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    ring
  rwa [ht] at h

/-- **The defining property of `rstarS`.**  Without this the definition above would be an
unchecked guess; with it, `rstarS c k` really is the defect residue. -/
theorem rstarS_spec {c k : ℕ} (hk : 1 ≤ k) :
    (3 * rstarS c k + c) % 2 ^ k = 0 := by
  have hN : 0 < 2 ^ k := Nat.two_pow_pos k
  have he : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  -- 3 * 3^(e-1) = 3^e
  have hmul : 3 * 3 ^ (2 ^ (k - 1) - 1) = 3 ^ 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  -- reduce the outer mod, then use Euler
  have h1 : Nat.ModEq (2 ^ k) (3 * rstarS c k + c)
      ((2 ^ k - c % 2 ^ k) * 3 ^ 2 ^ (k - 1) + c) := by
    unfold rstarS
    have := (Nat.mod_modEq ((2 ^ k - c % 2 ^ k) * 3 ^ (2 ^ (k - 1) - 1)) (2 ^ k))
    calc 3 * (((2 ^ k - c % 2 ^ k) * 3 ^ (2 ^ k / 2 - 1)) % 2 ^ k) + c
        ≡ 3 * ((2 ^ k - c % 2 ^ k) * 3 ^ (2 ^ k / 2 - 1)) + c [MOD 2 ^ k] := by
          have hk2 : 2 ^ k / 2 = 2 ^ (k - 1) := by
            rw [show k = (k - 1) + 1 by omega, pow_succ]
            simp
          rw [hk2]
          exact Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ this)
      _ = (2 ^ k - c % 2 ^ k) * (3 * 3 ^ (2 ^ (k - 1) - 1)) + c := by
          have hk2 : 2 ^ k / 2 = 2 ^ (k - 1) := by
            rw [show k = (k - 1) + 1 by omega, pow_succ]; simp
          rw [hk2]; ring
      _ = (2 ^ k - c % 2 ^ k) * 3 ^ 2 ^ (k - 1) + c := by rw [hmul]
  have h2 : Nat.ModEq (2 ^ k) ((2 ^ k - c % 2 ^ k) * 3 ^ 2 ^ (k - 1) + c)
      ((2 ^ k - c % 2 ^ k) * 1 + c) :=
    Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ (three_pow_totient hk))
  have h3 : (2 ^ k - c % 2 ^ k) * 1 + c ≡ 0 [MOD 2 ^ k] := by
    have hlt : c % 2 ^ k < 2 ^ k := Nat.mod_lt _ hN
    have hc : Nat.ModEq (2 ^ k) c (c % 2 ^ k) := (Nat.mod_modEq c (2 ^ k)).symm
    have : (2 ^ k - c % 2 ^ k) * 1 + c % 2 ^ k = 2 ^ k := by omega
    calc (2 ^ k - c % 2 ^ k) * 1 + c
        ≡ (2 ^ k - c % 2 ^ k) * 1 + c % 2 ^ k [MOD 2 ^ k] := Nat.ModEq.add_left _ hc
      _ = 2 ^ k := this
      _ ≡ 0 [MOD 2 ^ k] := (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
  exact (h1.trans (h2.trans h3))

/-!
--------------------------------------------------------------------------------
## §4. Non-vacuity: a second concrete odd shift
--------------------------------------------------------------------------------

**CORRECTION, 2026-08-05 — read this before citing anything in this section.**

This section used to say that `c = 2^k - 1` *is* the `3x−1` shift, and that its statements are
"about the `3x−1` operator".  **That is false, and it is this corpus's own failure mode (2): the
right-looking theorem about the wrong object.**

`-1` and `2^k - 1` agree mod `2^k`, but `oddPart` is **not** a function of the residue mod `2^k`
— the lift window is the whole point of the construction.  Concretely at `k = 3`, `n = 1`:

```
    oddPart (3·1 − 1)       = 1
    oddPart (3·1 + 2^3 − 1) = 5
```

The two transfer operators differ entrywise at every `k` measured (total entry difference
`2, 12, 8, 44, 32, 172` at `k = 3..8`).  So the statements below are true theorems about the
legitimate odd shift `2^k - 1`; they are **not** about `3x−1`, and this section does not advance
the control experiment.  `syracuseS` takes `c : ℕ`, so it **cannot express `3x−1` at all** — that
needs an integer shift, and building it is open work.

**The conclusion survives the correction, measured independently (`calibrate_true_minus_one`
gate, added the same day).**  The genuine `3x−1` operator, integer shift `c = −1`, passes all
four calibration gates at `k = 4..8`: `cert ≤ 0.8536` (measured `0.578`–`0.606`), Lemma A's clean
block norms **exactly** `2^{-(b-a)/2}`, `rank D = 1`, `‖D‖₂ ≤ √3 · 2^{-k/2}`.  So nothing that
was believed about `3x−1` is now in doubt — but it was being *checked* on a substitute.

**SCOPE OF THE ERROR, checked rather than assumed.**  The original control experiment is
**unaffected** — `probe_cycle_link.py`, `probe_cycle_link_cert.py` and `extremal_values_check.py`
all take a genuine integer `sign = -1` (`oddpart(3n + sign)`), so `CYCLE_CLAIM_REFUTED.md`'s
table is about the real `3x−1` map and its refutation stands.  The substitution entered only
with the `3x + c` generalisation line, where `c` was parametrised as a **natural number** and
`-1` had to be represented as `2^k - 1`: `calibrate_general_shift.py` gates G1–G4, and this file.
Both now carry the correction, and G5 checks the real map directly.

**One recorded risk moves with the correction.**  This file's header flags gate 3 as nearly
saturated "at `c = 2^k − 1`, i.e. exactly the `3x−1` case" — `0.13%` margin at `k = 8`.  That
saturation belongs to the **substitute**: `‖D‖·2^{k/2}` is `1.7298` there against `√3 = 1.7321`,
but only `1.5284` for the true `c = −1`, an `11.8%` margin.  The `√3` sharpness worry was
attached to the wrong operator.
-/

/-- `2^k - 1` is odd for `k ≥ 1`: this shift is in scope of every theorem above.  It is **not**
the `3x−1` shift — see the correction at the head of this section. -/
theorem sub_one_odd {k : ℕ} (hk : 1 ≤ k) : (2 ^ k - 1) % 2 = 1 := by
  have h : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hp : 0 < 2 ^ (k - 1) := Nat.two_pow_pos _
  omega

/-- The `3x+1` step sends odd residues to odd residues. -/
example {n : ℕ} (hn : n % 2 = 1) : syracuseS 1 n % 2 = 1 :=
  syracuseS_odd (by norm_num) hn

/-- **And so does the `3x + (2^k − 1)` step**, at every level.  Previously captioned "the first
Lean statement about the `3x−1` operator"; it is not — see the section correction. -/
example {k n : ℕ} (hk : 1 ≤ k) (hn : n % 2 = 1) : syracuseS (2 ^ k - 1) n % 2 = 1 :=
  syracuseS_odd (sub_one_odd hk) hn

/-- **Non-vacuity at a second concrete shift.**  The fibre count holds for `c = 2^k − 1`, not
merely for a hypothetical odd `c`.  Previously captioned "non-vacuity for `3x−1`", which it is
not — the two operators differ entrywise; see the section correction. -/
example {x K k : ℕ} (hk : 1 ≤ k) (hx : x % 2 = 1)
    (hK : v2 (3 * x + (2 ^ k - 1)) < K) (m0 : ℕ) :
    ((range (2 ^ K)).filter
        (fun m => syracuseS (2 ^ k - 1) (x + m * 2 ^ K) % 2 ^ K
                    = syracuseS (2 ^ k - 1) (x + m0 * 2 ^ K) % 2 ^ K)).card
      = 2 ^ (K - v2 (3 * x + (2 ^ k - 1))) :=
  cu_syracuse_fibre_cardS (sub_one_odd hk) hx hK m0


/-!
--------------------------------------------------------------------------------
## §5. The shifted clean operator  (Lemma A at a general shift, brief step 1)
--------------------------------------------------------------------------------

`OperatorBlock.Uclean` is `(TkC k)ᵀ` with the row `idx (rstar k)` zeroed.  The shifted
analogue needs three ingredients, and only the third is not immediate:

* a complexified shifted matrix — `TkSC`;
* the defect index, `idx (rstarS c k)`.  §3's `rstarS_spec` already proves that `rstarS c k`
  solves `3r + c ≡ 0 (mod 2^k)`, which is what makes it the right row to zero;
* the identification of the shifted shell union with *"every odd residue but `rstarS c k`"*
  (`cleanOddsS_eq_erase`).  At `c = 1` `OperatorBlock` gets this from
  `CountingLemmas.odds_partition` and `defect_card`; both are re-proved here for a general odd
  shift.  Both proofs are the `c = 1` arguments with `1` replaced by `c`, and they go through
  for the same reason everything else in this file does: the only property of the shift ever
  used is that `3r + c` is even for odd `r`.

**Numbering.**  The brief calls this material "§2f".  It is numbered §5 instead because it
consumes `rstarS`, which is §3 — it cannot sit before its own input.

**Scope, unchanged from §4.**  `c : ℕ`, so nothing here is about `3x − 1`.
-/

section CleanShifted

open LemmaA CharacterBasis BlockVanishing OperatorBlock CollisionBound

/-- The shifted defect set: odd `r < 2^k` with `2^k ∣ 3r + c`.  Mirror of
`CountingLemmas.defectSet`, and note the same INEQUALITY `k ≤ v₂` rather than an equality. -/
def defectSetS (c k : ℕ) : Finset ℕ :=
  (range (2 ^ k)).filter (fun r => 0 < r ∧ r % 2 = 1 ∧ k ≤ v2 (3 * r + c))

/-- At `c = 1` the shifted defect set is `CountingLemmas.defectSet`. -/
theorem defectSetS_one (k : ℕ) : defectSetS 1 k = defectSet k := rfl

/-- `k ≤ v₂(3r+c)` is exactly `(3r+c) ≡ 0 (mod 2^k)`.  Stated in divisibility form on the
right-hand side, per the project's standing rule about `v₂`. -/
theorem defectS_iff {c k r : ℕ} (hc : c % 2 = 1) :
    k ≤ v2 (3 * r + c) ↔ (3 * r + c) % 2 ^ k = 0 := by
  have hne : 3 * r + c ≠ 0 := by omega
  constructor
  · intro h
    obtain ⟨d, hd⟩ := (padicValNat_dvd_iff_le hne).2 h
    rw [hd, Nat.mul_mod_right]
  · intro h
    exact (padicValNat_dvd_iff_le hne).1 (Nat.dvd_of_mod_eq_zero h)

/-- `rstarS c k` is a residue mod `2^k`, by construction. -/
theorem rstarS_lt {c k : ℕ} : rstarS c k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)

/-- `rstarS c k` is odd — forced by `3r + c ≡ 0` with `c` odd, not assumed. -/
theorem rstarS_odd {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) : rstarS c k % 2 = 1 := by
  have h := rstarS_spec (c := c) (k := k) hk
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hmm := Nat.mod_mod_of_dvd (3 * rstarS c k + c) h2
  rw [h, Nat.zero_mod] at hmm
  omega

theorem rstarS_mem_defectSetS {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) :
    rstarS c k ∈ defectSetS c k := by
  have hodd := rstarS_odd hc hk
  rw [defectSetS, mem_filter, mem_range]
  exact ⟨rstarS_lt, by omega, hodd, (defectS_iff hc).2 (rstarS_spec hk)⟩

/-- **The shifted defect set is the singleton `{rstarS c k}`.**  Existence is `rstarS_spec`;
uniqueness is `mul_three_mod_cancel` (the coprimality of `3` with `2^k`), and the shift
cancels before that argument starts — exactly as it does in `sbS_injOn`. -/
theorem defectSetS_eq_singleton {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) :
    defectSetS c k = {rstarS c k} := by
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨rstarS_mem_defectSetS hc hk, ?_⟩
  intro r hr
  rw [defectSetS, mem_filter, mem_range] at hr
  have h1 : (3 * r + c) % 2 ^ k = 0 := (defectS_iff hc).1 hr.2.2.2
  have h2 : (3 * rstarS c k + c) % 2 ^ k = 0 := rstarS_spec hk
  have hme : Nat.ModEq (2 ^ k) (3 * r + c) (3 * rstarS c k + c) := by
    unfold Nat.ModEq; rw [h1, h2]
  have h4 := mul_three_mod_cancel (Nat.ModEq.add_right_cancel' c hme)
  rwa [Nat.mod_eq_of_lt hr.1, Nat.mod_eq_of_lt rstarS_lt] at h4

/-- At `c = 1` the two defect residues agree.  They are *not* definitionally equal —
`CollisionBound.rstar` is the repunit closed form `(2^{ek k} − 1)/3` and `rstarS` is written
with an explicit inverse of `3` — so this is a theorem, proved by uniqueness. -/
theorem rstarS_one {k : ℕ} (hk : 1 ≤ k) : rstarS 1 k = rstar k := by
  have h : rstarS 1 k ∈ defectSet k := by
    rw [← defectSetS_one]; exact rstarS_mem_defectSetS (by norm_num) hk
  rw [defectSet_eq_singleton hk, mem_singleton] at h
  exact h

/-- **Every odd `r < 2^k` lies in exactly one shifted shell, or is `rstarS c k`.**  Mirror of
`CountingLemmas.odds_partition`; the `1 ≤ v₂(3r+c)` step is where the oddness of `c` is used. -/
theorem oddsS_partition {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) :
    oddResidues k = ((Icc 1 (k - 1)).biUnion (shellS c k)) ∪ defectSetS c k := by
  ext r
  constructor
  · intro hr
    simp only [oddResidues, mem_filter, mem_range] at hr
    obtain ⟨hrk, hodd⟩ := hr
    have hne : 3 * r + c ≠ 0 := by omega
    rw [mem_union]
    by_cases hcase : k ≤ v2 (3 * r + c)
    · right
      simp only [defectSetS, mem_filter, mem_range]
      exact ⟨hrk, by omega, hodd, hcase⟩
    · left
      push_neg at hcase
      have hj1 : 1 ≤ v2 (3 * r + c) := by
        by_contra hcon
        push_neg at hcon
        have hz : v2 (3 * r + c) = 0 := by omega
        have h0 := ((v2_eq_iff_dvd hne).1 hz).2
        rw [zero_add, pow_one] at h0
        exact h0 (by omega)
      rw [mem_biUnion]
      refine ⟨v2 (3 * r + c), by rw [mem_Icc]; omega, ?_⟩
      simp only [shellS, mem_filter, mem_range]
      exact ⟨hrk, by omega, hodd, trivial⟩
  · intro hr
    rw [mem_union] at hr
    simp only [oddResidues, mem_filter, mem_range]
    rcases hr with h | h
    · rw [mem_biUnion] at h
      obtain ⟨j, _, hmem⟩ := h
      simp only [shellS, mem_filter, mem_range] at hmem
      exact ⟨hmem.1, hmem.2.2.1⟩
    · simp only [defectSetS, mem_filter, mem_range] at h
      exact ⟨h.1, h.2.2.1⟩

/-- **The shifted clean sources ARE the odd residues minus `rstarS c k`.**  This is the
statement that makes `idx (rstarS c k)` the correct row to zero, rather than a plausible one. -/
theorem cleanOddsS_eq_erase {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) :
    (Icc 1 (k - 1)).biUnion (shellS c k) = (oddResidues k).erase (rstarS c k) := by
  ext r
  constructor
  · intro h
    have hmem : r ∈ oddResidues k := by
      rw [oddsS_partition hc hk]; exact mem_union_left _ h
    refine mem_erase.2 ⟨?_, hmem⟩
    rw [mem_biUnion] at h
    obtain ⟨j, hj, hrj⟩ := h
    rw [mem_Icc] at hj
    simp only [shellS, mem_filter, mem_range] at hrj
    intro hcon
    subst hcon
    have hdvd : (2 : ℕ) ^ k ∣ 3 * rstarS c k + c := Nat.dvd_of_mod_eq_zero (rstarS_spec hk)
    have hne : 3 * rstarS c k + c ≠ 0 := by omega
    exact ((v2_eq_iff_dvd hne).1 hrj.2.2.2).2
      (dvd_trans (pow_dvd_pow 2 (by omega)) hdvd)
  · intro h
    rw [mem_erase] at h
    have h2 := h.2
    rw [oddsS_partition hc hk, mem_union] at h2
    rcases h2 with h1 | h2
    · exact h1
    · rw [defectSetS_eq_singleton hc hk, mem_singleton] at h2
      exact absurd h2 h.1

/-- `T_k^{(c)}` complexified. -/
noncomputable def TkSC (c k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℂ :=
  fun u r => (TcountS c k (od u) (od r) : ℂ) / 2 ^ k

theorem TkSC_one (k : ℕ) : TkSC 1 k = TkC k := rfl

/-- **The shifted `U_clean`**: the transpose of `T_k^{(c)}` with the defect row removed.
The orientation — transpose, and the `r*` row rather than the `r*` column — is the one
`OperatorBlock` §0.1 checks numerically at `c = 1`; it is inherited here, not re-derived. -/
noncomputable def UcleanS (c k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℂ :=
  fun r u => if (r : ℕ) = idx (rstarS c k) then 0 else Matrix.transpose (TkSC c k) r u

theorem UcleanS_apply (c k : ℕ) (r u : Fin (2 ^ (k - 1))) :
    UcleanS c k r u = if (r : ℕ) = idx (rstarS c k) then 0 else TkSC c k u r := rfl

/-- The zeroed row is exactly the row `rstarS_spec` identifies. -/
theorem UcleanS_defect_row (c k : ℕ) {r : Fin (2 ^ (k - 1))} (hr : (r : ℕ) = idx (rstarS c k))
    (u : Fin (2 ^ (k - 1))) : UcleanS c k r u = 0 := by
  rw [UcleanS_apply, if_pos hr]

/-- Off the defect row, the shifted `U_clean` is the transpose of `T_k^{(c)}`. -/
theorem UcleanS_clean_row (c k : ℕ) {r : Fin (2 ^ (k - 1))} (hr : (r : ℕ) ≠ idx (rstarS c k))
    (u : Fin (2 ^ (k - 1))) : UcleanS c k r u = TkSC c k u r := by
  rw [UcleanS_apply, if_neg hr]

/-- **Specialisation check.**  At `c = 1` the shifted clean operator is `OperatorBlock.Uclean`.
Not `rfl`: it needs `rstarS_one`, since the two closed forms for `r*` differ. -/
theorem UcleanS_one {k : ℕ} (hk : 1 ≤ k) : UcleanS 1 k = Uclean k := by
  funext r u
  rw [UcleanS_apply, Uclean_apply, rstarS_one hk]
  rfl

/-- The shifted `U_clean` as an endomorphism of `ℓ²`. -/
noncomputable def UendS (c k : ℕ) : Module.End ℂ (EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :=
  Matrix.toEuclideanLin (UcleanS c k)

@[simp] theorem UendS_apply (c k : ℕ) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1))))
    (r : Fin (2 ^ (k - 1))) : (UendS c k x) r = ∑ u, UcleanS c k r u * x u := rfl

/-- `od s = rstarS c k` exactly when `s` is the shifted defect index. -/
theorem od_eq_rstarS_iff {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) (s : Fin (2 ^ (k - 1))) :
    od (s : ℕ) = rstarS c k ↔ (s : ℕ) = idx (rstarS c k) := by
  constructor
  · intro h
    have hid : idx (od (s : ℕ)) = idx (rstarS c k) := by rw [h]
    rwa [show idx (od (s : ℕ)) = (s : ℕ) by unfold od idx; omega] at hid
  · intro h
    rw [h, od_idx (rstarS_odd hc hk)]

/-- A sum over `Fin (2^(k-1))` with the shifted defect index killed IS a sum over the shifted
clean sources.  This is where `cleanOddsS_eq_erase` is consumed. -/
theorem sum_fin_cleanS {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) (F : ℕ → ℂ) :
    ∑ s : Fin (2 ^ (k - 1)), (if (s : ℕ) = idx (rstarS c k) then (0 : ℂ) else F (od (s : ℕ)))
      = ∑ r ∈ (Icc 1 (k - 1)).biUnion (shellS c k), F r := by
  have hstep : ∀ s : Fin (2 ^ (k - 1)),
      (if (s : ℕ) = idx (rstarS c k) then (0 : ℂ) else F (od (s : ℕ)))
        = (if od (s : ℕ) = rstarS c k then (0 : ℂ) else F (od (s : ℕ))) := by
    intro s
    by_cases h : (s : ℕ) = idx (rstarS c k)
    · rw [if_pos h, if_pos ((od_eq_rstarS_iff hc hk s).2 h)]
    · rw [if_neg h, if_neg (fun hcon => h ((od_eq_rstarS_iff hc hk s).1 hcon))]
  have key : ∑ s : Fin (2 ^ (k - 1)),
        (if od (s : ℕ) = rstarS c k then (0 : ℂ) else F (od (s : ℕ)))
      = ∑ r ∈ oddResidues k, (if r = rstarS c k then (0 : ℂ) else F r) :=
    sum_fin_od hk (fun r => if r = rstarS c k then (0 : ℂ) else F r)
  rw [Finset.sum_congr rfl (fun s _ => hstep s), key, cleanOddsS_eq_erase hc hk]
  rw [← Finset.sum_subset (Finset.erase_subset (rstarS c k) (oddResidues k))
    (fun x hx hnx => by
      have hxr : x = rstarS c k := by
        by_contra hcon
        exact hnx (mem_erase.2 ⟨hcon, hx⟩)
      rw [if_pos hxr])]
  exact Finset.sum_congr rfl (fun x hx => if_neg (mem_erase.1 hx).1)

end CleanShifted

/-!
**Satisfiability witnesses for §5.**  `rstarS` and `defectSetS` are computable.  The defect
set is a singleton at every shift, and its element is `rstarS` — the content of
`defectSetS_eq_singleton`, evaluated here rather than only asserted.  `#eval`, not `decide`:
`v2` is `padicValNat`, which the kernel does not reduce.
-/

#eval (defectSetS 1 6).card              -- 1
#eval (defectSetS 5 6).card              -- 1
#eval (defectSetS 63 6).card             -- 1
#eval decide (defectSetS 5 6 = {rstarS 5 6})   -- true
#eval decide (rstarS 1 6 = CollisionBound.rstar 6)   -- true
#eval decide (rstarS 1 6 = rstarS 5 6)         -- false: the defect row MOVES with the shift

-- the clean sources are 2^{k-1} - 1 of the 2^{k-1} odd residues, at every shift
#eval ((Finset.Icc 1 5).biUnion (shellS 7 6)).card   -- 31 = 2^5 - 1

/-!
--------------------------------------------------------------------------------
## §6. The shifted character pairing  (brief step 2)
--------------------------------------------------------------------------------

`OperatorBlock.inner_chiVec_Uend` says the matrix element of `U_clean` between two characters
is `cleanEntry` divided by `N = 2^{k-1}`.  This section is that statement at a general odd
shift, and the `c = 1` proof transfers line for line: it uses the shift only through

* `syracuse_odd` — here `syracuseS_odd`, which holds for **every** odd `c` (§1); and
* the clean-source index set — here `sum_fin_cleanS` (§5).

Nothing about `3x + 1` enters.  The two `1/√N` of `chiVec` compose to the `1/N`, exactly as
at `c = 1`.
-/

section PairingShifted

open LemmaA CharacterBasis BlockVanishing OperatorBlock CollisionBound

/-- Even targets are unreachable from an odd source, at any odd shift.  This is the arithmetic
twin of the orientation trap: if `Syr_c` did not preserve oddness the target index would leave
range and `sum_targetsS` would be false. -/
theorem TcountS_even_zero {c k u r : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) (hr : r % 2 = 1)
    (hu : u % 2 = 0) : TcountS c k u r = 0 := by
  unfold TcountS
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro m _ hcon
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hodd : syracuseS c (r + m * 2 ^ k) % 2 ^ k % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ h2]
    exact syracuseS_odd hc (lift_odd hk hr)
  rw [hcon] at hodd
  omega

/-- The shifted target sum over `range (2^k)` collapses to the odd targets. -/
theorem sum_targetsS {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) {r : ℕ} (hr : r % 2 = 1)
    (g : ℕ → ℂ) :
    ∑ u ∈ range (2 ^ k), (TcountS c k u r : ℂ) * g u
      = ∑ s : Fin (2 ^ (k - 1)), (TcountS c k (od (s : ℕ)) r : ℂ) * g (od (s : ℕ)) := by
  have key : ∑ s : Fin (2 ^ (k - 1)), (TcountS c k (od (s : ℕ)) r : ℂ) * g (od (s : ℕ))
      = ∑ u ∈ oddResidues k, (TcountS c k u r : ℂ) * g u :=
    sum_fin_od hk (fun u => (TcountS c k u r : ℂ) * g u)
  rw [key]
  refine (Finset.sum_subset (fun x hx => by
    simp only [oddResidues, mem_filter] at hx; exact hx.1) ?_).symm
  intro x hx hnx
  have hx2 : x % 2 ≠ 1 := by
    intro h
    exact hnx (by
      simp only [oddResidues, mem_filter, mem_range]
      exact ⟨mem_range.1 hx, h⟩)
  rw [TcountS_even_zero hc hk hr (by omega), Nat.cast_zero, zero_mul]

/-- **The shifted clean character-basis entry**, built from `TcountS` alone.  Mirror of
`BlockVanishing.cleanEntry`, with the shifted shells as the source index set. -/
noncomputable def cleanEntryS (c k η : ℕ) (ξ : ℤ) : ℂ :=
  ∑ r ∈ (Icc 1 (k - 1)).biUnion (shellS c k),
    (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (TcountS c k u r : ℂ) * w k ^ (η * u))
      * wz k (-(ξ * (r : ℤ)))

/-- At `c = 1` the shifted clean entry is `BlockVanishing.cleanEntry`. -/
theorem cleanEntryS_one (k η : ℕ) (ξ : ℤ) : cleanEntryS 1 k η ξ = cleanEntry k η ξ := rfl

/-- **THE SHIFTED NORMALISATION.**  The matrix element of the shifted `U_clean` between two
characters is `cleanEntryS`, divided by `N = 2^{k-1}`. -/
theorem inner_chiVec_UendS {c k : ℕ} (hc : c % 2 = 1) (hk : 1 ≤ k) (ξ η : Fin (2 ^ (k - 1))) :
    (@inner ℂ _ _ (chiVec k ξ) (UendS c k (chiVec k η)) : ℂ)
      = (((2 ^ (k - 1) : ℕ) : ℂ))⁻¹ * cleanEntryS c k (η : ℕ) ((ξ : ℕ) : ℤ) := by
  have hpow : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero k two_ne_zero
  set F : ℕ → ℂ := fun r =>
    (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (TcountS c k u r : ℂ) * w k ^ ((η : ℕ) * u))
      * wz k (-(((ξ : ℕ) : ℤ) * (r : ℤ))) with hF
  have hpt : ∀ s : Fin (2 ^ (k - 1)),
      (inner ℂ ((chiVec k ξ).ofLp s) ((UendS c k (chiVec k η)).ofLp s) : ℂ)
        = (((2 ^ (k - 1) : ℕ) : ℂ))⁻¹
            * (if (s : ℕ) = idx (rstarS c k) then (0 : ℂ) else F (od (s : ℕ))) := by
    intro s
    rw [RCLike.inner_apply]
    show (UendS c k (chiVec k η)) s * (starRingEnd ℂ) (chi k (ξ : ℕ) (s : ℕ) / (rt k : ℂ)) = _
    rw [map_div₀, Complex.conj_ofReal, chi, conj_w_pow]
    by_cases hs : (s : ℕ) = idx (rstarS c k)
    · rw [if_pos hs]
      have hz : (UendS c k (chiVec k η)) s = 0 := by
        rw [UendS_apply]
        exact Finset.sum_eq_zero fun u _ => by rw [UcleanS_defect_row c k hs u, zero_mul]
      rw [hz, zero_mul, mul_zero]
    · rw [if_neg hs]
      have hval : (UendS c k (chiVec k η)) s
          = (rt k : ℂ)⁻¹ * (((2 : ℂ) ^ k)⁻¹
              * ∑ u ∈ range (2 ^ k), (TcountS c k u (od (s : ℕ)) : ℂ)
                  * w k ^ ((η : ℕ) * u)) := by
        rw [UendS_apply]
        rw [sum_targetsS hc hk (od_odd s) (fun u => w k ^ ((η : ℕ) * u))]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [UcleanS_clean_row c k hs u]
        show (TcountS c k (od (u : ℕ)) (od (s : ℕ)) : ℂ) / 2 ^ k
            * (chi k (η : ℕ) (u : ℕ) / (rt k : ℂ)) = _
        rw [chi]
        field_simp
      rw [hval, hF]
      rw [show -(((ξ : ℕ) * od (s : ℕ) : ℕ) : ℤ) = -(((ξ : ℕ) : ℤ) * ((od (s : ℕ) : ℕ) : ℤ)) by
        push_cast; ring]
      have hrt : ((2 ^ (k - 1) : ℕ) : ℂ)⁻¹ = (rt k : ℂ)⁻¹ * (rt k : ℂ)⁻¹ := by
        rw [← mul_inv, rt_mul_rt]
      rw [hrt]
      ring
  rw [PiLp.inner_apply, Fintype.sum_congr _ _ hpt, ← Finset.mul_sum,
    sum_fin_cleanS hc hk F, cleanEntryS, hF]

end PairingShifted

/-!
--------------------------------------------------------------------------------
## §7. The shifted entry theorem  (brief step 3 — the only new mathematics)
--------------------------------------------------------------------------------

### What is actually new, and what is not

`BRIEF_LEMMA_A_GENERAL_SHIFT.md` §0 establishes, **by measurement before any Lean was
written** (`calibrate_lemmaA_shift_structure.py`, H1/H2), that the shift enters the clean
operator only as a per-entry phase: the support of the clean block is the same set for every
odd `c`, and the entrywise moduli agree to `1.5e-14`.  That is why this section is one entry
theorem rather than a five-file refactor.

The arithmetic content is a single line.  On the shifted shell `3r + c = 2^j q`, so with
`u = 3⁻¹ (mod 2^k)` we have `r ≡ u(2^j q − c)`, and

```
    η·q − ξ·r  ≡  (η − ξ·u·2^j)·q + ξ·u·c  =  alphaJ η ξ u j · q + ξ·u·c   (mod 2^k)
```

**`alphaJ` is identical to the `c = 1` case — it never mentions the shift.**  Only the
constant changes: `ξ·u` at `c = 1` becomes `ξ·u·c`.  Since the downstream Gram argument
consumes the first factor only through `‖wz‖ = 1` (`GramIdentity.norm_wz`) and the second
through `alphaJ`, everything above this theorem transfers unchanged.  That is brief step 4,
and it is not done here.

### The wrong turn this section does NOT take

Hypothesis **H3** — that the ratio `B_c / B_1` is a *column* phase, which would have made the
whole generalisation a two-line diagonal-unitary conjugation — is **measured false**, by a
deviation of `~2.0`, i.e. as wrong as it can be.  The norm invariance comes from disjoint
support (H1), not from a factorisation.  Do not try to rescue H3.

### Scope

`c : ℕ`.  Nothing in this section is about `3x − 1`; see §4's correction.
-/

section EntryShifted

open LemmaA CharacterBasis BlockVanishing OperatorBlock CollisionBound GramIdentity

/-- On a shifted shell, `Syr_c(r)` is the exact quotient `(3r+c)/2^j`. -/
theorem syracuseS_on_shellS {c k j r : ℕ} (hj : 1 ≤ j) (hr : r ∈ shellS c k j) :
    syracuseS c r = (3 * r + c) / 2 ^ j := by
  simp only [shellS, mem_filter] at hr
  have hodd : r % 2 = 1 := hr.2.2.1
  unfold syracuseS
  rw [if_neg (by omega)]
  simp only [hr.2.2.2]

/-- **Lemma SB, as a change of summation variable at a general shift.**  This is where
`sbS_bijective` (§2e, brief step 0) is consumed. -/
theorem shellS_reindex {c k j : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) (hjk : j + 1 ≤ k) (α : ℕ) :
    ∑ r ∈ shellS c k j, w k ^ (α * sbMapS c k j r) = Sodd k α (k - j) := by
  rw [Sodd_eq_oddResidues, ← sbS_image_eq hc hj hjk, Finset.sum_image (sbS_injOn hc hj hjk)]

/-- **The shifted phase identity**, mod `2^k`: `η·q − ξ·r ≡ alphaJ η ξ u j · q + ξ·u·c`.

Stated on its own because it is the whole arithmetic content of this section, and because it
makes visible the claim the brief turns on: **`alphaJ` is the `c = 1` `alphaJ`.**  The shift
appears only in the additive constant `ξ·u·c`. -/
theorem phase_congrS {c k j r : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) (hr : r ∈ shellS c k j)
    {η ξ u : ℤ} (hu : (2 : ℤ) ^ k ∣ 3 * u - 1) :
    (2 : ℤ) ^ k ∣
      (alphaJ η ξ u j * (((3 * r + c) / 2 ^ j : ℕ) : ℤ) + ξ * u * (c : ℤ))
        - (η * (((3 * r + c) / 2 ^ j : ℕ) : ℤ) - ξ * (r : ℤ)) := by
  obtain ⟨hq, _⟩ := shellS_oddpart hc hj hr
  obtain ⟨t, ht⟩ := hu
  have hqz : (2 : ℤ) ^ j * (((3 * r + c) / 2 ^ j : ℕ) : ℤ) = 3 * (r : ℤ) + (c : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hq.symm
  refine ⟨-(ξ * (r : ℤ) * t), ?_⟩
  unfold alphaJ
  linear_combination (-(ξ * u)) * hqz + (-(ξ * (r : ℤ))) * ht

/-- **S1 AT A GENERAL ODD SHIFT, ONE SHELL.**  The shell-`j` character sum is exactly
`w^{ξuc} · Sodd(alpha_j, k−j)`.

Compare `BlockVanishing.shell_character_sum`, which is this statement at `c = 1` with the
phase `w^{ξu}`.  The `Sodd` factor and its argument `alphaJ η ξ u j` are **identical**; the
shift lives entirely in the unimodular prefactor.  That is the fact brief step 4 will consume,
and the reason it needs no new mathematics.

`α : ℕ` is any representative of `alpha_j` mod `2^k`; `hvj` is the `2^j ∣ alpha_j`
prerequisite without which the shell sum does not reduce to a `Sodd` at all. -/
theorem shell_character_sumS {c k j : ℕ} (hc : c % 2 = 1) (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    {η ξ u : ℤ} (hu : (2 : ℤ) ^ k ∣ 3 * u - 1)
    {α : ℕ} (hres : (2 : ℤ) ^ k ∣ (α : ℤ) - alphaJ η ξ u j)
    (hvj : (2 : ℤ) ^ j ∣ alphaJ η ξ u j) :
    ∑ r ∈ shellS c k j, wz k (η * ((syracuseS c r : ℕ) : ℤ) - ξ * (r : ℤ))
      = wz k (ξ * u * (c : ℤ)) * Sodd k α (k - j) := by
  have hαj : (2 : ℤ) ^ j ∣ (α : ℤ) := by
    obtain ⟨d, hd⟩ := hres
    obtain ⟨e, he⟩ := hvj
    exact ⟨e + 2 ^ (k - j) * d, by
      have hsplit : (2 : ℤ) ^ k = 2 ^ j * 2 ^ (k - j) := by
        rw [← pow_add]; congr 1; omega
      have hα : (α : ℤ) = alphaJ η ξ u j + 2 ^ k * d := by linarith
      rw [hα, he, hsplit]; ring⟩
  have hterm : ∀ r ∈ shellS c k j,
      wz k (η * ((syracuseS c r : ℕ) : ℤ) - ξ * (r : ℤ))
        = wz k (ξ * u * (c : ℤ)) * w k ^ (α * sbMapS c k j r) := by
    intro r hr
    have h1 : wz k (η * ((syracuseS c r : ℕ) : ℤ) - ξ * (r : ℤ))
        = wz k ((α : ℤ) * (((3 * r + c) / 2 ^ j : ℕ) : ℤ)) * wz k (ξ * u * (c : ℤ)) := by
      rw [syracuseS_on_shellS hj hr, ← wz_add]
      obtain ⟨d, hd⟩ := hres
      obtain ⟨t, ht⟩ := hu
      obtain ⟨hq, _⟩ := shellS_oddpart hc hj hr
      have hqz : (2 : ℤ) ^ j * (((3 * r + c) / 2 ^ j : ℕ) : ℤ) = 3 * (r : ℤ) + (c : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hq.symm
      unfold alphaJ at hd
      refine wz_congr ⟨ξ * (r : ℤ) * t - d * (((3 * r + c) / 2 ^ j : ℕ) : ℤ), ?_⟩
      linear_combination (-(((3 * r + c) / 2 ^ j : ℕ) : ℤ)) * hd + (ξ * u) * hqz
        + (ξ * (r : ℤ)) * ht
    have h2 : wz k ((α : ℤ) * (((3 * r + c) / 2 ^ j : ℕ) : ℤ))
        = w k ^ (α * sbMapS c k j r) := by
      rw [wz_period (k := k) (j := j) (by omega) hαj ((3 * r + c) / 2 ^ j),
        show ((α : ℤ) * ((((3 * r + c) / 2 ^ j) % 2 ^ (k - j) : ℕ) : ℤ))
            = ((α * (((3 * r + c) / 2 ^ j) % 2 ^ (k - j)) : ℕ) : ℤ) by push_cast; ring,
        wz_natCast]
      rfl
    rw [h1, h2, mul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, shellS_reindex hc hj hjk]

/-- **Specialisation check.**  At `c = 1` the shifted shell character sum is
`BlockVanishing.shell_character_sum`: the prefactor `w^{ξ·u·1}` is `w^{ξ·u}`. -/
theorem shell_character_sumS_one {k j : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    {η ξ u : ℤ} (hu : (2 : ℤ) ^ k ∣ 3 * u - 1)
    {α : ℕ} (hres : (2 : ℤ) ^ k ∣ (α : ℤ) - alphaJ η ξ u j)
    (hvj : (2 : ℤ) ^ j ∣ alphaJ η ξ u j) :
    ∑ r ∈ shellS 1 k j, wz k (η * ((syracuseS 1 r : ℕ) : ℤ) - ξ * (r : ℤ))
      = wz k (ξ * u) * Sodd k α (k - j) := by
  rw [shell_character_sumS (by norm_num) hj hjk hu hres hvj]
  norm_num

/-- The shifted shells are pairwise disjoint: `j` is recoverable from any member. -/
theorem shellS_disjoint {c k j j' : ℕ} (h : j ≠ j') :
    Disjoint (shellS c k j) (shellS c k j') := by
  rw [Finset.disjoint_left]
  intro r hr hr'
  simp only [shellS, mem_filter] at hr hr'
  exact h (by rw [← hr.2.2.2, hr'.2.2.2])

/-- The shifted masked source set: odd `r < 2^k` with `1 ≤ v₂(3r+c) ≤ b`. -/
def maskedOddsS (c k b : ℕ) : Finset ℕ := (Icc 1 b).biUnion (shellS c k)

theorem maskedOddsS_one (k b : ℕ) : maskedOddsS 1 k b = maskedOdds k b := rfl

/-- The shifted odd part, as a quotient. -/
theorem syracuseS_eq_quot {c r : ℕ} (hr : r % 2 = 1) :
    syracuseS c r = (3 * r + c) / 2 ^ v2 (3 * r + c) := by
  unfold syracuseS
  rw [if_neg (by omega)]

/-- The shifted target sum against `TcountS` is the lift-window sum.  This is `TcountS`'s
definition read backwards; no arithmetic is involved and no shift is used. -/
theorem char_col_as_liftS (c k r η : ℕ) :
    ∑ u ∈ range (2 ^ k), (TcountS c k u r : ℂ) * w k ^ (η * u)
      = ∑ m ∈ range (2 ^ k), w k ^ (η * syracuseS c (r + m * 2 ^ k)) := by
  have hmaps : ∀ m ∈ range (2 ^ k), syracuseS c (r + m * 2 ^ k) % 2 ^ k ∈ range (2 ^ k) :=
    fun m _ => mem_range.2 (Nat.mod_lt _ (Nat.two_pow_pos k))
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun m => w k ^ (η * (syracuseS c (r + m * 2 ^ k) % 2 ^ k)))
  have hstep : ∀ u ∈ range (2 ^ k),
      (TcountS c k u r : ℂ) * w k ^ (η * u)
        = ∑ m ∈ (range (2 ^ k)).filter
              (fun m => syracuseS c (r + m * 2 ^ k) % 2 ^ k = u),
            w k ^ (η * (syracuseS c (r + m * 2 ^ k) % 2 ^ k)) := by
    intro u _
    have hcong : ∀ m ∈ (range (2 ^ k)).filter
        (fun m => syracuseS c (r + m * 2 ^ k) % 2 ^ k = u),
        w k ^ (η * (syracuseS c (r + m * 2 ^ k) % 2 ^ k)) = w k ^ (η * u) :=
      fun m hm => by rw [(mem_filter.1 hm).2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul, TcountS]
  rw [Finset.sum_congr rfl hstep, hfib]
  exact Finset.sum_congr rfl fun m _ => w_pow_mod k η _

/-- **THE GAUSS COLLAPSE AT A GENERAL ODD SHIFT.**  For a clean source `r`
(`v := v₂(3r+c) < k`), the shifted transfer operator's column sum against the character
`w^{η·}` collapses to a single phase, gated by `2^v ∣ η`.

The only coset-uniformity input is `cu_syracuse_affineS` (§2b), which is already general.
`ratio_one_iff` is shift-free and is imported unchanged. -/
theorem gauss_collapseS {c k r : ℕ} (hc : c % 2 = 1) (hr : r % 2 = 1)
    (hK : v2 (3 * r + c) < k) (η : ℕ) :
    ∑ u ∈ range (2 ^ k), (TcountS c k u r : ℂ) * w k ^ (η * u)
      = if 2 ^ v2 (3 * r + c) ∣ η then ((2 ^ k : ℕ) : ℂ) * w k ^ (η * syracuseS c r) else 0 := by
  rw [char_col_as_liftS c k r η]
  have hstep : ∀ m ∈ range (2 ^ k),
      w k ^ (η * syracuseS c (r + m * 2 ^ k))
        = w k ^ (η * syracuseS c r) * (w k ^ (η * 3 * 2 ^ (k - v2 (3 * r + c)))) ^ m := by
    intro m _
    rw [cu_syracuse_affineS hc r m k hr hK, ← syracuseS_eq_quot (c := c) hr, Nat.mul_add,
      show η * (3 * m * 2 ^ (k - v2 (3 * r + c)))
          = (η * 3 * 2 ^ (k - v2 (3 * r + c))) * m by ring,
      pow_add, pow_mul (w k) (η * 3 * 2 ^ (k - v2 (3 * r + c))) m]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  by_cases hcase : 2 ^ v2 (3 * r + c) ∣ η
  · rw [if_pos hcase, (ratio_one_iff (le_of_lt hK)).2 hcase]
    simp [mul_comm]
  · rw [if_neg hcase]
    have hzero : ∑ m ∈ range (2 ^ k), (w k ^ (η * 3 * 2 ^ (k - v2 (3 * r + c)))) ^ m = 0 := by
      refine (geomSum_eq_zero_iff (by positivity : (2 : ℕ) ^ k ≠ 0)).2 ⟨?_, ?_⟩
      · rw [← pow_mul, w_pow_eq_one_iff]
        exact ⟨η * 3 * 2 ^ (k - v2 (3 * r + c)), by ring⟩
      · exact fun hcon => hcase ((ratio_one_iff (le_of_lt hK)).1 hcon)
    rw [hzero, mul_zero]

/-- **The join, shifted.**  The shifted clean entry of `T_k^{(c)}` *is* the shifted masked
sum.  The `[v(r) ≤ b]` mask is produced by `gauss_collapseS` rather than assumed; `gate_iff`
is shift-free and is used unchanged. -/
theorem cleanEntryS_eq_masked {c k b η : ℕ} {η' : ℤ} (hc : c % 2 = 1)
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hbk : b + 1 ≤ k) (ξ : ℤ) :
    cleanEntryS c k η ξ
      = ∑ r ∈ maskedOddsS c k b, wz k ((η : ℤ) * ((syracuseS c r : ℕ) : ℤ) - ξ * (r : ℤ)) := by
  have hd1 : (↑(Icc 1 (k - 1)) : Set ℕ).PairwiseDisjoint (shellS c k) := by
    intro x _ y _ hxy; exact shellS_disjoint hxy
  have hd2 : (↑(Icc 1 b) : Set ℕ).PairwiseDisjoint (shellS c k) := by
    intro x _ y _ hxy; exact shellS_disjoint hxy
  rw [cleanEntryS, Finset.sum_biUnion hd1, maskedOddsS, Finset.sum_biUnion hd2]
  have hpow : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero k two_ne_zero
  have hshell : ∀ j ∈ Icc 1 (k - 1),
      (∑ r ∈ shellS c k j,
        (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (TcountS c k u r : ℂ) * w k ^ (η * u))
          * wz k (-(ξ * (r : ℤ))))
        = if j ≤ b then
            ∑ r ∈ shellS c k j,
              wz k ((η : ℤ) * ((syracuseS c r : ℕ) : ℤ) - ξ * (r : ℤ)) else 0 := by
    intro j hj
    rw [mem_Icc] at hj
    have hterm : ∀ r ∈ shellS c k j,
        (((2 : ℂ) ^ k)⁻¹ * ∑ u ∈ range (2 ^ k), (TcountS c k u r : ℂ) * w k ^ (η * u))
            * wz k (-(ξ * (r : ℤ)))
          = if j ≤ b then
              wz k ((η : ℤ) * ((syracuseS c r : ℕ) : ℤ) - ξ * (r : ℤ)) else 0 := by
      intro r hr
      simp only [shellS, mem_filter] at hr
      have hrodd : r % 2 = 1 := hr.2.2.1
      have hvj : v2 (3 * r + c) = j := hr.2.2.2
      have hclean : v2 (3 * r + c) < k := by omega
      rw [gauss_collapseS hc hrodd hclean η, hvj]
      by_cases hcase : (2 : ℕ) ^ j ∣ η
      · rw [if_pos hcase, if_pos ((gate_iff hη hη').1 hcase)]
        rw [show (((2 ^ k : ℕ) : ℂ)) = (2 : ℂ) ^ k by push_cast; ring, ← mul_assoc,
          inv_mul_cancel₀ hpow, one_mul, ← wz_natCast, ← wz_add,
          show ((η * syracuseS c r : ℕ) : ℤ) + -(ξ * (r : ℤ))
              = (η : ℤ) * ((syracuseS c r : ℕ) : ℤ) - ξ * (r : ℤ) by push_cast; ring]
      · rw [if_neg hcase, if_neg (fun hcon => hcase ((gate_iff hη hη').2 hcon)), mul_zero,
          zero_mul]
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

/-- **THE SHIFTED UPPER-REGIME ENTRY THEOREM.**  For `a < b` the shifted clean entry
collapses onto the single shell `j = d := b − a`:

```
    cleanEntryS c k η ξ = w^{ξ·u·c} · Sodd(resJ k η ξ u d, k − d)
```

Compare `GramIdentity.upper_entry_eq`, which is this at `c = 1` with `w^{ξ·u}`.

**The `Sodd` factor is bit-for-bit the `c = 1` one** — same `resJ`, same `alphaJ`, same
range — and the first factor is unimodular (`GramIdentity.norm_wz`).  Those are exactly the
two properties `Bent_eq_zero_of_not_owned` and `norm_Bent_of_owned` consume, so brief step 4
(the substitution through `gram_upper`, `norm_sq_clean_block`, `norm_clean_block_le`,
`clean_bound`) introduces no new mathematics.  **Step 4 is not done here.**

Everything the proof needs about the dead band — `shell_dvd_upper` and
`LemmaA.shell_sum_vanishes` — is already shift-free: neither mentions `c`, because both are
statements about `alphaJ`, and `alphaJ` does not see the shift. -/
theorem upper_entry_eqS {c k a b η : ℕ} {ξ η' ξ' u : ℤ} (hc : c % 2 = 1)
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k) :
    cleanEntryS c k η ξ
      = wz k (ξ * u * (c : ℤ)) * Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) := by
  rw [cleanEntryS_eq_masked hc hη hη' (by omega) ξ, maskedOddsS,
    Finset.sum_biUnion (fun x _ y _ hxy => shellS_disjoint hxy)]
  refine (Finset.sum_eq_single_of_mem (b - a) (mem_Icc.2 ⟨by omega, by omega⟩) ?_).trans ?_
  · -- every shell other than `j = d` is inside the dead band
    intro j hj hjd
    rw [mem_Icc] at hj
    rw [shell_character_sumS hc hj.1 (by omega) huinv (resJ_spec k (η : ℤ) ξ u j)
        (shell_dvd_upper hη hη' hξ hξ' hu hab hbk hj.1 hj.2),
      shell_sum_vanishes hη hη' hξ hξ' hu hab hbk hj.1 hj.2 hjd
        (resJ_spec k (η : ℤ) ξ u j),
      mul_zero]
  · -- the surviving shell
    exact shell_character_sumS hc (by omega) (by omega) huinv
      (resJ_spec k (η : ℤ) ξ u (b - a))
      (shell_dvd_upper (j := b - a) hη hη' hξ hξ' hu hab hbk (by omega) (by omega))

/-- **The shifted prefactor is unimodular** — the only property of it the Gram argument uses,
and therefore the precise sense in which the shift is invisible above this section. -/
theorem norm_shift_phase (k : ℕ) (ξ u : ℤ) (c : ℕ) : ‖wz k (ξ * u * (c : ℤ))‖ = 1 :=
  norm_wz k _

/-- **Off the support the shifted entry is exactly `0`**, by the same dead-band argument as
`GramIdentity.upper_entry_eq_zero`.  Immediate from `upper_entry_eqS`, because the vanishing
lives entirely in the `Sodd` factor, which is the unshifted one. -/
theorem upper_entry_eqS_zero {c k a b η : ℕ} {ξ η' ξ' u : ℤ} (hc : c % 2 = 1)
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k)
    (hno : ¬ (2 : ℤ) ^ (k - 1) ∣ alphaJ (η : ℤ) ξ u (b - a)) :
    cleanEntryS c k η ξ = 0 := by
  have hz : Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) = 0 := by
    have h1 : cleanEntry k η ξ
        = wz k (ξ * u) * Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) :=
      upper_entry_eq hη hη' hξ hξ' hu huinv hab hbk
    have h2 : cleanEntry k η ξ = 0 :=
      upper_entry_eq_zero hη hη' hξ hξ' hu huinv hab hbk hno
    have h3 : wz k (ξ * u) * Sodd k (resJ k (η : ℤ) ξ u (b - a)) (k - (b - a)) = 0 := by
      rw [← h1, h2]
    have hne : wz k (ξ * u) ≠ 0 := by
      intro hcon
      have := norm_wz k (ξ * u)
      rw [hcon, norm_zero] at this
      exact absurd this (by norm_num)
    exact (mul_eq_zero.1 h3).resolve_left hne
  rw [upper_entry_eqS hc hη hη' hξ hξ' hu huinv hab hbk, hz, mul_zero]

end EntryShifted

/-!
--------------------------------------------------------------------------------
## §8. Lemma A's clean block norms at a general shift  (brief step 4)
--------------------------------------------------------------------------------

**This section is a substitution, and it is worth saying exactly why it is allowed to be.**

`GramIdentity`'s chain from the entry theorem to `(CLEAN)` consumes the operator through
precisely two facts:

| Fact | Statement | Shifted version |
|---|---|---|
| `Bent_eq_zero_of_not_owned` | off the owner set the entry is `0` | `BentS_eq_zero_of_not_owned` |
| `norm_Bent_of_owned` | on the owner set the modulus is exactly `(1/2)^{b−a}` | `norm_BentS_of_owned` |

**Neither mentions a phase.**  §7's `upper_entry_eqS` produces the shifted entry as
`(unimodular) · Sodd (the c = 1 argument)`, so the first fact survives because the vanishing
lives in the `Sodd` factor, and the second because `‖wz‖ = 1` (`norm_shift_phase`).  Every
step below — `gram_upperS`, `norm_sq_clean_blockS`, `norm_clean_block_leS`, `clean_boundS` —
is then the `c = 1` proof with `Uend` replaced by `UendS`.

Three pieces of the machinery are reused **unchanged, not re-proved**, because they never
mentioned the shift in the first place:

* `OwnerPartition.ownedBy` / `ownedBy_card` / `ownedBy_disjoint` / `owner_biUnion` — already
  abstract in the odd multiplier `u`, which is where `OwnerCount`'s Bezout generalisation
  went;
* `GramIdentity.uinv k = −r*_1` — an inverse of `3` mod `2^k`.  It is defined from the `c = 1`
  defect residue, but nothing about it is `c`-specific: all that is ever used is
  `2^k ∣ 3u − 1` and `Odd u`.  It is **not** the shifted defect residue and must not be
  confused with `rstarS`;
* `CharacterBasis.P`, `ManifestInstance.norm_sq_P`, `Assembly.s` — level projections and the
  constant `√(1/2)`, all shift-free.

### WHAT THIS DOES **NOT** GIVE, AND THE MISREADING TO AVOID

`clean_boundS` is **(CLEAN) for the shifted operator**: Lemma A's clean block bound
`‖P_a U_clean^{(c)} P_b‖ ≤ s^{b−a}` at every odd `c`.  That is Lemma A, finished.

**It is NOT a certificate for `3x + c`.**  The certificate is `clean + defect`, and the defect
half — Lemma B for general `c`, i.e. a bound on `‖D_c‖` — is **open**.  §2c proves only the
`a = 3` case of the AP model, and even that is not tied to the shifted defect fibre by a
theorem.  So:

* `gap_certificate_unconditional` has **no shifted analogue here**, and none may be inferred;
* and `c : ℕ` still, so none of this is about `3x − 1` (§4).

A reader who takes `clean_boundS` as "the `3x+c` certificate is formalised" has made exactly
the error §4 corrects, one level up.
-/

section CleanBlockShifted

open LemmaA CharacterBasis BlockVanishing OperatorBlock CollisionBound GramIdentity
open DefectSplit ManifestInstance OwnerPartition OwnerCount CleanBlock

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-- **On the sharp points the shifted entry has modulus exactly `2^{k−d−1}`.**  The shift
drops out at the first step: `‖wz k (ξ·u·c)‖ = 1`, and what is left is S4's FULL branch
(`LemmaA.norm_Sodd_full`) applied to the **unshifted** `Sodd`. -/
theorem norm_upper_entryS {c k a b η : ℕ} {ξ η' ξ' u : ℤ} (hc : c % 2 = 1)
    (hη : (η : ℤ) = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ') (hξ' : Odd ξ')
    (hu : Odd u) (huinv : (2 : ℤ) ^ k ∣ 3 * u - 1) (hab : a < b) (hbk : b + 2 ≤ k)
    (how : (2 : ℤ) ^ (k - 1) ∣ alphaJ (η : ℤ) ξ u (b - a)) :
    ‖cleanEntryS c k η ξ‖ = (2 : ℝ) ^ (k - (b - a) - 1) := by
  rw [upper_entry_eqS hc hη hη' hξ hξ' hu huinv hab hbk, norm_mul, norm_wz, one_mul,
    norm_Sodd_full k _ _ (by omega) ((resJ_dvd_iff (by omega) _ _ _ _).2 how)]
  push_cast
  ring

/-- `B_c[ξ,η] := ⟪χ_ξ, U_clean^{(c)} χ_η⟫`, the shifted level-block entry. -/
noncomputable def BentS (c k : ℕ) (ξ η : Fin (2 ^ (k - 1))) : ℂ :=
  (@inner ℂ _ _ (chiVec k ξ) (UendS c k (chiVec k η)) : ℂ)

/-- At `c = 1` the shifted block entry is `GramIdentity.Bent`.  **Not `rfl`** — it runs through
`UcleanS_one`, because the two closed forms for `r*` are not definitionally equal. -/
theorem BentS_one {k : ℕ} (hk : 1 ≤ k) (ξ η : Fin (2 ^ (k - 1))) :
    BentS 1 k ξ η = Bent k ξ η := by
  unfold BentS Bent UendS Uend
  rw [UcleanS_one hk]

/-- **Off the owner set the shifted block entry vanishes.**  The owner predicate is the
`c = 1` one — `ownedBy k a b (uinv k) η` — because it is a statement about `alphaJ`, and
`alphaJ` does not see the shift.  That is the whole reason this transfers. -/
theorem BentS_eq_zero_of_not_owned {c k a b : ℕ} (hc : c % 2 = 1) (hk : 2 ≤ k) (hab : a < b)
    {ξ η : Fin (2 ^ (k - 1))} (hξ : ξ ∈ levelSet k a) (hη : η ∈ levelSet k b)
    (hno : ξ ∉ ownedBy k a b (uinv k) η) :
    BentS c k ξ η = 0 := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨m, hm, hmo⟩ := level_split hη
  obtain ⟨n, hn, hnodd⟩ := level_split hξ
  have hdvd : ¬ (2 : ℤ) ^ (k - 1) ∣
      alphaJ ((η : ℕ) : ℤ) ((ξ : ℕ) : ℤ) (uinv k) (b - a) := by
    intro hcon
    exact hno (mem_ownedBy.2 ⟨hξ, hcon⟩)
  rw [BentS, inner_chiVec_UendS hc hk1 ξ η,
    upper_entry_eqS_zero (a := a) (b := b) hc hm hmo hn hnodd (uinv_odd hk1) (uinv_spec hk1)
      hab (level_bound hk hη) hdvd,
    mul_zero]

/-- **On the owner set the shifted block entry has modulus exactly `2^{−d}`** — the SAME
number as `c = 1` (`GramIdentity.norm_Bent_of_owned`).  This is H2 of the calibration, which
measured the entrywise moduli equal across shifts to `1.5e-14`, now proved. -/
theorem norm_BentS_of_owned {c k a b : ℕ} (hc : c % 2 = 1) (hk : 2 ≤ k) (hab : a < b)
    {ξ η : Fin (2 ^ (k - 1))} (hη : η ∈ levelSet k b)
    (how : ξ ∈ ownedBy k a b (uinv k) η) :
    ‖BentS c k ξ η‖ = (1 / 2 : ℝ) ^ (b - a) := by
  have hk1 : 1 ≤ k := by omega
  have hξ : ξ ∈ levelSet k a := ownedBy_subset how
  have hbk : b + 2 ≤ k := level_bound hk hη
  obtain ⟨m, hm, hmo⟩ := level_split hη
  obtain ⟨n, hn, hnodd⟩ := level_split hξ
  have hd : (2 : ℤ) ^ (k - 1) ∣ alphaJ ((η : ℕ) : ℤ) ((ξ : ℕ) : ℤ) (uinv k) (b - a) :=
    (mem_ownedBy.1 how).2
  rw [BentS, inner_chiVec_UendS hc hk1 ξ η, norm_mul, norm_inv, Complex.norm_natCast,
    norm_upper_entryS (a := a) (b := b) hc hm hmo hn hnodd (uinv_odd hk1) (uinv_spec hk1)
      hab hbk hd]
  have hsplit : ((2 ^ (k - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (k - (b - a) - 1) * 2 ^ (b - a) := by
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, one_div, inv_pow]
  field_simp

/-- **(F3) THE GRAM IDENTITY, SHIFTED.**  `B_c* B_c = 2^{−d} · I`.

This is where the calibration's H1 becomes a theorem: the off-diagonal vanishes by **disjoint
support** (`ownedBy_disjoint`), not by any cancellation among the phases — which is why H3's
column-phase factorisation being false costs nothing. -/
theorem gram_upperS {c k a b : ℕ} (hc : c % 2 = 1) (hk : 2 ≤ k) (hab : a < b)
    {η η' : Fin (2 ^ (k - 1))} (hη : η ∈ levelSet k b) (hη' : η' ∈ levelSet k b) :
    ∑ ξ ∈ levelSet k a, (starRingEnd ℂ) (BentS c k ξ η) * BentS c k ξ η'
      = if η = η' then (((1 / 2 : ℝ) ^ (b - a) : ℝ) : ℂ) else 0 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hbk : b + 2 ≤ k := level_bound hk hη
  by_cases hne : η = η'
  · subst hne
    rw [if_pos rfl]
    have hrestrict : ∑ ξ ∈ levelSet k a, (starRingEnd ℂ) (BentS c k ξ η) * BentS c k ξ η
        = ∑ ξ ∈ ownedBy k a b (uinv k) η,
            (starRingEnd ℂ) (BentS c k ξ η) * BentS c k ξ η := by
      refine (Finset.sum_subset ownedBy_subset ?_).symm
      intro ξ hξ hno
      rw [BentS_eq_zero_of_not_owned hc hk hab hξ hη hno, map_zero, mul_zero]
    have hval : ∀ ξ ∈ ownedBy k a b (uinv k) η,
        (starRingEnd ℂ) (BentS c k ξ η) * BentS c k ξ η
          = (((1 / 4 : ℝ) ^ (b - a) : ℝ) : ℂ) := by
      intro ξ hξ
      rw [RCLike.conj_mul, norm_BentS_of_owned hc hk hab hη hξ]
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
    · have hno : ξ ∉ ownedBy k a b (uinv k) η' :=
        fun hcon => (disjoint_left.1 (ownedBy_disjoint (Ne.symm hne))) hcon how
      rw [BentS_eq_zero_of_not_owned hc hk hab hξ hη' hno, mul_zero]
    · rw [BentS_eq_zero_of_not_owned hc hk hab hξ hη how, map_zero, zero_mul]

/-- The shifted clean level block `P_a U_clean^{(c)} P_b`, as a linear map. -/
noncomputable def cleanBlockOpS (c k a b : ℕ) : Fsp k →ₗ[ℂ] Fsp k :=
  (P k a).comp ((UendS c k).comp (P k b))

/-- The same as a continuous linear map, so that it has an operator norm. -/
noncomputable def cleanBlockCLMS (c k a b : ℕ) : Fsp k →L[ℂ] Fsp k :=
  LinearMap.toContinuousLinearMap (cleanBlockOpS c k a b)

@[simp] theorem cleanBlockCLMS_apply (c k a b : ℕ) (x : Fsp k) :
    cleanBlockCLMS c k a b x = P k a (UendS c k (P k b x)) := rfl

/-- At `c = 1` the shifted clean block is `CleanBlock.cleanBlockCLM`.  Again not `rfl`. -/
theorem cleanBlockCLMS_one {k : ℕ} (hk : 1 ≤ k) (a b : ℕ) :
    cleanBlockCLMS 1 k a b = cleanBlockCLM k a b := by
  unfold cleanBlockCLMS cleanBlockCLM cleanBlockOpS cleanBlockOp UendS Uend
  rw [UcleanS_one hk]

/-- **The shifted clean upper block's norm, squared, exactly.**

`‖P_a U_clean^{(c)} P_b x‖² = 2^{−d}·‖P_b x‖²` — an **equality**, at every odd `c`.  This is
the statement `calibrate_general_shift.py`'s gate 2 measures (clean block norms exactly
`2^{-(b-a)/2}` for every `c`, to `1e-14`), now proved rather than calibrated. -/
theorem norm_sq_clean_blockS {c k a b : ℕ} (hc : c % 2 = 1) (hk : 2 ≤ k) (hab : a < b)
    (hbk : b + 2 ≤ k) (x : Fsp k) :
    ‖P k a (UendS c k (P k b x))‖ ^ 2 = (1 / 2 : ℝ) ^ (b - a) * ‖P k b x‖ ^ 2 := by
  classical
  have hk1 : 1 ≤ k := by omega
  have hu : Odd (uinv k) := uinv_odd hk1
  have hcoef : ∀ ξ : Fin (2 ^ (k - 1)),
      (@inner ℂ _ _ (chiVec k ξ) (UendS c k (P k b x)) : ℂ)
        = ∑ η ∈ levelSet k b,
            (@inner ℂ _ _ (chiVec k η) x : ℂ) * BentS c k ξ η := by
    intro ξ
    rw [P_apply, map_sum, inner_sum]
    exact Finset.sum_congr rfl fun η _ => by rw [map_smul, inner_smul_right, BentS]
  rw [norm_sq_P hk1 a, norm_sq_P hk1 b,
    ← owner_biUnion (k := k) (a := a) (b := b) (u := uinv k) hu (le_of_lt hab) hbk,
    Finset.sum_biUnion owner_pairwiseDisjoint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun η hη => ?_
  have hterm : ∀ ξ ∈ ownedBy k a b (uinv k) η,
      ‖(@inner ℂ _ _ (chiVec k ξ) (UendS c k (P k b x)) : ℂ)‖ ^ 2
        = (1 / 4 : ℝ) ^ (b - a) * ‖(@inner ℂ _ _ (chiVec k η) x : ℂ)‖ ^ 2 := by
    intro ξ hξ
    have hξa : ξ ∈ levelSet k a := ownedBy_subset hξ
    have hsingle : (@inner ℂ _ _ (chiVec k ξ) (UendS c k (P k b x)) : ℂ)
        = (@inner ℂ _ _ (chiVec k η) x : ℂ) * BentS c k ξ η := by
      rw [hcoef ξ]
      refine Finset.sum_eq_single_of_mem η hη ?_
      intro η' hη' hne
      have hno : ξ ∉ ownedBy k a b (uinv k) η' :=
        fun hcon => (disjoint_left.1 (ownedBy_disjoint hne)) hcon hξ
      rw [BentS_eq_zero_of_not_owned hc hk hab hξa hη' hno, mul_zero]
    rw [hsingle, norm_mul, mul_pow, norm_BentS_of_owned hc hk hab hη hξ, ← pow_mul,
      show (b - a) * 2 = 2 * (b - a) by ring, pow_mul]
    norm_num
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    ownedBy_card hu (le_of_lt hab) hbk hη, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- **(CLEAN) at a general shift, pointwise.** -/
theorem norm_clean_block_leS {c k a b : ℕ} (hc : c % 2 = 1) (hk : 2 ≤ k) (hab : a < b)
    (hbk : b + 2 ≤ k) (x : Fsp k) :
    ‖P k a (UendS c k (P k b x))‖ ≤ Assembly.s ^ (b - a) * ‖x‖ := by
  have hk1 : 1 ≤ k := by omega
  have hsq := norm_sq_clean_blockS hc hk hab hbk x
  have hs : (Assembly.s ^ (b - a)) ^ 2 = (1 / 2 : ℝ) ^ (b - a) := by
    rw [← pow_mul, mul_comm, pow_mul, Assembly.s_sq]
  have hPb : ‖P k b x‖ ≤ ‖x‖ := norm_P_le hk1 b x
  have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (b - a) := by positivity
  refine le_of_sq_le_sq (norm_nonneg _)
    (mul_nonneg (pow_nonneg Assembly.s_pos.le _) (norm_nonneg _)) ?_
  rw [hsq, mul_pow, hs]
  exact mul_le_mul_of_nonneg_left
    (by nlinarith [norm_nonneg (P k b x), norm_nonneg x]) hpos

/-- **LEMMA A AT A GENERAL ODD SHIFT.**  `‖P_a U_clean^{(c)} P_b‖ ≤ s^{b−a}`, `s = √(1/2)`,
for every odd `c` and every `a < b`.  This is brief step 4, and it closes Lemma A's clean
block norms for the shifted operator.

**Read the section preamble before citing this.**  It is Lemma A, not a certificate: the
defect half (Lemma B for general `c`) is open, so there is deliberately no shifted analogue of
`GramIdentity.gap_certificate_unconditional` in this file. -/
theorem clean_boundS {c k : ℕ} (hc : c % 2 = 1) (hk : 3 ≤ k) (a b : Fin (k - 1))
    (hab : (a : ℕ) < (b : ℕ)) :
    ‖cleanBlockCLMS c k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ)) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg Assembly.s_pos.le _) fun x => ?_
  rw [cleanBlockCLMS_apply]
  have hb := b.isLt
  exact norm_clean_block_leS hc (two_le hk) hab (by omega) x

/-- **Specialisation check.**  At `c = 1` the shifted clean bound is
`GramIdentity.clean_bound`, via `cleanBlockCLMS_one`. -/
theorem clean_boundS_one {k : ℕ} (hk : 3 ≤ k) (a b : Fin (k - 1))
    (hab : (a : ℕ) < (b : ℕ)) :
    ‖cleanBlockCLMS 1 k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ)) := by
  rw [cleanBlockCLMS_one (by omega : 1 ≤ k)]
  exact clean_bound hk a b hab

/-- **Non-vacuity.**  The shifted clean bound at a concrete second shift, so the theorem above
is not a statement about an empty hypothesis class.  `c = 5` is odd and is not `1`. -/
example {k : ℕ} (hk : 3 ≤ k) (a b : Fin (k - 1)) (hab : (a : ℕ) < (b : ℕ)) :
    ‖cleanBlockCLMS 5 k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ)) :=
  clean_boundS (by norm_num) hk a b hab

/-- And at `c = 2^m − 1`, the legitimate odd shift §4 discusses.  Still **not** `3x − 1`. -/
example {k m : ℕ} (hm : 1 ≤ m) (hk : 3 ≤ k) (a b : Fin (k - 1)) (hab : (a : ℕ) < (b : ℕ)) :
    ‖cleanBlockCLMS (2 ^ m - 1) k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ)) :=
  clean_boundS (sub_one_odd hm) hk a b hab

end CleanBlockShifted

/-!
--------------------------------------------------------------------------------
## §9. Axiom audit
--------------------------------------------------------------------------------
-/

#print axioms oddPart_odd
#print axioms syracuseS_one
#print axioms syracuseS_odd
#print axioms TcountS_one
#print axioms TkS_one
#print axioms TkS_nonneg
#print axioms cu_decompositionS
#print axioms cu_valuation_frozenS
#print axioms cu_syracuse_affineS
#print axioms cu_syracuse_affineS_one
#print axioms cu_syracuse_fibre_cardS
#print axioms oddPart_mul_odd
#print axioms oddPart_three_add
#print axioms oddPart_factor
#print axioms oddPart_injOn_block
#print axioms exists_shift_into_block
#print axioms oddPart_two_pow_mul
#print axioms existsUnique_in_block
#print axioms block_fibre_card
#print axioms block_fibre_card_self
#print axioms block_fibre_card_lower
#print axioms pair_count_closed
#print axioms sameOddPartCount_eq_sum
#print axioms sameOddPartCount_comm
#print axioms sameOddPartCount_union_left
#print axioms Icc_split_block
#print axioms Icc_disjoint_block
#print axioms sameOddPartCount_lower_block
#print axioms sameOddPartCount_block_block
#print axioms pairCount_double
#print axioms pairCount_two
#print axioms pairCount_pow_closed
#print axioms oddPart_lt_two_pow
#print axioms mul_three_mod_cancel
#print axioms fibVal3_eq_iff
#print axioms coll3_eq_pairCount
#print axioms coll3_closed
#print axioms coll3_le
#print axioms shellS_one
#print axioms shellS_eq
#print axioms shellS_oddpart
#print axioms sbMapS_one
#print axioms sbS_injOn
#print axioms sbS_image_eq
#print axioms sbS_bijective
#print axioms shellS_card
#print axioms three_coprime_two_pow
#print axioms three_pow_totient
#print axioms rstarS_spec
#print axioms sub_one_odd
-- §5, the shifted clean operator
#print axioms defectSetS_one
#print axioms defectS_iff
#print axioms rstarS_odd
#print axioms defectSetS_eq_singleton
#print axioms rstarS_one
#print axioms oddsS_partition
#print axioms cleanOddsS_eq_erase
#print axioms TkSC_one
#print axioms UcleanS_defect_row
#print axioms UcleanS_clean_row
#print axioms UcleanS_one
#print axioms od_eq_rstarS_iff
#print axioms sum_fin_cleanS
-- §6, the shifted character pairing
#print axioms TcountS_even_zero
#print axioms sum_targetsS
#print axioms cleanEntryS_one
#print axioms inner_chiVec_UendS
-- §7, the shifted entry theorem
#print axioms syracuseS_on_shellS
#print axioms shellS_reindex
#print axioms phase_congrS
#print axioms shell_character_sumS
#print axioms shell_character_sumS_one
#print axioms shellS_disjoint
#print axioms maskedOddsS_one
#print axioms syracuseS_eq_quot
#print axioms char_col_as_liftS
#print axioms gauss_collapseS
#print axioms cleanEntryS_eq_masked
#print axioms upper_entry_eqS
#print axioms norm_shift_phase
#print axioms upper_entry_eqS_zero
-- §8, Lemma A's clean block norms at a general shift
#print axioms norm_upper_entryS
#print axioms BentS_one
#print axioms BentS_eq_zero_of_not_owned
#print axioms norm_BentS_of_owned
#print axioms gram_upperS
#print axioms cleanBlockCLMS_apply
#print axioms cleanBlockCLMS_one
#print axioms norm_sq_clean_blockS
#print axioms norm_clean_block_leS
#print axioms clean_boundS
#print axioms clean_boundS_one

end ShiftedOperator
