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

Two things ARE finished, and the boundary between them and the rest is the point of this note:

1. **Coset uniformity for a general odd shift** (§2b) — the engine Lemma A runs on, `c`-uniform.
2. **Lemma B's `a = 3` case, complete and sorry-free** (§2c, 2026-08-05):
   `coll3_closed : coll3 k + 2 = 3 * 2 ^ k`.  `a = 3` was the one offset case a general odd
   shift produces that `CollisionBound.lean` did not already cover.  **Read the caveat at the
   end of §2c before citing this**: it is a complete theorem about the `a = 3` AP model, and the
   theorem tying that model to the actual `3x+c` defect fibre — the general-`c` analogue of
   `CollisionBound.syracuse_defect_fibre` — is not proved here.

Still open for general `c`: **Lemma A's clean block norms** (calibrated to `1e-14`, not proved)
and the assembly.  Until both land, the `3x-1` control experiment remains a Python observation.

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

Sorry-free.  Specialisation lemmas throughout, mutation table below, axiom audit `§6`.

## MUTATIONS (30, all fail)

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
-/

import TransferOperator

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
## §5. Axiom audit
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
#print axioms three_coprime_two_pow
#print axioms three_pow_totient
#print axioms rstarS_spec
#print axioms sub_one_odd

end ShiftedOperator
