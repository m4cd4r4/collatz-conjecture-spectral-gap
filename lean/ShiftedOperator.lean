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

## THE CALIBRATION THAT JUSTIFIED STARTING

Run before writing any of this (`calibrate_general_shift.py`, public repo).  Four gates, every
odd `c` tested, `k = 4..8`, all pass:

* `cert_c(k) ≤ 0.853553...` — the same **bound**, not the same value (measured `0.604`–`0.682`);
* **Lemma A's clean block norms are exactly `2^{-(b-a)/2}` for every odd `c`, to `1e-14`.**  This
  is the structural fact the certificate rests on and it is completely shift-independent — the
  decisive evidence that the generalisation is real rather than hoped for;
* Lemma B's `‖D‖₂ ≤ √3 · 2^{-k/2}` holds throughout;
* `rank(D) = 1`, with `r*` the solution of `3r + c ≡ 0 (mod 2^k)`.

**One risk carried forward:** gate 3 is nearly saturated at `c = 2^k - 1`, i.e. exactly the
`3x-1` case — at `k = 8`, `0.108112` against a limit of `0.108253`, a margin of `0.13%`.  The
`√3` constant may be sharp there, so no later step may lean on slack that does not exist for
the shift the control experiment actually cares about.

## THE ONE STRUCTURAL DIFFERENCE FROM `c = 1`

`CollisionBound.rstar k = (2 ^ ek k - 1) / 3` solves `3r + 1 = 2^(ek k)`, and that closed form
is specific to the shift `1`.  For general `c` the defect residue is the solution of
`3r + c ≡ 0 (mod 2^k)`, given here as `rstarS c k` via the inverse of `3`.  Everything else in
this file is `c`-uniform.

Sorry-free.  Specialisation lemmas throughout, mutation table below, axiom audit `§6`.

## MUTATIONS (12, all fail)

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
## §4. Non-vacuity: the two maps the control experiment compares
--------------------------------------------------------------------------------
-/

/-- `2^k - 1` is odd for `k ≥ 1`: the `3x−1` shift is in scope of every theorem above. -/
theorem sub_one_odd {k : ℕ} (hk : 1 ≤ k) : (2 ^ k - 1) % 2 = 1 := by
  have h : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hp : 0 < 2 ^ (k - 1) := Nat.two_pow_pos _
  omega

/-- The `3x+1` step sends odd residues to odd residues. -/
example {n : ℕ} (hn : n % 2 = 1) : syracuseS 1 n % 2 = 1 :=
  syracuseS_odd (by norm_num) hn

/-- **And so does the `3x−1` step**, at every level.  This is the first Lean statement in the
certificate tree that is about the `3x−1` operator rather than about `3x+1`. -/
example {k n : ℕ} (hk : 1 ≤ k) (hn : n % 2 = 1) : syracuseS (2 ^ k - 1) n % 2 = 1 :=
  syracuseS_odd (sub_one_odd hk) hn

/-- **Non-vacuity for `3x−1`.**  The fibre count holds for the shift the control experiment
cares about, not merely for a hypothetical odd `c`. -/
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
#print axioms three_coprime_two_pow
#print axioms three_pow_totient
#print axioms rstarS_spec
#print axioms sub_one_odd

end ShiftedOperator
