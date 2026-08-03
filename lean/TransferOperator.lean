/-
# `T_k`: the Syracuse transfer operator, defined

Task L7. Every prior file in this development states things *about* an operator without
ever defining one. `Assembly.lean` §7 delta (5) records that plainly:

> **(5) The operator is not defined.** `T_k` itself - the Syracuse transfer operator on odd
> residues mod `2^k` - is never constructed in Lean. [...] Consequence: `colStoch` is assumed
> rather than proved from a definition [...] Label: **NOT DONE**, stated plainly.

This file constructs `T_k` and proves its structural facts from that definition.

## SCOPE DECISION (option C1) - read this before reading anything else

L7 offered three scopes: (C1) define `T_k` and prove its basic structural facts; (C2) C1 plus
the character transform and the definition of `Q[a,b]`; (C3) C2 plus discharging
`hQupper`/`hQlower`. **This file takes (C1), and only (C1).**

Concretely it proves, for all `k`:

* `Tcount_col_sum`, `Tk_col_sum` - **column-stochasticity, from the definition.** This
  discharges `Assembly.LemmaAFacts.colStoch` for a concrete operator (§5).
* `attained_eq_coset`, `clean_col_count` - the **exact** column profile of every clean
  source `r` with `v := v2(3r+1) < k`: mass `2^(k-v)` on each of the `2^v` targets of the
  coset `q0 + 2^(k-v)·ℤ`, `0` elsewhere (CU).
* `defect_col_eq_cf` - the defect column IS `CollisionBound.cf`, so `Assembly.cvec` (which is
  `cf k t / 2^k` by definition) is literally a column of `T_k` (§4).
* `Tk_row_sum` - the **exact `T·1` identity**
  `T_k · 1 = (1 - 2^{1-k})·1 + c`, the boxed non-uniform-stationarity warning of
  `THEOREM.md` Part I.1, with `c` the defect column. Assembled from CU + SB.

## What is NOT discharged (do not soften this)

**`Assembly.LemmaAFacts.hQupper` and `hQlower` remain OPEN _as of this file_. 0 of the 2
residue fields are closed by this file.** (STATUS 2026-08-03: both are since closed for the
concrete `T_k` - `hQlower` at L12, `hQupper` at F3. The per-file claim stands.) Neither is even *stated* here: both are bounds on
`Q[a,b] = ‖P_a U_k P_b‖₂`, which needs the character-basis transform of `T_k` and the
operator norms of its level blocks. This file does not build the character basis, does not
define `Q`, and proves nothing about any operator norm. What it removes is the *prerequisite*
both fields were blocked on - "no file in this development defines `T_k`" (L6's closing
finding) - not the fields themselves.

## Orientation (pinned by task T3.5; an orientation drift nearly shipped in L2)

`Tcount k u r` is indexed **target-first**: `u` is the target odd residue, `r` the source.
`U = Tᵀ`. Under this convention:

* the **column** sums are the trivial ones - `∑_u T[u,r] = 1` for every source `r`, because
  the `2^k` lifts of `r` are partitioned by their targets (`Tcount_col_sum`). This is
  `1ᵀ T = 1ᵀ`, i.e. column-stochasticity.
* the **row** sums are the non-trivial ones - `∑_r T[u,r]` is NOT `1`, and computing it is the
  whole content of §6. It needs CU *and* SB, and its answer `(1 - 2^{1-k}) + c_u` is exactly
  why the stationary vector is not uniform.

Getting these the wrong way round makes the hard half look free. They are not interchangeable.

## Sign scope (STANDING GATE, inherited from `Assembly.lean` §GATE 1)

`3` appears here (in `syracuse`), so unlike `LemmaA.lean` this file is not literally
sign-agnostic. It is still **not** evidence about Collatz cycles: everything proved below is
a counting fact about lifts and valuations, and the `3x-1` operator satisfies the same shape
(`CYCLE_CLAIM_REFUTED.md`). Nothing here is an obstruction to cycles of anything.

## Calibration

`syracuse` routes through `v2 = padicValNat 2`, which the kernel cannot reduce, so `Tcount` is
not directly `#eval`-able. §2 therefore builds a **computable mirror** `oddPartC`, proves it
equal to `CollisionBound.oddPart` (`oddPartC_eq`, not asserted), and `#guard`s the resulting
`TcountC` against a direct Python enumeration of `build_T` for `k = 3, 4`. The guarded numbers
are the same ones the corpus's own `analytic_proofs.build_T` produces; the session-side
enumeration additionally reproduced `cert(8) = 0.634659`, `cert(13) = 0.634412`, binding row
`e* = k - a* = 4` for `k = 4..13`, `ρ(Q_8) = 0.566061` and `|λ₂(T_8)| = 0.2549` from this
same matrix. Sorry-free; axioms audited in §8.
-/

import CollisionBound
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace TransferOperator

open Finset CountingLemmas CollisionBound GapCertificate

/-!
--------------------------------------------------------------------------------
## §1. The operator
--------------------------------------------------------------------------------

`T_k[u, r] := (1 / 2^k) · #{ m < 2^k : Syr(r + m·2^k) ≡ u (mod 2^k) }`.

The average is over the **finite lift window** `m ∈ [0, 2^k)`, exactly as in
`analytic_proofs.build_T`. States are odd residues mod `2^k`; `od s = 2s+1` indexes them by
`s < 2^(k-1)`.
-/

/-- The odd residue with index `s`. -/
def od (s : ℕ) : ℕ := 2 * s + 1

theorem od_odd (s : ℕ) : od s % 2 = 1 := by unfold od; omega

theorem od_lt {k s : ℕ} (hk : 1 ≤ k) (hs : s < 2 ^ (k - 1)) : od s < 2 ^ k := by
  have h : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  unfold od; omega

/-- The index of an odd residue. Inverse to `od` on odd residues. -/
def idx (u : ℕ) : ℕ := u / 2

theorem od_idx {u : ℕ} (hu : u % 2 = 1) : od (idx u) = u := by
  unfold od idx; omega

theorem idx_lt {k u : ℕ} (hk : 1 ≤ k) (hu : u < 2 ^ k) : idx u < 2 ^ (k - 1) := by
  have h : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  unfold idx; omega

/-- **The transition count.** `Tcount k u r` is the number of lifts `m ∈ [0, 2^k)` of the
source odd residue `r` whose Syracuse image is `≡ u (mod 2^k)`. Target-first. -/
def Tcount (k u r : ℕ) : ℕ :=
  ((range (2 ^ k)).filter (fun m => syracuse (r + m * 2 ^ k) % 2 ^ k = u)).card

/-- **The transfer operator `T_k`**, as a real matrix on the `2^(k-1)` odd residues mod `2^k`,
target-first (`T[u,r]`, `U = Tᵀ`). -/
noncomputable def Tk (k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℝ :=
  fun u r => (Tcount k (od u) (od r) : ℝ) / 2 ^ k

@[simp] theorem Tk_apply (k : ℕ) (u r : Fin (2 ^ (k - 1))) :
    Tk k u r = (Tcount k (od u) (od r) : ℝ) / 2 ^ k := rfl

theorem Tk_nonneg (k : ℕ) (u r : Fin (2 ^ (k - 1))) : 0 ≤ Tk k u r := by
  rw [Tk_apply]; positivity

/-!
--------------------------------------------------------------------------------
## §2. A computable mirror, for calibration only
--------------------------------------------------------------------------------

`v2 = padicValNat 2` does not reduce in the kernel, so `#eval Tcount` is impossible.
`oddPartC` is a fuel-free structural recursion computing the same function; `oddPartC_eq`
proves they agree, so the `#guard`s below test the REAL definition, not a lookalike.
-/

/-- Computable odd part. -/
def oddPartC (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 1 then n else oddPartC (n / 2)
termination_by n
decreasing_by omega

/-- `oddPartC = oddPart` on positives. Proved, not assumed - so the calibration below is a
check on `syracuse` itself. -/
theorem oddPartC_eq : ∀ n : ℕ, n ≠ 0 → oddPartC n = oddPart n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [oddPartC]
    rw [if_neg hn]
    by_cases hodd : n % 2 = 1
    · rw [if_pos hodd]
      unfold oddPart
      rw [v2_odd_mod n hodd, pow_zero, Nat.div_one]
    · rw [if_neg hodd]
      have h2 : n = 2 ^ 1 * (n / 2) := by omega
      have hne : n / 2 ≠ 0 := by omega
      rw [ih (n / 2) (by omega) hne]
      conv_rhs => rw [h2]
      rw [oddPart_two_pow_mul hne]

/-- Computable Syracuse, for calibration. -/
def syracuseC (n : ℕ) : ℕ := if n % 2 = 0 then n else oddPartC (3 * n + 1)

theorem syracuseC_eq (n : ℕ) : syracuseC n = syracuse n := by
  unfold syracuseC syracuse
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact oddPartC_eq (3 * n + 1) (by omega)

/-- Computable transition count. -/
def TcountC (k u r : ℕ) : ℕ :=
  ((range (2 ^ k)).filter (fun m => syracuseC (r + m * 2 ^ k) % 2 ^ k = u)).card

theorem TcountC_eq (k u r : ℕ) : TcountC k u r = Tcount k u r := by
  unfold TcountC Tcount
  congr 1
  apply filter_congr
  intro m _
  rw [syracuseC_eq]

/-- The `u`-row of the count matrix, at level `k`, as a list over source INDICES. -/
def TrowC (k u : ℕ) : List ℕ := (List.range (2 ^ (k - 1))).map (fun s => TcountC k u (od s))

-- Direct Python enumeration of `build_T` at k = 3 (counts, target-major).
#guard TrowC 3 1 = [2, 4, 3, 0]
#guard TrowC 3 3 = [2, 0, 1, 4]
#guard TrowC 3 5 = [2, 4, 2, 0]
#guard TrowC 3 7 = [2, 0, 2, 4]
-- k = 4, the first and last rows and the defect column's row profile.
#guard TrowC 4 1 = [4, 0, 4, 0, 0, 8, 2, 0]
#guard TrowC 4 15 = [0, 0, 1, 0, 4, 0, 2, 8]
-- Column sums are `2^k` (the theorem of §3, evaluated).
#guard ((List.range 8).map (fun s => (List.range 8).map (fun t => TcountC 4 (od t) (od s))
  |>.sum)) = [16, 16, 16, 16, 16, 16, 16, 16]
-- Row sums are NOT constant - the whole point of §6. `2^4 - 2 = 14` plus the defect column.
#guard ((List.range 8).map (fun t => (List.range 8).map (fun s => TcountC 4 (od t) (od s))
  |>.sum)) = [18, 15, 17, 17, 15, 16, 15, 15]
#guard ((List.range 8).map (fun t => TcountC 4 (od t) (od 2))) = [4, 1, 3, 3, 1, 2, 1, 1]

/-!
--------------------------------------------------------------------------------
## §3. Column-stochasticity (`1ᵀ T = 1ᵀ`), from the definition
--------------------------------------------------------------------------------

The `2^k` lifts of a source are partitioned by their target residue, so the column sums are
`2^k` counts, i.e. `1` after normalisation. This is the TRIVIAL of the two sums under the
target-first orientation - see the header.
-/

/-- The odd part of a positive number is odd. -/
theorem oddPart_odd {n : ℕ} (hn : n ≠ 0) : oddPart n % 2 = 1 := by
  have hsplit := two_pow_mul_oddPart hn
  have hnd := ((v2_eq_iff_dvd hn).1 rfl).2
  by_contra hc
  obtain ⟨c, hc2⟩ : 2 ∣ oddPart n := by omega
  exact hnd ⟨c, by
    calc n = 2 ^ v2 n * oddPart n := hsplit.symm
      _ = 2 ^ (v2 n + 1) * c := by rw [hc2, pow_succ]; ring⟩

/-- `Syr(n)` is odd for odd `n`. -/
theorem syracuse_odd {n : ℕ} (hn : n % 2 = 1) : syracuse n % 2 = 1 := by
  unfold syracuse
  rw [if_neg (by omega)]
  exact oddPart_odd (by omega)

/-- The lift `r + m·2^k` of an odd `r` is odd (`k ≥ 1`). -/
theorem lift_odd {k r m : ℕ} (hk : 1 ≤ k) (hr : r % 2 = 1) : (r + m * 2 ^ k) % 2 = 1 := by
  have h2 : (2 : ℕ) ∣ m * 2 ^ k := (dvd_pow_self 2 (by omega : k ≠ 0)).mul_left m
  omega

/-- The target of a lift is a legitimate index: `idx (Syr(r + m·2^k) mod 2^k) < 2^(k-1)`.
(`_hr` is retained for fidelity to the setting and is not used: the bound holds for any
residue, oddness is what makes `od (idx ·)` invert it - see `Tcount_col_sum`.) -/
theorem tgt_lt {k r m : ℕ} (hk : 1 ≤ k) (_hr : r % 2 = 1) :
    idx (syracuse (r + m * 2 ^ k) % 2 ^ k) < 2 ^ (k - 1) :=
  idx_lt hk (Nat.mod_lt _ (Nat.two_pow_pos k))

/-- **COLUMN-STOCHASTICITY, count form.** `∑_u Tcount k (od u) r = 2^k` for every odd source
`r`: the lift window is partitioned by target.

Not closable by `decide`/`omega` for symbolic `k` - it is `card_eq_sum_card_fiberwise` against
`tgt_lt`, and it is the statement that FAILS if the target index leaves range (i.e. if
`Syr` were not odd, the orientation trap's arithmetic twin). -/
theorem Tcount_col_sum {k r : ℕ} (hk : 1 ≤ k) (hr : r % 2 = 1) :
    ∑ u ∈ range (2 ^ (k - 1)), Tcount k (od u) r = 2 ^ k := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun m => idx (syracuse (r + m * 2 ^ k) % 2 ^ k))
    (s := range (2 ^ k)) (t := range (2 ^ (k - 1)))
    (fun m _ => Finset.mem_range.mpr (tgt_lt hk hr))
  rw [Finset.card_range] at h
  refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) h.symm
  unfold Tcount
  congr 1
  apply filter_congr
  intro m _
  have h2 : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hodd : syracuse (r + m * 2 ^ k) % 2 ^ k % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ h2]
    exact syracuse_odd (lift_odd (k := k) (r := r) (m := m) hk hr)
  constructor
  · intro hm
    show idx (syracuse (r + m * 2 ^ k) % 2 ^ k) = u
    rw [hm]; unfold od idx; omega
  · intro hm
    have hm' : idx (syracuse (r + m * 2 ^ k) % 2 ^ k) = u := hm
    rw [← hm', od_idx hodd]

/-- **COLUMN-STOCHASTICITY.** Every column of `T_k` sums to `1`. -/
theorem Tk_col_sum {k : ℕ} (hk : 1 ≤ k) (r : Fin (2 ^ (k - 1))) :
    ∑ u : Fin (2 ^ (k - 1)), Tk k u r = 1 := by
  have hsum : ∑ u : Fin (2 ^ (k - 1)), (Tcount k (od u) (od r) : ℝ)
      = ((2 : ℕ) ^ k : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun u => (Tcount k (od u) (od r) : ℝ)) (2 ^ (k - 1))]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Tcount_col_sum hk (od_odd r))
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  calc ∑ u : Fin (2 ^ (k - 1)), Tk k u r
      = (∑ u : Fin (2 ^ (k - 1)), (Tcount k (od u) (od r) : ℝ)) / 2 ^ k := by
        rw [Finset.sum_div]; rfl
    _ = 1 := by rw [hsum]; push_cast; field_simp

/-!
--------------------------------------------------------------------------------
## §4. The defect column IS `Assembly.cvec`
--------------------------------------------------------------------------------

`CollisionBound.rstar k` is the unique odd residue with `v2(3r+1) ≥ k`, and
`CollisionBound.cf k t` counts its fibre. §4 shows `cf` is literally the `r*` COLUMN of the
matrix defined in §1 - so `Assembly.cvec` is a column of `T_k`, not a separately-postulated
vector.
-/

/-- **The defect column of `T_k` is `cf`.** `Tcount k u (rstar k) = cf k u`. -/
theorem defect_col_eq_cf {k : ℕ} (hk : 1 ≤ k) (u : ℕ) :
    Tcount k u (rstar k) = cf k u := by
  unfold Tcount cf
  congr 1
  apply filter_congr
  intro m _
  rw [syracuse_defect_fibre hk m]

/-!
--------------------------------------------------------------------------------
## §5. `Assembly.LemmaAFacts.colStoch`, DISCHARGED for the concrete operator
--------------------------------------------------------------------------------

`Assembly.lean` §7 delta (5) labels this **NOT DONE**: *"`colStoch` is assumed rather than
proved from a definition, which is a real gap against L5's own acceptance list."* Below,
`Tend k` is `T_k` as an endomorphism of `EuclideanSpace ℂ (Fin (2^(k-1)))`, `onesCov k` is
the Perron covector `1ᵀ`, and `colStoch_concrete` is `φ ∘ₗ T = φ` - the literal shape of the
manifest field - proved from `Tk_col_sum`.
-/

/-- `T_k` complexified. -/
noncomputable def TkC (k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℂ :=
  fun u r => (Tcount k (od u) (od r) : ℂ) / 2 ^ k

/-- `T_k` as an endomorphism of `ℓ²`: the matrix `TkC k` acting on Euclidean space. -/
noncomputable def Tend (k : ℕ) : Module.End ℂ (EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :=
  Matrix.toEuclideanLin (TkC k)

@[simp] theorem Tend_apply (k : ℕ) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1))))
    (u : Fin (2 ^ (k - 1))) : (Tend k x) u = ∑ r, TkC k u r * x r := rfl

/-- The Perron covector `1ᵀ`. -/
noncomputable def onesCov (k : ℕ) : EuclideanSpace ℂ (Fin (2 ^ (k - 1))) →ₗ[ℂ] ℂ where
  toFun x := ∑ u, x u
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

@[simp] theorem onesCov_apply (k : ℕ) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    onesCov k x = ∑ u, x u := rfl

/-- Column-stochasticity of the complexified matrix. -/
theorem TkC_col_sum {k : ℕ} (hk : 1 ≤ k) (r : Fin (2 ^ (k - 1))) :
    ∑ u : Fin (2 ^ (k - 1)), TkC k u r = 1 := by
  have hsum : ∑ u : Fin (2 ^ (k - 1)), (Tcount k (od u) (od r) : ℂ)
      = ((2 : ℕ) ^ k : ℂ) := by
    rw [Fin.sum_univ_eq_sum_range (fun u => (Tcount k (od u) (od r) : ℂ)) (2 ^ (k - 1))]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (Tcount_col_sum hk (od_odd r))
  have h2 : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero k (by norm_num)
  calc ∑ u : Fin (2 ^ (k - 1)), TkC k u r
      = (∑ u : Fin (2 ^ (k - 1)), (Tcount k (od u) (od r) : ℂ)) / 2 ^ k := by
        rw [Finset.sum_div]; rfl
    _ = 1 := by rw [hsum]; push_cast; field_simp

/-- **`colStoch`, DISCHARGED.** `1ᵀ ∘ T_k = 1ᵀ`, in exactly the shape
`Assembly.LemmaAFacts.colStoch` demands, for the operator defined in §1. -/
theorem colStoch_concrete {k : ℕ} (hk : 1 ≤ k) :
    (onesCov k) ∘ₗ (Tend k) = onesCov k := by
  ext x
  show ∑ u, (Tend k x) u = ∑ r, x r
  calc ∑ u, (Tend k x) u = ∑ u, ∑ r, TkC k u r * x r := rfl
    _ = ∑ r, (∑ u, TkC k u r) * x r := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ => by rw [Finset.sum_mul]
    _ = ∑ r, x r := by
        exact Finset.sum_congr rfl fun r _ => by rw [TkC_col_sum hk r, one_mul]

/-!
--------------------------------------------------------------------------------
## §6. The exact `T·1` identity (the non-uniform-stationarity warning, as a theorem)
--------------------------------------------------------------------------------

`THEOREM.md` Part I.1 carries a boxed warning that `T_k` is NOT doubly stochastic and its
stationary vector is NOT uniform. The exact statement is

```
    T_k · 1  =  (1 - 2^{1-k}) · 1  +  c ,        c = the defect column.
```

This is the NON-trivial sum (see the header): the row sums. It needs both uniform-fibre
lemmas of `CountingLemmas`:

* **CU** gives the profile of a clean column: `2^(k-j)` on each target of the coset, `0`
  elsewhere.
* **SB** gives that within shell `j`, exactly ONE source has that coset containing the given
  target - so shell `j` contributes exactly `2^(k-j)` to the row, whatever the target is.

Summing `∑_{j=1}^{k-1} 2^(k-j) = 2^k - 2` gives the constant, and the one source not in any
shell is `r*`, contributing its column `c`.
-/

/-- `Syr(r + m·2^k) mod 2^k = (q0 + cuMap k v m) mod 2^k`, the form CU's counting lemmas
consume. (Extracted from the proof of `cu_syracuse_image_card`.) -/
theorem syracuse_lift_mod {r k : ℕ} (hr : r % 2 = 1) (hK : v2 (3 * r + 1) < k) (m : ℕ) :
    syracuse (r + m * 2 ^ k) % 2 ^ k
      = ((3 * r + 1) / 2 ^ v2 (3 * r + 1) + cuMap k (v2 (3 * r + 1)) m) % 2 ^ k := by
  set v := v2 (3 * r + 1) with hv
  rw [cu_syracuse_affine r m k hr hK]
  unfold cuMap
  have h1 : ((3 * r + 1) / 2 ^ v + (3 * 2 ^ (k - v) * m) % 2 ^ k) % 2 ^ k
      = ((3 * r + 1) / 2 ^ v + 3 * 2 ^ (k - v) * m) % 2 ^ k :=
    Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
  rw [h1, show (3 * r + 1) / 2 ^ v + 3 * m * 2 ^ (k - v)
        = (3 * r + 1) / 2 ^ v + 3 * 2 ^ (k - v) * m by ring]

/-- The set of targets actually attained by the source `r` over the lift window. -/
def attained (k r : ℕ) : Finset ℕ :=
  (range (2 ^ k)).image (fun m => syracuse (r + m * 2 ^ k) % 2 ^ k)

/-- The coset of targets CU predicts: `q0 + 2^(k-v)·ℤ` intersected with `[0, 2^k)`. -/
def coset (k r : ℕ) : Finset ℕ :=
  (range (2 ^ k)).filter (fun u =>
    u % 2 ^ (k - v2 (3 * r + 1))
      = ((3 * r + 1) / 2 ^ v2 (3 * r + 1)) % 2 ^ (k - v2 (3 * r + 1)))

/-- **CU: the attained set IS the coset.** One easy inclusion (`attained ⊆ coset`, because
`cuMap`'s values are multiples of `2^(k-v)`) plus equal cardinalities: `|attained| = 2^v` is
CU's image count, `|coset| = 2^v` is a residue-class count.

Note the direction - **image size `2^v`, fibre size `2^(k-v)`** - which an earlier plan had
inverted. Mutating either exponent breaks the `card_le` step, so this is load-bearing. -/
theorem attained_eq_coset {k r : ℕ} (hr : r % 2 = 1) (hK : v2 (3 * r + 1) < k) :
    attained k r = coset k r := by
  have hdvd : (2 : ℕ) ^ (k - v2 (3 * r + 1)) ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro u hu
    simp only [attained, mem_image, mem_range] at hu
    obtain ⟨m, _, rfl⟩ := hu
    simp only [coset, mem_filter, mem_range]
    rw [syracuse_lift_mod hr hK m]
    refine ⟨Nat.mod_lt _ (Nat.two_pow_pos k), ?_⟩
    rw [Nat.mod_mod_of_dvd _ hdvd]
    obtain ⟨c, hc⟩ : (2 : ℕ) ^ (k - v2 (3 * r + 1)) ∣ cuMap k (v2 (3 * r + 1)) m := by
      unfold cuMap
      exact (Nat.dvd_mod_iff hdvd).mpr ⟨3 * m, by ring⟩
    rw [hc, Nat.add_mul_mod_self_left]
  · have hA : (attained k r).card = 2 ^ v2 (3 * r + 1) := cu_syracuse_image_card hr hK
    have hC : (coset k r).card = 2 ^ v2 (3 * r + 1) := by
      unfold coset
      rw [residue_class_card (m := k - v2 (3 * r + 1)) (k := k) (by omega)
        (Nat.mod_lt _ (Nat.two_pow_pos (k - v2 (3 * r + 1)))),
        show k - (k - v2 (3 * r + 1)) = v2 (3 * r + 1) by omega]
    rw [hA, hC]

/-- **CU, column profile.** For a clean source `r` (`v := v2(3r+1) < k`), the column count at a
target `u < 2^k` is `2^(k-v)` on the `2^v` targets of the coset and `0` elsewhere. -/
theorem clean_col_count {k r u : ℕ} (hr : r % 2 = 1) (hK : v2 (3 * r + 1) < k)
    (_hu : u < 2 ^ k) :
    Tcount k u r = if u ∈ coset k r then 2 ^ (k - v2 (3 * r + 1)) else 0 := by
  by_cases hcase : u ∈ coset k r
  · rw [if_pos hcase]
    rw [← attained_eq_coset hr hK] at hcase
    obtain ⟨m0, _, hm0⟩ := Finset.mem_image.mp hcase
    unfold Tcount
    have hrw : (range (2 ^ k)).filter (fun m => syracuse (r + m * 2 ^ k) % 2 ^ k = u)
        = (range (2 ^ k)).filter (fun m =>
            syracuse (r + m * 2 ^ k) % 2 ^ k = syracuse (r + m0 * 2 ^ k) % 2 ^ k) := by
      apply filter_congr; intro m _; rw [hm0]
    rw [hrw, cu_syracuse_fibre_card hr hK m0]
  · rw [if_neg hcase]
    rw [← attained_eq_coset hr hK] at hcase
    unfold Tcount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m hm hmu
    exact hcase (Finset.mem_image.mpr ⟨m, hm, hmu⟩)

/-!
### The shell sum

`sbMap k j r = ((3r+1)/2^j) mod 2^(k-j)` is exactly the coset label appearing in
`clean_col_count`, so the hit criterion for a shell-`j` source is `sbMap k j r = u mod 2^(k-j)`,
and SB says exactly one source in the shell satisfies it.
-/

/-- On the shell `S_j` the CU coset criterion is literally `sbMap`, SB's map. -/
theorem shell_col_count {k j u : ℕ} (_hj : 1 ≤ j) (hjk : j + 1 ≤ k) {r : ℕ}
    (hr : r ∈ shell k j) (hu : u < 2 ^ k) :
    Tcount k u r = if sbMap k j r = u % 2 ^ (k - j) then 2 ^ (k - j) else 0 := by
  simp only [shell, mem_filter, mem_range] at hr
  obtain ⟨_, _, hodd, hval⟩ := hr
  have hK : v2 (3 * r + 1) < k := by omega
  rw [clean_col_count hodd hK hu]
  have hmem : (u ∈ coset k r) ↔ (sbMap k j r = u % 2 ^ (k - j)) := by
    unfold coset sbMap
    rw [hval, mem_filter, mem_range]
    constructor
    · rintro ⟨_, h⟩; exact h.symm
    · intro h; exact ⟨hu, h.symm⟩
  rw [hval] at *
  by_cases h : sbMap k j r = u % 2 ^ (k - j)
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hmem.mp hc)), if_neg h]

/-- **The shell contributes `2^(k-j)` to every row.** For an odd target `u < 2^k`, summing the
column counts over the shell `S_j` gives `2^(k-j)` - independent of `u`. This is SB: exactly
one source in the shell owns the target. -/
theorem shell_row_contrib {k j u : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    (hu : u < 2 ^ k) (huodd : u % 2 = 1) :
    ∑ r ∈ shell k j, Tcount k u r = 2 ^ (k - j) := by
  have hkj : 1 ≤ k - j := by omega
  have hcongr : ∑ r ∈ shell k j, Tcount k u r
      = ∑ r ∈ shell k j, (if sbMap k j r = u % 2 ^ (k - j) then 2 ^ (k - j) else 0) :=
    Finset.sum_congr rfl fun r hr => shell_col_count hj hjk hr hu
  rw [hcongr, ← Finset.sum_filter]
  have htarget : u % 2 ^ (k - j) ∈ oddResidues (k - j) := by
    unfold oddResidues
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos (k - j))), ?_⟩
    have h2 : (2 : ℕ) ∣ 2 ^ (k - j) := dvd_pow_self 2 (by omega)
    rw [Nat.mod_mod_of_dvd _ h2]
    exact huodd
  obtain ⟨r0, hr0, hr0eq⟩ := (sb_bijective hj hjk).surjOn (by simpa using htarget)
  have hfilter : (shell k j).filter (fun r => sbMap k j r = u % 2 ^ (k - j)) = {r0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨mem_filter.mpr ⟨by simpa using hr0, hr0eq⟩, ?_⟩
    intro x hx
    obtain ⟨hxmem, hxeq⟩ := mem_filter.mp hx
    exact sb_injOn hj hjk (by simpa using hxmem) (by simpa using hr0) (by rw [hxeq, hr0eq])
  rw [hfilter, Finset.sum_singleton]

/-- `∑_{j=1}^{k-1} 2^(k-j) = 2^k - 2`. -/
theorem geom_row_const {k : ℕ} (hk : 1 ≤ k) : ∑ j ∈ Icc 1 (k - 1), 2 ^ (k - j) = 2 ^ k - 2 := by
  have hrw : ∑ j ∈ Icc 1 (k - 1), (2 : ℕ) ^ (k - j)
      = ∑ j ∈ Icc 1 (k - 1), 2 * 2 ^ ((k - 1) - j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [mem_Icc] at hj
    rw [show k - j = ((k - 1) - j) + 1 by omega, pow_succ]
    ring
  rw [hrw, ← Finset.mul_sum, geom_sum_shells]
  have h1 : (1 : ℕ) ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-- **THE `T·1` IDENTITY, count form.** For every odd target `u < 2^k`,
`∑_r Tcount k u r = (2^k - 2) + cf k u`, the sum being over all `2^(k-1)` odd sources.

This is the exact identity `T·1 = (1 - 2^{1-k})·1 + c` before normalisation. The `2^k - 2` is
uniform in `u`; the defect column `cf` is what breaks uniform stationarity. -/
theorem Tcount_row_sum {k u : ℕ} (hk : 1 ≤ k) (hu : u < 2 ^ k) (huodd : u % 2 = 1) :
    ∑ r ∈ oddResidues k, Tcount k u r = (2 ^ k - 2) + cf k u := by
  have hdisj : (↑(Icc 1 (k - 1)) : Set ℕ).PairwiseDisjoint (shell k) := by
    intro j _ j' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro r hr hr'
    simp only [shell, mem_filter] at hr hr'
    exact hne (hr.2.2.2.symm.trans hr'.2.2.2)
  have hdisj2 : Disjoint ((Icc 1 (k - 1)).biUnion (shell k)) (defectSet k) := by
    rw [Finset.disjoint_left]
    intro r hr hr'
    rw [mem_biUnion] at hr
    obtain ⟨j, hj, hmem⟩ := hr
    simp only [mem_Icc] at hj
    simp only [shell, mem_filter] at hmem
    simp only [defectSet, mem_filter] at hr'
    omega
  have hdefect : defectSet k = {rstar k} := by
    have hmem := rstar_mem_defectSet hk
    have hcard := defect_card hk
    exact (Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hmem, fun x hx => Finset.card_le_one.mp (le_of_eq hcard) x hx (rstar k) hmem⟩)
  have hshells : ∑ j ∈ Icc 1 (k - 1), ∑ r ∈ shell k j, Tcount k u r = 2 ^ k - 2 := by
    rw [← geom_row_const hk]
    exact Finset.sum_congr rfl fun j hj => by
      simp only [mem_Icc] at hj
      exact shell_row_contrib (by omega) (by omega) hu huodd
  rw [odds_partition hk, Finset.sum_union hdisj2, Finset.sum_biUnion hdisj, hdefect,
    Finset.sum_singleton, defect_col_eq_cf hk, hshells]

/-- **THE `T·1` IDENTITY.** `(T_k · 1)_u = (1 - 2^{1-k}) + c_u`, with `c` the defect column
`cf k (od u) / 2^k`. This is `THEOREM.md` Part I.1's boxed warning, as a theorem:
`T_k` is NOT doubly stochastic, and the deviation from `1` is exactly the defect fibre. -/
theorem Tk_row_sum {k : ℕ} (hk : 1 ≤ k) (u : Fin (2 ^ (k - 1))) :
    ∑ r : Fin (2 ^ (k - 1)), Tk k u r
      = (1 - 2 / (2 : ℝ) ^ k) + (cf k (od u) : ℝ) / 2 ^ k := by
  have huodd : od u % 2 = 1 := od_odd u
  have hulr : od u < 2 ^ k := od_lt hk u.isLt
  -- reindex `Fin (2^(k-1))` to the odd residues
  have hreindex : ∑ r : Fin (2 ^ (k - 1)), (Tcount k (od u) (od r) : ℝ)
      = ∑ r ∈ oddResidues k, (Tcount k (od u) r : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun r => (Tcount k (od u) (od r) : ℝ)) (2 ^ (k - 1))]
    rw [show oddResidues k = (range (2 ^ (k - 1))).image od from ?_]
    · rw [Finset.sum_image (by intro x _ y _ h; unfold od at h; omega)]
    · ext q
      simp only [oddResidues, mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hq, hodd⟩
        exact ⟨idx q, idx_lt hk hq, od_idx hodd⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨od_lt hk hs, od_odd s⟩
  have hcount := Tcount_row_sum hk hulr huodd
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hge : (2 : ℕ) ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hcast : ∑ r ∈ oddResidues k, (Tcount k (od u) r : ℝ)
      = ((2 : ℝ) ^ k - 2) + (cf k (od u) : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcount
    push_cast [Nat.cast_sub hge] at h
    exact h
  calc ∑ r : Fin (2 ^ (k - 1)), Tk k u r
      = (∑ r : Fin (2 ^ (k - 1)), (Tcount k (od u) (od r) : ℝ)) / 2 ^ k := by
        rw [Finset.sum_div]; rfl
    _ = (((2 : ℝ) ^ k - 2) + (cf k (od u) : ℝ)) / 2 ^ k := by rw [hreindex, hcast]
    _ = (1 - 2 / (2 : ℝ) ^ k) + (cf k (od u) : ℝ) / 2 ^ k := by
        field_simp

/-!
--------------------------------------------------------------------------------
## §7. Anti-vacuity and mutation resistance
--------------------------------------------------------------------------------

**The failure modes checked, and how.**

1. *A theorem `omega`/`decide` can close on its own.* `Tcount_col_sum`, `Tcount_row_sum` and
   `clean_col_count` are all statements about `Finset.card` of a filter over `range (2^k)` for
   SYMBOLIC `k` - no decision procedure touches them. `Tcount_row_sum` in particular routes
   through `odds_partition`, `sb_bijective` and `cu_syracuse_fibre_card`.
   Mutation-tested (five mutants, each built alone; **all five FAIL**, exit 1):
   | mutant | change | build |
   |---|---|---|
   | M1 | `Tcount_row_sum`'s `2^k - 2` → `2^k - 1` | FAILS |
   | M2 | `shell_row_contrib`'s `2^(k-j)` → `2^(k-j-1)` | FAILS |
   | M3 | `clean_col_count`'s fibre `2^(k-v)` → image `2^v` (the CU orientation trap) | FAILS |
   | M4 | §2's row-sum `#guard` forced to the uniform `[16,...]` a doubly-stochastic lookalike would give | FAILS |
   | M5 | `defect_col_eq_cf`'s `cf k u` → `cf k (u+2)` | FAILS |
2. *The right statement about the wrong object.* Guarded by §2's `#guard`s, which compare
   `TcountC` (proved equal to `Tcount`) against a direct enumeration of the corpus's own
   `build_T` at `k = 3, 4`, entry by entry - including the non-constant row sums, which is
   where a transposed definition would show up immediately.
3. *A vacuous hypothesis block.* `hyp_satisfiable` below instantiates every hypothesis of
   `clean_col_count` and `shell_row_contrib` at concrete values, and the `example` after it
   type-checks only if they are simultaneously satisfiable.
4. *A claim whose justification doesn't support it.* See the header: this file does NOT
   discharge `hQupper` or `hQlower`, and says so in those terms.
-/

/-- The hypotheses of §6 are satisfiable: `k = 4`, `j = 2`, source `r = 5` (`3·5+1 = 16`,
`v2 = 4 ≥ k`, so `5` is the DEFECT at `k = 4` - deliberately not this one), source `r = 1`
(`3·1+1 = 4`, `v2 = 2`, so `1 ∈ S_2`), target `u = 1`. -/
theorem hyp_satisfiable : (1 : ℕ) ∈ shell 4 2 ∧ (1 : ℕ) < 2 ^ 4 ∧ (1 : ℕ) % 2 = 1 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  simp only [shell, mem_filter, mem_range]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  show v2 4 = 2
  unfold v2
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]

/-- The witness is a genuine instance of `shell_col_count`: this only type-checks if every
hypothesis holds simultaneously at these values. -/
example : Tcount 4 1 1 = if sbMap 4 2 1 = 1 % 2 ^ (4 - 2) then 2 ^ (4 - 2) else 0 :=
  shell_col_count (k := 4) (j := 2) (u := 1) (by omega) (by omega) hyp_satisfiable.1 (by norm_num)

/-- And of `shell_row_contrib`. -/
example : ∑ r ∈ shell 4 2, Tcount 4 1 r = 2 ^ (4 - 2) :=
  shell_row_contrib (k := 4) (j := 2) (u := 1) (by omega) (by omega) (by norm_num) (by norm_num)

/-!
--------------------------------------------------------------------------------
## §8. Axiom audit
--------------------------------------------------------------------------------

Every exported declaration must depend on a SUBSET of `{propext, Classical.choice,
Quot.sound}`. Several depend on strictly fewer - the check is subset, not string equality.
-/

#print axioms od
#print axioms od_odd
#print axioms od_lt
#print axioms od_idx
#print axioms idx_lt
#print axioms Tcount
#print axioms Tk
#print axioms Tk_nonneg
#print axioms oddPartC
#print axioms oddPartC_eq
#print axioms syracuseC_eq
#print axioms TcountC_eq
#print axioms oddPart_odd
#print axioms syracuse_odd
#print axioms lift_odd
#print axioms tgt_lt
#print axioms Tcount_col_sum
#print axioms Tk_col_sum
#print axioms defect_col_eq_cf
#print axioms TkC
#print axioms Tend
#print axioms Tend_apply
#print axioms onesCov
#print axioms TkC_col_sum
#print axioms colStoch_concrete
#print axioms syracuse_lift_mod
#print axioms attained
#print axioms coset
#print axioms attained_eq_coset
#print axioms clean_col_count
#print axioms shell_col_count
#print axioms shell_row_contrib
#print axioms geom_row_const
#print axioms Tcount_row_sum
#print axioms Tk_row_sum
#print axioms hyp_satisfiable

end TransferOperator
