/-
# The character basis, the level projections, and R1

Task L8. `TransferOperator.lean` (task L7) defines `T_k` concretely and closes with a single
named blocker:

> This file does not build the character basis, does not define `Q`, and proves nothing about
> any operator norm.

and `Assembly.lean`'s manifest `LemmaAFacts` has exactly two residue fields, `hQupper` and
`hQlower`, both bounds on `Q[a,b] := ‖P_a U_k P_b‖₂`. Neither can even be *stated* until the
frequency variable `ξ` and the level decomposition `a = v₂(ξ)` exist as Lean objects.

## SCOPE DECISION (D1 plus the R1 arithmetic core) - read this before reading anything else

L8 offered three scopes: (D1) the character basis `F`, its orthonormality on odd residues, and
the level projections `P_a`; (D2) D1 plus `U_k` and the definition of `Q[a,b]`; (D3) D2 plus
discharging `hQlower`. **This file takes D1, and adds the arithmetic core of R1 - the fact
`hQlower` rests on - but does NOT reach D2 or D3.**

Concretely it proves, for all `k`:

* `gram_self`, `gram_eq_zero`, `chiVec_orthonormal` - the characters `χ_ξ(r) = w^{ξr}`,
  restricted to the `2^{k-1}` **odd** residues and indexed by `ξ ∈ [0, 2^{k-1})`, are an
  orthogonal family of constant norm `2^{(k-1)/2}`. Orthogonality is `LemmaA.Sodd_eq_zero_iff`
  (S4) at `m = k`: it is the *same* dead band that drives the cascade, used once at full width.
* `chiBasis` - hence an `OrthonormalBasis`. This is the Fourier matrix `F[r,ξ] = w^{ξr}/√N`.
* `levelSet`, `levelSet_partition`, `P`, `P_idem`, `P_orthogonal`, `P_selfadjoint`,
  `P_resolution` - the level projections `P_a` indexed by `a = v₂(ξ)`, `a ∈ [0, k-2]`, and the
  resolution `∑_{a<k-1} P_a + P_perron = 1`, with `P_perron` the `ξ = 0` (constant) direction.
* `valuation_lower`, `survivor_dead_band_lower`, `shell_sum_vanishes_lower`,
  `lower_block_entry_vanishes` - **R1's arithmetic core**: for `a ≥ b`, *every* shell
  `j ∈ [1,b]` lands in S4's dead band, so every shell contributes exactly `0` and any weighted
  shell sum vanishes. `LemmaA.survivor_dead_band` covers only `a < b` (its hypothesis is
  `hab : a < b`); the `a ≥ b` half is proved here for the first time, and it is the reason
  `P_a U_clean P_b = 0` on and below the diagonal.

## What is NOT discharged (do not soften this)

**`Assembly.LemmaAFacts.hQupper` and `hQlower` both remain OPEN. This file closes 0 of the 2
residue fields.** `Q` is still not defined anywhere in this development, and no operator norm
is bounded anywhere in this file. Three named gaps stand between `lower_block_entry_vanishes`
and `hQlower`:

1. **The S1 reduction is not formalised.** `HALFSHIFT_S4_LEMMA_A_PROOF.md` §4 turns the
   character-basis entry `hat(η,ξ) = Σ_{r odd, v(r) ≤ b} w^{ηq(r) − ξr}` into the shell sum
   `Σ_j w^{ξ·3⁻¹}·Sodd(alpha_j, k−j)`. The Shell-Bijection SB it rests on **is** already in
   Lean (`CountingLemmas.sb_bijective`, `odds_partition`); what is missing is the character
   step on top of it - re-indexing `r ↦ q = Syr(r)` inside the exponential and using
   `v₂(alpha_j) ≥ j` to see that `w^{q·alpha_j}` depends only on `q mod 2^{k-j}`, so that the
   `j`-shell sum lands in `Sodd`'s canonical range. `lower_block_entry_vanishes` therefore
   takes the shell decomposition as its *shape* (an arbitrary weighted sum over `j ∈ [1,b]` of
   `Sodd` values at residues of `alpha_j`) and proves that shape vanishes; it does not prove
   that `hat(η,ξ)` *has* that shape.
2. **The defect is not decomposed.** `hQlower`'s bound `Q[a,b] ≤ s^{a+1}·v_b` is the norm of
   the rank-one defect `D = e_{r*}c*`. `TransferOperator.defect_col_eq_cf` identifies the
   defect *column*; the rank-one factorisation, and `‖P_a e_{r*}‖ = 2^{-(a+1)/2}` (foundation
   R3), are not proved here.
3. **No operator norms.** `Q[a,b] = ‖P_a U P_b‖₂` needs the `ℓ²` operator norm of a block of
   `U = T_kᵀ`. Nothing in this file mentions `T_k`, `U`, or any norm of an operator.

So the honest summary is: L8 removes the *stated* blocker of L7 (the character basis and the
level projections now exist and are proved correct), and proves the arithmetic half of R1 for
all `k`. It does not close `hQlower`.

## Orientation (pinned by L7; an orientation drift nearly shipped in L2)

`T_k` is target-first, `U = T_kᵀ`, `Q[a,b] = ‖P_a U P_b‖₂` with `a` the **target** level and
`b` the **source** level. Column sums of `T_k` are the trivial ones, row sums the hard ones.
Nothing in this file uses either, because nothing in this file touches `T_k` - but the level
convention below (`a = v₂(ξ)`, `a` increasing = finer frequency, `u_a = 2^{-(a+1)/2}`
decreasing in `a`) is the one `Assembly.LemmaAFacts.hQupper`/`hQlower` are written in, and was
checked against the numerics rather than assumed. See the calibration note.

## Sign scope (STANDING GATE, inherited from `Assembly.lean` §GATE 1)

`3` does not appear in this file at all: `3⁻¹` is carried as an abstract **odd** `u : ℤ`,
exactly as in `LemmaA.lean`. Every statement below is therefore literally true of the `3x−1`
operator as well, and is not evidence about Collatz cycles of anything.

## Calibration (session-side, `l8_calib.py`; scripts not committed)

The character basis, `U = T_kᵀ`, the level projections and `Q` were built numerically first,
from `TransferOperator`'s own target-first `Tcount`, and reproduce the corpus's published
values exactly:

```
k     cert(k)     a*    e* = k − a*    ρ(Q_k)     |λ₂(T_k)|
6     0.633784     2         4        0.553529     0.2767
8     0.634659     4         4        0.566061     0.2549
12    0.634477     8         4        0.565553     (n/a)
13    0.634412     9         4        0.564415     (n/a)
```

matching `EXTREMAL_VALUES.md` row 5 to all six printed digits, including its statement that
"for every `k ≥ 4` the row attaining `cert(k)` is `a* = k−4`". Also confirmed directly, and
this is the fact R1 asserts: with `U_clean` built from the masked-phase formula, the
**diagonal-and-below block is exactly zero** - `max |P_a U_clean P_b|` over `a ≥ b` is
`0.000e+00` at `k = 6` and `k = 8`, not merely small. Two supporting numbers used below:
`‖F*F − I‖_max ≈ 1e-13` (orthonormality of the basis this file constructs), and
`‖P_a e_{r*}‖ = 2^{-(a+1)/2}` to machine precision for every `a` (foundation R3 - **measured,
not proved here**).

## Hypotheses that are declared and not used (recorded, not silenced)

Following `LemmaA.lean`'s convention. These make the theorems *weaker* than they could be,
never stronger:

* `level_lt`: `hk : 2 ≤ k` unused - `ξ < 2^{k-1}` already forces it when `ξ ≠ 0` exists.
* `P_selfadjoint`: `hk : 1 ≤ k` unused - self-adjointness of a coefficient-extraction sum
  does not need the characters to be orthonormal, only `inner_conj_symm`.

## Mutation tests (failure mode 1: a theorem a tactic closes on its own)

Six single-token mutations were applied to the load-bearing statements and the build was run
on each. **All six failed to compile**, i.e. none of these theorems is true for a trivial
reason:

| # | mutation | result |
|---|---|---|
| M1 | `gram_eq_zero_of_lt`: `ξ < 2^{k-1}` → `ξ < 2^k` (drop the half-modulus) | fails |
| M2 | `survivor_dead_band_lower`: `b+2 ≤ k` → `b+1 ≤ k` (dead-band upper edge) | fails |
| M3 | `valuation_lower`: `1 ≤ j` → `0 ≤ j` (shell range lower edge) | fails |
| M4 | `level_lt`: conclusion `< k-1` → `< k-2` | fails |
| M5 | `lower_block_entry_vanishes`: `b ≤ a` → `a ≤ b` (the orientation) | fails |
| M6 | `gram_self`: `2^{k-1}` → `2^k` (the normalisation) | fails |

Sorry-free. Axioms audited in §6.
-/

import LemmaA
import TransferOperator

namespace CharacterBasis

open Finset GapCertificate LemmaA TransferOperator

/-!
--------------------------------------------------------------------------------
## §1. The characters, and their Gram matrix
--------------------------------------------------------------------------------

`χ_ξ(s) := w^{ξ·od s}`, with `od s = 2s+1` the `s`-th odd residue (`TransferOperator` §1) and
`w = exp(2πi/2^k)` (`LemmaA` §1). Frequencies run over `ξ ∈ [0, 2^{k-1})`, which is exactly
`2^{k-1} = ` the number of odd residues.

The Gram entry is a full-width `Sodd`:
`⟨χ_{ξ'}, χ_ξ⟩ = Σ_{q odd < 2^k} w^{(ξ-ξ')q} = Sodd(ξ-ξ', k)`.
S4 at `m = k` reads `2^{k-k} = 1 ∣ α` (vacuous) and `2^{k-1} ∤ α`, so the sum vanishes for
every `α ≢ 0 (mod 2^{k-1})` - which is every nonzero difference of two frequencies in range.
-/

/-- `χ_ξ(s) = w^{ξ·(2s+1)}`. -/
noncomputable def chi (k ξ s : ℕ) : ℂ := w k ^ (ξ * od s)

/-- The odd residues below `2^k` are indexed by `s < 2^{k-1}` via `od`, so a sum over them is
a `Sodd` at full width `m = k`. -/
theorem sum_odd_pow (k α : ℕ) (hk : 1 ≤ k) :
    ∑ s ∈ range (2 ^ (k - 1)), w k ^ (α * od s) = Sodd k α k := by
  unfold Sodd
  rw [oddRange_eq_image hk, sum_image (by intro x _ y _ h; dsimp only at h; omega)]
  exact sum_congr rfl fun l _ => by unfold od; ring_nf

/-- `conj (χ_{ξ'}(s)) · χ_ξ(s) = w^{(ξ-ξ')·od s}` when `ξ' ≤ ξ`. Uses only `‖w‖ = 1`. -/
theorem conj_chi_mul (k ξ ξ' s : ℕ) (h : ξ' ≤ ξ) :
    (starRingEnd ℂ) (chi k ξ' s) * chi k ξ s = w k ^ ((ξ - ξ') * od s) := by
  have hn : ‖w k ^ (ξ' * od s)‖ = 1 := by rw [norm_pow, norm_w, one_pow]
  have key : w k ^ (ξ' * od s) * w k ^ ((ξ - ξ') * od s) = w k ^ (ξ * od s) := by
    rw [← pow_add]
    congr 1
    have hd : ξ' + (ξ - ξ') = ξ := by omega
    calc ξ' * od s + (ξ - ξ') * od s = (ξ' + (ξ - ξ')) * od s := by ring
      _ = ξ * od s := by rw [hd]
  have hne : w k ^ (ξ' * od s) ≠ 0 := pow_ne_zero _ (w_ne_zero k)
  unfold chi
  rw [← Complex.inv_eq_conj hn, ← key, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The Gram entry `⟨χ_{ξ'}, χ_ξ⟩` (unnormalised), in the `∑ conj · ·` convention Mathlib's
`inner` uses on `EuclideanSpace`. -/
noncomputable def gram (k ξ ξ' : ℕ) : ℂ :=
  ∑ s ∈ range (2 ^ (k - 1)), (starRingEnd ℂ) (chi k ξ' s) * chi k ξ s

theorem gram_eq_Sodd {k ξ ξ' : ℕ} (hk : 1 ≤ k) (h : ξ' ≤ ξ) :
    gram k ξ ξ' = Sodd k (ξ - ξ') k := by
  unfold gram
  rw [← sum_odd_pow k (ξ - ξ') hk]
  exact sum_congr rfl fun s _ => conj_chi_mul k ξ ξ' s h

/-- The Gram matrix is Hermitian. -/
theorem gram_conj (k ξ ξ' : ℕ) : gram k ξ ξ' = (starRingEnd ℂ) (gram k ξ' ξ) := by
  unfold gram
  rw [map_sum]
  exact sum_congr rfl fun s _ => by rw [map_mul, Complex.conj_conj, mul_comm]

/-- Every character has squared norm `2^{k-1}` - the FULL branch of S4 at `α = 0`. -/
theorem gram_self {k ξ : ℕ} (hk : 1 ≤ k) : gram k ξ ξ = ((2 ^ (k - 1) : ℕ) : ℂ) := by
  rw [gram_eq_Sodd hk le_rfl, Nat.sub_self, Sodd_full k 0 k hk (dvd_zero _), pow_zero, mul_one]

/-- **Orthogonality, the `ξ' < ξ` half.** The difference `ξ - ξ'` is nonzero and `< 2^{k-1}`,
so it sits strictly inside S4's dead band at `m = k`. -/
theorem gram_eq_zero_of_lt {k ξ ξ' : ℕ} (hk : 1 ≤ k) (hlt : ξ' < ξ) (hξ : ξ < 2 ^ (k - 1)) :
    gram k ξ ξ' = 0 := by
  rw [gram_eq_Sodd hk (le_of_lt hlt)]
  refine (Sodd_eq_zero_iff k (ξ - ξ') k hk).2 ⟨by simp, ?_⟩
  intro hd
  have hpos : 0 < ξ - ξ' := by omega
  have := Nat.le_of_dvd hpos hd
  omega

/-- **Orthogonality.** Distinct frequencies in `[0, 2^{k-1})` give a vanishing Gram entry. -/
theorem gram_eq_zero {k ξ ξ' : ℕ} (hk : 1 ≤ k) (hne : ξ ≠ ξ')
    (hξ : ξ < 2 ^ (k - 1)) (hξ' : ξ' < 2 ^ (k - 1)) : gram k ξ ξ' = 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [gram_conj, gram_eq_zero_of_lt hk h hξ', map_zero]
  · exact gram_eq_zero_of_lt hk h hξ

/-!
--------------------------------------------------------------------------------
## §2. `F`: the normalised character basis as an `OrthonormalBasis`
--------------------------------------------------------------------------------

`F[r,ξ] = w^{ξr}/√N`, `N = 2^{k-1}`. The columns of `F` are `chiVec`; §1 says they are
orthonormal, and there are `N = finrank` of them, so they are an orthonormal *basis*.
-/

/-- `√N`, `N = 2^{k-1}`. -/
noncomputable def rt (k : ℕ) : ℝ := Real.sqrt ((2 ^ (k - 1) : ℕ) : ℝ)

theorem rt_pos (k : ℕ) : 0 < rt k := Real.sqrt_pos.2 (by positivity)

theorem rt_ne_zero (k : ℕ) : (rt k : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (rt_pos k)

theorem rt_mul_rt (k : ℕ) : (rt k : ℂ) * (rt k : ℂ) = ((2 ^ (k - 1) : ℕ) : ℂ) := by
  have h : rt k * rt k = ((2 ^ (k - 1) : ℕ) : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h

/-- The `ξ`-th column of the Fourier matrix `F[r,ξ] = w^{ξr}/√N`, as a vector of `ℓ²`. -/
noncomputable def chiVec (k : ℕ) (ξ : Fin (2 ^ (k - 1))) :
    EuclideanSpace ℂ (Fin (2 ^ (k - 1))) :=
  WithLp.toLp 2 (fun s : Fin (2 ^ (k - 1)) => chi k (ξ : ℕ) (s : ℕ) / (rt k : ℂ))

@[simp] theorem chiVec_apply (k : ℕ) (ξ s : Fin (2 ^ (k - 1))) :
    chiVec k ξ s = chi k (ξ : ℕ) (s : ℕ) / (rt k : ℂ) := rfl

/-- The inner product of two basis columns is the Gram entry, normalised. -/
theorem inner_chiVec (k : ℕ) (ξ ξ' : Fin (2 ^ (k - 1))) :
    (@inner ℂ _ _ (chiVec k ξ) (chiVec k ξ') : ℂ)
      = gram k (ξ' : ℕ) (ξ : ℕ) / ((2 ^ (k - 1) : ℕ) : ℂ) := by
  rw [PiLp.inner_apply]
  have hpt : ∀ s : Fin (2 ^ (k - 1)),
      (inner ℂ ((chiVec k ξ).ofLp s) ((chiVec k ξ').ofLp s) : ℂ)
        = ((starRingEnd ℂ) (chi k (ξ : ℕ) (s : ℕ)) * chi k (ξ' : ℕ) (s : ℕ))
            / ((2 ^ (k - 1) : ℕ) : ℂ) := by
    intro s
    rw [RCLike.inner_apply]
    show (chi k (ξ' : ℕ) (s : ℕ) / (rt k : ℂ))
        * (starRingEnd ℂ) (chi k (ξ : ℕ) (s : ℕ) / (rt k : ℂ)) = _
    rw [map_div₀, Complex.conj_ofReal, div_mul_div_comm, rt_mul_rt]
    ring
  rw [Fintype.sum_congr _ _ hpt, ← sum_div]
  unfold gram
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun s => (starRingEnd ℂ) (chi k (ξ : ℕ) s) * chi k (ξ' : ℕ) s) (2 ^ (k - 1))

/-- **`F` is orthonormal on the odd residues.** -/
theorem chiVec_orthonormal {k : ℕ} (hk : 1 ≤ k) : Orthonormal ℂ (chiVec k) := by
  have hN : ((2 ^ (k - 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  refine orthonormal_iff_ite.2 fun ξ ξ' => ?_
  rw [inner_chiVec]
  by_cases h : ξ = ξ'
  · subst h; rw [if_pos rfl, gram_self hk, div_self hN]
  · rw [if_neg h, gram_eq_zero hk (fun hc => h (Fin.ext hc.symm)) ξ'.isLt ξ.isLt, zero_div]

/-- **`F` as an orthonormal basis.** -/
noncomputable def chiBasis {k : ℕ} (hk : 1 ≤ k) :
    OrthonormalBasis (Fin (2 ^ (k - 1))) ℂ (EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :=
  (basisOfLinearIndependentOfCardEqFinrank
      (chiVec_orthonormal hk).linearIndependent (by simp)).toOrthonormalBasis
    (by rw [coe_basisOfLinearIndependentOfCardEqFinrank]; exact chiVec_orthonormal hk)

@[simp] theorem chiBasis_apply {k : ℕ} (hk : 1 ≤ k) (ξ : Fin (2 ^ (k - 1))) :
    chiBasis hk ξ = chiVec k ξ := by
  rw [chiBasis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfLinearIndependentOfCardEqFinrank]

/-- Resolution of the identity in the character basis. -/
theorem chiBasis_sum_repr {k : ℕ} (hk : 1 ≤ k)
    (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    ∑ ξ : Fin (2 ^ (k - 1)), (@inner ℂ _ _ (chiVec k ξ) x : ℂ) • chiVec k ξ = x := by
  have h := (chiBasis hk).sum_repr' x
  simpa [chiBasis_apply] using h

/-!
--------------------------------------------------------------------------------
## §3. Levels and the projections `P_a`
--------------------------------------------------------------------------------

The level of a frequency is `a := v₂(ξ)`. For `ξ ∈ [0, 2^{k-1})` nonzero this forces
`a ≤ k-2` - the truncated level range of `THEOREM.md` Part III and of
`Assembly.LemmaAFacts.hKk` (`K ≤ k-1`, i.e. `a ∈ {0,...,k-2}`).

`ξ = 0` is excluded: `χ_0 ≡ 1` is the constant vector, i.e. the Perron direction, and
`ker(1ᵀ)` is its orthogonal complement. So the level sets partition `univ.erase 0`, and the
projections resolve `1 − P_perron`.
-/

/-- The frequencies of level `a`. -/
def levelSet (k a : ℕ) : Finset (Fin (2 ^ (k - 1))) :=
  univ.filter (fun ξ => (ξ : ℕ) ≠ 0 ∧ v2 (ξ : ℕ) = a)

theorem mem_levelSet {k a : ℕ} {ξ : Fin (2 ^ (k - 1))} :
    ξ ∈ levelSet k a ↔ (ξ : ℕ) ≠ 0 ∧ v2 (ξ : ℕ) = a := by
  simp [levelSet]

/-- **The truncated level range.** A nonzero frequency below `2^{k-1}` has level `≤ k-2`. -/
theorem level_lt {k : ℕ} {ξ : Fin (2 ^ (k - 1))} (hk : 2 ≤ k) (h0 : (ξ : ℕ) ≠ 0) :
    v2 (ξ : ℕ) < k - 1 := by
  have hdvd : 2 ^ v2 (ξ : ℕ) ∣ (ξ : ℕ) := pow_padicValNat_dvd
  have hle : 2 ^ v2 (ξ : ℕ) ≤ (ξ : ℕ) := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd
  have hlt : (2 : ℕ) ^ v2 (ξ : ℕ) < 2 ^ (k - 1) := lt_of_le_of_lt hle ξ.isLt
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt

/-- Distinct levels are disjoint. -/
theorem levelSet_disjoint {k a a' : ℕ} (h : a ≠ a') :
    Disjoint (levelSet k a) (levelSet k a') := by
  refine disjoint_left.2 fun ξ hξ hξ' => ?_
  rw [mem_levelSet] at hξ hξ'
  exact h (hξ.2 ▸ hξ'.2 ▸ rfl)

/-- **The levels partition the non-Perron frequencies.** -/
theorem levelSet_partition {k : ℕ} (hk : 2 ≤ k) :
    (range (k - 1)).biUnion (levelSet k) = univ.erase (0 : Fin (2 ^ (k - 1))) := by
  have hk1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  ext ξ
  simp only [mem_biUnion, mem_range, mem_erase, mem_univ, and_true, mem_levelSet]
  constructor
  · rintro ⟨a, _, h0, _⟩
    intro hc
    exact h0 (by rw [hc]; rfl)
  · intro h0
    have h0' : (ξ : ℕ) ≠ 0 := by
      intro hc
      exact h0 (Fin.ext (by simpa using hc))
    exact ⟨v2 (ξ : ℕ), level_lt hk h0', h0', rfl⟩

/-- `P_a`, the orthogonal projection onto the span of the level-`a` characters. -/
noncomputable def P (k a : ℕ) :
    EuclideanSpace ℂ (Fin (2 ^ (k - 1))) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 ^ (k - 1))) where
  toFun x := ∑ ξ ∈ levelSet k a, (@inner ℂ _ _ (chiVec k ξ) x : ℂ) • chiVec k ξ
  map_add' x y := by
    simp only [inner_add_right, add_smul]
    exact sum_add_distrib
  map_smul' c x := by
    simp only [inner_smul_right, RingHom.id_apply, smul_sum, smul_smul]

theorem P_apply (k a : ℕ) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    P k a x = ∑ ξ ∈ levelSet k a, (@inner ℂ _ _ (chiVec k ξ) x : ℂ) • chiVec k ξ := rfl

/-- The coefficient extraction that makes `P_a` idempotent: pairing a character against a
combination of characters picks out its own coefficient. -/
theorem inner_chiVec_sum {k : ℕ} (hk : 1 ≤ k) (S : Finset (Fin (2 ^ (k - 1))))
    (c : Fin (2 ^ (k - 1)) → ℂ) (η : Fin (2 ^ (k - 1))) :
    (@inner ℂ _ _ (chiVec k η) (∑ ξ ∈ S, c ξ • chiVec k ξ) : ℂ)
      = if η ∈ S then c η else 0 := by
  rw [inner_sum]
  have hon := chiVec_orthonormal hk
  have : ∀ ξ ∈ S, (@inner ℂ _ _ (chiVec k η) (c ξ • chiVec k ξ) : ℂ)
      = if η = ξ then c ξ else 0 := by
    intro ξ _
    rw [inner_smul_right, orthonormal_iff_ite.1 hon η ξ]
    by_cases h : η = ξ <;> simp [h]
  rw [sum_congr rfl this, sum_ite_eq S η c]

/-- `P_a` is idempotent. -/
theorem P_idem {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    P k a (P k a x) = P k a x := by
  simp only [P_apply]
  refine sum_congr rfl fun η hη => ?_
  rw [inner_chiVec_sum hk, if_pos hη]

/-- Distinct levels are orthogonal: `P_a P_{a'} = 0`. -/
theorem P_orthogonal {k : ℕ} (hk : 1 ≤ k) {a a' : ℕ} (h : a ≠ a')
    (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) : P k a (P k a' x) = 0 := by
  simp only [P_apply]
  refine sum_eq_zero fun η hη => ?_
  rw [inner_chiVec_sum hk, if_neg, zero_smul]
  exact fun hc => (disjoint_left.1 (levelSet_disjoint h)) hη hc

/-- `P_a` is self-adjoint. -/
theorem P_selfadjoint {k : ℕ} (hk : 1 ≤ k) (a : ℕ)
    (x y : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    (@inner ℂ _ _ (P k a x) y : ℂ) = @inner ℂ _ _ x (P k a y) := by
  rw [P_apply, P_apply, sum_inner, inner_sum]
  refine sum_congr rfl fun ξ _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

/-- **Resolution of the identity.** `∑_{a < k-1} P_a + P_perron = 1`, with `P_perron` the
rank-one projection onto the constant vector `χ_0`. -/
theorem P_resolution {k : ℕ} (hk : 2 ≤ k) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    (∑ a ∈ range (k - 1), P k a x)
      + (@inner ℂ _ _ (chiVec k 0) x : ℂ) • chiVec k 0 = x := by
  have hk1 : 1 ≤ k := by omega
  have hsum : ∑ a ∈ range (k - 1), P k a x
      = ∑ ξ ∈ univ.erase (0 : Fin (2 ^ (k - 1))),
          (@inner ℂ _ _ (chiVec k ξ) x : ℂ) • chiVec k ξ := by
    rw [← levelSet_partition hk,
        sum_biUnion (fun a _ a' _ h => levelSet_disjoint h)]
    rfl
  rw [hsum, Finset.sum_erase_add univ _ (mem_univ (0 : Fin (2 ^ (k - 1))))]
  exact chiBasis_sum_repr hk1 x

/-!
--------------------------------------------------------------------------------
## §4. R1: the diagonal-and-below block, arithmetically
--------------------------------------------------------------------------------

### STATEMENT FIDELITY (`STEP4_BLOCK_FORMULA_FOUNDATION.md` §1, quoted verbatim)

> **Diagonal/lower (a >= b):  P_a U_clean P_b = 0  EXACTLY** (verified to 5e-11).
> U_clean is strictly upper-triangular in level.

The mechanism, in HALFSHIFT §4's variables: the shell-`j` contribution to the block entry is
`w^{ξ·3⁻¹}·Sodd(alpha_j, k−j)` with `alpha_j = η − ξ·2^j·3⁻¹`, `v₂(η) = b`, `v₂(ξ) = a`, and
`j` running over `[1,b]`. When `a ≥ b`, `v₂(ξ·2^j·3⁻¹) = a + j ≥ b + 1 > b` for **every**
`j ≥ 1`, so `v₂(alpha_j) = b` exactly, on the nose, in every shell. And `j ≤ b ≤ k−2` puts `b`
inside S4's dead band `[j, k−2]`. So every shell dies - there is no surviving `j = d` shell
because `d = b − a ≤ 0` is not in the shell range `[1,b]` at all.

`LemmaA.survivor_dead_band` cannot be reused: its hypothesis is `hab : a < b`, and its `j > d`
branch routes through `LemmaA.valuation_above`, whose factorisation
`2^b·(η' − 2^{j−(b−a)}·ξ'u)` needs `a ≤ b`. The `a ≥ b` factorisation below is
`2^b·(η' − 2^{a−b+j}·ξ'u)` - a different exponent, and simpler, since `a − b + j ≥ 1` needs
only `j ≥ 1` rather than a case split on `d`.
-/

/-- **Valuation table, the lower/diagonal rows (`b ≤ a`).** For every shell `j ≥ 1`,
`v₂(alpha_j) = b` exactly. Only `η'` odd is used - as in `LemmaA.valuation_above`, the other
oddness hypotheses are not needed. -/
theorem valuation_lower {a b j : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ')
    (hj : 1 ≤ j) (hab : b ≤ a) :
    (2 : ℤ) ^ b ∣ alphaJ η ξ u j ∧ ¬ (2 : ℤ) ^ (b + 1) ∣ alphaJ η ξ u j := by
  have hkey : alphaJ η ξ u j = 2 ^ b * (η' - 2 ^ (a - b + j) * (ξ' * u)) := by
    unfold alphaJ
    subst hη; subst hξ
    have e2 : (2 : ℤ) ^ b * 2 ^ (a - b + j) = 2 ^ a * 2 ^ j := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    calc 2 ^ b * η' - 2 ^ a * ξ' * 2 ^ j * u
        = 2 ^ b * η' - (2 ^ a * 2 ^ j) * (ξ' * u) := by ring
      _ = 2 ^ b * η' - (2 ^ b * 2 ^ (a - b + j)) * (ξ' * u) := by rw [e2]
      _ = 2 ^ b * (η' - 2 ^ (a - b + j) * (ξ' * u)) := by ring
  rw [hkey]
  exact v2_of_odd_mul (hη'.sub_even (even_two_pow_mul (by omega) (ξ' * u)))

/-- **(S5) for `a ≥ b`: every shell is dead.** `2^j ∣ alpha_j` (from `j ≤ b`) and
`2^{k-1} ∤ alpha_j` (from `b + 1 ≤ k - 1`, i.e. `b ≤ k-2`). -/
theorem survivor_dead_band_lower {k a b j : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ')
    (hab : b ≤ a) (hbk : b + 2 ≤ k) (hj1 : 1 ≤ j) (hjb : j ≤ b) :
    (2 : ℤ) ^ j ∣ alphaJ η ξ u j ∧ ¬ (2 : ℤ) ^ (k - 1) ∣ alphaJ η ξ u j := by
  obtain ⟨hd, hnd⟩ := valuation_lower (ξ' := ξ') hη hη' hξ hj1 hab
  refine ⟨dvd_trans (pow_dvd_pow 2 hjb) hd, fun hc => hnd ?_⟩
  exact dvd_trans (pow_dvd_pow 2 (by omega)) hc

/-- **R1, one shell.** For `a ≥ b` and every shell `j ∈ [1,b]`, the shell's character sum
`Sodd(alpha_j, k−j)` is exactly zero. `α : ℕ` is any residue representative of `alpha_j`
mod `2^k`. -/
theorem shell_sum_vanishes_lower {k a b j α : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ')
    (hab : b ≤ a) (hbk : b + 2 ≤ k) (hj1 : 1 ≤ j) (hjb : j ≤ b)
    (hres : (2 : ℤ) ^ k ∣ (α : ℤ) - alphaJ η ξ u j) :
    Sodd k α (k - j) = 0 := by
  obtain ⟨hlow, hhigh⟩ :=
    survivor_dead_band_lower (ξ' := ξ') hη hη' hξ hab hbk hj1 hjb
  have hjk : j ≤ k := by omega
  refine (Sodd_eq_zero_iff k α (k - j) (by omega)).2 ⟨?_, ?_⟩
  · have hkj : k - (k - j) = j := by omega
    rw [hkj, ← Int.natCast_dvd_natCast]
    push_cast
    exact (dvd_congr_mod hjk hres).2 hlow
  · intro hc
    refine hhigh ?_
    have hint : ((2 : ℤ) ^ (k - 1) ∣ (α : ℤ)) := by
      rw [← Int.natCast_dvd_natCast] at hc; push_cast at hc; exact hc
    exact (dvd_congr_mod (by omega) hres).1 hint

/-- **R1, the block entry.** For `a ≥ b`, *any* weighted sum over the shell range `[1,b]` of
the shell character sums vanishes. The coefficients `c` are arbitrary, so this is not a
statement about one particular normalisation: `HALFSHIFT` §4's entry
`hat(η,ξ) = Σ_j w^{ξ·3⁻¹}·Sodd(alpha_j, k−j)` is the instance `c j = w^{ξ·3⁻¹}`.

**This is not `hQlower`.** It is the arithmetic half of R1. Turning it into
`P_a U_clean P_b = 0` needs the SB shell decomposition (`HALFSHIFT` §1), which is not
formalised; see the header. -/
theorem lower_block_entry_vanishes {k a b : ℕ} {η ξ u η' ξ' : ℤ}
    (hη : η = 2 ^ b * η') (hη' : Odd η') (hξ : ξ = 2 ^ a * ξ')
    (hab : b ≤ a) (hbk : b + 2 ≤ k)
    (c : ℕ → ℂ) (res : ℕ → ℕ)
    (hres : ∀ j ∈ Icc 1 b, (2 : ℤ) ^ k ∣ ((res j : ℤ) - alphaJ η ξ u j)) :
    ∑ j ∈ Icc 1 b, c j * Sodd k (res j) (k - j) = 0 := by
  refine sum_eq_zero fun j hj => ?_
  rw [mem_Icc] at hj
  rw [shell_sum_vanishes_lower (a := a) (η' := η') (ξ' := ξ')
        hη hη' hξ hab hbk hj.1 hj.2 (hres j (mem_Icc.2 hj)), mul_zero]

/-!
--------------------------------------------------------------------------------
## §5. Satisfiability and calibration (failure mode 3: vacuity)
--------------------------------------------------------------------------------

Every hypothesis block above is exhibited at a concrete point, and the `example`s below
type-check only if the whole block is simultaneously satisfiable. The `#guard`s pin the level
partition against a decidable recomputation of `v₂`.
-/

/-- A concrete lower-triangular point: `k = 6`, `a = 3`, `b = 2` (so `a > b`),
`η = 2²·1 = 4`, `ξ = 2³·1 = 8`, `u = 1`. Then `alpha_1 = 4 - 16 = -12` (`v₂ = 2 = b`) and
`alpha_2 = 4 - 32 = -28` (`v₂ = 2 = b`). Both sit in the dead band. -/
theorem hyp_satisfiable_lower :
    alphaJ (2 ^ 2 * 1) (2 ^ 3 * 1) 1 1 = -12 ∧ alphaJ (2 ^ 2 * 1) (2 ^ 3 * 1) 1 2 = -28 ∧
      (2 : ℤ) ^ 1 ∣ (-12 : ℤ) ∧ ¬ (2 : ℤ) ^ (6 - 1) ∣ (-12 : ℤ) ∧
      (2 : ℤ) ^ 2 ∣ (-28 : ℤ) ∧ ¬ (2 : ℤ) ^ (6 - 1) ∣ (-28 : ℤ) := by
  refine ⟨by unfold alphaJ; norm_num, by unfold alphaJ; norm_num,
    ⟨-6, by norm_num⟩, by decide, ⟨-7, by norm_num⟩, by decide⟩

/-- The witness is literally an instance of `survivor_dead_band_lower`: this `example`
type-checks only if every hypothesis is satisfiable simultaneously. -/
example : (2 : ℤ) ^ 1 ∣ alphaJ (2 ^ 2 * 1) (2 ^ 3 * 1) 1 1 ∧
    ¬ (2 : ℤ) ^ (6 - 1) ∣ alphaJ (2 ^ 2 * 1) (2 ^ 3 * 1) 1 1 :=
  survivor_dead_band_lower (k := 6) (a := 3) (b := 2) (j := 1) (ξ' := 1)
    rfl ⟨0, by ring⟩ rfl (by omega) (by omega) (by omega) (by omega)

/-- And an instance of `lower_block_entry_vanishes` at the same point, with both shells
present (`Icc 1 2`) and arbitrary coefficients. Residue representatives:
`52 ≡ -12` and `36 ≡ -28` mod `2^6 = 64`. -/
example (c : ℕ → ℂ) :
    ∑ j ∈ Icc 1 2, c j * Sodd 6 (if j = 1 then 52 else 36) (6 - j) = 0 :=
  lower_block_entry_vanishes (k := 6) (a := 3) (b := 2)
    (η := 4) (ξ := 8) (u := 1) (η' := 1) (ξ' := 1)
    (res := fun j => if j = 1 then 52 else 36)
    (by norm_num) ⟨0, by ring⟩ (by norm_num) (by omega) (by omega) c
    (by
      intro j hj
      obtain ⟨h1, h2⟩ := mem_Icc.1 hj
      interval_cases j
      · unfold alphaJ; norm_num
      · unfold alphaJ; norm_num)

/-- Decidable recomputation of the level of a frequency, via `CountingLemmas.v2EqDec`
(justified there by `v2_eq_iff_mod`, proved, not asserted). -/
def levelCountEval (k a : ℕ) : ℕ :=
  ((List.range (2 ^ (k - 1))).filter (fun x => x != 0 && CountingLemmas.v2EqDec x a)).length

-- `|levelSet k a| = 2^{k-2-a}`, and the levels `a = 0 .. k-2` exhaust `2^{k-1} - 1`
-- frequencies (all but `ξ = 0`). Measured by the same enumeration `l8_calib.py` uses to
-- index the level blocks.
#guard (List.range 5).map (levelCountEval 6) = [16, 8, 4, 2, 1]
#guard (List.range 7).map (levelCountEval 8) = [64, 32, 16, 8, 4, 2, 1]
#guard ((List.range 5).map (levelCountEval 6)).sum = 2 ^ 5 - 1
#guard ((List.range 7).map (levelCountEval 8)).sum = 2 ^ 7 - 1
-- The top occupied level is `k-2`, i.e. `levelCountEval k (k-1) = 0` - this is `level_lt`.
#guard levelCountEval 6 5 = 0
#guard levelCountEval 8 7 = 0

/-!
--------------------------------------------------------------------------------
## §6. Axiom audit
--------------------------------------------------------------------------------

Every exported declaration must use a SUBSET of `{propext, Classical.choice, Quot.sound}`.
Several use strictly fewer; that is expected and is not a violation.
-/

#print axioms sum_odd_pow
#print axioms conj_chi_mul
#print axioms gram_eq_Sodd
#print axioms gram_conj
#print axioms gram_self
#print axioms gram_eq_zero_of_lt
#print axioms gram_eq_zero
#print axioms rt_mul_rt
#print axioms inner_chiVec
#print axioms chiVec_orthonormal
#print axioms chiBasis_apply
#print axioms chiBasis_sum_repr
#print axioms mem_levelSet
#print axioms level_lt
#print axioms levelSet_disjoint
#print axioms levelSet_partition
#print axioms inner_chiVec_sum
#print axioms P_idem
#print axioms P_orthogonal
#print axioms P_selfadjoint
#print axioms P_resolution
#print axioms valuation_lower
#print axioms survivor_dead_band_lower
#print axioms shell_sum_vanishes_lower
#print axioms lower_block_entry_vanishes
#print axioms hyp_satisfiable_lower

end CharacterBasis
