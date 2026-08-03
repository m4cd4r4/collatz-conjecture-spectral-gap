/-
# Assembly: the top-level uniform spectral gap, with an explicit hypothesis manifest

Lean 4 glue file for the `collatz-cycle-certificate` development (task L5). It does three
things and nothing else:

1. **Discharges `hParseval`** - the single named gap left by `CollisionBound.lean` (L4) in the
   counting half of the certificate. Both halves of it are proved here, unconditionally:
   `∑_b ‖P_b c‖² ≤ ‖c‖²` (Parseval in the level-decomposed picture) and
   `‖c‖² = coll(k)/4^k` (the identification of the defect fibre's `ℓ²` norm with the collision
   count, for a *concretely defined* `c`). See §3.
2. **Glues** `OperatorChain.lean` (I.1-I.2), `LevelMajorisation.lean` (I.3-I.4),
   `CountingLemmas.lean`/`CollisionBound.lean` (Lemma B) and `GapCertificate.lean` (Part III)
   into ONE theorem, `gap_certificate`, whose every remaining assumption sits in ONE named
   structure `LemmaAFacts`. See §4-§5.
3. **Audits** that theorem against `THEOREM.md`'s boxed statement, delta by delta. See §7.

## STANDING GATE 1 - sign scope (read this before reading anything else)

**Nothing in this file, or in the four files it imports, says anything about Collatz cycles,
and nothing it proves about `3x+1` is not equally true of `3x-1`.**

Every hypothesis of `LemmaAFacts` is satisfied verbatim by the `3x-1` transfer operator, which
passes the identical certificate (`cert ~ 0.6061` against `0.6347`, both `< 0.8536`) and *has
real cycles*. See `CYCLE_CLAIM_REFUTED.md`. A spectral gap for a Markov model of the map is not
an obstruction to cycles of the map.

Sharper, from task T3.2 / **Theorem T** (truncation localisation, private phase file, 2026-08-03):
define the honest 2-adic kernel `K` (clean rows as in `T_k`, defect row uniform). Then
`K_- = Π K_+ Π` **bit-exactly** and `(K - rank1)^(k+2) = 0` exactly, so `K`'s non-Perron part is
nilpotent and `|λ₂(K)| = 0`. Consequently the entire sign-sensitivity of `T_k` - the cert gap,
and the whole measured `|λ₂(T_k)| ~ 0.27` - is an artefact of the finite lift window `[0, 2^k)`,
not of mod-`2^k` averaging. What `T_k`'s spectral gap measures is largely that truncation.

## STANDING GATE 2 - known-quantity anchor

`EXTREMAL_VALUES.md` line 170 (independently rebuilt at line 278): the measured certificate at
`k = 8` is `cert(8) = 0.634659`, with `ρ(Q_8) = 0.566061` and `|λ₂(T_8)| = 0.2549`, the binding
row being `e = 4`. The bound proved here is `0.8535534`. So

```
    |λ₂(T_8)| = 0.2549   ≤   cert(8) = 0.634659   ≤   proven bound 0.8535534
```

i.e. **bound > measurement**, in the right direction, with slack - consistent, and *not* tight.
The bound is deliberately not the sharpest available (see §2, the Lemma C note); its value is
that it is uniform in `k`.

## STANDING GATE 4 - absurd height

At `k = 10^9` the statement of `gap_certificate` is *character-for-character the same*: the
bound is still `envelope s 3 < 0.853554`, with no `k`-dependent term anywhere in it. The
uniformity IS the content; there is no height at which the constant degrades. (Equally, there
is no height at which it says anything about a cycle - see gate 1.)

## What is NOT here

No `0.656`, no `0.6553`, no `0.683` refinement is stated anywhere in this file, deliberately.
`THEOREM.md` prints "with Lemma C the constant improves to `0.656`"; `EXTREMAL_VALUES.md`
(rows 2 and 3 of its table, and the 2026-08-03 correction block) records that

* the **proven** Lemma C sharpening is `(3 + 6√2 + 2√6)/24 = 0.6826775358`, resting on
  `g_b < √(3/4)` (`LEMMA_C_PROOF.md` line 25); and
* the sharp constant `g_b ≤ 3/4`, which would give `(1 + 3√2)/8 = 0.6553300859`, is **DATA** -
  machine-verified for `k ≤ 26` only, and `LEMMA_C_PROOF.md` line 28 says so in as many words.

Labels never round up: a bound consuming a `DATA` input is `DATA`. This file states only the
`PROVEN` Lemma A + Lemma B constant `2^{-3/2} + 2^{-1}`.
-/

import CollisionBound
import LevelMajorisation

namespace Assembly

open Finset
open GapCertificate CountingLemmas CollisionBound LevelMajorisation

/-!
--------------------------------------------------------------------------------
## §1. The constant `s = 2^{-1/2}` and the numeral `2^{-3/2} + 2^{-1}`
--------------------------------------------------------------------------------

`GapCertificate.lean` carries `s` abstractly, as any positive real with `s² = 1/2`. The boxed
theorem prints a *numeral*, so the glue must pin `s` down and prove the numeral from the same
proof term the bound is built out of - otherwise the printed constant and the proved constant
are two different objects that happen to agree in a comment.

`envelope s 3 = s³ + s² = 2^{-3/2} + 2^{-1} = 0.85355339...`, bracketed below on both sides.
-/

/-- `s := 2^{-1/2}`, the single constant the whole certificate is built from. -/
noncomputable def s : ℝ := Real.sqrt (1 / 2)

theorem s_pos : 0 < s := Real.sqrt_pos.mpr (by norm_num)

theorem s_sq : s ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)

/-- `s < 0.70710679` (since `0.70710679² > 1/2`). -/
theorem s_lt : s < 0.70710679 := by nlinarith [s_sq, s_pos]

/-- `0.70710678 < s` (since `0.70710678² < 1/2`). Kept so the numeral is bracketed on BOTH
sides: a one-sided bound would also be satisfied by a much smaller `s`, and then
`envelope s 3 < 0.853554` would be true for the wrong reason. -/
theorem s_gt : 0.70710678 < s := by nlinarith [s_sq, s_pos]

/-- `envelope s 3 = s³ + s² = 2^{-3/2} + 2^{-1}`. -/
theorem envelope_three_eq : envelope s 3 = s ^ 3 + s ^ 2 := envelope_three s

/-- **The numeral, upper.** `2^{-3/2} + 2^{-1} < 0.853554`. -/
theorem envelope_three_lt : envelope s 3 < 0.853554 := by
  rw [envelope_three_eq]
  have h3 : s ^ 3 = s * (1 / 2) := by
    have h : s ^ 3 = s * s ^ 2 := by ring
    rw [h, s_sq]
  rw [h3, s_sq]
  nlinarith [s_lt]

/-- **The numeral, lower.** `0.853553 < 2^{-3/2} + 2^{-1}`. Together with
`envelope_three_lt` this pins the printed constant `0.853553...` to five decimal places from
the proof term itself. -/
theorem envelope_three_gt : 0.853553 < envelope s 3 := by
  rw [envelope_three_eq]
  have h3 : s ^ 3 = s * (1 / 2) := by
    have h : s ^ 3 = s * s ^ 2 := by ring
    rw [h, s_sq]
  rw [h3, s_sq]
  nlinarith [s_gt]

/-- `2^{-3/2} + 2^{-1} < 1`. This is `GapCertificate.envelope_lt_one` at the pinned `s`. -/
theorem envelope_three_lt_one : envelope s 3 < 1 := envelope_lt_one s_pos s_sq

/-!
--------------------------------------------------------------------------------
## §2. Parseval in the level-decomposed picture
--------------------------------------------------------------------------------

`THEOREM.md` I.3: *"The levels are orthogonal and exhaust `V`"*. In the decomposed
representation `LevelMajorisation.lean` works in, `P_b g` is the coordinate `g b`, so this is
`PiLp.norm_eq_of_L2` and L2 already carries it as `norm_eq_l2norm_levelEnergy`. What is added
here is the *squared, un-square-rooted* form, and its truncation to an arbitrary initial
segment `range J` - which is the shape `GapCertificate.assembly_row_bound` wants for `hL2`.

`levelVec g` is `THEOREM.md`'s `v_b = ‖P_b c‖` read as a function on `ℕ` (zero off the level
range), so that it can be fed to the `ℕ`-indexed abstract assembly.
-/

section Parseval

variable {K : ℕ} {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)]

/-- **Parseval, squared form.** `∑_m ‖P_m g‖² = ‖g‖²`. -/
theorem sum_levelEnergy_sq (g : PiLp 2 G) : ∑ m, ‖g m‖ ^ 2 = ‖g‖ ^ 2 := by
  rw [norm_eq_l2norm_levelEnergy, l2norm,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  rfl

/-- The level-energy vector `a(g)_b = ‖P_b g‖` as a function on `ℕ`, zero off the level range.
This is `THEOREM.md`'s `v_b` when `g` is the (mean-zero part of the) defect fibre `c`. -/
noncomputable def levelVec (g : PiLp 2 G) : ℕ → ℝ :=
  fun b => if h : b < K then ‖g ⟨b, h⟩‖ else 0

theorem levelVec_nonneg (g : PiLp 2 G) (b : ℕ) : 0 ≤ levelVec g b := by
  unfold levelVec; split <;> positivity

@[simp] theorem levelVec_of_lt (g : PiLp 2 G) {b : ℕ} (h : b < K) :
    levelVec g b = ‖g ⟨b, h⟩‖ := by simp [levelVec, h]

theorem levelVec_of_ge (g : PiLp 2 G) {b : ℕ} (h : K ≤ b) : levelVec g b = 0 := by
  simp [levelVec, Nat.not_lt.mpr h]

/-- **Parseval on the full level range.** -/
theorem sum_levelVec_sq (g : PiLp 2 G) :
    ∑ b ∈ range K, (levelVec g b) ^ 2 = ‖g‖ ^ 2 := by
  rw [← sum_levelEnergy_sq g,
    ← Fin.sum_univ_eq_sum_range (fun b => (levelVec (G := G) g b) ^ 2) K]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [levelVec, m.isLt]

/-- **Bessel on an arbitrary initial segment.** `∑_{b < J} ‖P_b g‖² ≤ ‖g‖²` for every `J`.

This is the *left half* of L4's `hParseval`. It is an equality when `J = K` and a genuine
inequality only through truncation - matching `LEMMA_B_PROOF.md`'s remark that the level sum
"omits the Perron direction `ξ = 0` [...] the omitted term only strengthens the bound". -/
theorem sum_levelVec_sq_le (g : PiLp 2 G) (J : ℕ) :
    ∑ b ∈ range J, (levelVec g b) ^ 2 ≤ ‖g‖ ^ 2 := by
  rw [← sum_levelVec_sq g]
  rcases le_total J K with h | h
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
      (fun i _ _ => by positivity)
  · refine le_of_eq (Finset.sum_subset (Finset.range_subset_range.mpr h) ?_).symm
    intro x _ hx
    have hxK : K ≤ x := Nat.not_lt.mp (by simpa using hx)
    simp [levelVec_of_ge g hxK]

end Parseval

/-!
--------------------------------------------------------------------------------
## §3. `hParseval`, DISCHARGED
--------------------------------------------------------------------------------

`CollisionBound.lean` §8 left exactly one named hypothesis in the counting chain:

> `hParseval` is `∑_b ‖P_b c‖² ≤ ‖c‖² = coll(k)/4^k` -- Bessel for the level decomposition
> (L2's territory, see §8). [...] Discharging `hParseval` requires the concrete level-projection
> `P_b` on `ℓ²(Z/2^k)` and `c` as an actual vector -- objects that do not yet exist in this Lean
> development.

Both objects now exist. `hParseval` splits into two halves and **both are proved here**:

| half | statement | status |
|---|---|---|
| (P1) Bessel/Parseval | `∑_{b<J} ‖P_b g‖² ≤ ‖g‖²` | **PROVEN**, `sum_levelVec_sq_le` (§2) |
| (P2) the norm identity | `‖c‖² = coll(k)/4^k` | **PROVEN**, `cvec_norm_sq` (below) |

`c` is defined concretely as `cvec k : EuclideanSpace ℝ (Fin (2^k))`, `c t = cf(k,t)/2^k`, from
L4's already-formalised fibre counts `cf` - i.e. it *is* `THEOREM.md` Part II's "`c` its fiber
distribution", built from the same `cf` whose square-sum is `coll(k)`. `cvec_norm_sq` is the
line `THEOREM.md` Lemma B prints as `‖c‖² = coll(k)/4^k`, and it is now a theorem.

**What remains, stated plainly.** `hParseval` is discharged *as a mathematical statement*. It is
replaced in the manifest by `hDefectVec : ‖gc‖ ≤ ‖cvec k‖` - the *definitional identification*
that the vector whose level energies are `THEOREM.md`'s `v_b` is (the mean-zero part of) this
`c`. That is not an inequality anyone needs to prove; it is a statement about the concrete
`T_k`, which this development does not define (see §6, KILL CRITERION). The trade is real: a
Bessel inequality plus a norm computation have become theorems, and what is left is a naming.
-/

/-- **`c`, the defect fibre distribution, concretely.** `c t = cf(k,t)/2^k`: the probability that
a uniform lift over the defect residue `r*` lands on odd residue `t`, with `cf` the fibre count
formalised in `CollisionBound.lean`. This is `THEOREM.md` Part II's "`c` its fiber
distribution". -/
noncomputable def cvec (k : ℕ) : EuclideanSpace ℝ (Fin (2 ^ k)) :=
  WithLp.toLp 2 (fun t => (cf k t : ℝ) / 2 ^ k)

@[simp] theorem cvec_apply (k : ℕ) (t : Fin (2 ^ k)) :
    cvec k t = (cf k t : ℝ) / 2 ^ k := rfl

/-- **Anti-"wrong object" check.** The fibre counts sum to the number of lifts: `∑_t cf(k,t) = 2^k`.
Not decidable for symbolic `k` (it is `Finset.card_eq_sum_card_fiberwise` against `fibVal_lt`), and
it is the statement that would FAIL if `cf` counted something other than the fibres of the defect
row - e.g. if the fibre/image orientation had been inverted, the failure mode L3's referee
finding names. -/
theorem cf_sum (k : ℕ) : ∑ t ∈ range (2 ^ k), cf k t = 2 ^ k := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fibVal k) (s := range (2 ^ k)) (t := range (2 ^ k))
    (fun m _ => Finset.mem_range.mpr (fibVal_lt k m))
  simpa [cf, Finset.card_range] using h.symm

/-- **`c` is a probability vector**: `∑_t c t = 1`. So `cvec` is the *distribution* THEOREM.md
Part II calls "`c` its fiber distribution", not merely a vector built from the right integers. -/
theorem cvec_sum (k : ℕ) : ∑ t : Fin (2 ^ k), cvec k t = 1 := by
  have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hsum : ∑ t : Fin (2 ^ k), (cf k (t : ℕ) : ℝ) = (2 : ℝ) ^ k := by
    rw [Fin.sum_univ_eq_sum_range (fun t => (cf k t : ℝ)) (2 ^ k)]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (cf_sum k)
  calc ∑ t : Fin (2 ^ k), cvec k t
      = (∑ t : Fin (2 ^ k), (cf k (t : ℕ) : ℝ)) / 2 ^ k := by
        rw [Finset.sum_div]; rfl
    _ = 1 := by rw [hsum]; field_simp

/-- **(P2), `THEOREM.md` Lemma B's `‖c‖² = coll(k)/4^k`.** Proved, not assumed. -/
theorem cvec_norm_sq (k : ℕ) : ‖cvec k‖ ^ 2 = (coll k : ℝ) / 4 ^ k := by
  have hpow : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  have hterm : ∀ t : Fin (2 ^ k), ‖cvec k t‖ ^ 2 = ((cf k t : ℝ)) ^ 2 / 4 ^ k := by
    intro t
    rw [cvec_apply, Real.norm_eq_abs, sq_abs, div_pow, hpow]
  rw [Finset.sum_congr rfl (fun t _ => hterm t), ← Finset.sum_div]
  congr 1
  rw [coll]
  push_cast
  exact Fin.sum_univ_eq_sum_range (fun t => ((cf k t : ℝ)) ^ 2) (2 ^ k)

section ParsevalDischarge

variable {K : ℕ} {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)]

/-- **`hParseval`, discharged.** For any level vector `g` no longer than the defect fibre `c`,
the level energies satisfy L4's `hParseval` hypothesis. (P1) + (P2). -/
theorem hParseval_of_norm_le {k : ℕ} (J : ℕ) (g : PiLp 2 G) (hg : ‖g‖ ≤ ‖cvec k‖) :
    ∑ b ∈ range J, (levelVec g b) ^ 2 ≤ (coll k : ℝ) / 4 ^ k := by
  calc ∑ b ∈ range J, (levelVec g b) ^ 2 ≤ ‖g‖ ^ 2 := sum_levelVec_sq_le g J
    _ ≤ ‖cvec k‖ ^ 2 := by nlinarith [norm_nonneg g, norm_nonneg (cvec k)]
    _ = (coll k : ℝ) / 4 ^ k := cvec_norm_sq k

/-- **Lemma B, end to end, with no named hypothesis left.** `∑_b v_b² ≤ 3·2^{-k}`, tracing
back through `hParseval_of_norm_le` (§3) and `coll_le` (L4) rather than assuming either. This
is the `hL2` input of `GapCertificate.assembly_row_bound`. -/
theorem hL2_discharged {k : ℕ} (hk : 3 ≤ k) (J : ℕ) (g : PiLp 2 G) (hg : ‖g‖ ≤ ‖cvec k‖) :
    ∑ b ∈ range J, (levelVec g b) ^ 2 ≤ 3 * s ^ (2 * k) :=
  hL2_of_parseval s_pos s_sq hk (hParseval_of_norm_le J g hg)

end ParsevalDischarge

/-!
--------------------------------------------------------------------------------
## §4. The hypothesis manifest
--------------------------------------------------------------------------------

Everything the top theorem still assumes, in one structure. Each field carries its source
document and its evidence label. The vocabulary is `EXTREMAL_VALUES.md`'s:

* **PROVEN** - unconditional proof written out in this repo, all `k`
* **CITED** - imported from a named external source
* **COMPLETE-at-sketch-level** - the argument is written and believed complete but not
  machine-checked here
* **DATA** - machine-verified on a finite range

The honest summary: **the residue is Lemma A**, i.e. `THEOREM.md` Part II's operator-norm facts,
which nobody has formalised. That is the analytic content of `HALFSHIFT_S4_LEMMA_A_PROOF.md`,
and it was never in scope for the L-track.
-/

section Manifest

variable {k K : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {φ : F →ₗ[ℂ] ℂ} {T : Module.End ℂ F}
  {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, NormedSpace ℂ (G m)]

/-- Row `a` of `Q` read as a function on `ℕ`, zero off the level range: the bridge between
`LevelMajorisation`'s `Matrix (Fin K) (Fin K) ℝ` and `GapCertificate`'s `ℕ → ℝ`. -/
noncomputable def rowFun (Q : Matrix (Fin K) (Fin K) ℝ) (a : Fin K) : ℕ → ℝ :=
  fun b => if h : b < K then Q a ⟨b, h⟩ else 0

theorem rowFun_of_ge (Q : Matrix (Fin K) (Fin K) ℝ) (a : Fin K) {b : ℕ} (h : K ≤ b) :
    rowFun Q a b = 0 := by simp [rowFun, Nat.not_lt.mpr h]

/-- **The hypothesis manifest.**

`k` is the modulus exponent, `K` the number of character levels carried (`K ≤ k-1`), `φ` the
Perron covector `1ᵀ`, `T` the transfer operator, `e` the level decomposition of the mean-zero
space `V = ker φ`, `U` the Koopman/adjoint partner `T^T` compressed to `V`, `Q` the level-block
norm matrix, and `gc` the level decomposition of the defect fibre. -/
structure LemmaAFacts (k K : ℕ) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (φ : F →ₗ[ℂ] ℂ) (T : Module.End ℂ F)
    {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, NormedSpace ℂ (G m)]
    (e : LinearMap.ker φ ≃ₗᵢ[ℂ] PiLp 2 G) (U : Module.End ℂ (LinearMap.ker φ))
    (Q : Matrix (Fin K) (Fin K) ℝ) (gc : PiLp 2 G) : Prop where
  /-- `k ≥ 3`. THEOREM.md's boxed range. **PROVEN** (a side condition, not an assumption
  about any object). -/
  hk : 3 ≤ k
  /-- At least one level is carried. **PROVEN** side condition. -/
  hK0 : 0 < K
  /-- The level range is the truncated one, `b ≤ k-2`. THEOREM.md Part III: *"the clean upper
  series truncates at the top: `b <= k-2`"*. **PROVEN** side condition. -/
  hKk : K ≤ k - 1
  /-- **I.1, column-stochasticity `1ᵀ T = 1ᵀ`.** THEOREM.md I.1. For the concrete `T_k` this is
  the partition-of-unity sum over lifts. Evidence label: **COMPLETE-at-sketch-level** (proved on
  paper in THEOREM.md; not machine-checked, because `T_k` is not concretely defined here). -/
  colStoch : φ ∘ₗ T = φ
  /-- **I.2, the adjoint bridge `A* = U_V` with `U = T^T`.** THEOREM.md I.2. On a
  finite-dimensional `ker φ` this is satisfied by `U := adjoint (compression colStoch)`, so it is
  never an obstruction. Evidence label: **PROVEN** (in the sense that a witness always exists;
  `LevelMajorisation.norm_pow_le_of_adjoint_bound` consumes it directly). -/
  hadj : ∀ x y : LinearMap.ker φ,
    @inner ℂ _ _ (T (x : F)) (y : F) = @inner ℂ _ _ (x : F) ((U y : LinearMap.ker φ) : F)
  /-- `Q` is entrywise nonnegative. It is a matrix of operator norms, so this is definitional
  for the concrete `Q_k`. **PROVEN**. -/
  hQ0 : ∀ i j, 0 ≤ Q i j
  /-- **The definition of `Q`.** THEOREM.md: *"`Q_k[a,b] := ‖P_a U_k P_b‖_2` is the matrix of
  level-block operator norms"*, written pointwise. **PROVEN** for the concrete `Q_k` by
  definition; here it says `Q` dominates `U`'s blocks, which is all the chain uses. -/
  hQblock : ∀ (m : Fin K) (y : G m) (m' : Fin K),
    ‖(e (U (e.symm (levelSingle m y)))) m'‖ ≤ Q m' m * ‖y‖
  /-- **LEMMA A, upper part.** THEOREM.md Part II: *"`‖P_a U_clean P_b‖_2 = 2^{-(b-a)/2}` for
  `a < b`"*, plus the rank-one defect `D = e_{r*} c*` with `u_a = ‖P_a e_{r*}‖ = 2^{-(a+1)/2}`
  (foundation R3), giving `Q[a,b] ≤ 2^{-(b-a)/2} + u_a v_b`.
  Source: `HALFSHIFT_S4_LEMMA_A_PROOF.md` §§1,3,4 + `STEP4_BLOCK_FORMULA_FOUNDATION.md` R3.
  Evidence label: **COMPLETE-at-sketch-level** - proved on paper for all `k` (confirmed
  2026-08-02, task W1-A), NOT formalised. **This is the residue.** -/
  hQupper : ∀ a b : Fin K, (a : ℕ) < (b : ℕ) →
    Q a b ≤ s ^ ((b : ℕ) - (a : ℕ)) + s ^ ((a : ℕ) + 1) * levelVec gc (b : ℕ)
  /-- **LEMMA A, lower part (R1).** THEOREM.md Part II: *"`P_a U_clean P_b = 0` for `a ≥ b`"*, so
  on and below the diagonal `Q[a,b] ≤ u_a v_b` is pure defect.
  Source: `STEP4_BLOCK_FORMULA_FOUNDATION.md` R1 + `HALFSHIFT_S4_LEMMA_A_PROOF.md`.
  Evidence label: **COMPLETE-at-sketch-level**. **This is the residue.** -/
  hQlower : ∀ a b : Fin K, (b : ℕ) ≤ (a : ℕ) →
    Q a b ≤ s ^ ((a : ℕ) + 1) * levelVec gc (b : ℕ)
  /-- **The identification of the defect covector.** `gc` is the level decomposition of the
  mean-zero part of the defect fibre distribution `c`, hence no longer than `c` itself. This is
  what remains of L4's `hParseval` after §3 discharged its two mathematical halves: a naming,
  requiring the concrete `T_k` to state as a theorem. Source: THEOREM.md Part II, `LEMMA_B_PROOF.md`.
  Evidence label: **COMPLETE-at-sketch-level** (definitional). -/
  hDefectVec : ‖gc‖ ≤ ‖cvec k‖

end Manifest

/-!
--------------------------------------------------------------------------------
## §5. The top-level theorem
--------------------------------------------------------------------------------

`THEOREM.md`'s boxed statement, in the form the completed pieces support. See §7 for the
delta-by-delta audit against the box.
-/

section TopLevel

variable {k K : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {φ : F →ₗ[ℂ] ℂ} {T : Module.End ℂ F}
  {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, NormedSpace ℂ (G m)]
  {e : LinearMap.ker φ ≃ₗᵢ[ℂ] PiLp 2 G} {U : Module.End ℂ (LinearMap.ker φ)}
  {Q : Matrix (Fin K) (Fin K) ℝ} {gc : PiLp 2 G}

/-- Row-index bookkeeping: `a < K ≤ k-1` and `k ≥ 3` give `a + 2 ≤ k`, the hypothesis
`GapCertificate.assembly_row_bound` needs (`e := k - a ≥ 2`). -/
theorem row_index_bound (h : LemmaAFacts k K φ T e U Q gc) (a : Fin K) : (a : ℕ) + 2 ≤ k := by
  have h1 : (a : ℕ) < K := a.isLt
  have h2 : K ≤ k - 1 := h.hKk
  have h3 : 3 ≤ k := h.hk
  omega

/-- The `ℕ`-indexed row sum equals the `Fin K`-indexed weighted row sum of `Q`. Pure
re-indexing; the point is that no orientation is silently transposed (`Q a b`, row `a`, stays
row `a`). -/
theorem rowSum_eq (Q : Matrix (Fin K) (Fin K) ℝ) (a : Fin K) {J : ℕ} (hJ : K ≤ J) :
    ∑ b ∈ range J, rowFun Q a b * ((2 : ℝ) ^ (a : ℕ) * ((1 : ℝ) / 2) ^ b)
      = ∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) := by
  have h1 : ∑ b ∈ range J, rowFun Q a b * ((2 : ℝ) ^ (a : ℕ) * ((1 : ℝ) / 2) ^ b)
      = ∑ b ∈ range K, rowFun Q a b * ((2 : ℝ) ^ (a : ℕ) * ((1 : ℝ) / 2) ^ b) := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr hJ) ?_).symm
    intro x _ hx
    have hxK : K ≤ x := Nat.not_lt.mp (by simpa using hx)
    simp [rowFun_of_ge Q a hxK]
  rw [h1, ← Fin.sum_univ_eq_sum_range
    (fun b => rowFun Q a b * ((2 : ℝ) ^ (a : ℕ) * ((1 : ℝ) / 2) ^ b)) K]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb : rowFun Q a (b : ℕ) = Q a b := by simp [rowFun, b.isLt]
  rw [hb]
  congr 1
  rw [div_pow, one_pow, mul_one_div]

/-- **The certificate bound, row by row.** For every row `a`, the weighted row sum of `Q` is at
most `envelope s 3 = 2^{-3/2} + 2^{-1}`. This is `THEOREM.md`'s
`cert(k) := max_a Σ_b Q[a,b] 2^{a-b} ≤ 2^{-3/2} + 2^{-1}`, i.e. the second inequality of the
boxed chain, assembled from Lemma A (`hQupper`/`hQlower`) and Lemma B (§3, discharged). -/
theorem cert_le (h : LemmaAFacts k K φ T e U Q gc) (a : Fin K) :
    ∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) ≤ envelope s 3 := by
  have hJ : K ≤ k - 1 := h.hKk
  have ha : (a : ℕ) + 2 ≤ k := row_index_bound h a
  -- Lemma A, extended off the level range (where `Q` is read as 0)
  have hup : ∀ b : ℕ, (a : ℕ) < b →
      rowFun Q a b ≤ s ^ (b - (a : ℕ)) + s ^ ((a : ℕ) + 1) * levelVec gc b := by
    intro b hab
    by_cases hb : b < K
    · have hQ := h.hQupper a ⟨b, hb⟩ (by simpa using hab)
      simpa [rowFun, hb] using hQ
    · have h0 : rowFun Q a b = 0 := rowFun_of_ge Q a (Nat.not_lt.mp hb)
      have hA : (0 : ℝ) ≤ s ^ (b - (a : ℕ)) := pow_nonneg s_pos.le _
      have hB : (0 : ℝ) ≤ s ^ ((a : ℕ) + 1) * levelVec gc b :=
        mul_nonneg (pow_nonneg s_pos.le _) (levelVec_nonneg gc b)
      rw [h0]; linarith
  have hlow : ∀ b : ℕ, b ≤ (a : ℕ) →
      rowFun Q a b ≤ s ^ ((a : ℕ) + 1) * levelVec gc b := by
    intro b hab
    have hb : b < K := lt_of_le_of_lt hab a.isLt
    have hQ := h.hQlower a ⟨b, hb⟩ (by simpa using hab)
    simpa [rowFun, hb] using hQ
  -- Lemma B, discharged in §3
  have hL2 : ∑ b ∈ range (k - 1), (levelVec gc b) ^ 2 ≤ 3 * s ^ (2 * k) :=
    hL2_discharged h.hk (k - 1) gc h.hDefectVec
  have hrow := assembly_row_bound s_pos s_sq ha (levelVec_nonneg gc) hup hlow hL2
  have henv : envelope s (k - (a : ℕ)) ≤ envelope s 3 :=
    envelope_max s_pos s_sq (by omega : 2 ≤ k - (a : ℕ))
  rw [← rowSum_eq Q a hJ]
  linarith

/-- **THE THEOREM.** `|λ₂(T)| ≤ cert(k) ≤ 2^{-3/2} + 2^{-1}`, uniformly in `k ≥ 3`.

For every eigenvalue `μ ≠ 1` of `T` (with an eigenvector), `‖μ‖ ≤ envelope s 3`. Combined with
`envelope_three_lt` and `envelope_three_lt_one` below, this is
`‖μ‖ < 0.853554 < 1` with no `k`-dependence whatsoever.

**Read §7 before quoting this**: the hypothesis bundle `LemmaAFacts` still contains Lemma A. -/
theorem gap_certificate (h : LemmaAFacts k K φ T e U Q gc)
    {μ : ℂ} (hμ : μ ≠ 1) {x : F} (hx0 : x ≠ 0) (hx : T x = μ • x) :
    ‖μ‖ ≤ envelope s 3 := by
  have hadj' : ∀ x y : LinearMap.ker φ,
      @inner ℂ _ _ ((OperatorChain.compression h.colStoch) x) y = @inner ℂ _ _ x (U y) := by
    intro u w
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact h.hadj u w
  exact norm_eigenvalue_le_cert_adjoint h.colStoch h.hK0 U hadj' e Q h.hQ0 h.hQblock
    (envelope s 3) (cert_le h) hμ hx0 hx

/-- **The theorem with the numeral.** `|λ₂(T)| < 0.853554`, machine-tied: the constant is
`envelope s 3` from the same proof term, bracketed in §1 by `0.853553 < envelope s 3 < 0.853554`. -/
theorem gap_certificate_numeral (h : LemmaAFacts k K φ T e U Q gc)
    {μ : ℂ} (hμ : μ ≠ 1) {x : F} (hx0 : x ≠ 0) (hx : T x = μ • x) :
    ‖μ‖ < 0.853554 :=
  lt_of_le_of_lt (gap_certificate h hμ hx0 hx) envelope_three_lt

/-- **The gap.** `|λ₂(T)| < 1`. -/
theorem gap_certificate_lt_one (h : LemmaAFacts k K φ T e U Q gc)
    {μ : ℂ} (hμ : μ ≠ 1) {x : F} (hx0 : x ≠ 0) (hx : T x = μ • x) :
    ‖μ‖ < 1 :=
  lt_of_le_of_lt (gap_certificate h hμ hx0 hx) envelope_three_lt_one

end TopLevel

/-!
--------------------------------------------------------------------------------
## §6. Anti-vacuity: the bundle is satisfiable, and the conclusion is inhabited
--------------------------------------------------------------------------------

**The failure mode this section exists to rule out.** A theorem of the form
`(h : Bundle) → conclusion` is worthless if `Bundle` is unsatisfiable, and nearly worthless if
every instance makes the conclusion vacuous (no `μ ≠ 1` eigenvalue exists to bound). L1 caught
this class in itself with `colSum_comp_mulVecLin`, L2 with its calibration section; this is the
same check for `LemmaAFacts`.

The witness below takes `φ = 0` (so `V = ker φ` is everything), `T = 0`, `U = 0`, `Q = 0`,
`gc = 0`, `k = 3`, `K = 2`. Every field of `LemmaAFacts` holds, and `T = 0` has the eigenvalue
`μ = 0 ≠ 1` with a nonzero eigenvector, so `gap_certificate` fires on an actual eigenpair and
returns a true statement about it: `‖(0 : ℂ)‖ ≤ envelope s 3`.

A **second** witness, `witness_facts_nonzero`, keeps everything else and replaces `Q = 0` with
`Qw2 = !![0, s; 0, 0]`, which saturates Lemma A's upper entry (`hQupper` holds with equality at
`(a,b) = (0,1)`) and has a genuinely nonzero weighted row sum `s/2 = 0.3536 < 0.8536`. It rules
out the reading "the bundle is only satisfiable at `Q = 0`, so `cert_le` bounds nothing".

**GRADED HONESTLY.** These are *consistency + inhabitation* witnesses: they show the ten fields
are simultaneously satisfiable, that `Q` need not be degenerate, and that the eigenvalue side is
not empty. They are **NOT** evidence that Lemma A's shape is achievable for a real transfer
operator, nor that the bound is near-tight - the operator is `T = 0`, whose `|λ₂| = 0`. The
non-trivial operator-side witness is L2's `calib_operator_bound`, which bounds `‖B²g‖` for
arbitrary `g` with an irrational constant and cannot be closed by `norm_num`/`decide`/`omega`.
Read the three together.
-/

section Witness

/-- The witness space: two levels, each `ℂ`. -/
abbrev Gw : Fin 2 → Type := fun _ => ℂ

/-- The witness ambient space `F = ℓ²({0,1}; ℂ)`. -/
abbrev Fw : Type := PiLp 2 Gw

/-- `φ = 0`: the mean-zero space is everything. -/
noncomputable def φw : Fw →ₗ[ℂ] ℂ := 0

/-- `T = 0`. -/
noncomputable def Tw : Module.End ℂ Fw := 0

/-- `ker 0 ≃ₗᵢ F`. -/
noncomputable def ew : LinearMap.ker φw ≃ₗᵢ[ℂ] PiLp 2 Gw where
  toFun x := (x : Fw)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨y, by simp [φw]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl

/-- `U = 0`. -/
noncomputable def Uw : Module.End ℂ (LinearMap.ker φw) := 0

/-- `Q = 0`. -/
def Qw : Matrix (Fin 2) (Fin 2) ℝ := 0

/-- `gc = 0`. -/
def gcw : PiLp 2 Gw := 0

/-- **Satisfiability.** Every field of `LemmaAFacts` holds at the witness. -/
theorem witness_facts : LemmaAFacts 3 2 φw Tw ew Uw Qw gcw where
  hk := by norm_num
  hK0 := by norm_num
  hKk := by norm_num
  colStoch := by simp [φw]
  hadj := by intro u w; simp [Tw, Uw]
  hQ0 := by intro i j; simp [Qw]
  hQblock := by
    intro m y m'
    simp [Uw, Qw]
  hQupper := by
    intro a b _
    have h1 : (0 : ℝ) ≤ s ^ ((b : ℕ) - (a : ℕ)) := pow_nonneg s_pos.le _
    have h2 : (0 : ℝ) ≤ s ^ ((a : ℕ) + 1) * levelVec gcw (b : ℕ) :=
      mul_nonneg (pow_nonneg s_pos.le _) (levelVec_nonneg _ _)
    simp only [Qw, Matrix.zero_apply]
    linarith
  hQlower := by
    intro a b _
    have h2 : (0 : ℝ) ≤ s ^ ((a : ℕ) + 1) * levelVec gcw (b : ℕ) :=
      mul_nonneg (pow_nonneg s_pos.le _) (levelVec_nonneg _ _)
    simp only [Qw, Matrix.zero_apply]
    linarith
  hDefectVec := by
    have : ‖gcw‖ = 0 := by simp [gcw]
    rw [this]; exact norm_nonneg _

/-- Every level energy of the zero defect vector is zero. -/
theorem levelVec_gcw (b : ℕ) : levelVec gcw b = 0 := by
  unfold levelVec gcw
  split <;> simp

/-- A **second** witness matrix, deliberately NOT zero: the top-right Lemma-A entry `s` at its
extreme allowed value (`hQupper` holds with equality there). Its weighted row sums are
`s/2 = 0.3536` and `0` - non-degenerate, and still under the bound. -/
noncomputable def Qw2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, s; 0, 0]

theorem Qw2_ne_zero : Qw2 ≠ 0 := by
  intro h
  have h1 : Qw2 0 1 = (0 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by rw [h]
  simp [Qw2] at h1
  exact absurd h1 (ne_of_gt s_pos)

theorem Qw2_nonneg : ∀ i j, 0 ≤ Qw2 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Qw2] <;> exact s_pos.le

/-- **Satisfiability with a nonzero `Q`.** The same witness, but with `Q` saturating Lemma A's
upper entry rather than vanishing. This rules out the reading "the bundle is only satisfiable
when `Q = 0`, so `cert_le` bounds nothing". -/
theorem witness_facts_nonzero : LemmaAFacts 3 2 φw Tw ew Uw Qw2 gcw where
  hk := by norm_num
  hK0 := by norm_num
  hKk := by norm_num
  colStoch := by simp [φw]
  hadj := by intro u w; simp [Tw, Uw]
  hQ0 := Qw2_nonneg
  hQblock := by
    intro m y m'
    have hL : ‖(ew (Uw (ew.symm (levelSingle m y)))) m'‖ = 0 := by simp [Uw]
    rw [hL]
    exact mul_nonneg (Qw2_nonneg m' m) (norm_nonneg y)
  hQupper := by
    intro a b hab
    rw [levelVec_gcw, mul_zero, add_zero]
    fin_cases a <;> fin_cases b <;> simp_all [Qw2]
  hQlower := by
    intro a b hab
    rw [levelVec_gcw, mul_zero]
    fin_cases a <;> fin_cases b <;> simp_all [Qw2]
  hDefectVec := by
    have h0 : ‖gcw‖ = 0 := by simp [gcw]
    rw [h0]; exact norm_nonneg _

/-- The witness eigenvector: `e_0`, nonzero. -/
noncomputable def xw : Fw := levelSingle (G := Gw) 0 (1 : ℂ)

theorem xw_ne_zero : xw ≠ 0 := by
  intro hz
  have h1 : (xw : Fw) 0 = (1 : ℂ) := by simp [xw, levelSingle]
  rw [hz] at h1
  simp at h1

/-- **Inhabitation.** `Tw` genuinely has an eigenvalue `≠ 1` with a nonzero eigenvector, so the
conclusion of `gap_certificate` is not vacuous at the witness. -/
theorem witness_eigenpair : Tw xw = (0 : ℂ) • xw := by simp [Tw]

/-- **The theorem fires at the witness.**

Graded honestly: the *statement* `‖(0 : ℂ)‖ ≤ envelope s 3` is arithmetically trivial and
`norm_num` would close it. The content is not in the statement, it is in the **elaboration**:
this term is `gap_certificate` applied to `witness_facts`, so it only type-checks if every field
of `LemmaAFacts` is genuinely inhabited at the witness AND `μ = 0 ≠ 1` with `xw ≠ 0` is a real
eigenpair of `Tw`. That is the anti-vacuity fact; the inequality is just its residue. -/
theorem witness_conclusion : ‖(0 : ℂ)‖ ≤ envelope s 3 :=
  gap_certificate witness_facts (by norm_num) xw_ne_zero witness_eigenpair

end Witness

/-!
--------------------------------------------------------------------------------
## §7. STATEMENT-FIDELITY AUDIT (the named deliverable)
--------------------------------------------------------------------------------

### THEOREM.md's boxed statement, verbatim

> **Theorem (uniform spectral gap).** Let `T_k` be the Syracuse transfer operator on the
> `N = 2^{k-1}` odd residues mod `2^k` (column-stochastic; its stationary distribution is close to
> but NOT exactly uniform - see I.1), and let `lambda_2(T_k)` be its second-largest eigenvalue in
> modulus. Then for every `k >= 3`,
> ```
>     |lambda_2(T_k)|  <=  cert(k)  <=  2^{-3/2} + 2^{-1}  =  0.853553...  <  1 ,
> ```
> where `cert(k) := max_a sum_b Q_k[a,b] 2^{a-b}` and `Q_k[a,b] := ||P_a U_k P_b||_2` is the matrix
> of level-block operator norms. With Lemma C the constant improves to `0.656`; the measured values
> are `cert(k) ~ 0.6345`, `rho(Q_k) ~ 0.566`, `|lambda_2| ~ 0.27`.

### The Lean statement, verbatim

```lean
theorem gap_certificate (h : LemmaAFacts k K φ T e U Q gc)
    {μ : ℂ} (hμ : μ ≠ 1) {x : F} (hx0 : x ≠ 0) (hx : T x = μ • x) :
    ‖μ‖ ≤ envelope s 3
```
with `cert_le : ∀ a, ∑ b, Q a b * (2^a / 2^b) ≤ envelope s 3`,
`envelope_three_gt/lt : 0.853553 < envelope s 3 < 0.853554`, and
`envelope_three_lt_one : envelope s 3 < 1`.

### The deltas, numbered

**(1) The hypothesis bundle.** THEOREM.md asserts the bound for *the* Syracuse operator `T_k`.
Lean asserts it for *any* `T` satisfying `LemmaAFacts`. The bundle's ten fields, by label:

| field | content | label |
|---|---|---|
| `hk`, `hK0`, `hKk` | `k ≥ 3`, `0 < K ≤ k-1` | **PROVEN** (side conditions) |
| `colStoch` | I.1, `1ᵀT = 1ᵀ` | **COMPLETE-at-sketch-level** |
| `hadj` | I.2, `A* = U_V` | **PROVEN** (a witness always exists in finite dimension) |
| `hQ0`, `hQblock` | `Q[a,b] = ‖P_a U P_b‖`, nonneg | **PROVEN** (definitional for `Q_k`) |
| `hQupper`, `hQlower` | **LEMMA A** | **COMPLETE-at-sketch-level** - THE RESIDUE |
| `hDefectVec` | `gc` is the defect fibre's level vector | **COMPLETE-at-sketch-level** (definitional) |

So the honest reading is: *Lemma A, plus the definition of `T_k`, is what stands between this
Lean theorem and THEOREM.md's box.* Lemma B is **not** in the bundle - §3 discharged it. Part I
and Part III are **not** in the bundle - L1, L2 and `GapCertificate.lean` proved them.

**(2) How `λ₂` is expressed. THIS IS A GENUINE WEAKENING, and it is inherited from L1.**
THEOREM.md I.1 says *"the characteristic polynomial factors, so `spec(T) = {1} ∪ spec(A)` as
multisets"* - an **algebraic**-multiplicity statement, which is what licenses the phrase "its
second-largest eigenvalue". `OperatorChain.lean` records that the multiset form is
COMPLETE-at-sketch-level and that what is unconditional there is the **geometric** version:
every `μ ≠ 1` admitting an eigenvector is bounded. `gap_certificate` inherits exactly that: its
hypotheses are `μ ≠ 1`, `x ≠ 0`, `T x = μ • x`.

Practical effect: the Lean theorem bounds every eigenvalue of `T` other than `1`. It does **not**
by itself rule out a Jordan block at `1` of algebraic multiplicity `> 1` masquerading as "the
second eigenvalue". For a column-stochastic `T` with a one-dimensional Perron eigenspace this is
a distinction without a difference, but that last clause is not proved here. Label of the delta:
**COMPLETE-at-sketch-level**.

**(3) `cert(k)` as a max vs as a bound on every row.** THEOREM.md defines
`cert(k) := max_a Σ_b Q[a,b] 2^{a-b}` and bounds the max. `cert_le` bounds *every* row by the
same constant, which is equivalent (a finite max is ≤ `c` iff every entry is) and is the form
the chain consumes. No `max` is ever formed, so no nonemptiness side condition appears.
Label: **PROVEN**, no weakening.

**(4) k-range.** Identical: THEOREM.md says `k ≥ 3`, `LemmaAFacts.hk` says `3 ≤ k`. The
`e := k - a ≥ 2` truncation and the `f(3)` maximum are both live at `k = 3`, and `envelope_max`
is applied at `2 ≤ k - a` exactly. **No k-range difference.** Label: **PROVEN**.

**(5) The operator is not defined.** `T_k` itself - the Syracuse transfer operator on odd
residues mod `2^k` - is never constructed in Lean. This is L5's declared kill criterion,
triggered deliberately: a concrete matrix definition that instantiates L2's abstract theorems
was judged more expensive than its value, and *"a partially-instantiated but honest manifest
beats a fully-wired theorem with a fudged definition"*. Consequence: `colStoch` is assumed rather
than proved from a definition, which is a real gap against L5's own acceptance list (which asked
for column-stochasticity proved from the definition). Label: **NOT DONE**, stated plainly.

**(6) `N = 2^{k-1}`, the state count.** THEOREM.md fixes the dimension. Lean fixes only the
number of levels `K ≤ k-1` and leaves `F` an arbitrary inner-product space. Nothing in the chain
uses `N`, so this is a generalisation, not a weakening. Label: **PROVEN**.

**(7) The `0.656` clause of the box.** Not stated, deliberately - see the header. The proven
Lemma C sharpening is `0.6826775358`; `0.6553300859` needs the `DATA` constant `g_b ≤ 3/4`
(`k ≤ 26`). Label of the omission: intentional, per `EXTREMAL_VALUES.md`.

**(8) The measured values (`~0.6345`, `~0.566`, `~0.27`).** Not stated - they are `DATA`. They
appear in the header as gate 2's anchor only, in a comment, never in a statement.

--------------------------------------------------------------------------------
## §8. Self-adversarial pass (task L5 gate 3, run in-file)
--------------------------------------------------------------------------------

*"Find any way this statement is weaker than THEOREM.md's box, or any hypothesis that makes it
vacuous."* Findings, each recorded whether or not it was fixed:

1. **"`hQupper`/`hQlower` could be jointly unsatisfiable with `hQblock`, making the theorem
   empty."** Real risk; addressed by §6, which exhibits a simultaneous witness with an
   inhabited conclusion, and a second with `Q` nonzero and Lemma A's upper entry *saturated*.
   Graded honestly there: the operator is still `T = 0`, so this establishes consistency,
   non-degeneracy of `Q`, and non-vacuity of the *conclusion* - not that Lemma A's shape is
   achievable for a real transfer operator. **Open, mitigated.**
2. **"`hDefectVec` could be trivially satisfiable by `gc = 0`, so §3's discharge might be
   vacuous."** True of the witnesses, and false of the intended instance. But note that `gc = 0`
   makes `hQupper`/`hQlower` *harder*, not easier (the defect term vanishes and `Q` must be
   bounded by the clean cascade alone) - so a `gc = 0` instance is a strengthening of Lemma A,
   not a loophole. **Not a defect.**
8. **"`cvec` might not be the `c` the collision bound is about."** Guarded by `cf_sum` and
   `cvec_sum`: the fibre counts sum to `2^k` and `cvec` sums to `1`, so it is the fibre
   *distribution*, and it is built from the same `cf` that defines `coll`. Neither is decidable
   for symbolic `k`. **Clear.**
9. **"§3 might have discharged a renamed version of `hParseval` rather than `hParseval`."**
   Checked by following the call chain: `cert_le` obtains its `hL2` from `hL2_discharged`, whose
   only input is `hDefectVec`; `hL2_of_parseval`'s `hParseval` argument is supplied by
   `hParseval_of_norm_le`, which is proved. No occurrence of an assumed `hParseval` survives
   anywhere in the chain feeding `gap_certificate`. **Clear.**
3. **"The transpose trap."** `Q a b` is fed to `norm_eigenvalue_le_cert_adjoint`, whose `hQblock`
   is stated in `U`'s (i.e. THEOREM.md's) orientation, so the constant is literally `cert(k)`
   and not the weighted column sum. `rowSum_eq` re-indexes only; it never swaps arguments. L2
   documents that the transposed reading is *false*, not merely differently-worded, at its
   calibration matrix - so this is checkable, and checked. **Clear.**
4. **"A theorem closable by `omega`/`simp`/`decide` alone, reading as a proved cross-check."**
   Audited: `cert_le` and `gap_certificate` route through `assembly_row_bound`, `envelope_max`
   and `norm_eigenvalue_le_cert_adjoint`, none of which is decidable. `cvec_norm_sq` is a real
   computation over `Fin (2^k)` for symbolic `k` - `decide` cannot touch it. The arithmetic-only
   declarations are `s_lt`, `s_gt`, `envelope_three_lt`, `envelope_three_gt`, and they are
   *labelled as numerals*, not presented as evidence. **Clear.**
5. **"Proving the right-looking statement about the wrong object."** The object at risk here is
   `c`. `cvec` is built from `CollisionBound.cf`, the same `cf` that defines `coll` - so
   `cvec_norm_sq` cannot be about a different vector than the collision bound is about. It would
   be a different object if `cf` itself were wrong, which is L3/L4's audited territory.
   **Clear at this layer, inherited elsewhere.**
6. **"`envelope s 3 < 0.853554` might be true while the bound is much larger."** This is why
   `s_gt` and `envelope_three_gt` exist: the constant is bracketed on both sides, so the numeral
   is pinned, not merely dominated. **Fixed.**
7. **"The theorem might be stronger than the box and therefore suspicious."** It is more general
   (delta 6: arbitrary `F`, no `N = 2^{k-1}`) and strictly weaker in one place (delta 2:
   geometric, not algebraic, multiplicity). Net: not stronger. **Clear.**
-/

/-!
--------------------------------------------------------------------------------
## §9. Axiom audit
--------------------------------------------------------------------------------

Every exported declaration must depend only on a SUBSET of `{propext, Classical.choice,
Quot.sound}`. Several depend on strictly fewer - so the check is subset, not string equality.
-/

#print axioms s
#print axioms s_pos
#print axioms s_sq
#print axioms s_lt
#print axioms s_gt
#print axioms envelope_three_eq
#print axioms envelope_three_lt
#print axioms envelope_three_gt
#print axioms envelope_three_lt_one
#print axioms sum_levelEnergy_sq
#print axioms levelVec
#print axioms levelVec_nonneg
#print axioms levelVec_of_lt
#print axioms levelVec_of_ge
#print axioms sum_levelVec_sq
#print axioms sum_levelVec_sq_le
#print axioms cvec
#print axioms cvec_apply
#print axioms cf_sum
#print axioms cvec_sum
#print axioms cvec_norm_sq
#print axioms hParseval_of_norm_le
#print axioms hL2_discharged
#print axioms rowFun
#print axioms rowFun_of_ge
#print axioms LemmaAFacts
#print axioms row_index_bound
#print axioms rowSum_eq
#print axioms cert_le
#print axioms gap_certificate
#print axioms gap_certificate_numeral
#print axioms gap_certificate_lt_one
#print axioms φw
#print axioms Tw
#print axioms ew
#print axioms Uw
#print axioms Qw
#print axioms gcw
#print axioms levelVec_gcw
#print axioms Qw2
#print axioms Qw2_ne_zero
#print axioms Qw2_nonneg
#print axioms witness_facts
#print axioms witness_facts_nonzero
#print axioms xw
#print axioms xw_ne_zero
#print axioms witness_eigenpair
#print axioms witness_conclusion

-- Transitive coverage: the upstream declarations `gap_certificate` actually consumes.
#print axioms GapCertificate.assembly_row_bound
#print axioms GapCertificate.envelope_max
#print axioms GapCertificate.envelope_lt_one
#print axioms OperatorChain.norm_eigenvalue_le_of_compression_pow_bound
#print axioms LevelMajorisation.norm_eigenvalue_le_cert_adjoint
#print axioms CollisionBound.coll_le
#print axioms CollisionBound.hL2_of_parseval

end Assembly
