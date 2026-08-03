/-
# `LemmaAFacts`, instantiated at the concrete `T_k`

Task L12. `Assembly.lean` §4 states the whole residue of the certificate as one structure,
`LemmaAFacts k K φ T e U Q gc`, with ten fields. Until now that structure had exactly two
witnesses, both degenerate (`Assembly.witness_facts`, `witness_facts_nonzero`, at `T = 0`).
This file builds the **real** witness: `φ = onesCov k`, `T = Tend k` (the Syracuse transfer
operator of `TransferOperator.lean`), `K = k - 1`, `G` the genuine character level spaces,
`e` the character level decomposition of `ker(1ᵀ)`, `U` the adjoint of the compression,
`Q` the matrix of level-block operator norms, and `gc` the level decomposition of the
mean-zero part of the defect fibre.

## What lands, and what does not

**Nine of the ten fields are discharged for the concrete operator.** The one that is not is
`hQupper` - `THEOREM.md` Part II's `‖P_a U_clean P_b‖ = 2^{-(b-a)/2}` for `a < b`, which needs
the isometry `B*B = 2^{-d} I` and was never in the L-track's scope. `facts_of_hQupper` below
takes it as its single hypothesis and returns the full manifest; `gap_certificate_concrete`
then delivers `THEOREM.md`'s boxed conclusion for the concretely defined `T_k`, conditional on
that one named piece of mathematics and nothing else.

Field by field:

| field | status here | supplier |
|---|---|---|
| `hk`, `hK0`, `hKk` | **PROVEN** | `omega` on `K = k-1`, `3 ≤ k` |
| `colStoch` | **PROVEN** | `TransferOperator.colStoch_concrete` (L7) |
| `hadj` | **PROVEN** | §5-§6, `U` := the compression of `U_full = Tᵀ` to `ker φ` |
| `hQ0` | **PROVEN** | `norm_nonneg`, `Q` is a matrix of operator norms |
| `hQblock` | **PROVEN** | §7, `ContinuousLinearMap.le_opNorm` |
| `hQlower` | **PROVEN** | §7, from L11's `norm_P_U_P_le` - and with **equality**, `Qmat_lower_eq` |
| `hDefectVec` | **PROVEN** | §8 |
| `hQupper` | **CLOSED 2026-08-03 (F3).** Was "the sole residue". | `GramIdentity.hQupper_holds` |

## STANDING GATE - sign scope, unchanged

Nothing here says anything about Collatz cycles. Every construction below is available verbatim
for the `3x-1` operator, which has real cycles and passes the same certificate. See
`Assembly.lean`'s standing gate 1 and `CYCLE_CLAIM_REFUTED.md`. This file narrows the *hypothesis
count* of `Assembly.gap_certificate` from ten to one; it does not change what that theorem is
about.

## The orientation trap (L2's near-miss), and where it is discharged here

`THEOREM.md`'s `Q[a,b] = ‖P_a U P_b‖` is built for `U = Tᵀ`, **not** for the compression
`A = T|_V`; the two are transposes, and a weighted row sum of one is a weighted column sum of
the other. The manifest's `hQblock` is therefore stated for `U`, and `hadj` is the only bridge
between the two. Here:

* `inner_Tend_Uendfull` (§6) proves `⟨T x, y⟩ = ⟨x, U_full y⟩` for `U_full = DefectSplit.Uendfull
  = (T_k)ᵀ`, i.e. that the transpose really is the adjoint. Its only content is that the entries
  of `T_k` are real (`conj_TkC`), and it is what makes `hadj` a theorem rather than a convention;
* `U` is then the **compression** of `U_full` to `ker φ` (§5). The projection is not decoration:
  `ker φ` is `T`-invariant but **not** `U_full`-invariant, because the row sums of `T_k` are not
  constant - `TransferOperator.Tk_row_sum`, `THEOREM.md` I.1's boxed warning. `P_Uop_eq` then
  proves `U` and `U_full` agree *after projection to a level*, which is what routes L11's block
  bound - built for `U_full` - into `hQblock`, which is stated for `U`.

`LinearMap.adjoint` was tried first and abandoned: instance synthesis for the adjoint on a
`Submodule` of `EuclideanSpace` does not terminate here (a real Mathlib-side cost, recorded for
the next task). The explicit compression is equivalent and cheap.

Those two steps are the whole orientation argument, and both are theorems, not conventions.

## Calibration (done before proving, against `EXTREMAL_VALUES.md` line 170)

`Q` was rebuilt numerically from `TransferOperator.Tcount` exactly as defined below
(`Q[a,b] = ‖P_a Tᵀ P_b‖₂` in the character basis, levels `a = v₂(ξ)`), for `k = 4..13`:

```
  cert(8)  = 0.634659      rho(Q_8) = 0.566061      |lambda_2(T_8)| = 0.2549
  cert(13) = 0.634412      binding row  e* = k - a* = 4  for every k in 4..13
  column sums of T_k exactly 1 (max deviation 0.0e+00)
```

all matching the recorded values. Two further facts the numerics fix, both then proved below:

* `Q[a,b] = s^{a+1}·‖P_b c*‖` for `b ≤ a`, to `1e-16` - i.e. `hQlower` is **tight**, not an
  over-estimate. Proved as `Qmat_lower_eq` (§7).
* `‖c*‖² − ‖gc‖² = |⟨χ₀, c*⟩|²` exactly - `gc` really is the mean-zero part.

Non-degeneracy of the instance (failure mode 3) is §9.
-/

import DefectSplit

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace ManifestInstance

open Finset GapCertificate LemmaA CountingLemmas CollisionBound TransferOperator
open CharacterBasis BlockVanishing OperatorBlock DefectSplit

/-- The ambient space `ℓ²(odd residues mod 2^k)`. -/
abbrev Fsp (k : ℕ) : Type := EuclideanSpace ℂ (Fin (2 ^ (k - 1)))

theorem two_le {k : ℕ} (hk : 3 ≤ k) : 2 ≤ k := Nat.le_of_succ_le hk

theorem one_le {k : ℕ} (hk : 3 ≤ k) : 1 ≤ k := Nat.le_of_succ_le (Nat.le_of_succ_le hk)

theorem one_le' {k : ℕ} (hk : 2 ≤ k) : 1 ≤ k := Nat.le_of_succ_le hk

/-!
--------------------------------------------------------------------------------
## §1. `ker(1ᵀ)` is the orthogonal complement of the Perron character
--------------------------------------------------------------------------------

The step the task brief flags as the place a "π is uniform" assumption would sneak in.
`φ = onesCov k` is the covector `1ᵀ`, a LEFT eigenvector; it is *not* the stationary
distribution, and nothing below assumes it is. What is true, and proved here, is the purely
Fourier-analytic statement that `1ᵀ` is `√N` times the `ξ = 0` character functional, so
`ker φ` is exactly the span of the characters with `ξ ≠ 0`.
-/

theorem inner_chiVec_zero {k : ℕ} (x : Fsp k) :
    (@inner ℂ _ _ (chiVec k 0) x : ℂ) = (onesCov k x) / (rt k : ℂ) := by
  rw [PiLp.inner_apply, onesCov_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [RCLike.inner_apply]
  show x s * (starRingEnd ℂ) (chi k ((0 : Fin (2 ^ (k - 1))) : ℕ) (s : ℕ) / (rt k : ℂ))
      = x s / (rt k : ℂ)
  rw [chi]
  simp [Complex.conj_ofReal, div_eq_mul_inv]

theorem mem_ker_iff {k : ℕ} (x : Fsp k) :
    x ∈ LinearMap.ker (onesCov k) ↔ (@inner ℂ _ _ (chiVec k 0) x : ℂ) = 0 := by
  rw [LinearMap.mem_ker, inner_chiVec_zero, div_eq_zero_iff]
  constructor
  · intro h; exact Or.inl h
  · rintro (h | h)
    · exact h
    · exact absurd h (rt_ne_zero k)

/-- Every non-Perron character is mean-zero. -/
theorem chiVec_mem_ker {k : ℕ} (hk : 1 ≤ k) {ξ : Fin (2 ^ (k - 1))} (h : ξ ≠ 0) :
    chiVec k ξ ∈ LinearMap.ker (onesCov k) := by
  rw [mem_ker_iff]
  have hon := chiVec_orthonormal hk
  rw [orthonormal_iff_ite.1 hon 0 ξ, if_neg (fun hc => h hc.symm)]

theorem ne_zero_of_mem_levelSet {k a : ℕ} {ξ : Fin (2 ^ (k - 1))} (h : ξ ∈ levelSet k a) :
    ξ ≠ 0 := by
  intro hc
  exact (mem_levelSet.1 h).1 (by rw [hc]; rfl)

/-- Dropping the Perron frequency from a sum whose Perron term vanishes. -/
theorem sum_erase_zero {k : ℕ} {M : Type} [AddCommMonoid M] (f : Fin (2 ^ (k - 1)) → M)
    (h0 : f 0 = 0) :
    ∑ ξ ∈ univ.erase (0 : Fin (2 ^ (k - 1))), f ξ = ∑ ξ : Fin (2 ^ (k - 1)), f ξ := by
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro y _ hy
  have hy0 : y = 0 := by
    by_contra hc
    exact hy (Finset.mem_erase.2 ⟨hc, Finset.mem_univ y⟩)
  rw [hy0, h0]

/-!
--------------------------------------------------------------------------------
## §2. Coefficient facts about the level projections `P_a`
--------------------------------------------------------------------------------
-/

/-- `‖P_a x‖² = ∑_{ξ ∈ levelSet a} |⟨χ_ξ, x⟩|²`. The general-coefficient form of
`DefectSplit.norm_sq_P_single`. -/
theorem norm_sq_P {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (x : Fsp k) :
    ‖P k a x‖ ^ 2 = ∑ ξ ∈ levelSet k a, ‖(@inner ℂ _ _ (chiVec k ξ) x : ℂ)‖ ^ 2 := by
  have hon := chiVec_orthonormal hk
  set c : Fin (2 ^ (k - 1)) → ℂ := fun ξ => (@inner ℂ _ _ (chiVec k ξ) x : ℂ) with hc
  have hinner : (@inner ℂ _ _ (P k a x) (P k a x) : ℂ)
      = (((∑ ξ ∈ levelSet k a, ‖c ξ‖ ^ 2 : ℝ)) : ℂ) := by
    rw [P_apply k a x, hon.inner_sum c c (levelSet k a)]
    push_cast
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := P k a x)
  rw [hinner] at h1
  have h2 : ((‖P k a x‖ ^ 2 : ℝ) : ℂ) = (((∑ ξ ∈ levelSet k a, ‖c ξ‖ ^ 2 : ℝ)) : ℂ) := by
    push_cast; push_cast at h1; exact h1.symm
  exact Complex.ofReal_inj.mp h2

/-- Parseval in the character basis: `∑_ξ |⟨χ_ξ, x⟩|² = ‖x‖²`. -/
theorem sum_sq_coeff {k : ℕ} (hk : 1 ≤ k) (x : Fsp k) :
    ∑ ξ : Fin (2 ^ (k - 1)), ‖(@inner ℂ _ _ (chiVec k ξ) x : ℂ)‖ ^ 2 = ‖x‖ ^ 2 := by
  have hrepr : ∀ ξ, ((chiBasis hk).repr x) ξ = (@inner ℂ _ _ (chiVec k ξ) x : ℂ) := by
    intro ξ
    rw [OrthonormalBasis.repr_apply_apply, chiBasis_apply]
  have hnorm : ‖(chiBasis hk).repr x‖ = ‖x‖ := (chiBasis hk).repr.norm_map x
  have hE := EuclideanSpace.norm_eq ((chiBasis hk).repr x)
  rw [hnorm] at hE
  have h2 : ∑ ξ : Fin (2 ^ (k - 1)), ‖((chiBasis hk).repr x) ξ‖ ^ 2
      = ∑ ξ : Fin (2 ^ (k - 1)), ‖(@inner ℂ _ _ (chiVec k ξ) x : ℂ)‖ ^ 2 :=
    Finset.sum_congr rfl fun ξ _ => by rw [hrepr ξ]
  rw [← h2, hE, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]

/-- `P_a` kills the Perron direction. -/
theorem P_chiVec_zero {k : ℕ} (hk : 1 ≤ k) (a : ℕ) :
    P k a (chiVec k (0 : Fin (2 ^ (k - 1)))) = 0 := by
  rw [P_apply]
  refine Finset.sum_eq_zero fun ξ hξ => ?_
  have hon := chiVec_orthonormal hk
  rw [orthonormal_iff_ite.1 hon ξ 0, if_neg (ne_zero_of_mem_levelSet hξ), zero_smul]

/-- `P_a` is a contraction. -/
theorem norm_P_le {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (x : Fsp k) : ‖P k a x‖ ≤ ‖x‖ := by
  have hself : (@inner ℂ _ _ (P k a x) (P k a x) : ℂ) = @inner ℂ _ _ x (P k a x) := by
    rw [P_selfadjoint hk a x (P k a x), P_idem hk]
  have h1 : ‖P k a x‖ ^ 2 = RCLike.re (@inner ℂ _ _ x (P k a x) : ℂ) := by
    rw [← hself]; exact (inner_self_eq_norm_sq _).symm
  have h2 : RCLike.re (@inner ℂ _ _ x (P k a x) : ℂ) ≤ ‖(@inner ℂ _ _ x (P k a x) : ℂ)‖ :=
    RCLike.re_le_norm _
  have h3 : ‖(@inner ℂ _ _ x (P k a x) : ℂ)‖ ≤ ‖x‖ * ‖P k a x‖ := norm_inner_le_norm _ _
  nlinarith [norm_nonneg (P k a x), norm_nonneg x]

/-!
--------------------------------------------------------------------------------
## §3. The level index type and the level spaces `G`
--------------------------------------------------------------------------------

`K := k - 1`, levels `m ∈ {0, ..., k-2}` - the truncated range `CharacterBasis.level_lt`
proves is the real one. `G m` is the level-`m` character coordinate space; §9 shows every
one of them is nonzero, so the manifest is not being instantiated at a degenerate `G`.
-/

/-- The level-`m` coordinate space. -/
abbrev Glev (k : ℕ) (m : Fin (k - 1)) : Type := EuclideanSpace ℂ ↥(levelSet k (m : ℕ))

/-- Summing a function of frequencies level by level is summing it over all nonzero
frequencies. `CharacterBasis.levelSet_partition`, in the shape the isometry needs. -/
theorem sum_levels {k : ℕ} (hk : 2 ≤ k) {M : Type} [AddCommMonoid M]
    (f : Fin (2 ^ (k - 1)) → M) :
    ∑ m : Fin (k - 1), ∑ ξ ∈ levelSet k (m : ℕ), f ξ
      = ∑ ξ ∈ univ.erase (0 : Fin (2 ^ (k - 1))), f ξ := by
  rw [Fin.sum_univ_eq_sum_range (fun m => ∑ ξ ∈ levelSet k m, f ξ) (k - 1),
    ← levelSet_partition hk, sum_biUnion (fun a _ a' _ h => levelSet_disjoint h)]

/-!
--------------------------------------------------------------------------------
## §4. The isometry `e : ker φ ≃ₗᵢ PiLp 2 G`
--------------------------------------------------------------------------------
-/

/-- The coordinate map: `x ↦ (⟨χ_ξ, x⟩)_{ξ}`, grouped by level. -/
noncomputable def eFun (k : ℕ) (x : Fsp k) : PiLp 2 (Glev k) :=
  WithLp.toLp 2 (fun m => WithLp.toLp 2 (fun ξ : ↥(levelSet k (m : ℕ)) =>
    (@inner ℂ _ _ (chiVec k (ξ : Fin (2 ^ (k - 1)))) x : ℂ)))

@[simp] theorem eFun_apply (k : ℕ) (x : Fsp k) (m : Fin (k - 1))
    (ξ : ↥(levelSet k (m : ℕ))) :
    eFun k x m ξ = (@inner ℂ _ _ (chiVec k (ξ : Fin (2 ^ (k - 1)))) x : ℂ) := rfl

theorem norm_sq_eFun_component {k : ℕ} (x : Fsp k) (m : Fin (k - 1)) :
    ‖eFun k x m‖ ^ 2 = ∑ ξ ∈ levelSet k (m : ℕ), ‖(@inner ℂ _ _ (chiVec k ξ) x : ℂ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  exact Finset.sum_attach (levelSet k (m : ℕ))
    (fun ζ => ‖(@inner ℂ _ _ (chiVec k ζ) x : ℂ)‖ ^ 2)

theorem norm_eFun_component {k : ℕ} (hk : 1 ≤ k) (x : Fsp k) (m : Fin (k - 1)) :
    ‖eFun k x m‖ = ‖P k (m : ℕ) x‖ := by
  refine sq_eq_of_nonneg (norm_nonneg _) (norm_nonneg _) ?_
  rw [norm_sq_eFun_component, norm_sq_P hk]

/-- The coefficient of `y` at frequency `ζ`, read at level `m` (zero off that level). -/
noncomputable def coefOf {k : ℕ} (y : PiLp 2 (Glev k)) (m : Fin (k - 1)) :
    Fin (2 ^ (k - 1)) → ℂ :=
  fun ζ => if h : ζ ∈ levelSet k (m : ℕ) then y m ⟨ζ, h⟩ else 0

/-- The synthesis map: `y ↦ ∑_ξ y_ξ χ_ξ`. -/
noncomputable def eInv {k : ℕ} (y : PiLp 2 (Glev k)) : Fsp k :=
  ∑ m : Fin (k - 1), ∑ ζ ∈ levelSet k (m : ℕ), coefOf y m ζ • chiVec k ζ

theorem eInv_mem_ker {k : ℕ} (hk : 1 ≤ k) (y : PiLp 2 (Glev k)) :
    eInv y ∈ LinearMap.ker (onesCov k) := by
  rw [mem_ker_iff, eInv, inner_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [inner_sum]
  refine Finset.sum_eq_zero fun ζ hζ => ?_
  have hon := chiVec_orthonormal hk
  rw [inner_smul_right, orthonormal_iff_ite.1 hon 0 ζ,
    if_neg (fun hc => ne_zero_of_mem_levelSet hζ hc.symm), mul_zero]

/-- The coefficient of `∑_ξ y_ξ χ_ξ` at a frequency `η` of level `m₀` is `y_{m₀,η}`. -/
theorem inner_eInv {k : ℕ} (hk : 2 ≤ k) (y : PiLp 2 (Glev k)) (m₀ : Fin (k - 1))
    (η : ↥(levelSet k (m₀ : ℕ))) :
    (@inner ℂ _ _ (chiVec k (η : Fin (2 ^ (k - 1)))) (eInv y) : ℂ) = y m₀ η := by
  have hk1 : 1 ≤ k := by omega
  rw [eInv, inner_sum]
  have hterm : ∀ m : Fin (k - 1), (@inner ℂ _ _ (chiVec k (η : Fin (2 ^ (k - 1))))
      (∑ ζ ∈ levelSet k (m : ℕ), coefOf y m ζ • chiVec k ζ) : ℂ)
      = if (η : Fin (2 ^ (k - 1))) ∈ levelSet k (m : ℕ) then coefOf y m (η : Fin (2 ^ (k - 1)))
        else 0 := fun m => inner_chiVec_sum hk1 (levelSet k (m : ℕ)) (coefOf y m) _
  rw [Finset.sum_congr rfl (fun m _ => hterm m),
    Finset.sum_eq_single_of_mem m₀ (Finset.mem_univ m₀)]
  · rw [if_pos η.2, coefOf, dif_pos η.2]
  · intro m _ hm
    refine if_neg fun hc => hm ?_
    have h1 := (mem_levelSet.1 hc).2
    have h2 := (mem_levelSet.1 η.2).2
    exact Fin.ext (by omega)

theorem norm_eFun {k : ℕ} (hk : 2 ≤ k) (x : LinearMap.ker (onesCov k)) :
    ‖eFun k (x : Fsp k)‖ = ‖x‖ := by
  have hk1 : 1 ≤ k := by omega
  have hzero : (@inner ℂ _ _ (chiVec k (0 : Fin (2 ^ (k - 1)))) (x : Fsp k) : ℂ) = 0 :=
    (mem_ker_iff _).1 x.2
  refine sq_eq_of_nonneg (norm_nonneg _) (norm_nonneg _) ?_
  rw [← Assembly.sum_levelEnergy_sq (G := Glev k) (eFun k (x : Fsp k))]
  rw [Finset.sum_congr rfl (fun (m : Fin (k - 1)) _ =>
    norm_sq_eFun_component (x : Fsp k) m)]
  rw [sum_levels hk (fun ξ => ‖(@inner ℂ _ _ (chiVec k ξ) (x : Fsp k) : ℂ)‖ ^ 2)]
  rw [sum_erase_zero (fun ξ => ‖(@inner ℂ _ _ (chiVec k ξ) (x : Fsp k) : ℂ)‖ ^ 2)
    (by simp [hzero])]
  exact sum_sq_coeff hk1 (x : Fsp k)

/-- **The level decomposition of the mean-zero space**, as a linear isometry equivalence. -/
noncomputable def elev {k : ℕ} (hk : 2 ≤ k) :
    LinearMap.ker (onesCov k) ≃ₗᵢ[ℂ] PiLp 2 (Glev k) where
  toFun x := eFun k (x : Fsp k)
  map_add' x y := by
    ext m ξ
    simp only [eFun_apply, Submodule.coe_add, inner_add_right]
    rfl
  map_smul' c x := by
    ext m ξ
    simp only [eFun_apply, SetLike.val_smul, inner_smul_right]
    rfl
  invFun y := ⟨eInv y, eInv_mem_ker (one_le' hk) y⟩
  left_inv x := by
    have hk1 : 1 ≤ k := by omega
    refine Subtype.ext ?_
    show eInv (eFun k (x : Fsp k)) = (x : Fsp k)
    have hzero : (@inner ℂ _ _ (chiVec k (0 : Fin (2 ^ (k - 1)))) (x : Fsp k) : ℂ) = 0 :=
      (mem_ker_iff _).1 x.2
    have hstep : ∀ m : Fin (k - 1), ∑ ζ ∈ levelSet k (m : ℕ),
        coefOf (eFun k (x : Fsp k)) m ζ • chiVec k ζ
        = ∑ ζ ∈ levelSet k (m : ℕ),
            (@inner ℂ _ _ (chiVec k ζ) (x : Fsp k) : ℂ) • chiVec k ζ := by
      intro m
      refine Finset.sum_congr rfl fun ζ hζ => ?_
      rw [coefOf, dif_pos hζ]
      rfl
    rw [eInv, Finset.sum_congr rfl (fun m _ => hstep m),
      sum_levels hk (fun ζ => (@inner ℂ _ _ (chiVec k ζ) (x : Fsp k) : ℂ) • chiVec k ζ),
      sum_erase_zero (fun ζ => (@inner ℂ _ _ (chiVec k ζ) (x : Fsp k) : ℂ) • chiVec k ζ)
        (by simp [hzero]),
      chiBasis_sum_repr hk1]
  right_inv y := by
    ext m ξ
    show (@inner ℂ _ _ (chiVec k (ξ : Fin (2 ^ (k - 1)))) (eInv y) : ℂ) = y m ξ
    exact inner_eInv hk y m ξ
  norm_map' x := norm_eFun hk x

@[simp] theorem elev_apply {k : ℕ} (hk : 2 ≤ k) (x : LinearMap.ker (onesCov k))
    (m : Fin (k - 1)) (ξ : ↥(levelSet k (m : ℕ))) :
    (elev hk x) m ξ = (@inner ℂ _ _ (chiVec k (ξ : Fin (2 ^ (k - 1)))) (x : Fsp k) : ℂ) := rfl

/-- **`e` carries the level decomposition**: the norm of the level-`m` coordinate block is the
norm of the level-`m` projection. -/
theorem norm_elev_component {k : ℕ} (hk : 2 ≤ k) (x : LinearMap.ker (onesCov k))
    (m : Fin (k - 1)) : ‖(elev hk x) m‖ = ‖P k (m : ℕ) (x : Fsp k)‖ :=
  norm_eFun_component (one_le' hk) (x : Fsp k) m

/-!
--------------------------------------------------------------------------------
## §5. `U`, and `hadj`
--------------------------------------------------------------------------------

`A = T|_V` is `OperatorChain.compression`, available because `colStoch_concrete` proves
`φ ∘ₗ T = φ`. `U := adjoint A`, so `hadj` is Mathlib's defining property of the adjoint and
the orientation cannot be off by a transpose.
-/

/-- `A = T_k|_V`, the compression to the mean-zero space: the operator `U` is the adjoint
partner of. Recorded because `Assembly.gap_certificate` pairs `U` against exactly this. -/
noncomputable def Aop {k : ℕ} (hk : 1 ≤ k) : Module.End ℂ (LinearMap.ker (onesCov k)) :=
  OperatorChain.compression (colStoch_concrete hk)

/-- The rank-one Perron part `v ↦ ⟨χ₀, v⟩ χ₀`. -/
noncomputable def perronPart (k : ℕ) : Fsp k →ₗ[ℂ] Fsp k where
  toFun v := (@inner ℂ _ _ (chiVec k (0 : Fin (2 ^ (k - 1)))) v : ℂ)
    • chiVec k (0 : Fin (2 ^ (k - 1)))
  map_add' u v := by rw [inner_add_right, add_smul]
  map_smul' c v := by rw [inner_smul_right, RingHom.id_apply, mul_smul]

/-- The orthogonal projection onto `ker φ = χ₀^⊥`. -/
noncomputable def mzProj (k : ℕ) : Fsp k →ₗ[ℂ] Fsp k := LinearMap.id - perronPart k

@[simp] theorem mzProj_apply (k : ℕ) (v : Fsp k) :
    mzProj k v = v - (@inner ℂ _ _ (chiVec k (0 : Fin (2 ^ (k - 1)))) v : ℂ)
      • chiVec k (0 : Fin (2 ^ (k - 1))) := rfl

theorem mzProj_mem_ker {k : ℕ} (hk : 1 ≤ k) (v : Fsp k) :
    mzProj k v ∈ LinearMap.ker (onesCov k) := by
  rw [mem_ker_iff, mzProj_apply, inner_sub_right, inner_smul_right]
  have hon := chiVec_orthonormal hk
  rw [orthonormal_iff_ite.1 hon (0 : Fin (2 ^ (k - 1))) 0, if_pos rfl, mul_one, sub_self]

/-- The level projections do not see the Perron part. -/
theorem P_mzProj {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (v : Fsp k) :
    P k a (mzProj k v) = P k a v := by
  rw [mzProj_apply, map_sub, map_smul, P_chiVec_zero hk, smul_zero, sub_zero]

/-- **`U`, the Koopman partner**: the compression of `U_full = Tᵀ` to the mean-zero space.

`ker φ` is **not** `U_full`-invariant - that is exactly `THEOREM.md` I.1's boxed warning that
the row sums of `T_k` are not constant - so the projection `mzProj` is not decoration: it is
what makes `U` an endomorphism of `ker φ` at all. -/
noncomputable def Uop {k : ℕ} (hk : 1 ≤ k) : Module.End ℂ (LinearMap.ker (onesCov k)) where
  toFun z := ⟨mzProj k (Uendfull k (z : Fsp k)), mzProj_mem_ker hk _⟩
  map_add' u v := by
    refine Subtype.ext ?_
    show mzProj k (Uendfull k ((u : Fsp k) + (v : Fsp k))) = _
    rw [map_add, map_add]; rfl
  map_smul' c v := by
    refine Subtype.ext ?_
    show mzProj k (Uendfull k (c • (v : Fsp k))) = _
    rw [map_smul, map_smul]; rfl

@[simp] theorem Uop_coe {k : ℕ} (hk : 1 ≤ k) (z : LinearMap.ker (onesCov k)) :
    ((Uop hk z : LinearMap.ker (onesCov k)) : Fsp k)
      = mzProj k (Uendfull k (z : Fsp k)) := rfl

/-!
--------------------------------------------------------------------------------
## §6. The bridge to `Uendfull = Tᵀ` (the orientation step)
--------------------------------------------------------------------------------

L11's block bound is stated for `DefectSplit.Uendfull`, the transpose matrix acting on the
whole of `ℓ²`. The manifest's `hQblock` is stated for `U`, an operator on `ker φ`. These are
different objects; `P_Uop_eq` is the theorem that they agree after projecting to a level,
which is exactly what is needed and is the only thing that is true.
-/

theorem conj_TkC (k : ℕ) (u r : Fin (2 ^ (k - 1))) :
    (starRingEnd ℂ) (TkC k u r) = TkC k u r := by
  show (starRingEnd ℂ) ((Tcount k (od (u : ℕ)) (od (r : ℕ)) : ℂ) / 2 ^ k)
      = (Tcount k (od (u : ℕ)) (od (r : ℕ)) : ℂ) / 2 ^ k
  rw [show ((Tcount k (od (u : ℕ)) (od (r : ℕ)) : ℂ) / 2 ^ k)
      = (((Tcount k (od (u : ℕ)) (od (r : ℕ)) : ℝ) / 2 ^ k : ℝ) : ℂ) by push_cast; ring]
  exact Complex.conj_ofReal _

@[simp] theorem Uendfull_apply (k : ℕ) (y : Fsp k) (r : Fin (2 ^ (k - 1))) :
    (Uendfull k y) r = ∑ u, Ufull k r u * y u := rfl

/-- `Uendfull = Tᵀ` really is the adjoint of `Tend` on the ambient space. -/
theorem inner_Tend_Uendfull {k : ℕ} (x y : Fsp k) :
    (@inner ℂ _ _ (Tend k x) y : ℂ) = @inner ℂ _ _ x (Uendfull k y) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have hL : ∀ u : Fin (2 ^ (k - 1)),
      (inner ℂ ((Tend k x).ofLp u) (y.ofLp u) : ℂ)
        = ∑ r, y u * (TkC k u r * (starRingEnd ℂ) (x r)) := by
    intro u
    rw [RCLike.inner_apply]
    show y u * (starRingEnd ℂ) (∑ r, TkC k u r * x r) = _
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [map_mul, conj_TkC]
  have hR : ∀ r : Fin (2 ^ (k - 1)),
      (inner ℂ (x.ofLp r) ((Uendfull k y).ofLp r) : ℂ)
        = ∑ u, y u * (TkC k u r * (starRingEnd ℂ) (x r)) := by
    intro r
    rw [RCLike.inner_apply]
    show (∑ u, Ufull k r u * y u) * (starRingEnd ℂ) (x r) = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by rw [Ufull_apply]; ring
  rw [Fintype.sum_congr _ _ hL, Fintype.sum_congr _ _ hR]
  exact Finset.sum_comm

/-- **The orientation bridge.** For every level `a`, `P_a U = P_a Tᵀ` on `ker φ`. -/
theorem P_Uop_eq {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (z : LinearMap.ker (onesCov k)) :
    P k a (((Uop hk z : LinearMap.ker (onesCov k)) : Fsp k))
      = P k a (Uendfull k (z : Fsp k)) := by
  rw [Uop_coe, P_mzProj hk]

/-- **`hadj`, DISCHARGED.** `⟨T x, y⟩ = ⟨x, U y⟩` for mean-zero `x`, `y`. The Perron correction
inside `U` is invisible to `x ∈ ker φ`, which is precisely why the compression is the right
`U` - and the identity is `inner_Tend_Uendfull`, i.e. `U_full = Tᵀ`, so the orientation is a
theorem rather than a convention. -/
theorem hadj_concrete {k : ℕ} (hk : 1 ≤ k) (x y : LinearMap.ker (onesCov k)) :
    (@inner ℂ _ _ (Tend k (x : Fsp k)) (y : Fsp k) : ℂ)
      = @inner ℂ _ _ (x : Fsp k) (((Uop hk y : LinearMap.ker (onesCov k)) : Fsp k)) := by
  have hx : (@inner ℂ _ _ (chiVec k (0 : Fin (2 ^ (k - 1)))) (x : Fsp k) : ℂ) = 0 :=
    (mem_ker_iff _).1 x.2
  have hx' : (@inner ℂ _ _ (x : Fsp k) (chiVec k (0 : Fin (2 ^ (k - 1)))) : ℂ) = 0 := by
    rw [← inner_conj_symm, hx, map_zero]
  rw [Uop_coe, mzProj_apply, inner_sub_right, inner_smul_right, hx', mul_zero, sub_zero]
  exact inner_Tend_Uendfull (x : Fsp k) (y : Fsp k)

/-!
--------------------------------------------------------------------------------
## §7. `Q`, and the two block fields
--------------------------------------------------------------------------------
-/

/-- The level block of the full operator, as a linear map. -/
noncomputable def blockOp (k a b : ℕ) : Fsp k →ₗ[ℂ] Fsp k :=
  (P k a).comp ((Uendfull k).comp (P k b))

/-- The same, as a continuous linear map (finite dimensions), so that it has an operator norm. -/
noncomputable def blockCLM (k a b : ℕ) : Fsp k →L[ℂ] Fsp k :=
  LinearMap.toContinuousLinearMap (blockOp k a b)

@[simp] theorem blockCLM_apply (k a b : ℕ) (x : Fsp k) :
    blockCLM k a b x = P k a (Uendfull k (P k b x)) := rfl

/-- **`Q[a,b] := ‖P_a U P_b‖₂`**, `THEOREM.md`'s matrix of level-block operator norms. -/
noncomputable def Qmat (k : ℕ) : Matrix (Fin (k - 1)) (Fin (k - 1)) ℝ :=
  fun a b => ‖blockCLM k (a : ℕ) (b : ℕ)‖

theorem Qmat_nonneg (k : ℕ) (a b : Fin (k - 1)) : 0 ≤ Qmat k a b := norm_nonneg _

/-- The mean-zero part of the defect fibre covector. -/
noncomputable def mzc (k : ℕ) : Fsp k := mzProj k (cvecE k)

theorem mzc_mem_ker {k : ℕ} (hk : 1 ≤ k) : mzc k ∈ LinearMap.ker (onesCov k) :=
  mzProj_mem_ker hk _

/-- The level projections do not see the Perron component, so `P_b` of the mean-zero part is
`P_b` of the defect covector itself. This is the identification L11 flagged as unproven. -/
theorem P_mzc {k : ℕ} (hk : 1 ≤ k) (b : ℕ) : P k b (mzc k) = P k b (cvecE k) :=
  P_mzProj hk b _

/-- **`gc`, the level decomposition of the mean-zero defect fibre.** -/
noncomputable def gcVec {k : ℕ} (hk : 2 ≤ k) : PiLp 2 (Glev k) :=
  elev hk ⟨mzc k, mzc_mem_ker (one_le' hk)⟩

/-- **`levelVec gc b = ‖P_b c*‖`, proved rather than asserted.** -/
theorem levelVec_gcVec {k : ℕ} (hk : 2 ≤ k) {b : ℕ} (hb : b < k - 1) :
    Assembly.levelVec (gcVec hk) b = ‖P k b (cvecE k)‖ := by
  rw [Assembly.levelVec_of_lt _ hb, gcVec,
    norm_elev_component hk ⟨mzc k, mzc_mem_ker (one_le' hk)⟩ ⟨b, hb⟩]
  show ‖P k b (mzc k)‖ = ‖P k b (cvecE k)‖
  rw [P_mzc (one_le' hk) b]

theorem s_pow_norm_nonneg {k : ℕ} (a b : ℕ) :
    (0 : ℝ) ≤ Assembly.s ^ (a + 1) * ‖P k b (cvecE k)‖ :=
  mul_nonneg (pow_nonneg Assembly.s_pos.le _) (norm_nonneg _)

/-- **`hQlower`, DISCHARGED**, from L11's `norm_P_U_P_le`. -/
theorem Qmat_lower_le {k : ℕ} (hk : 2 ≤ k) (a b : Fin (k - 1)) (hab : (b : ℕ) ≤ (a : ℕ)) :
    Qmat k a b ≤ Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖ := by
  have ha : (a : ℕ) + 2 ≤ k := by have := a.isLt; omega
  refine ContinuousLinearMap.opNorm_le_bound _ (s_pow_norm_nonneg _ _) fun x => ?_
  calc ‖blockCLM k (a : ℕ) (b : ℕ) x‖
      ≤ Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖ * ‖P k (b : ℕ) x‖ :=
        norm_P_U_P_le hk hab ha x
    _ ≤ Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (norm_P_le (one_le' hk) (b : ℕ) x) (s_pow_norm_nonneg _ _)

/-- **`hQlower` is TIGHT**: for `b ≤ a` the block norm is *exactly* `s^{a+1}·‖P_b c*‖`.

The numerics say so to `1e-16` (see the header); this is the theorem. It matters twice: it
shows `Q`'s lower triangle is not a loose over-estimate, and it is the anti-degeneracy check
for `gc` - if `gc` were zero, `Q`'s whole lower triangle would be zero, so a degenerate `gc`
cannot hide behind a large `Q`. -/
theorem Qmat_lower_eq {k : ℕ} (hk : 2 ≤ k) (a b : Fin (k - 1)) (hab : (b : ℕ) ≤ (a : ℕ)) :
    Qmat k a b = Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖ := by
  have hk1 : 1 ≤ k := by omega
  have ha : (a : ℕ) + 2 ≤ k := by have := a.isLt; omega
  refine le_antisymm (Qmat_lower_le hk a b hab) ?_
  rcases eq_or_lt_of_le (norm_nonneg (P k (b : ℕ) (cvecE k))) with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  -- the witness `x := P_b c*` saturates the bound
  have hPv : P k (b : ℕ) (P k (b : ℕ) (cvecE k)) = P k (b : ℕ) (cvecE k) := P_idem hk1 _ _
  have hcoef : (@inner ℂ _ _ (cvecE k) (P k (b : ℕ) (P k (b : ℕ) (cvecE k))) : ℂ)
      = @inner ℂ _ _ (P k (b : ℕ) (cvecE k)) (P k (b : ℕ) (cvecE k)) :=
    (P_selfadjoint hk1 (b : ℕ) (cvecE k) (P k (b : ℕ) (cvecE k))).symm
  have hval : ‖blockCLM k (a : ℕ) (b : ℕ) (P k (b : ℕ) (cvecE k))‖
      = Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖ * ‖P k (b : ℕ) (cvecE k)‖ := by
    show ‖P k (a : ℕ) (Uendfull k (P k (b : ℕ) (P k (b : ℕ) (cvecE k))))‖ = _
    rw [P_U_P_eq_defect hk hab, norm_smul, norm_P_single ha, hcoef,
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp only [norm_pow, RCLike.norm_ofReal, abs_norm]
    ring
  have hle := (blockCLM k (a : ℕ) (b : ℕ)).le_opNorm (P k (b : ℕ) (cvecE k))
  rw [hval] at hle
  refine le_of_mul_le_mul_right ?_ hpos
  show (Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖) * ‖P k (b : ℕ) (cvecE k)‖
      ≤ ‖blockCLM k (a : ℕ) (b : ℕ)‖ * ‖P k (b : ℕ) (cvecE k)‖
  linarith

/-!
--------------------------------------------------------------------------------
## §8. `hDefectVec`
--------------------------------------------------------------------------------
-/

/-- The mean-zero part is no longer than the whole. -/
theorem norm_mzc_le {k : ℕ} (hk : 1 ≤ k) : ‖mzc k‖ ≤ ‖cvecE k‖ := by
  have hon := chiVec_orthonormal hk
  have hcoef : ∀ ξ : Fin (2 ^ (k - 1)), ξ ≠ 0 →
      (@inner ℂ _ _ (chiVec k ξ) (mzc k) : ℂ) = @inner ℂ _ _ (chiVec k ξ) (cvecE k) := by
    intro ξ hξ
    rw [mzc, mzProj_apply, inner_sub_right, inner_smul_right,
      orthonormal_iff_ite.1 hon ξ (0 : Fin (2 ^ (k - 1))), if_neg hξ, mul_zero, sub_zero]
  have hzero : (@inner ℂ _ _ (chiVec k (0 : Fin (2 ^ (k - 1)))) (mzc k) : ℂ) = 0 :=
    (mem_ker_iff _).1 (mzc_mem_ker hk)
  have hsq : ‖mzc k‖ ^ 2 ≤ ‖cvecE k‖ ^ 2 := by
    rw [← sum_sq_coeff hk (mzc k), ← sum_sq_coeff hk (cvecE k)]
    refine Finset.sum_le_sum fun ξ _ => ?_
    by_cases h : ξ = 0
    · subst h; rw [hzero]; simp
    · rw [hcoef ξ h]
  nlinarith [norm_nonneg (mzc k), norm_nonneg (cvecE k)]

/-- `‖c*‖` over the odd residues is at most `‖c‖` over all residues: the odd residues are a
subset, and every term is nonnegative. -/
theorem norm_cvecE_le {k : ℕ} (hk : 1 ≤ k) : ‖cvecE k‖ ≤ ‖Assembly.cvec k‖ := by
  have hterm : ∀ u : Fin (2 ^ (k - 1)),
      ‖(cvecE k) u‖ ^ 2 = ((cf k (od (u : ℕ)) : ℝ) / 2 ^ k) ^ 2 := by
    intro u
    show ‖(starRingEnd ℂ) (cstar k u)‖ ^ 2 = _
    rw [RCLike.norm_conj, cstar,
      show ((cf k (od (u : ℕ)) : ℂ) / 2 ^ k) = (((cf k (od (u : ℕ)) : ℝ) / 2 ^ k : ℝ) : ℂ) by
        push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hL : ‖cvecE k‖ ^ 2 = ∑ u : Fin (2 ^ (k - 1)), ((cf k (od (u : ℕ)) : ℝ) / 2 ^ k) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    exact Finset.sum_congr rfl fun u _ => hterm u
  have hR : ‖Assembly.cvec k‖ ^ 2 = ∑ t ∈ range (2 ^ k), ((cf k t : ℝ) / 2 ^ k) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity),
      ← Fin.sum_univ_eq_sum_range (fun t => ((cf k t : ℝ) / 2 ^ k) ^ 2) (2 ^ k)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Assembly.cvec_apply, Real.norm_eq_abs, sq_abs]
  have hsub : ∑ u : Fin (2 ^ (k - 1)), ((cf k (od (u : ℕ)) : ℝ) / 2 ^ k) ^ 2
      ≤ ∑ t ∈ range (2 ^ k), ((cf k t : ℝ) / 2 ^ k) ^ 2 := by
    have himg : ∑ u : Fin (2 ^ (k - 1)), ((cf k (od (u : ℕ)) : ℝ) / 2 ^ k) ^ 2
        = ∑ t ∈ (range (2 ^ (k - 1))).image od, ((cf k t : ℝ) / 2 ^ k) ^ 2 := by
      rw [Finset.sum_image (by intro x _ y _ h; exact od_injective h)]
      exact Fin.sum_univ_eq_sum_range (fun u => ((cf k (od u) : ℝ) / 2 ^ k) ^ 2) (2 ^ (k - 1))
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact Finset.mem_range.2 (od_lt hk (Finset.mem_range.1 hu))
  rw [← Real.sqrt_sq (norm_nonneg (cvecE k)), ← Real.sqrt_sq (norm_nonneg (Assembly.cvec k))]
  exact Real.sqrt_le_sqrt (by rw [hL, hR]; exact hsub)

/-- **`hDefectVec`, DISCHARGED.** -/
theorem hDefectVec_concrete {k : ℕ} (hk : 2 ≤ k) : ‖gcVec hk‖ ≤ ‖Assembly.cvec k‖ := by
  have h1 : ‖gcVec hk‖ = ‖mzc k‖ := by
    rw [gcVec, (elev hk).norm_map]
    rfl
  rw [h1]
  exact le_trans (norm_mzc_le (one_le' hk)) (norm_cvecE_le (one_le' hk))

/-!
--------------------------------------------------------------------------------
## §9. Non-degeneracy (failure mode 3)
--------------------------------------------------------------------------------

A manifest instantiation is worthless if it is taken at a degenerate `K`, `G` or `gc`: every
field would then hold trivially and `gap_certificate` would say nothing. The checks:

* **`K` is the real level count.** `K = k - 1` exactly, and `CharacterBasis.level_lt` proves
  every nonzero frequency has level `< k - 1`, so no level is being dropped and none invented.
* **No `G m` is the zero space.** `levelSet_nonempty` below: `|levelSet k m| = 2^{k-2-m} ≥ 1`
  for every `m : Fin (k-1)`. At `k = 6` the five cards are `16, 8, 4, 2, 1`.
* **`Q` is pinned, not free.** `Qmat_lower_eq` (§7) computes the whole lower triangle of `Q`
  *exactly*, as `s^{a+1}‖P_b c*‖`. A degenerate `gc` therefore forces a degenerate `Q`; they
  cannot be chosen independently to make the bundle vacuously true. Numerically at `k = 8` the
  lower triangle is nonzero throughout (max entry `2.949e-2`) and
  `levelVec gc = (0.0417, 0.0201, 0.0107, 0.0046, 0.0029, 0.00069, 0.00069)`.
* **`c*` itself is not zero**: its entries sum to `1` (`sum_cstar`), which is
  column-stochasticity read at the defect column.

Not proved here, and stated plainly: that `gc ≠ 0`. That is equivalent to `c*` not being the
uniform distribution on odd residues, which needs the *values* of `cf`, not its structure.
Numerically it is false-with-margin (`‖gc‖ = 0.0478` at `k = 8` against `‖c*‖ = 0.1005`), and
the whole point of `THEOREM.md`'s Part I.1 boxed warning is that `c*` is not uniform - but no
theorem in this development derives it, so it is recorded as open, not asserted.
-/

theorem levelSet_nonempty {k : ℕ} (hk : 2 ≤ k) (m : Fin (k - 1)) :
    (levelSet k (m : ℕ)).Nonempty := by
  have hm : (m : ℕ) + 2 ≤ k := by have := m.isLt; omega
  rw [← Finset.card_pos, levelSet_card hm]
  positivity

/-- The defect fibre is a probability vector on the odd residues: `∑_u c*_u = 1`. So `c*` is
not the zero vector, and `gc` is the level decomposition of something real. -/
theorem sum_cstar {k : ℕ} (hk : 1 ≤ k) : ∑ u : Fin (2 ^ (k - 1)), cstar k u = 1 := by
  rw [← TkC_col_sum hk (rstarIdx hk)]
  refine Finset.sum_congr rfl fun u _ => ?_
  show (cf k (od (u : ℕ)) : ℂ) / 2 ^ k
      = (Tcount k (od (u : ℕ)) (od ((rstarIdx hk : Fin (2 ^ (k - 1))) : ℕ)) : ℂ) / 2 ^ k
  rw [od_rstarIdx hk, defect_col_eq_cf hk (od (u : ℕ))]

theorem cvecE_ne_zero {k : ℕ} (hk : 1 ≤ k) : cvecE k ≠ 0 := by
  intro hc
  have h1 : ∑ u : Fin (2 ^ (k - 1)), cstar k u = 0 := by
    have hz : ∀ u : Fin (2 ^ (k - 1)), cstar k u = 0 := by
      intro u
      have h2 : (starRingEnd ℂ) (cstar k u) = 0 := by
        show (cvecE k) u = 0
        rw [hc]; rfl
      simpa using congrArg (starRingEnd ℂ) h2
    simp [hz]
  rw [sum_cstar hk] at h1
  exact one_ne_zero h1

/-!
--------------------------------------------------------------------------------
## §10. The manifest, instantiated
--------------------------------------------------------------------------------
-/

/-- **THE INSTANTIATION.** Every field of `Assembly.LemmaAFacts` for the concretely defined
Syracuse transfer operator `T_k`, with `hQupper` - and only `hQupper` - taken as a hypothesis.

Compare `Assembly.witness_facts`, whose `T` is `0`. Here `φ`, `T`, `e`, `U`, `Q` and `gc` are
all the real objects: `T = Tend k` is built from `TransferOperator.Tcount`, `Q` is a matrix of
genuine operator norms whose lower triangle `Qmat_lower_eq` computes exactly, and `K = k - 1`
is the true level count. -/
theorem facts_of_hQupper {k : ℕ} (hk : 3 ≤ k)
    (hup : ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      Qmat k a b ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ))
        + Assembly.s ^ ((a : ℕ) + 1) * Assembly.levelVec (gcVec (two_le hk)) (b : ℕ)) :
    Assembly.LemmaAFacts k (k - 1) (onesCov k) (Tend k) (elev (two_le hk))
      (Uop (one_le hk)) (Qmat k) (gcVec (two_le hk)) where
  hk := hk
  hK0 := by omega
  hKk := le_rfl
  colStoch := colStoch_concrete (one_le hk)
  hadj := hadj_concrete (one_le hk)
  hQ0 := Qmat_nonneg k
  hQblock := by
    intro m y m'
    have hk1 : 1 ≤ k := one_le hk
    have hk2 : 2 ≤ k := two_le hk
    set z : LinearMap.ker (onesCov k) :=
      (elev hk2).symm (LevelMajorisation.levelSingle m y) with hz
    have hez : elev hk2 z = LevelMajorisation.levelSingle m y := (elev hk2).apply_symm_apply _
    have hnorm : ‖(z : Fsp k)‖ = ‖y‖ := by
      show ‖z‖ = ‖y‖
      rw [hz, (elev hk2).symm.norm_map]
      refine sq_eq_of_nonneg (norm_nonneg _) (norm_nonneg _) ?_
      rw [← Assembly.sum_levelEnergy_sq (G := Glev k) (LevelMajorisation.levelSingle m y),
        Finset.sum_eq_single_of_mem m (Finset.mem_univ m)]
      · rw [LevelMajorisation.levelSingle_apply, Pi.single_eq_same]
      · intro b _ hb
        rw [LevelMajorisation.levelSingle_apply, Pi.single_eq_of_ne hb, norm_zero]
        ring
    -- every other level of `z` vanishes
    have hother : ∀ b : Fin (k - 1), b ≠ m → P k (b : ℕ) (z : Fsp k) = 0 := by
      intro b hb
      refine norm_eq_zero.1 ?_
      rw [← norm_elev_component hk2 z b, hez, LevelMajorisation.levelSingle_apply,
        Pi.single_eq_of_ne hb, norm_zero]
    -- so `P_m z = z`
    have hPz : P k (m : ℕ) (z : Fsp k) = (z : Fsp k) := by
      have hres := P_resolution hk2 (z : Fsp k)
      have hperron : (@inner ℂ _ _ (chiVec k (0 : Fin (2 ^ (k - 1)))) (z : Fsp k) : ℂ) = 0 :=
        (mem_ker_iff _).1 z.2
      rw [hperron, zero_smul, add_zero] at hres
      calc P k (m : ℕ) (z : Fsp k)
          = ∑ a : Fin (k - 1), P k (a : ℕ) (z : Fsp k) := by
            rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ m)]
            intro b _ hb
            exact hother b hb
        _ = ∑ a ∈ range (k - 1), P k a (z : Fsp k) :=
            Fin.sum_univ_eq_sum_range (fun a => P k a (z : Fsp k)) (k - 1)
        _ = (z : Fsp k) := hres
    have hkey : ‖(elev hk2 (Uop hk1 z)) m'‖ = ‖blockCLM k (m' : ℕ) (m : ℕ) (z : Fsp k)‖ := by
      rw [norm_elev_component hk2 (Uop hk1 z) m', P_Uop_eq hk1 (m' : ℕ) z]
      show _ = ‖P k (m' : ℕ) (Uendfull k (P k (m : ℕ) (z : Fsp k)))‖
      rw [hPz]
    calc ‖(elev hk2 (Uop hk1 ((elev hk2).symm (LevelMajorisation.levelSingle m y)))) m'‖
        = ‖blockCLM k (m' : ℕ) (m : ℕ) (z : Fsp k)‖ := by rw [← hz]; exact hkey
      _ ≤ Qmat k m' m * ‖(z : Fsp k)‖ := (blockCLM k (m' : ℕ) (m : ℕ)).le_opNorm _
      _ = Qmat k m' m * ‖y‖ := by rw [hnorm]
  hQupper := hup
  hQlower := by
    intro a b hab
    rw [levelVec_gcVec (two_le hk) b.isLt]
    exact Qmat_lower_le (two_le hk) a b hab
  hDefectVec := hDefectVec_concrete (two_le hk)

/-- **`THEOREM.md`'s boxed conclusion, for the concretely defined `T_k`.** Every eigenvalue of
the Syracuse transfer operator other than `1` has modulus at most `2^{-3/2} + 2^{-1}`,
uniformly in `k ≥ 3` - conditional on `hQupper` and on nothing else. -/
theorem gap_certificate_concrete {k : ℕ} (hk : 3 ≤ k)
    (hup : ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      Qmat k a b ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ))
        + Assembly.s ^ ((a : ℕ) + 1) * Assembly.levelVec (gcVec (two_le hk)) (b : ℕ))
    {μ : ℂ} (hμ : μ ≠ 1) {x : Fsp k} (hx0 : x ≠ 0) (hx : Tend k x = μ • x) :
    ‖μ‖ ≤ envelope Assembly.s 3 :=
  Assembly.gap_certificate (facts_of_hQupper hk hup) hμ hx0 hx

/-- The same with the numeral. -/
theorem gap_certificate_concrete_numeral {k : ℕ} (hk : 3 ≤ k)
    (hup : ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      Qmat k a b ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ))
        + Assembly.s ^ ((a : ℕ) + 1) * Assembly.levelVec (gcVec (two_le hk)) (b : ℕ))
    {μ : ℂ} (hμ : μ ≠ 1) {x : Fsp k} (hx0 : x ≠ 0) (hx : Tend k x = μ • x) :
    ‖μ‖ < 0.853554 :=
  Assembly.gap_certificate_numeral (facts_of_hQupper hk hup) hμ hx0 hx

/-!
--------------------------------------------------------------------------------
## §11. Satisfiability at a concrete `k`
--------------------------------------------------------------------------------
-/

/-- `k = 6`: the five level sets are all inhabited, so `G` is nowhere degenerate. -/
example : (levelSet 6 0).card = 16 ∧ (levelSet 6 1).card = 8 ∧ (levelSet 6 2).card = 4
    ∧ (levelSet 6 3).card = 2 ∧ (levelSet 6 4).card = 1 :=
  ⟨by rw [levelSet_card (by norm_num : (0 : ℕ) + 2 ≤ 6)]; norm_num,
   by rw [levelSet_card (by norm_num : (1 : ℕ) + 2 ≤ 6)]; norm_num,
   by rw [levelSet_card (by norm_num : (2 : ℕ) + 2 ≤ 6)]; norm_num,
   by rw [levelSet_card (by norm_num : (3 : ℕ) + 2 ≤ 6)]; norm_num,
   by rw [levelSet_card (by norm_num : (4 : ℕ) + 2 ≤ 6)]; norm_num⟩

/-- The lower triangle of `Q` at `k = 6`, exactly. -/
example : Qmat 6 ⟨3, by norm_num⟩ ⟨2, by norm_num⟩
    = Assembly.s ^ 4 * ‖P 6 2 (cvecE 6)‖ :=
  Qmat_lower_eq (by norm_num) ⟨3, by norm_num⟩ ⟨2, by norm_num⟩ (by norm_num)

/-!
--------------------------------------------------------------------------------
## §12. Axiom audit
--------------------------------------------------------------------------------
-/

#print axioms inner_chiVec_zero
#print axioms mem_ker_iff
#print axioms chiVec_mem_ker
#print axioms sum_erase_zero
#print axioms norm_sq_P
#print axioms sum_sq_coeff
#print axioms P_chiVec_zero
#print axioms norm_P_le
#print axioms sum_levels
#print axioms norm_sq_eFun_component
#print axioms norm_eFun_component
#print axioms eInv_mem_ker
#print axioms inner_eInv
#print axioms norm_eFun
#print axioms elev
#print axioms norm_elev_component
#print axioms Aop
#print axioms mzProj_mem_ker
#print axioms P_mzProj
#print axioms Uop
#print axioms hadj_concrete
#print axioms conj_TkC
#print axioms inner_Tend_Uendfull
#print axioms P_Uop_eq
#print axioms Qmat_nonneg
#print axioms mzc_mem_ker
#print axioms P_mzc
#print axioms levelVec_gcVec
#print axioms Qmat_lower_le
#print axioms Qmat_lower_eq
#print axioms norm_mzc_le
#print axioms norm_cvecE_le
#print axioms hDefectVec_concrete
#print axioms levelSet_nonempty
#print axioms sum_cstar
#print axioms cvecE_ne_zero
#print axioms facts_of_hQupper
#print axioms gap_certificate_concrete
#print axioms gap_certificate_concrete_numeral

end ManifestInstance
