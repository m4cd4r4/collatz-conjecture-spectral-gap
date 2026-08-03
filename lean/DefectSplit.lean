/-
# L11: the defect splitting `U = U_clean + D`, the level norms of a basis vector,
and the first bound on the FULL `U` below the diagonal.

--------------------------------------------------------------------------------
## §0. What this file does, and what it does not
--------------------------------------------------------------------------------

L10 (`OperatorBlock.lean`) proved `P_a U_clean P_b = 0` for `a ≥ b`, where `U_clean` is
`(T_k)ᵀ` **with the defect row deleted**. Its own stated next blocker:

> `U = U_clean + D` is not stated. Until that decomposition exists in Lean - with `D` the
> rank-one `e_{r*} ⊗ c*` - §6 cannot be connected to any statement about the full `U`.

This file states and proves that decomposition (§2), the level norms of a standard basis
vector (§3), and combines the two into the first inequality in this development that is
about the **full** `U` rather than its clean part (§4).

### §0.1 Orientation (the trap that has cost this project a defect)

Everything is target-first: `T[u,r]`, `U = Tᵀ`. `TransferOperator.defect_col_eq_cf` says the
defect is the `r*` **COLUMN** of `T`, hence the `r*` **ROW** of `U`, hence `U_clean` zeroes
the ROW `idx (rstar k)`. `D` therefore has exactly that one nonzero row, and is the rank-one
`e_{r*} ⊗ c*`.

The numerical guard on this choice is `0.125`, at every `k` measured (§0.2), so it does not
decay with `k` the way the earlier guard did - but the calibration was still run at `k = 4`
first, where a wrong index cannot be mistaken for float noise.

### §0.2 Numerical calibration (run BEFORE proving, from the target-first `Tcount`)

Independently in Python from `TransferOperator.Tcount`'s own definition, at `k = 4, 5, 6, 8`:

| check | k=4 | k=5 | k=6 | k=8 |
|---|---|---|---|---|
| `max │U − (U_clean + D)│` | `0.0` | `0.0` | `0.0` | `0.0` |
| `max │P_a U_clean P_b│`, `a ≥ b` | `2.9e-16` | `5.4e-16` | `2.9e-15` | `3.1e-14` |
| same, WRONG index (column zeroed) | `0.125` | `0.125` | `0.125` | `0.125` |
| `max │P_a U P_b│`, `a ≥ b` (FULL `U`) | `4.7e-2` | `2.3e-2` | `1.6e-2` | `4.9e-3` |
| `max_r │‖P_a e_r‖ − 2^{-(a+1)/2}│` | `3.3e-16` | `7.6e-15` | `5.2e-14` | `6.0e-13` |
| `‖c*‖` | `0.4050` | `0.2795` | `0.2013` | `0.1005` |

The splitting is EXACT (`0.0`, not `1e-16`) because it is a partition of the rows, not an
arithmetic identity.

The fourth row is the honest one: `P_a U P_b` is **not** zero for `a ≥ b`. The defect term is
genuinely there, and a bound is the only thing available - §4 gives one.

The fifth row was run over `r ∈ {0, 1, r*, N−1, 3}`, i.e. **including `r ≠ r*`**. It agrees at
every `r`, which is the check that `‖P_a e_r‖ = 2^{-(a+1)/2}` has nothing to do with `r*`:
every entry of the character matrix has modulus `1/√N`, so every character coefficient of ANY
standard basis vector has modulus `1/√N`, and

  `‖P_a e_r‖² = |levelSet k a| / N = 2^{k-2-a} / 2^{k-1} = 2^{-(a+1)}`.

So §3 is stated for all `r`, not for `r*`. The general form is both simpler to prove and
strictly stronger.

### §0.3 What is NOT discharged here

* **`Assembly.LemmaAFacts.hQlower` is NOT closed.** That field is a statement about an
  abstract `Q : Matrix (Fin K) (Fin K) ℝ` attached to an operator on `LinearMap.ker φ` through
  an isometry `e`. This file proves an inequality about the concrete `U` on the **whole**
  space `EuclideanSpace ℂ (Fin (2^(k-1)))`. No `Q` is constructed here, `ker φ` is not
  entered, and `e` does not appear. §4 has the *shape* of `hQlower` - the constant is
  literally `Assembly.s ^ (a+1)` and the second factor is `‖P_b c*‖` - but the shape of a
  bound is not the bound.
* **The mean-zero reduction is not done.** `hQlower`'s second factor is `levelVec gc b` with
  `gc` the level decomposition of the **mean-zero part** of the defect distribution. §4's
  factor is `‖P k b (cvecE k)‖`, the level-`b` part of the raw `c*`. `P k b` does annihilate
  the `ξ = 0` (Perron) direction for every `b` (`levelSet` excludes `0` by definition), so the
  raw and mean-zero versions cannot differ at any level `b` - but no such identification is
  stated or proved here, and `gc` never appears in this file.
* **What §4 does and does not amount to.** In the intended reading `Q[a,b]` is the norm of the
  `(a,b)` block, so §4 supplies exactly the inequality `Q[a,b] ≤ s^{a+1} · v_b` that `hQlower`
  asserts. What is missing is not the inequality: it is the *definition* of `Q`, the
  restriction to `ker φ`, and the isometry `e` that carries the level decomposition. Until
  those three exist in Lean, `hQlower` cannot even be stated for the concrete operator.
* **`Assembly.cvec k` is a different object** (`EuclideanSpace ℝ (Fin (2^k))`, real, indexed by
  all residues). `cvecE k` here is complex and indexed by `Fin (2^(k-1))`. The two are not
  identified in this file.

Sorry-free. Axioms audited in §7. Mutation table in §6.
-/

import OperatorBlock
import Assembly

namespace DefectSplit

open Finset GapCertificate LemmaA CountingLemmas CollisionBound TransferOperator
open CharacterBasis BlockVanishing OperatorBlock

/-!
--------------------------------------------------------------------------------
## §1. The three objects: the full `U`, the defect index, and the defect covector
--------------------------------------------------------------------------------
-/

/-- **The full operator matrix `U = Tᵀ`**, target-first (`§0.1`). -/
noncomputable def Ufull (k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℂ :=
  Matrix.transpose (TkC k)

theorem Ufull_apply (k : ℕ) (r u : Fin (2 ^ (k - 1))) : Ufull k r u = TkC k u r := rfl

/-- The row index of the defect: `idx (rstar k)`, the SAME index `Uclean` zeroes. -/
def rstarIdx {k : ℕ} (hk : 1 ≤ k) : Fin (2 ^ (k - 1)) :=
  ⟨idx (rstar k), idx_lt hk (rstar_lt hk)⟩

@[simp] theorem rstarIdx_val {k : ℕ} (hk : 1 ≤ k) : ((rstarIdx hk : Fin (2 ^ (k - 1))) : ℕ)
    = idx (rstar k) := rfl

theorem od_rstarIdx {k : ℕ} (hk : 1 ≤ k) : od ((rstarIdx hk : Fin (2 ^ (k - 1))) : ℕ)
    = rstar k := od_idx (rstar_odd hk)

/-- **The defect covector `c*`**: the `r*` column of `T_k`, normalised the same way `TkC` is.
`TransferOperator.defect_col_eq_cf` identifies its numerator with `CollisionBound.cf`. -/
noncomputable def cstar (k : ℕ) : Fin (2 ^ (k - 1)) → ℂ :=
  fun u => (cf k (od (u : ℕ)) : ℂ) / 2 ^ k

/-- The indicator of the defect row, `e_{r*}`, as a plain function. -/
noncomputable def estar (k : ℕ) : Fin (2 ^ (k - 1)) → ℂ :=
  fun r => if (r : ℕ) = idx (rstar k) then 1 else 0

/-- **`D`, the defect matrix, rank one BY CONSTRUCTION**: it is literally
`Matrix.vecMulVec (e_{r*}) (c*)`, i.e. the outer product `e_{r*} ⊗ c*`. -/
noncomputable def Dmat (k : ℕ) : Matrix (Fin (2 ^ (k - 1))) (Fin (2 ^ (k - 1))) ℂ :=
  Matrix.vecMulVec (estar k) (cstar k)

theorem Dmat_apply (k : ℕ) (r u : Fin (2 ^ (k - 1))) :
    Dmat k r u = estar k r * cstar k u := rfl

/-- Off the defect row `D` vanishes. -/
theorem Dmat_off (k : ℕ) {r : Fin (2 ^ (k - 1))} (hr : (r : ℕ) ≠ idx (rstar k))
    (u : Fin (2 ^ (k - 1))) : Dmat k r u = 0 := by
  rw [Dmat_apply, estar, if_neg hr, zero_mul]

/-- On the defect row `D` is `c*`. -/
theorem Dmat_on (k : ℕ) {r : Fin (2 ^ (k - 1))} (hr : (r : ℕ) = idx (rstar k))
    (u : Fin (2 ^ (k - 1))) : Dmat k r u = cstar k u := by
  rw [Dmat_apply, estar, if_pos hr, one_mul]

/-!
--------------------------------------------------------------------------------
## §2. **THE SPLITTING** `U = U_clean + D`
--------------------------------------------------------------------------------

L10 removed the defect row; this splits it off instead. The two matrices differ in exactly
one row by construction, so the only content is that `D`'s single row really is the `r*`
column of `T` - which is `defect_col_eq_cf`.
-/

/-- **`U = U_clean + D`.** The defect row of `U` is exactly `c*`; every other row agrees
with `U_clean`. -/
theorem U_split {k : ℕ} (hk : 1 ≤ k) : Uclean k + Dmat k = Ufull k := by
  ext r u
  rw [Matrix.add_apply, Ufull_apply]
  by_cases h : (r : ℕ) = idx (rstar k)
  · rw [Uclean_defect_row k h, Dmat_on k h, zero_add, cstar, TkC]
    have hod : od (r : ℕ) = rstar k := by rw [h]; exact od_idx (rstar_odd hk)
    rw [hod, defect_col_eq_cf hk (od (u : ℕ))]
  · rw [Uclean_clean_row k h, Dmat_off k h, add_zero]

/-- The same splitting, in the form `D = U − U_clean`. -/
theorem Dmat_eq_sub {k : ℕ} (hk : 1 ≤ k) : Dmat k = Ufull k - Uclean k := by
  rw [← U_split hk]; abel

/-- `U` as an endomorphism of `ℓ²`. -/
noncomputable def Uendfull (k : ℕ) : Module.End ℂ (EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :=
  Matrix.toEuclideanLin (Ufull k)

/-- `D` as an endomorphism of `ℓ²`. -/
noncomputable def Dend (k : ℕ) : Module.End ℂ (EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :=
  Matrix.toEuclideanLin (Dmat k)

/-- **The splitting, at the level of operators.** -/
theorem Uendfull_split {k : ℕ} (hk : 1 ≤ k) (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    Uendfull k x = Uend k x + Dend k x := by
  rw [Uendfull, Uend, Dend, ← U_split hk, map_add]
  rfl

/-!
--------------------------------------------------------------------------------
## §3. **R3**: `‖P_a e_r‖ = 2^{-(a+1)/2}`, for EVERY `r`
--------------------------------------------------------------------------------

Two ingredients: the level counts (`levelSet_card`), and the fact that every character
coefficient of a standard basis vector has modulus `1/√N` (`norm_inner_chiVec_single`).
Neither mentions `r*`.
-/

/-- Membership in `levelSet` as a single decidable congruence. `v2_eq_iff_mod` needs `n ≠ 0`;
the congruence supplies it, since `2^a ≠ 0`. -/
theorem mem_levelSet_mod {k a : ℕ} {ξ : Fin (2 ^ (k - 1))} :
    ξ ∈ levelSet k a ↔ (ξ : ℕ) % 2 ^ (a + 1) = 2 ^ a := by
  rw [mem_levelSet]
  constructor
  · rintro ⟨h0, hv⟩; exact (v2_eq_iff_mod h0).1 hv
  · intro h
    have h0 : (ξ : ℕ) ≠ 0 := by
      intro hc
      rw [hc, Nat.zero_mod] at h
      have hA : 0 < 2 ^ a := by positivity
      omega
    exact ⟨h0, (v2_eq_iff_mod h0).2 h⟩

/-- The parametrisation of level `a` by `Fin (2^{k-2-a})`: `t ↦ 2^{a+1} t + 2^a`, i.e.
`ξ = 2^a · odd`. -/
def levelParam {k a : ℕ} (hk : a + 2 ≤ k) (t : Fin (2 ^ (k - 2 - a))) : Fin (2 ^ (k - 1)) :=
  ⟨2 ^ (a + 1) * (t : ℕ) + 2 ^ a, by
    have hA : 0 < 2 ^ a := by positivity
    have hpow1 : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
    have hpow2 : (2 : ℕ) ^ (k - 1) = 2 ^ (a + 1) * 2 ^ (k - 2 - a) := by
      rw [← pow_add]; congr 1; omega
    have ht : (t : ℕ) + 1 ≤ 2 ^ (k - 2 - a) := t.isLt
    calc 2 ^ (a + 1) * (t : ℕ) + 2 ^ a
        < 2 ^ (a + 1) * (t : ℕ) + 2 ^ (a + 1) := by omega
      _ = 2 ^ (a + 1) * ((t : ℕ) + 1) := by ring
      _ ≤ 2 ^ (a + 1) * 2 ^ (k - 2 - a) := Nat.mul_le_mul_left _ ht
      _ = 2 ^ (k - 1) := hpow2.symm⟩

@[simp] theorem levelParam_val {k a : ℕ} (hk : a + 2 ≤ k) (t : Fin (2 ^ (k - 2 - a))) :
    ((levelParam hk t : Fin (2 ^ (k - 1))) : ℕ) = 2 ^ (a + 1) * (t : ℕ) + 2 ^ a := rfl

/-- **The level counts.** `|levelSet k a| = 2^{k-2-a}` for `a ≤ k-2`. The `#guard`s in
`CharacterBasis` §5 measured exactly this at `k = 6, 8`; here it is a theorem.

The bijection is `t ↦ 2^{a+1} t + 2^a`, i.e. `ξ = 2^a · (odd)`. -/
theorem levelSet_card {k a : ℕ} (hk : a + 2 ≤ k) :
    (levelSet k a).card = 2 ^ (k - 2 - a) := by
  have hA : 0 < 2 ^ a := by positivity
  have hpow1 : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
  have hpow2 : (2 : ℕ) ^ (k - 1) = 2 ^ (a + 1) * 2 ^ (k - 2 - a) := by
    rw [← pow_add]; congr 1; omega
  have hinj : Function.Injective (levelParam hk) := by
    intro s t h
    have h1 : 2 ^ (a + 1) * (s : ℕ) + 2 ^ a = 2 ^ (a + 1) * (t : ℕ) + 2 ^ a :=
      congrArg Fin.val h
    have h2 : 2 ^ (a + 1) * (s : ℕ) = 2 ^ (a + 1) * (t : ℕ) := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left (by positivity) h2)
  have himg : levelSet k a = Finset.image (levelParam hk) univ := by
    ext ξ
    rw [mem_levelSet_mod, mem_image]
    constructor
    · intro h
      have hb : (ξ : ℕ) < 2 ^ (a + 1) * 2 ^ (k - 2 - a) := hpow2 ▸ ξ.isLt
      refine ⟨⟨(ξ : ℕ) / 2 ^ (a + 1), Nat.div_lt_of_lt_mul hb⟩, mem_univ _, ?_⟩
      apply Fin.ext
      rw [levelParam_val]
      have hd := Nat.div_add_mod (ξ : ℕ) (2 ^ (a + 1))
      rw [h] at hd
      exact hd
    · rintro ⟨t, _, rfl⟩
      rw [levelParam_val, Nat.add_comm, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- `|chi| = 1`: the characters are roots of unity. -/
theorem norm_chi (k ξ s : ℕ) : ‖chi k ξ s‖ = 1 := by
  rw [chi, norm_pow, norm_w, one_pow]

/-- **Every character coefficient of ANY standard basis vector has modulus `1/√N`.**
This is the whole content of R3, and `r` is arbitrary. -/
theorem norm_inner_chiVec_single (k : ℕ) (ξ r : Fin (2 ^ (k - 1))) :
    ‖(@inner ℂ _ _ (chiVec k ξ) (EuclideanSpace.single r (1 : ℂ)) : ℂ)‖ = (rt k)⁻¹ := by
  rw [EuclideanSpace.inner_single_right, chiVec_apply, one_mul, RCLike.norm_conj,
    norm_div, norm_chi, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (rt_pos k), one_div]

/-- **R3, squared.** `‖P_a e_r‖² = |levelSet k a| / N`. Still no arithmetic on the level
counts - just orthonormality. -/
theorem norm_sq_P_single {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (r : Fin (2 ^ (k - 1))) :
    ‖P k a (EuclideanSpace.single r (1 : ℂ))‖ ^ 2
      = ((levelSet k a).card : ℝ) / ((2 ^ (k - 1) : ℕ) : ℝ) := by
  have hon := chiVec_orthonormal hk
  set x : EuclideanSpace ℂ (Fin (2 ^ (k - 1))) := EuclideanSpace.single r (1 : ℂ) with hx
  set c : Fin (2 ^ (k - 1)) → ℂ := fun ξ => (@inner ℂ _ _ (chiVec k ξ) x : ℂ) with hc
  have hnc : ∀ ξ : Fin (2 ^ (k - 1)), ‖c ξ‖ = (rt k)⁻¹ := by
    intro ξ; rw [hc]; exact norm_inner_chiVec_single k ξ r
  have hinner : (@inner ℂ _ _ (P k a x) (P k a x) : ℂ)
      = ((((levelSet k a).card : ℝ) * ((rt k)⁻¹ ^ 2) : ℝ) : ℂ) := by
    rw [P_apply k a x, hon.inner_sum c c (levelSet k a)]
    have hterm : ∀ ξ ∈ levelSet k a, (starRingEnd ℂ) (c ξ) * c ξ
        = ((((rt k)⁻¹ ^ 2 : ℝ)) : ℂ) := by
      intro ξ _
      rw [RCLike.conj_mul, hnc ξ]
      norm_cast
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  have hre : ‖P k a x‖ ^ 2 = ((levelSet k a).card : ℝ) * ((rt k)⁻¹ ^ 2) := by
    have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := P k a x)
    rw [hinner] at h1
    have h2 : ((‖P k a x‖ ^ 2 : ℝ) : ℂ)
        = ((((levelSet k a).card : ℝ) * ((rt k)⁻¹ ^ 2) : ℝ) : ℂ) := by
      push_cast
      push_cast at h1
      exact h1.symm
    exact Complex.ofReal_inj.mp h2
  rw [hre, rt, inv_pow, Real.sq_sqrt (by positivity), div_eq_mul_inv]

/-- **R3.** `‖P_a e_r‖ = s^{a+1} = 2^{-(a+1)/2}`, for EVERY `r` - `r*` plays no role.

The constant is written as `Assembly.s ^ (a+1)` because that is literally the constant
`Assembly.LemmaAFacts.hQlower` carries; `Assembly.s = √(1/2)`. -/
theorem sq_eq_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 = y ^ 2) : x = y := by
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ = Real.sqrt (y ^ 2) := by rw [h]
    _ = y := Real.sqrt_sq hy

/-- `s^{a+1}` squared is `(1/2)^{a+1}`. -/
theorem s_pow_sq (a : ℕ) : (Assembly.s ^ (a + 1)) ^ 2 = (1 / 2 : ℝ) ^ (a + 1) := by
  rw [← pow_mul, mul_comm (a + 1) 2, pow_mul, Assembly.s,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1 / 2)]

theorem norm_P_single {k a : ℕ} (hk : a + 2 ≤ k) (r : Fin (2 ^ (k - 1))) :
    ‖P k a (EuclideanSpace.single r (1 : ℂ))‖ = Assembly.s ^ (a + 1) := by
  have hk1 : 1 ≤ k := by omega
  refine sq_eq_of_nonneg (norm_nonneg _) (pow_nonneg Assembly.s_pos.le _) ?_
  rw [s_pow_sq, norm_sq_P_single hk1 a r, levelSet_card hk]
  have h1 : ((2 ^ (k - 2 - a) : ℕ) : ℝ) = (2 : ℝ) ^ (k - 2 - a) := by push_cast; ring
  have h2 : ((2 ^ (k - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (a + 1) * (2 : ℝ) ^ (k - 2 - a) := by
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [h1, h2, div_pow, one_pow]
  have hne : ((2 : ℝ) ^ (k - 2 - a)) ≠ 0 := by positivity
  have hne2 : ((2 : ℝ) ^ (a + 1)) ≠ 0 := by positivity
  field_simp

/-- R3 in explicit `2^{-(a+1)/2}` form (rpow), for readers matching THEOREM.md. -/
theorem s_pow_eq_rpow (a : ℕ) :
    Assembly.s ^ (a + 1) = (2 : ℝ) ^ (-((a : ℝ) + 1) / 2) := by
  have hR : (0:ℝ) ≤ (2 : ℝ) ^ (-((a : ℝ) + 1) / 2) := Real.rpow_nonneg (by norm_num) _
  refine sq_eq_of_nonneg (pow_nonneg Assembly.s_pos.le _) hR ?_
  rw [s_pow_sq, ← Real.rpow_natCast ((2 : ℝ) ^ (-((a : ℝ) + 1) / 2)) 2,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    show (-((a : ℝ) + 1) / 2 * ((2 : ℕ) : ℝ)) = -(((a + 1 : ℕ) : ℝ)) by push_cast; ring,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, div_pow, one_pow, one_div]

theorem norm_P_single_rpow {k a : ℕ} (hk : a + 2 ≤ k) (r : Fin (2 ^ (k - 1))) :
    ‖P k a (EuclideanSpace.single r (1 : ℂ))‖ = (2 : ℝ) ^ (-((a : ℝ) + 1) / 2) := by
  rw [norm_P_single hk r, s_pow_eq_rpow]

/-!
--------------------------------------------------------------------------------
## §4. The first bound on the FULL `U` below the diagonal
--------------------------------------------------------------------------------

`P_a U P_b = P_a U_clean P_b + P_a D P_b = 0 + P_a D P_b` by L10, and `D` is rank one, so
`P_a D P_b x` is a scalar multiple of `P_a e_{r*}`, whose norm §3 computes exactly.
-/

/-- The defect covector as an element of `ℓ²`, conjugated so that pairing against it is the
inner product. -/
noncomputable def cvecE (k : ℕ) : EuclideanSpace ℂ (Fin (2 ^ (k - 1))) :=
  WithLp.toLp 2 (fun u => (starRingEnd ℂ) (cstar k u))

theorem inner_cvecE (k : ℕ) (y : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    (@inner ℂ _ _ (cvecE k) y : ℂ) = ∑ u, cstar k u * y u := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [RCLike.inner_apply, cvecE]
  simp [mul_comm]

/-- **`D` acts as a rank-one operator**: `D y = ⟪c*, y⟫ · e_{r*}`. -/
theorem Dend_apply_eq {k : ℕ} (hk : 1 ≤ k) (y : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    Dend k y = (@inner ℂ _ _ (cvecE k) y : ℂ) • EuclideanSpace.single (rstarIdx hk) (1 : ℂ) := by
  ext r
  have hlhs : (Dend k y) r = ∑ u, Dmat k r u * y u := rfl
  rw [hlhs, inner_cvecE]
  by_cases h : (r : ℕ) = idx (rstar k)
  · have hr : r = rstarIdx hk := Fin.ext h
    rw [Finset.sum_congr rfl (fun u _ => by rw [Dmat_on k h])]
    subst hr
    simp
  · have hr : r ≠ rstarIdx hk := fun hc => h (by rw [hc]; rfl)
    rw [Finset.sum_congr rfl (fun u _ => by rw [Dmat_off k h, zero_mul]),
      Finset.sum_const_zero]
    simp [EuclideanSpace.single_apply, hr]

/-- **`P_a U P_b` is the defect term alone**, for `a ≥ b`. This is the first statement in the
development about the FULL `U`. -/
theorem P_U_P_eq_defect {k a b : ℕ} (hk : 2 ≤ k) (hab : b ≤ a)
    (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    P k a (Uendfull k (P k b x))
      = (@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)
          • P k a (EuclideanSpace.single (rstarIdx (by omega : 1 ≤ k)) (1 : ℂ)) := by
  have hk1 : 1 ≤ k := by omega
  rw [Uendfull_split hk1, map_add, P_Uclean_P_eq_zero hk hab, zero_add,
    Dend_apply_eq hk1, map_smul]

/-- **THE BOUND.** For `a ≥ b`,

  `‖P_a U P_b x‖ ≤ s^{a+1} · ‖P_b c*‖ · ‖P_b x‖`,  `s = 2^{-1/2}`.

This has the shape of `Assembly.LemmaAFacts.hQlower` - the constant is literally
`Assembly.s ^ (a+1)` and the second factor is the level-`b` part of the defect covector - but
see §0.3: no `Q` is constructed and `ker φ` is not entered, so `hQlower` is NOT closed. -/
theorem norm_P_U_P_le {k a b : ℕ} (hk : 2 ≤ k) (hab : b ≤ a) (ha : a + 2 ≤ k)
    (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    ‖P k a (Uendfull k (P k b x))‖
      ≤ Assembly.s ^ (a + 1) * ‖P k b (cvecE k)‖ * ‖P k b x‖ := by
  have hk1 : 1 ≤ k := by omega
  -- the coefficient only sees the level-`b` part of `c*`
  have hcoef : (@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)
      = @inner ℂ _ _ (P k b (cvecE k)) (P k b x) := by
    rw [P_selfadjoint hk1 b, P_idem hk1]
  have hCS : ‖(@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)‖
      ≤ ‖P k b (cvecE k)‖ * ‖P k b x‖ := by
    rw [hcoef]; exact norm_inner_le_norm _ _
  rw [P_U_P_eq_defect hk hab, norm_smul, norm_P_single ha]
  calc ‖(@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)‖ * Assembly.s ^ (a + 1)
      ≤ (‖P k b (cvecE k)‖ * ‖P k b x‖) * Assembly.s ^ (a + 1) :=
        mul_le_mul_of_nonneg_right hCS (pow_nonneg (Real.sqrt_nonneg _) _)
    _ = Assembly.s ^ (a + 1) * ‖P k b (cvecE k)‖ * ‖P k b x‖ := by ring

/-- The cruder bound, with the full `‖c*‖` in place of its level-`b` part. -/
theorem norm_P_U_P_le' {k a b : ℕ} (hk : 2 ≤ k) (hab : b ≤ a) (ha : a + 2 ≤ k)
    (x : EuclideanSpace ℂ (Fin (2 ^ (k - 1)))) :
    ‖P k a (Uendfull k (P k b x))‖
      ≤ Assembly.s ^ (a + 1) * ‖cvecE k‖ * ‖P k b x‖ := by
  have hk1 : 1 ≤ k := by omega
  have hCS : ‖(@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)‖ ≤ ‖cvecE k‖ * ‖P k b x‖ :=
    norm_inner_le_norm _ _
  rw [P_U_P_eq_defect hk hab, norm_smul, norm_P_single ha]
  calc ‖(@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)‖ * Assembly.s ^ (a + 1)
      ≤ (‖cvecE k‖ * ‖P k b x‖) * Assembly.s ^ (a + 1) :=
        mul_le_mul_of_nonneg_right hCS (pow_nonneg (Real.sqrt_nonneg _) _)
    _ = Assembly.s ^ (a + 1) * ‖cvecE k‖ * ‖P k b x‖ := by ring

/-!
--------------------------------------------------------------------------------
## §5. Satisfiability and calibration (failure mode 3: vacuity)
--------------------------------------------------------------------------------

Every hypothesis block above is exhibited at a concrete point, and every index set that could
silently be empty is shown inhabited.
-/

/-- `k = 6, a = 3, b = 2` satisfies every hypothesis of §4 simultaneously. -/
theorem hyp_satisfiable_split : 2 ≤ 6 ∧ 2 ≤ 3 ∧ 3 + 2 ≤ 6 := by norm_num

/-- The `a = 3` level set at `k = 6` is INHABITED (`ξ = 8`, `v₂ = 3`), so §3 and §4 are not
vacuous at that point. -/
example : (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 3 :=
  mem_levelSet_mod.2 (by norm_num)

/-- The level count at `k = 6, a = 3` is `2` - matching `CharacterBasis`'s `#guard`. -/
example : (levelSet 6 3).card = 2 := by
  rw [levelSet_card (by norm_num)]; norm_num

/-- ... and at `k = 8, a = 0` it is `64`, again matching the `#guard`. -/
example : (levelSet 8 0).card = 64 := by
  rw [levelSet_card (by norm_num)]; norm_num

/-- The defect index at `k = 6` is `10` (`rstar 6 = 21`), the same index `OperatorBlock`
zeroes - so `Dmat` and `Uclean` really do complement each other at a concrete `k`. -/
example : ((rstarIdx (by norm_num : 1 ≤ 6) : Fin (2 ^ (6 - 1))) : ℕ) = 10 :=
  defect_index_six

/-- §4 instantiated at `k = 6, a = 3, b = 2`. -/
example (x : EuclideanSpace ℂ (Fin (2 ^ (6 - 1)))) :
    ‖P 6 3 (Uendfull 6 (P 6 2 x))‖
      ≤ Assembly.s ^ 4 * ‖P 6 2 (cvecE 6)‖ * ‖P 6 2 x‖ :=
  norm_P_U_P_le (by norm_num) (by norm_num) (by norm_num) x

/-- The splitting at a concrete `k`. -/
example : Uclean 6 + Dmat 6 = Ufull 6 := U_split (by norm_num)

/-!
--------------------------------------------------------------------------------
## §6. Mutation tests (failure mode 1: a theorem a tactic closes on its own)
--------------------------------------------------------------------------------

Ten single-token mutations were applied to the load-bearing statements and the build was run
on each. **All ten failed to compile.** The build was restored and re-run green afterwards.

| # | mutation | result |
|---|---|---|
| M1 | `Ufull`: `(TkC k)ᵀ` → `TkC k` (drop the transpose) | fails |
| M2 | `cstar`: `cf k (od u)` → `cf k u` (drop the odd re-indexing) | fails |
| M3 | `estar`: `idx (rstar k)` → `idx (rstar k) + 1` (the wrong defect row) | fails |
| M4 | `U_split`: `Uclean k + Dmat k` → `Uclean k - Dmat k` | fails |
| M5 | `levelSet_card`: `2 ^ (k - 2 - a)` → `2 ^ (k - 1 - a)` (off by one) | fails |
| M6 | `norm_inner_chiVec_single`: `(rt k)⁻¹` → `rt k` (invert the normalisation) | fails |
| M7 | `norm_sq_P_single`: `card / N` → `card / N^2` | fails |
| M8 | `norm_P_single`: `Assembly.s ^ (a+1)` → `Assembly.s ^ a` (the exponent) | fails |
| M9 | `norm_P_U_P_le`: `hab : b ≤ a` → `a ≤ b` (the orientation) | fails |
| M10 | `Dend_apply_eq`: `single (rstarIdx hk)` → `single 0` (the rank-one direction) | fails |

M1, M3, M9 are three independent shots at the orientation trap. M5 is the one place where a
`decide`-style tactic could plausibly have closed a false statement, since the level counts
are small; it does not.

--------------------------------------------------------------------------------
## §7. Axiom audit
--------------------------------------------------------------------------------

Every exported declaration must use a SUBSET of `{propext, Classical.choice, Quot.sound}`.
Several use strictly fewer; that is expected and is not a violation.
-/

#print axioms Ufull_apply
#print axioms od_rstarIdx
#print axioms Dmat_apply
#print axioms Dmat_off
#print axioms Dmat_on
#print axioms U_split
#print axioms Dmat_eq_sub
#print axioms Uendfull_split
#print axioms mem_levelSet_mod
#print axioms levelSet_card
#print axioms norm_chi
#print axioms norm_inner_chiVec_single
#print axioms norm_sq_P_single
#print axioms norm_P_single
#print axioms sq_eq_of_nonneg
#print axioms s_pow_sq
#print axioms s_pow_eq_rpow
#print axioms norm_P_single_rpow
#print axioms levelParam_val
#print axioms inner_cvecE
#print axioms Dend_apply_eq
#print axioms P_U_P_eq_defect
#print axioms norm_P_U_P_le
#print axioms norm_P_U_P_le'
#print axioms hyp_satisfiable_split

end DefectSplit
