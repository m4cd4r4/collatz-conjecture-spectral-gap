/-
# Operator chain: the Perron split and the Gelfand-shaped eigenvalue bound

Lean 4 formalisation of the abstract operator-theoretic skeleton of **Part I.1-I.2** of
`THEOREM.md` (the uniform spectral gap, consolidated, 2026-07-05) in the public
`collatz-cycle-certificate` repo. `GapCertificate.lean` formalises the elementary 2-adic
core and explicitly records this chain as *not* formalised; this file closes the I.1-I.2
half of that gap in abstract form.

Nothing here mentions the Syracuse map, `3x+1`, or any specific operator: every statement
is about an arbitrary linear map on an arbitrary space. That is deliberate - see the two
scope notes below.

## Scope note 1 (model scope, standing gate)

Everything proved here is **sign-agnostic**: it holds verbatim for the `3x-1` transfer
operator, which passes the identical certificate yet has genuine cycles
(`CYCLE_CLAIM_REFUTED.md`). Consequently **this file proves nothing about Collatz cycles.**
It is operator-model theory only: a column-stochastic linear map has a one-dimensional
Perron direction and its remaining spectrum is that of the compression to the mean-zero
subspace.

## Scope note 2 (the referee find that this file must not re-introduce)

`THEOREM.md` Part I opens with:

> **Warning fixed here (referee find, 2026-07-05).** Earlier write-ups asserted `T_k` is doubly
> stochastic with uniform stationary distribution, and used `T_r^p = T_k^p - (1/N)J`. Both are
> FALSE: columns of `T` sum to 1 exactly, but row sums deviate (`||T1 - 1||_2 ~ 0.76 * 2^{-k/2}`,
> another face of the `r*` defect), so the stationary distribution is only approximately uniform
> and `TJ != J`.

Accordingly **no theorem in this file assumes double stochasticity, `T J = J`, a uniform
stationary distribution, normality, self-adjointness, or diagonalisability.** The only
hypothesis on `T` is the one-sided `φ ∘ T = φ` (i.e. `1ᵀ T = 1ᵀ`, column-stochasticity), and
the block-triangular form carries a *nonzero* off-diagonal block `d` throughout - see
`charpoly_perron_block`, whose `d` is an arbitrary matrix and is never assumed `0`.

## Statement-fidelity table

| Lean name | `THEOREM.md` sentence formalised |
|---|---|
| `meanZero_invariant` | I.1: "the mean-zero space `V = ker(1^T) = 1^perp` is `T`-invariant (`1^T (Tf) = 1^T f = 0`)" |
| `mem_meanZero_of_eigenvector` | I.1, the eigenvector form of the same split: an eigenvector for `μ ≠ 1` lies in `V` |
| `hasEigenvalue_compression_of_ne_one` | I.1: "`spec(T) = {1} u spec(A)`", set-level direction `spec(T) ⊆ {1} ∪ spec(A)` |
| `hasEigenvalue_compression_one_of_two_le_finrank` | I.1: the multiplicity content of "as multisets" at `μ = 1`, in the **geometric**-multiplicity reading |
| `spectrum_subset_insert_one` | I.1: `spec(T) ⊆ {1} ∪ spec(A)` stated on `spectrum` |
| `charpoly_perron_block`, `roots_charpoly_perron_block` | I.1: "In a basis adapted to `C^N = span(1) (+) V`, `T` is block-triangular, `T = [[1, 0], [d, A]]` ... The characteristic polynomial factors, so `spec(T) = {1} u spec(A)` as multisets" (**conditional on the adapted basis**, see the gap note) |
| `norm_eigenvalue_pow_le_of_pow_bound` | I.2: "`rho(U_V) <= || U_V^p ||_2^{1/p}`, valid for any matrix - no normality or diagonalisability input" |
| `norm_eigenvalue_pow_le_opNorm_pow`, `norm_eigenvalue_le_rpow` | I.2, same sentence, in the `‖μ‖ ≤ ‖A^p‖^(1/p)` shape |
| `norm_eigenvalue_le_of_compression_pow_bound` | I.1 + I.2 composed: the interface I.3 actually consumes |

## What is proved outright vs what is conditional (honest labelling)

* **PROVEN outright**, no extra hypotheses: `meanZero_invariant`, `mem_meanZero_of_eigenvector`,
  `hasEigenvalue_compression_of_ne_one`, `hasEigenvalue_compression_one_of_two_le_finrank`,
  `spectrum_subset_insert_one`, all of §3 (the Gelfand substitute), and the §4 chain.
* **PROVEN, conditional on an adapted basis**: `charpoly_perron_block` /
  `roots_charpoly_perron_block` prove the multiset factorisation *for a matrix already presented
  in the block form* `[[1,0],[d,A]]`. The existence of a basis putting `T` in that form is
  classical but is **not** proved here.
* **Gelfand**: Mathlib does have the genuine Gelfand formula for complex Banach algebras
  (`spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius`,
  `Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`). This file does **not** use it: §3
  proves the elementary eigenvector-growth substitute outright, which is all that Part I.3
  consumes and which needs neither completeness nor a normed-algebra structure on the
  operators. Label: **PROVEN**, not CITED.

## Missing Mathlib API (recorded per the task's kill criteria)

Mathlib has `Matrix.charpoly_fromBlocks_zero₁₂` (block-triangular charpoly factorisation) and
`Module.End.mem_spectrum_iff_isRoot_charpoly`, but it has **no** lemma of the shape
"`charpoly f = charpoly (f.restrict h) * charpoly (f mod p)`" for an invariant submodule `p` -
i.e. no charpoly multiplicativity along a short exact sequence of modules. Closest neighbours:
`Matrix.charpoly_fromBlocks_zero₁₂` (needs the adapted basis supplied by hand),
`Algebra.DirectSum.LinearMap.toMatrix_directSum` (only for `f`-invariant *internal direct
sums*, i.e. when the complement is also invariant - which is exactly what fails here, since
`d ≠ 0`). Supplying the adapted basis and reindexing `Fin 1 ⊕ ι` is the remaining work for
the unconditional multiset form; the set-level and geometric-multiplicity forms below are
proved without it.

## Dimension uniformity (absurd-height sanity, standing gate)

Every statement below is uniform in the dimension: no constant, bound, or hypothesis depends
on `finrank K E` or on the index type's cardinality. Instantiating at the Collatz-relevant
scale `N = 2^(k-1) ≈ 10^9` changes nothing in any statement - `p` and the bound `C` in §3 are
the only parameters, and neither is dimension-indexed.
-/

import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OperatorChain

open Module Module.End Submodule

/-!
## Section 1: the Perron split (THEOREM.md I.1)

`THEOREM.md` I.1 verbatim:

> **I.1 (Perron split).** `T := T_k` is column-stochastic: `1^T T = 1^T`, hence `rho(T) = 1` and
> the mean-zero space `V = ker(1^T) = 1^perp` is `T`-invariant (`1^T (Tf) = 1^T f = 0`). In a basis
> adapted to `C^N = span(1) (+) V`, `T` is block-triangular, `T = [[1, 0], [d, A]]` with
> `A = T|_V` (the off-diagonal `d` is the `V`-component of `T1`, nonzero here). The characteristic
> polynomial factors, so `spec(T) = {1} u spec(A)` as multisets, and `|lambda_2(T)| <= rho(A)`.

Here `φ` plays the role of `1^T` (an arbitrary linear functional - we never need it to be the
all-ones covector, nor `T` to be entrywise nonnegative), and `φ ∘ₗ T = φ` is exactly
`1^T T = 1^T`. No double stochasticity, no `T J = J`, no uniform stationary vector.
-/

section PerronSplit

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {φ : E →ₗ[K] K} {T : Module.End K E}

/-- **I.1, invariance.** "the mean-zero space `V = ker(1^T) = 1^perp` is `T`-invariant
(`1^T (Tf) = 1^T f = 0`)". -/
theorem meanZero_invariant (hT : φ ∘ₗ T = φ) : ∀ x ∈ LinearMap.ker φ, T x ∈ LinearMap.ker φ := by
  intro x hx
  have : φ (T x) = φ x := congrArg (fun f => f x) hT
  simpa [LinearMap.mem_ker, this] using hx

/-- `A = T|_V`, the compression of `T` to the mean-zero space `V = ker φ`.

This is the `A` of `THEOREM.md` I.1. Note it is the *restriction to an invariant subspace*, not
a similarity transform of `T`: the complement `span(1)` is **not** assumed `T`-invariant (that
would be `d = 0`, i.e. double stochasticity, which is false here). -/
noncomputable def compression (hT : φ ∘ₗ T = φ) : Module.End K (LinearMap.ker φ) :=
  T.restrict (meanZero_invariant hT)

@[simp]
theorem compression_coe_apply (hT : φ ∘ₗ T = φ) (x : LinearMap.ker φ) :
    ((compression hT) x : E) = T x := rfl

/-- **I.1, eigenvector form.** Any eigenvector of `T` for an eigenvalue `μ ≠ 1` lies in the
mean-zero space `V = ker(1^T)`.

Two lines of algebra: `φ (T v) = φ v` and `φ (T v) = μ * φ v`, so `(μ - 1) * φ v = 0`. -/
theorem mem_meanZero_of_eigenvector (hT : φ ∘ₗ T = φ) {μ : K} (hμ : μ ≠ 1) {v : E}
    (hv : T v = μ • v) : v ∈ LinearMap.ker φ := by
  have h1 : φ (T v) = φ v := congrArg (fun f => f v) hT
  rw [hv, map_smul, smul_eq_mul] at h1
  have : (μ - 1) * φ v = 0 := by ring_nf; linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hμ
  · exact h

/-- **I.1, set-level split.** Every eigenvalue of `T` other than `1` is an eigenvalue of the
compression `A = T|_V`. This is the `spec(T) ⊆ {1} ∪ spec(A)` direction of
"`spec(T) = {1} u spec(A)`". -/
theorem hasEigenvalue_compression_of_ne_one (hT : φ ∘ₗ T = φ) {μ : K} (hμ : μ ≠ 1)
    (h : T.HasEigenvalue μ) : (compression hT).HasEigenvalue μ := by
  obtain ⟨v, hv, hv0⟩ := h.exists_hasEigenvector
  have hvV : v ∈ LinearMap.ker φ := mem_meanZero_of_eigenvector hT hμ (mem_eigenspace_iff.mp hv)
  refine hasEigenvalue_of_hasEigenvector (x := (⟨v, hvV⟩ : LinearMap.ker φ)) ⟨?_, ?_⟩
  · rw [mem_eigenspace_iff]
    ext
    simpa using mem_eigenspace_iff.mp hv
  · simpa [Submodule.mk_eq_zero] using hv0

/-- **I.1, the multiplicity content at `μ = 1`, geometric reading.** If the `1`-eigenspace of `T`
has dimension at least `2` then `1` is also an eigenvalue of the compression `A = T|_V`.

This is what "as multisets" buys over the bare set inclusion at the single point where the two
differ: if `1` is a degenerate eigenvalue of `T`, then `λ₂(T) = 1` and the bound
`|λ₂(T)| ≤ ρ(A)` needs `1 ∈ spec(A)`. Proof: `V = ker φ` has codimension at most `1`, so it
meets any subspace of dimension `≥ 2` nontrivially. -/
theorem hasEigenvalue_compression_one_of_two_le_finrank [FiniteDimensional K E]
    (hT : φ ∘ₗ T = φ) (h2 : 2 ≤ finrank K (T.eigenspace 1)) :
    (compression hT).HasEigenvalue 1 := by
  set W := T.eigenspace 1 with hW
  -- restrict `φ` to `W`; its range sits in `K`, so has finrank ≤ 1
  set ψ : W →ₗ[K] K := φ.domRestrict W with hψ
  have hrk : finrank K (LinearMap.range ψ) + finrank K (LinearMap.ker ψ) = finrank K W :=
    ψ.finrank_range_add_finrank_ker
  have hle1 : finrank K (LinearMap.range ψ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range ψ)
    simpa using this
  have hker : 1 ≤ finrank K (LinearMap.ker ψ) := by omega
  have hne : LinearMap.ker ψ ≠ ⊥ := by
    intro hcon
    rw [hcon] at hker
    simp at hker
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  -- `w : W` with `φ w = 0` and `w ≠ 0`; push it into `V = ker φ`
  have hwV : (w : E) ∈ LinearMap.ker φ := by
    simpa [hψ, LinearMap.mem_ker] using hw
  have hwT : T (w : E) = (1 : K) • (w : E) := by
    simpa using mem_eigenspace_iff.mp w.2
  refine hasEigenvalue_of_hasEigenvector (x := (⟨(w : E), hwV⟩ : LinearMap.ker φ)) ⟨?_, ?_⟩
  · rw [mem_eigenspace_iff]; ext; simpa using hwT
  · simp only [ne_eq, Submodule.mk_eq_zero]
    intro hcon
    exact hw0 (by ext; exact hcon)

/-- **I.1 on `spectrum`.** `spec(T) ⊆ {1} ∪ spec(T|_V)`. -/
theorem spectrum_subset_insert_one [FiniteDimensional K E] (hT : φ ∘ₗ T = φ) :
    spectrum K T ⊆ insert (1 : K) (spectrum K (compression hT)) := by
  intro μ hμ
  by_cases h1 : μ = 1
  · exact Set.mem_insert_iff.mpr (Or.inl h1)
  · refine Set.mem_insert_iff.mpr (Or.inr ?_)
    exact hasEigenvalue_iff_mem_spectrum.mp
      (hasEigenvalue_compression_of_ne_one hT h1 (HasEigenvalue.of_mem_spectrum hμ))

end PerronSplit

/-!
## Section 2: block-triangular characteristic polynomial (THEOREM.md I.1, multiset form)

> "In a basis adapted to `C^N = span(1) (+) V`, `T` is block-triangular, `T = [[1, 0], [d, A]]`
> with `A = T|_V` (the off-diagonal `d` is the `V`-component of `T1`, nonzero here). The
> characteristic polynomial factors, so `spec(T) = {1} u spec(A)` as multisets".

`d` below is an **arbitrary** block and is never assumed zero - assuming `d = 0` is exactly the
double-stochasticity error the referee found, and the factorisation does not need it.

These two are conditional on being handed the adapted basis (see the gap note in the header):
they prove the factorisation for a matrix already in the block form.
-/

section BlockTriangular

open Polynomial Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **I.1, charpoly factorisation.** For the Perron block form `[[1, 0], [d, A]]` the
characteristic polynomial factors as `(X - 1) * charpoly A`, for **any** off-diagonal block `d`. -/
theorem charpoly_perron_block (d : Matrix ι (Fin 1) K) (A : Matrix ι ι K) :
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) K) 0 d A).charpoly
      = (X - C (1 : K)) * A.charpoly := by
  rw [Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_one]
  simp

/-- **I.1, `spec(T) = {1} u spec(A)` as multisets**, for the Perron block form. The roots of the
characteristic polynomial are taken with multiplicity, so this is the multiset statement. -/
theorem roots_charpoly_perron_block (d : Matrix ι (Fin 1) K) (A : Matrix ι ι K) :
    (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) K) 0 d A).charpoly.roots
      = (1 : K) ::ₘ A.charpoly.roots := by
  have hA : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  have hX : (X - C (1 : K)) ≠ 0 := X_sub_C_ne_zero _
  rw [charpoly_perron_block, Polynomial.roots_mul (mul_ne_zero hX hA), Polynomial.roots_X_sub_C]
  rfl

end BlockTriangular

/-!
## Section 3: the Gelfand-shaped bound (THEOREM.md I.2)

`THEOREM.md` I.2 verbatim:

> **I.2 (adjoint and Gelfand).** `A = P_V T P_V` on `V`, so `A^* = P_V U P_V =: U_V` with
> `U = T^T`, and `rho(A) = rho(U_V)`. (`V` need not be `U`-invariant - `U_V` is the compression,
> which is all that is used.) By Gelfand, for every `p`,
> `rho(U_V) <= || U_V^p ||_2^{1/p}`,
> valid for any matrix - no normality or diagonalisability input (this is what makes the route
> immune to the `kappa ~ 10^k` non-normality that broke the older perturbative argument).

We take the sanctioned elementary route: for an eigenpair `A v = μ v` with `v ≠ 0`,
`|μ|^p ‖v‖ = ‖A^p v‖ ≤ C ‖v‖` for any operator bound `C` on `A^p`, hence `|μ|^p ≤ C`. No
Gelfand, no completeness, no normality, no diagonalisability, no finite dimension - and it is
exactly the inequality Part I.3 consumes (with `C = ‖Q^p‖`).
-/

section GelfandSubstitute

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **I.2, elementary form.** If `‖A^p x‖ ≤ C ‖x‖` for all `x` and `A v = μ v` with `v ≠ 0`, then
`‖μ‖^p ≤ C`. No normality, diagonalisability, completeness, or finite-dimensionality. -/
theorem norm_eigenvalue_pow_le_of_pow_bound (A : Module.End 𝕜 F) (p : ℕ) (C : ℝ)
    (hC : ∀ x : F, ‖(A ^ p) x‖ ≤ C * ‖x‖) {μ : 𝕜} {v : F} (hv0 : v ≠ 0) (hv : A v = μ • v) :
    ‖μ‖ ^ p ≤ C := by
  have hev : A.HasEigenvector μ v := ⟨mem_eigenspace_iff.mpr hv, hv0⟩
  have hpow : (A ^ p) v = μ ^ p • v := hev.pow_apply p
  have h1 : ‖μ‖ ^ p * ‖v‖ ≤ C * ‖v‖ := by
    have := hC v
    rwa [hpow, norm_smul, norm_pow] at this
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  exact le_of_mul_le_mul_right (by linarith [h1]) hvn

/-- **I.2, operator-norm form.** `‖μ‖^p ≤ ‖A^p‖` for every eigenvalue `μ` of a continuous linear
map `A`. This is `rho(A)^p ≤ ‖A^p‖` restricted to eigenvalues, which is all Part I.3 uses. -/
theorem norm_eigenvalue_pow_le_opNorm_pow (A : F →L[𝕜] F) (p : ℕ) {μ : 𝕜} {v : F}
    (hv0 : v ≠ 0) (hv : A v = μ • v) : ‖μ‖ ^ p ≤ ‖A ^ p‖ := by
  have hpow : ∀ n : ℕ, (A ^ n) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ContinuousLinearMap.mul_apply, hv, map_smul, ih, smul_smul]
        congr 1
        ring
  have h1 : ‖μ‖ ^ p * ‖v‖ ≤ ‖A ^ p‖ * ‖v‖ := by
    have := (A ^ p).le_opNorm v
    rwa [hpow p, norm_smul, norm_pow] at this
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  exact le_of_mul_le_mul_right (by linarith [h1]) hvn

/-- **I.2 in the `rho <= ‖A^p‖^(1/p)` shape.** From `‖μ‖^p ≤ C` and `p ≠ 0`, `‖μ‖ ≤ C^(1/p)`. -/
theorem norm_eigenvalue_le_rpow {p : ℕ} (hp : p ≠ 0) {C : ℝ} {μ : 𝕜} (h : ‖μ‖ ^ p ≤ C) :
    ‖μ‖ ≤ C ^ ((p : ℝ)⁻¹) := by
  have hμ : (0 : ℝ) ≤ ‖μ‖ := norm_nonneg μ
  have hpow : (0 : ℝ) ≤ ‖μ‖ ^ p := pow_nonneg hμ p
  calc ‖μ‖ = (‖μ‖ ^ p) ^ ((p : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hμ hp).symm
    _ ≤ C ^ ((p : ℝ)⁻¹) := Real.rpow_le_rpow hpow h (by positivity)

end GelfandSubstitute

/-!
## Section 4: the chain I.1 -> I.2 as Part I.3 consumes it

`THEOREM.md` I.1 concludes `|lambda_2(T)| <= rho(A)` and I.2 continues
`rho(A) = rho(U_V) <= ||U_V^p||^{1/p}`. Composed, and with I.3 supplying the operator bound
`C = ||Q^p||` on the compression's `p`-th power, the chain delivers
`|lambda_2(T)| <= ||Q^p||^{1/p}` - which is the single fact Part I.3/I.4 turn into
`|lambda_2| <= rho(Q) <= cert(k)`.

The theorem below is the exact interface: it takes the column-stochasticity hypothesis and an
operator bound on `(T|_V)^p`, and returns the eigenvalue bound. It assumes nothing about `T`
beyond `φ ∘ T = φ`.
-/

section Chain

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {φ : F →ₗ[𝕜] 𝕜} {T : Module.End 𝕜 F}

/-- **I.1 + I.2 composed.** Let `φ ∘ T = φ` (column-stochasticity, `1ᵀ T = 1ᵀ`), let `μ ≠ 1` be an
eigenvalue of `T`, and suppose `‖(T|_V)^p x‖ ≤ C ‖x‖` on `V = ker φ`. Then `‖μ‖^p ≤ C`, hence
`‖μ‖ ≤ C^(1/p)`.

No double stochasticity, no uniform stationary distribution, no normality, no
diagonalisability, and no dependence on `finrank 𝕜 F`. -/
theorem norm_eigenvalue_le_of_compression_pow_bound (hT : φ ∘ₗ T = φ) (p : ℕ) (C : ℝ)
    (hC : ∀ x : LinearMap.ker φ, ‖((compression hT) ^ p) x‖ ≤ C * ‖x‖)
    {μ : 𝕜} (hμ : μ ≠ 1) {v : F} (hv0 : v ≠ 0) (hv : T v = μ • v) :
    ‖μ‖ ^ p ≤ C := by
  have hvV : v ∈ LinearMap.ker φ := mem_meanZero_of_eigenvector hT hμ hv
  refine norm_eigenvalue_pow_le_of_pow_bound (compression hT) p C hC
    (v := (⟨v, hvV⟩ : LinearMap.ker φ)) ?_ ?_
  · simpa [Submodule.mk_eq_zero] using hv0
  · ext; simpa using hv

/-- The same, in the `p`-th-root shape of I.2. -/
theorem norm_eigenvalue_le_rpow_of_compression_pow_bound (hT : φ ∘ₗ T = φ) {p : ℕ} (hp : p ≠ 0)
    (C : ℝ) (hC : ∀ x : LinearMap.ker φ, ‖((compression hT) ^ p) x‖ ≤ C * ‖x‖)
    {μ : 𝕜} (hμ : μ ≠ 1) {v : F} (hv0 : v ≠ 0) (hv : T v = μ • v) :
    ‖μ‖ ≤ C ^ ((p : ℝ)⁻¹) :=
  norm_eigenvalue_le_rpow hp
    (norm_eigenvalue_le_of_compression_pow_bound hT p C hC hμ hv0 hv)

end Chain

end OperatorChain
