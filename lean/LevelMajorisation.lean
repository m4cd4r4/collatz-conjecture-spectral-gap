/-
# Level majorisation: `a(U_V g) ≤ Q a(g)`, its iteration, and the weighted row-sum bound

Lean 4 formalisation of the abstract content of **Part I.3-I.4** of `THEOREM.md` (the uniform
spectral gap, consolidated, 2026-07-05) in the public `collatz-cycle-certificate` repo.
`OperatorChain.lean` formalises I.1-I.2 (the Perron split and the Gelfand-shaped eigenvalue
bound) and leaves the operator bound on `(T|_V)^p` as a hypothesis; **this file supplies exactly
that bound**, and the last section composes the two into `‖λ₂‖ ≤ c`.

Nothing here mentions the Syracuse map, `3x+1`, `3x-1`, residues, or any specific operator.

## Scope note (model scope, standing gate 1)

Every statement below is **sign-agnostic**: it is a fact about an arbitrary linear map on a
space with an orthogonal level decomposition, and holds verbatim for the `3x-1` transfer
operator, which passes the identical certificate yet has genuine cycles
(`CYCLE_CLAIM_REFUTED.md`). **Consequently this file proves nothing whatsoever about Collatz
cycles**, and nothing about `3x+1` that is not equally true of `3x-1`. It is linear algebra:
if an operator's level blocks are dominated entrywise by a nonnegative matrix `Q`, then its
eigenvalues are dominated by `Q`'s weighted row-sum bound.

The number-theoretic content that makes the abstract hypotheses true for the Syracuse operator
(the identification of `Q[a,b] = ‖P_a U P_b‖` and its bound `2^{-(b-a)/2}[b>a] + u_a v_b`) is
Lemma A / Lemma B, i.e. `THEOREM.md` Part II - explicitly **out of scope here** and supplied to
these theorems as hypotheses.

## Statement-fidelity table

`THEOREM.md` I.3 and I.4 verbatim (the sentences each Lean name formalises):

> **I.3 (level majorisation).** For `g in V` write the level-energy vector `a(g)_m := ||P_m g||_2`.
> Since `P_{m'} P_V = P_{m'}`, the triangle inequality and the definition of `Q = Q_k` give
> `||P_{m'} U_V g|| = ||P_{m'} U g|| <= sum_m Q[m',m] a(g)_m = (Q a(g))_{m'}`,
> i.e. `a(U_V g) <= Q a(g)` entrywise. `Q` is nonnegative, so this iterates:
> `a(U_V^p g) <= Q^p a(g)`. The levels are orthogonal and exhaust `V`, so
> `||U_V^p g||_2 = ||a(U_V^p g)||_2 <= ||Q^p||_2 ||g||_2`,
> hence `rho(A) = rho(U_V) <= lim_p ||Q^p||^{1/p} = rho(Q)`, and with I.1,
> `|lambda_2(T)| <= rho(Q)`.

> **I.4 (weighted row sum).** `Q` is nonnegative, so for the diagonal similarity
> `S = diag(2^0, ..., 2^{k-2})`:
> `rho(Q) = rho(S Q S^{-1}) <= ||S Q S^{-1}||_inf = max_a sum_b Q[a,b] 2^{a-b} = cert(k)`.

| Lean name | sentence formalised |
|---|---|
| `starProjection_level_of_le` | I.3: "Since `P_{m'} P_V = P_{m'}`" - the projection identity the first equality of I.3 rests on (CITED from Mathlib, see labelling below) |
| `norm_eq_l2norm_levelEnergy` | I.3: "The levels are orthogonal and exhaust `V`", in its only used form `‖g‖₂ = ‖a(g)‖₂` (Parseval) |
| `levelSplit` | I.3 (a): "`||P_{m'} U_V g|| <= sum_m Q[m',m] a(g)_m = (Q a(g))_{m'}`" |
| `levelEnergy_le_mulVec` | I.3: "i.e. `a(U_V g) <= Q a(g)` entrywise" |
| `levelEnergy_pow_le_mulVec` | I.3 (b): "`Q` is nonnegative, so this iterates: `a(U_V^p g) <= Q^p a(g)`" |
| `norm_pow_le_of_matrixBound` | I.3 (c): "`||U_V^p g||_2 = ||a(U_V^p g)||_2 <= ||Q^p||_2 ||g||_2`" |
| `weighted_mulVec_pow_le` | I.4 in power form: the diagonal similarity `S = diag(2^a)` iterated `p` times |
| `l2norm_mulVec_pow_le` | I.4 + I.3(c) combined: `‖Q^p x‖₂ ≤ C_K c^p ‖x‖₂` with the explicit `C_K` |
| `norm_pow_le_dimConst_mul` | the supplier for `OperatorChain`'s `hC` hypothesis: `‖B^p g‖ ≤ C_K c^p ‖g‖` |
| `inner_pow_adjoint`, `norm_pow_le_of_adjoint_bound` | I.2: "`A = P_V T P_V` on `V`, so `A^* = P_V U P_V =: U_V` with `U = T^T`, and `rho(A) = rho(U_V)`" - the adjoint bridge, proved without any spectral radius |
| `norm_eigenvalue_le_cert` | I.1 + I.2 + I.3 + I.4 composed, block bounds given for the compression `A` |
| `norm_eigenvalue_le_cert_adjoint` | the same in `THEOREM.md`'s own orientation (block bounds given for `U`): `|lambda_2(T)| <= cert(k)` |

## Representation choice (recorded per the task's kill criteria, NOT a gap)

The level decomposition is taken in **decomposed form**: instead of a family of submodules
`W_m ≤ V` of an ambient inner-product space together with orthogonal projections `P_m`, the
space is `PiLp 2 G`, i.e. the external orthogonal direct sum `⨁_m G m` with the `L²` norm, and
`P_m` is the coordinate projection `g ↦ g m`. Every finite orthogonal internal direct sum is
isometrically isomorphic to such a `PiLp 2 G`, and the composition theorem in §6 takes that
isometry (`e`) as a hypothesis, so no generality is lost for the downstream use. What this buys
is that Parseval, `‖g‖² = ∑_m ‖P_m g‖²`, is `PiLp.norm_eq_of_L2` rather than a fight with
`OrthogonalFamily` / `DirectSum.IsInternal`.

The one thing the decomposed representation cannot see is the sentence *"Since `P_{m'} P_V =
P_{m'}`"*, because in the decomposed picture `P_V` has already been absorbed. That identity is
therefore stated separately and honestly in §0, in the submodule language, where it has content.

## Honest labelling: proved vs cited vs deliberately not done

* **PROVEN outright** (no `sorry`, no added axiom): §1-§5, the §6 composition and the §6 adjoint
  bridge, i.e. items (a), (b), (c), (d) of I.3-I.4, the I.2 adjoint step, and the resulting
  `‖μ‖ ≤ c`.
* **Orientation, the trap this file nearly fell into.** `Q` in `THEOREM.md` is the block matrix of
  `U = T^T`, not of the compression `A = T|_V`; the two are transposes, and a weighted row sum of
  one is a weighted column sum of the other. `norm_eigenvalue_le_cert` takes the blocks of the
  operator it is applied to; `norm_eigenvalue_le_cert_adjoint` takes them for `U`, in
  `THEOREM.md`'s orientation, and is the one whose `c` is literally `cert(k)`. See the note above
  `AdjointBridge`.
* **CITED from Mathlib**, not reproved: `starProjection_level_of_le` is a thin wrapper around
  `Submodule.starProjection_comp_starProjection_of_le`. It is Mathlib's theorem; the wrapper
  exists only to name the `THEOREM.md` sentence it discharges.
* **NOT DONE, and not needed: `rho(Q)` as a named object.** `THEOREM.md` I.3-I.4 route through
  the spectral radius, `rho(U_V) ≤ rho(Q) ≤ cert(k)`. Mathlib has `spectralRadius` only for
  elements of a normed algebra (`Mathlib/Analysis/Normed/Algebra/Spectrum.lean`), as an
  `ℝ≥0∞`-valued supremum over the spectrum; there is **no** Perron-Frobenius theory for
  matrices in Mathlib (no `rho(Q) ≤ max row sum`, no `rho(S Q S⁻¹) = rho(Q)` for matrices).
  Reproving `rho(Q) = lim ‖Q^p‖^{1/p}` and the similarity invariance is a substantial detour.
  It is also unnecessary: the **power form** proved here, `‖Q^p x‖ ≤ C_K c^p ‖x‖`, feeds
  `OperatorChain.norm_eigenvalue_le_of_compression_pow_bound` directly and yields `‖μ‖ ≤ c` in
  §6 with no spectral radius anywhere. The named statement `rho(Q) ≤ max_a ∑_b Q[a,b] 2^{a-b}`
  is therefore recorded as **CITED** (standard, Perron-Frobenius-adjacent: `rho ≤ ‖·‖` for any
  submultiplicative norm, applied to `‖S Q S⁻¹‖_∞`) and is **not used** by anything below.
  Missing Mathlib API, named: spectral radius of a `Matrix`, and its invariance under
  similarity / domination by any induced matrix norm.
* **Matrix operator norm.** `‖Q^p‖₂` in I.3(c) is Mathlib's `Matrix.l2_opNorm`, which lives in
  `Mathlib/Analysis/CStarAlgebra/Matrix.lean` behind the deliberately-scoped instance
  `open scoped Matrix.Norms.L2Operator`. Rather than import the C*-algebra hierarchy for one
  numeral, `norm_pow_le_of_matrixBound` takes **any** constant `C` dominating the `ℓ²` action of
  `Q^p` on nonnegative vectors. That is strictly weaker as a hypothesis (`C := ‖Q^p‖₂` is one
  admissible choice) and strictly more general as a theorem.

## Dimension uniformity (absurd-height sanity, standing gate 3)

The constant `c` is **not** dimension-indexed: it is the hypothesised weighted row-sum bound, and
the final conclusion `‖μ‖ ≤ c` in `norm_eigenvalue_le_cert` contains no `K` at all. The only
`K`-dependent quantity anywhere is `dimConst K = √K · 2^K`, which appears solely inside the
`p`-th power bound; the §6 argument lets `p → ∞`, and `dimConst K ^ (1/p) → 1` for every fixed
`K`. Instantiating at the Collatz-relevant absurd height `K = 10^9` levels (or `K = 2^(k-1)` for
`k = 10^9`) changes nothing in the conclusion: `dimConst (10^9)` is a finite positive real, and
the contradiction argument in `norm_eigenvalue_le_cert` needs only `0 < dimConst K`. No constant
drifts, no bound degrades, and no hypothesis becomes harder to satisfy as `K` grows.

Worth stating sharply because it is the referee's question (iii): `dimConst K` **is** exponential
in `K`, and that is deliberate and harmless. It appears only as the `C` in `‖μ‖^p ≤ C c^p`, and
the final step chooses `p` large enough to swallow it. At `K = 10^9` the constant is
`√(10^9) · 2^(10^9)` - astronomically large, entirely irrelevant, and absent from the conclusion.
What would break uniformity is a `K`-dependence in `c`, and there is none: `c` is supplied by the
caller and the theorem never touches `K` when using it.
-/

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import OperatorChain

namespace LevelMajorisation

open Finset Matrix

/-!
## Section 0: the projection identity `P_{m'} P_V = P_{m'}` (THEOREM.md I.3, first equality)

`THEOREM.md` I.3 opens:

> Since `P_{m'} P_V = P_{m'}`, the triangle inequality and the definition of `Q = Q_k` give
> `||P_{m'} U_V g|| = ||P_{m'} U g||`

This is the one sentence the decomposed representation used from §1 onward cannot express (there,
`P_V` is already absorbed). It is stated here in the submodule language, where it has content:
each level `W_m` sits **inside** the mean-zero space `V`, and that containment is exactly what
lets the compression `U_V = P_V U P_V` be replaced by `U` after projecting onto a level.

Label: **CITED**. This is Mathlib's `Submodule.starProjection_comp_starProjection_of_le`; the
wrapper exists only to pin which `THEOREM.md` sentence it discharges. It is *proved*, not
assumed - the hypothesis `W ≤ V` is the honest one (a level is a subspace of the mean-zero
space), and it is not derived from anything hidden.
-/

section ProjectionIdentity

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **I.3, "Since `P_{m'} P_V = P_{m'}`".** For a level `W ≤ V` inside the mean-zero space `V`,
projecting onto `V` first is redundant. Hence `P_{m'} U_V = P_{m'} P_V U P_V = P_{m'} U P_V`,
which is the first equality of I.3.

CITED: this is `Submodule.starProjection_comp_starProjection_of_le` verbatim. -/
theorem starProjection_level_of_le (W V : Submodule 𝕜 E) [W.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : W ≤ V) :
    W.starProjection ∘L V.starProjection = W.starProjection :=
  Submodule.starProjection_comp_starProjection_of_le h

end ProjectionIdentity

/-!
## Section 1: the level-energy vector and Parseval

`THEOREM.md` I.3: *"For `g in V` write the level-energy vector `a(g)_m := ||P_m g||_2"* and
*"The levels are orthogonal and exhaust `V`, so `||U_V^p g||_2 = ||a(U_V^p g)||_2"*.

In the decomposed representation (see the header) `P_m g` is the coordinate `g m`, so
`a(g)_m = ‖g m‖` and Parseval is `PiLp.norm_eq_of_L2`.
-/

section Setup

variable {K : ℕ} {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)]

/-- The Euclidean norm of a real vector, written out rather than routed through
`EuclideanSpace`: `‖x‖₂ = √(∑ x_i²)`. -/
noncomputable def l2norm (x : Fin K → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- **I.3.** The level-energy vector `a(g)_m := ‖P_m g‖₂`. -/
noncomputable def levelEnergy (g : PiLp 2 G) : Fin K → ℝ := fun m => ‖g m‖

@[simp] theorem levelEnergy_apply (g : PiLp 2 G) (m : Fin K) : levelEnergy g m = ‖g m‖ := rfl

theorem levelEnergy_nonneg (g : PiLp 2 G) (m : Fin K) : 0 ≤ levelEnergy g m := norm_nonneg _

theorem l2norm_nonneg (x : Fin K → ℝ) : 0 ≤ l2norm x := Real.sqrt_nonneg _

/-- **I.3, Parseval.** *"The levels are orthogonal and exhaust `V`, so
`||U_V^p g||_2 = ||a(U_V^p g)||_2`"*. -/
theorem norm_eq_l2norm_levelEnergy (g : PiLp 2 G) : ‖g‖ = l2norm (levelEnergy g) := by
  rw [PiLp.norm_eq_of_L2, l2norm]
  rfl

/-- Monotonicity of the `ℓ²` norm on the nonnegative orthant. Used for the middle step of
I.3(c): `a(U_V^p g) ≤ Q^p a(g)` entrywise upgrades to a norm inequality. -/
theorem l2norm_le_of_le {x w : Fin K → ℝ} (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ w i) :
    l2norm x ≤ l2norm w := by
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  exact pow_le_pow_left₀ (hx i) (h i) 2

/-- A single coordinate is dominated by the `ℓ²` norm (nonnegative case). -/
theorem le_l2norm {x : Fin K → ℝ} (hx : ∀ i, 0 ≤ x i) (i : Fin K) : x i ≤ l2norm x := by
  have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : Real.sqrt (x i ^ 2) ≤ l2norm x := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (hx i)] at h2

/-- `ℓ²` is dominated by `√K` times the sup bound. Crude but explicit; it is the only place a
dimension constant enters. -/
theorem l2norm_le_sqrt_card_mul {x : Fin K → ℝ} {M : ℝ} (hx : ∀ i, 0 ≤ x i) (hM0 : 0 ≤ M)
    (hM : ∀ i, x i ≤ M) : l2norm x ≤ Real.sqrt K * M := by
  have hsum : ∑ i, x i ^ 2 ≤ (K : ℝ) * M ^ 2 := by
    have : ∑ _i : Fin K, M ^ 2 = (K : ℝ) * M ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin K, M ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hx i) (hM i) 2
      _ = (K : ℝ) * M ^ 2 := this
  calc l2norm x ≤ Real.sqrt ((K : ℝ) * M ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt K * M := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM0]

end Setup

/-!
## Section 2: (a) the level-split triangle inequality (THEOREM.md I.3, first display)

> `||P_{m'} U_V g|| = ||P_{m'} U g|| <= sum_m Q[m',m] a(g)_m = (Q a(g))_{m'}`

The single content step is: decompose `g = ∑_m P_m g`, push `B` through the sum, project onto
level `m'`, and apply the triangle inequality followed by the block bounds `Q[m',m]`.

`Q` is supplied as a hypothesis package (`hQ`), mirroring `GapCertificate.lean`'s
`assembly_row_bound` style: nothing constructs `Q` from an operator, so nothing here depends on
Lemma A. Note `hQ` is exactly `‖P_{m'} B P_m‖ ≤ Q[m',m]` written pointwise.
-/

section LevelSplit

variable {K : ℕ} {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, NormedSpace ℂ (G m)]

/-- The inclusion of level `m` into the decomposed space: `P_m`'s right inverse. -/
noncomputable def levelSingle (m : Fin K) (y : G m) : PiLp 2 G := WithLp.toLp 2 (Pi.single m y)

omit [∀ m, NormedSpace ℂ (G m)] in
@[simp] theorem levelSingle_apply (m m' : Fin K) (y : G m) :
    (levelSingle m y) m' = Pi.single m y m' := rfl

omit [∀ m, NormedSpace ℂ (G m)] in
/-- `g = ∑_m P_m g`: the levels exhaust the space. -/
theorem sum_levelSingle (g : PiLp 2 G) : ∑ m, levelSingle m (g m) = g := by
  ext i
  have h : (∑ m, levelSingle (G := G) m (g m)) i = ∑ m, (levelSingle (G := G) m (g m)) i := by
    change (∑ m, levelSingle (G := G) m (g m)).ofLp i = _
    rw [WithLp.ofLp_sum]
    exact Finset.sum_apply i _ _
  rw [h]
  simp

/-- **I.3 (a), the level-split triangle inequality.**

> `||P_{m'} U_V g|| = ||P_{m'} U g|| <= sum_m Q[m',m] a(g)_m = (Q a(g))_{m'}` -/
theorem levelSplit (B : Module.End ℂ (PiLp 2 G)) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : ∀ (m : Fin K) (y : G m) (m' : Fin K), ‖(B (levelSingle m y)) m'‖ ≤ Q m' m * ‖y‖)
    (g : PiLp 2 G) (m' : Fin K) :
    ‖(B g) m'‖ ≤ ∑ m, Q m' m * ‖g m‖ := by
  have hg : B g = ∑ m, B (levelSingle m (g m)) := by
    conv_lhs => rw [← sum_levelSingle g]
    exact map_sum B _ _
  have hproj : (∑ m, B (levelSingle (G := G) m (g m))) m'
      = ∑ m, (B (levelSingle (G := G) m (g m))) m' := by
    change (∑ m, B (levelSingle (G := G) m (g m))).ofLp m' = _
    rw [WithLp.ofLp_sum]
    exact Finset.sum_apply m' _ _
  rw [hg, hproj]
  exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => hQ m (g m) m')

/-- **I.3, "i.e. `a(U_V g) <= Q a(g)` entrywise".** -/
theorem levelEnergy_le_mulVec (B : Module.End ℂ (PiLp 2 G)) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : ∀ (m : Fin K) (y : G m) (m' : Fin K), ‖(B (levelSingle m y)) m'‖ ≤ Q m' m * ‖y‖)
    (g : PiLp 2 G) (m' : Fin K) :
    levelEnergy (B g) m' ≤ (Q *ᵥ levelEnergy g) m' := by
  have := levelSplit B Q hQ g m'
  simpa [Matrix.mulVec, dotProduct] using this

end LevelSplit

/-!
## Section 3: (b) the entrywise iteration `a(U_V^p g) ≤ Q^p a(g)`

> `Q` is nonnegative, so this iterates: `a(U_V^p g) <= Q^p a(g)`
-/

section Iteration

variable {K : ℕ}

/-- Entrywise monotonicity of `x ↦ Q x` for a nonnegative `Q`. -/
theorem mulVec_mono (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    {x w : Fin K → ℝ} (h : ∀ i, x i ≤ w i) (i : Fin K) : (Q *ᵥ x) i ≤ (Q *ᵥ w) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (hQ0 i j)

/-- Powers of an entrywise-nonnegative matrix are entrywise nonnegative. -/
theorem matrix_pow_nonneg (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j) :
    ∀ (p : ℕ) (i j : Fin K), 0 ≤ (Q ^ p) i j := by
  intro p
  induction p with
  | zero => intro i j; by_cases h : i = j <;> simp [h]
  | succ n ih =>
      intro i j
      rw [pow_succ']
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hQ0 i k) (ih k j)

variable {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, NormedSpace ℂ (G m)]

/-- **I.3 (b).** `a(U_V^p g) ≤ Q^p a(g)` entrywise, for every `p`. -/
theorem levelEnergy_pow_le_mulVec (B : Module.End ℂ (PiLp 2 G)) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : ∀ (m : Fin K) (y : G m) (m' : Fin K), ‖(B (levelSingle m y)) m'‖ ≤ Q m' m * ‖y‖)
    (hQ0 : ∀ i j, 0 ≤ Q i j) (g : PiLp 2 G) :
    ∀ (p : ℕ) (m' : Fin K), levelEnergy ((B ^ p) g) m' ≤ ((Q ^ p) *ᵥ levelEnergy g) m' := by
  intro p
  induction p with
  | zero => intro m'; simp [Matrix.one_mulVec]
  | succ n ih =>
      intro m'
      have hstep : levelEnergy ((B ^ (n + 1)) g) m'
          ≤ (Q *ᵥ levelEnergy ((B ^ n) g)) m' := by
        have hBB : (B ^ (n + 1)) g = B ((B ^ n) g) := by
          rw [pow_succ']; rfl
        rw [hBB]
        exact levelEnergy_le_mulVec B Q hQ _ m'
      have hmono : (Q *ᵥ levelEnergy ((B ^ n) g)) m' ≤ (Q *ᵥ ((Q ^ n) *ᵥ levelEnergy g)) m' :=
        mulVec_mono Q hQ0 ih m'
      have hcomp : (Q *ᵥ ((Q ^ n) *ᵥ levelEnergy g)) = (Q ^ (n + 1)) *ᵥ levelEnergy g := by
        rw [Matrix.mulVec_mulVec, ← pow_succ']
      calc levelEnergy ((B ^ (n + 1)) g) m' ≤ (Q *ᵥ levelEnergy ((B ^ n) g)) m' := hstep
        _ ≤ (Q *ᵥ ((Q ^ n) *ᵥ levelEnergy g)) m' := hmono
        _ = ((Q ^ (n + 1)) *ᵥ levelEnergy g) m' := by rw [hcomp]

end Iteration

/-!
## Section 4: (c) Parseval at both ends, `‖U_V^p g‖ ≤ ‖Q^p‖ ‖g‖`

> The levels are orthogonal and exhaust `V`, so
> `||U_V^p g||_2 = ||a(U_V^p g)||_2 <= ||Q^p||_2 ||g||_2`

`C` below stands in for `‖Q^p‖₂`; see the header for why the Mathlib `Matrix.l2_opNorm` is not
imported. Any `C` dominating the `ℓ²` action of `Q^p` on the nonnegative orthant works, and
`C := ‖Q^p‖₂` is one such.
-/

section Parseval

variable {K : ℕ} {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, NormedSpace ℂ (G m)]

/-- **I.3 (c).** `‖U_V^p g‖₂ = ‖a(U_V^p g)‖₂ ≤ ‖Q^p‖₂ ‖g‖₂`, with `C` in place of `‖Q^p‖₂`. -/
theorem norm_pow_le_of_matrixBound (B : Module.End ℂ (PiLp 2 G)) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : ∀ (m : Fin K) (y : G m) (m' : Fin K), ‖(B (levelSingle m y)) m'‖ ≤ Q m' m * ‖y‖)
    (hQ0 : ∀ i j, 0 ≤ Q i j) (p : ℕ) (C : ℝ)
    (hC : ∀ x : Fin K → ℝ, (∀ i, 0 ≤ x i) → l2norm ((Q ^ p) *ᵥ x) ≤ C * l2norm x)
    (g : PiLp 2 G) : ‖(B ^ p) g‖ ≤ C * ‖g‖ := by
  have hmono : l2norm (levelEnergy ((B ^ p) g)) ≤ l2norm ((Q ^ p) *ᵥ levelEnergy g) :=
    l2norm_le_of_le (fun i => levelEnergy_nonneg _ i)
      (fun i => levelEnergy_pow_le_mulVec B Q hQ hQ0 g p i)
  calc ‖(B ^ p) g‖ = l2norm (levelEnergy ((B ^ p) g)) := norm_eq_l2norm_levelEnergy _
    _ ≤ l2norm ((Q ^ p) *ᵥ levelEnergy g) := hmono
    _ ≤ C * l2norm (levelEnergy g) := hC _ (fun i => levelEnergy_nonneg _ i)
    _ = C * ‖g‖ := by rw [← norm_eq_l2norm_levelEnergy]

end Parseval

/-!
## Section 5: (d) the weighted row-sum bound, in power form (THEOREM.md I.4)

> **I.4 (weighted row sum).** `Q` is nonnegative, so for the diagonal similarity
> `S = diag(2^0, ..., 2^{k-2})`:
> `rho(Q) = rho(S Q S^{-1}) <= ||S Q S^{-1}||_inf = max_a sum_b Q[a,b] 2^{a-b} = cert(k)`.

We prove the statement `S Q S^{-1}` row-sum bound *iterated `p` times*, which is what the
`p`-th-power interface of `OperatorChain` consumes, and which needs no spectral radius: with
`c := max_a ∑_b Q[a,b] 2^{a-b}`,

`(Q^p x)_a ≤ c^p 2^{-a} · max_b (2^b x_b)`  for entrywise-nonnegative `x`.

`2^{a-b}` is written `2^a / 2^b` (equal for natural `a, b`, and avoids `zpow`).
-/

section Weighted

variable {K : ℕ}

/-- **I.4, power form (the induction).** `2^a (Q^p x)_a ≤ c^p D`, where `D` bounds the weighted
coordinates `2^b x_b` and `c` bounds the weighted row sums `∑_b Q[a,b] 2^{a-b}`.

This is exactly "`||S Q S^{-1}||_inf ≤ c` iterates to `||(S Q S^{-1})^p||_inf ≤ c^p`", written
out on vectors so that no matrix-norm API is needed. -/
theorem weighted_mulVec_pow_le (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (c : ℝ) (hc : ∀ a : Fin K, ∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) ≤ c)
    {x : Fin K → ℝ} (hx : ∀ i, 0 ≤ x i) {D : ℝ} (hD : ∀ b : Fin K, (2 : ℝ) ^ (b : ℕ) * x b ≤ D) :
    ∀ (p : ℕ) (a : Fin K), (2 : ℝ) ^ (a : ℕ) * ((Q ^ p) *ᵥ x) a ≤ c ^ p * D := by
  have hc0 : ∀ a : Fin K, (0 : ℝ) ≤ c := fun a =>
    le_trans (Finset.sum_nonneg fun b _ => mul_nonneg (hQ0 a b) (by positivity)) (hc a)
  have hD0 : ∀ a : Fin K, (0 : ℝ) ≤ D := fun a =>
    le_trans (mul_nonneg (by positivity) (hx a)) (hD a)
  intro p
  induction p with
  | zero => intro a; simpa [Matrix.one_mulVec] using hD a
  | succ n ih =>
      intro a
      have hcn : (0 : ℝ) ≤ c ^ n * D := mul_nonneg (pow_nonneg (hc0 a) n) (hD0 a)
      set y : Fin K → ℝ := (Q ^ n) *ᵥ x with hy
      have hsplit : ((Q ^ (n + 1)) *ᵥ x) a = ∑ b, Q a b * y b := by
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        simp [Matrix.mulVec, dotProduct, hy]
      have hterm : ∀ b : Fin K,
          (2 : ℝ) ^ (a : ℕ) * (Q a b * y b)
            = (Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ))) * ((2 : ℝ) ^ (b : ℕ) * y b) := by
        intro b
        have h2 : ((2 : ℝ) ^ (b : ℕ)) ≠ 0 := by positivity
        field_simp
      calc (2 : ℝ) ^ (a : ℕ) * ((Q ^ (n + 1)) *ᵥ x) a
          = ∑ b, (Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ))) * ((2 : ℝ) ^ (b : ℕ) * y b) := by
            rw [hsplit, Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => hterm b
        _ ≤ ∑ b, (Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ))) * (c ^ n * D) :=
            Finset.sum_le_sum fun b _ =>
              mul_le_mul_of_nonneg_left (ih b) (mul_nonneg (hQ0 a b) (by positivity))
        _ = (∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ))) * (c ^ n * D) := by
            rw [Finset.sum_mul]
        _ ≤ c * (c ^ n * D) := mul_le_mul_of_nonneg_right (hc a) hcn
        _ = c ^ (n + 1) * D := by ring

/-- **I.4, power form as consumed.** `(Q^p x)_a ≤ c^p 2^{-a} D`, i.e. the `2^{-a}` decay
profile is reproduced at every power. -/
theorem mulVec_pow_le_of_weighted (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (c : ℝ) (hc : ∀ a : Fin K, ∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) ≤ c)
    {x : Fin K → ℝ} (hx : ∀ i, 0 ≤ x i) {D : ℝ} (hD : ∀ b : Fin K, (2 : ℝ) ^ (b : ℕ) * x b ≤ D)
    (p : ℕ) (a : Fin K) : ((Q ^ p) *ᵥ x) a ≤ c ^ p * D / 2 ^ (a : ℕ) := by
  have h := weighted_mulVec_pow_le Q hQ0 c hc hx hD p a
  have h2 : (0 : ℝ) < 2 ^ (a : ℕ) := by positivity
  rw [le_div_iff₀ h2]
  linarith [h]

/-- The explicit dimension constant `C_K = √K · 2^K`.

`√K` comes from `‖·‖₂ ≤ √K ‖·‖_∞` and `2^K` from `max_b 2^b x_b ≤ 2^K ‖x‖₂`. It is *not*
optimised - a sharper `(2/√3) 2^{K-1}` is available from summing the `4^{-a}` profile - because
it is raised to the power `1/p` in the only place it is used, and `C_K^{1/p} → 1`. -/
noncomputable def dimConst (K : ℕ) : ℝ := Real.sqrt K * 2 ^ K

theorem dimConst_pos (hK : 0 < K) : 0 < dimConst K := by
  have h1 : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.mpr (by exact_mod_cast hK)
  have h2 : (0 : ℝ) < 2 ^ K := by positivity
  exact mul_pos h1 h2

/-- **I.4 + I.3(c).** `‖Q^p x‖₂ ≤ C_K c^p ‖x‖₂` for entrywise-nonnegative `x`, with the explicit
dimension constant `C_K = dimConst K`. This is the `C` that §4 wants. -/
theorem l2norm_mulVec_pow_le (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (c : ℝ) (hc : ∀ a : Fin K, ∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) ≤ c)
    (p : ℕ) {x : Fin K → ℝ} (hx : ∀ i, 0 ≤ x i) :
    l2norm ((Q ^ p) *ᵥ x) ≤ dimConst K * c ^ p * l2norm x := by
  have ha0 : Fin K := ⟨0, hK⟩
  have hc0 : (0 : ℝ) ≤ c :=
    le_trans (Finset.sum_nonneg fun b _ => mul_nonneg (hQ0 ha0 b) (by positivity)) (hc ha0)
  set D : ℝ := 2 ^ K * l2norm x with hDdef
  have hD0 : (0 : ℝ) ≤ D := by
    have := l2norm_nonneg x
    positivity
  have hD : ∀ b : Fin K, (2 : ℝ) ^ (b : ℕ) * x b ≤ D := by
    intro b
    have h1 : (2 : ℝ) ^ (b : ℕ) ≤ 2 ^ K := by
      apply pow_le_pow_right₀ (by norm_num)
      exact le_of_lt b.isLt
    have h2 : x b ≤ l2norm x := le_l2norm hx b
    calc (2 : ℝ) ^ (b : ℕ) * x b ≤ 2 ^ K * x b := by
          exact mul_le_mul_of_nonneg_right h1 (hx b)
      _ ≤ 2 ^ K * l2norm x := by
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
  -- every coordinate of `Q^p x` is nonnegative and bounded by `c^p D`
  have hnn : ∀ i, 0 ≤ ((Q ^ p) *ᵥ x) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (matrix_pow_nonneg Q hQ0 p i j) (hx j)
  have hub : ∀ i, ((Q ^ p) *ᵥ x) i ≤ c ^ p * D := by
    intro i
    have h := weighted_mulVec_pow_le Q hQ0 c hc hx hD p i
    have h2 : (1 : ℝ) ≤ 2 ^ (i : ℕ) := one_le_pow₀ (by norm_num)
    nlinarith [hnn i, h, h2]
  have hM0 : (0 : ℝ) ≤ c ^ p * D := mul_nonneg (pow_nonneg hc0 p) hD0
  calc l2norm ((Q ^ p) *ᵥ x) ≤ Real.sqrt K * (c ^ p * D) :=
        l2norm_le_sqrt_card_mul hnn hM0 hub
    _ = dimConst K * c ^ p * l2norm x := by
        rw [dimConst, hDdef]; ring

end Weighted

/-!
## Section 6: the composition with `OperatorChain` (I.1 + I.2 + I.3 + I.4)

`OperatorChain.norm_eigenvalue_le_of_compression_pow_bound` takes column-stochasticity
(`φ ∘ₗ T = φ`, i.e. `1ᵀ T = 1ᵀ`) plus a bound `‖(T|_V)^p x‖ ≤ C ‖x‖` and returns `‖μ‖^p ≤ C`
for every eigenvalue `μ ≠ 1`. Sections 2-5 of this file are precisely the supplier of that `C`.

Composed and taking `p → ∞` (the `C_K^{1/p} → 1` step, done here as an elementary contradiction
rather than a limit) this gives the headline of `THEOREM.md` Part I in abstract form:

`|lambda_2(T)| <= cert`,  `cert := max_a sum_b Q[a,b] 2^{a-b}`,

with **no** spectral radius, **no** Gelfand formula, and **no** normality/diagonalisability
input anywhere in the chain.
-/

section Composition

variable {K : ℕ} {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, NormedSpace ℂ (G m)]

/-- **(c) + (d).** The operator bound in exactly the shape `OperatorChain`'s `hC` hypothesis
wants: `‖B^p g‖ ≤ C_K c^p ‖g‖`. -/
theorem norm_pow_le_dimConst_mul (hK : 0 < K) (B : Module.End ℂ (PiLp 2 G))
    (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ : ∀ (m : Fin K) (y : G m) (m' : Fin K), ‖(B (levelSingle m y)) m'‖ ≤ Q m' m * ‖y‖)
    (hQ0 : ∀ i j, 0 ≤ Q i j) (c : ℝ)
    (hc : ∀ a : Fin K, ∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) ≤ c)
    (p : ℕ) (g : PiLp 2 G) : ‖(B ^ p) g‖ ≤ dimConst K * c ^ p * ‖g‖ :=
  norm_pow_le_of_matrixBound B Q hQ hQ0 p (dimConst K * c ^ p)
    (fun _ hx => l2norm_mulVec_pow_le hK Q hQ0 c hc p hx) g

/-- **THEOREM.md Part I, abstract form: `|lambda_2(T)| <= cert`.**

Hypotheses, in the order they appear:
* `hT : φ ∘ₗ T = φ` - I.1's column-stochasticity `1ᵀ T = 1ᵀ`. Nothing else about `T`: no double
  stochasticity, no `T J = J`, no uniform stationary distribution, no normality.
* `e` - the orthogonal level decomposition of the mean-zero space `V = ker φ`, presented as a
  linear isometry onto `⨁_m G m` (see the representation note in the header).
* `hQ` - the block norms: `‖P_{m'} (T|_V) P_m‖ ≤ Q[m',m]`. This is the only place the specific
  operator enters, and for the Syracuse operator it is Lemma A + Lemma B (out of scope here).
* `hQ0` - `Q` entrywise nonnegative (I.3, "`Q` is nonnegative").
* `hc` - `∑_b Q[a,b] 2^{a-b} ≤ c` for every row `a` (I.4, `c = cert(k)`).

Conclusion: every eigenvalue `μ ≠ 1` of `T` satisfies `‖μ‖ ≤ c`. -/
theorem norm_eigenvalue_le_cert {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ : F →ₗ[ℂ] ℂ} {T : Module.End ℂ F} (hT : φ ∘ₗ T = φ) (hK : 0 < K)
    (e : (LinearMap.ker φ) ≃ₗᵢ[ℂ] PiLp 2 G)
    (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (hQ : ∀ (m : Fin K) (y : G m) (m' : Fin K),
      ‖(e ((OperatorChain.compression hT) (e.symm (levelSingle m y)))) m'‖ ≤ Q m' m * ‖y‖)
    (c : ℝ) (hc : ∀ a : Fin K, ∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) ≤ c)
    {μ : ℂ} (hμ : μ ≠ 1) {v : F} (hv0 : v ≠ 0) (hv : T v = μ • v) :
    ‖μ‖ ≤ c := by
  classical
  set A : Module.End ℂ (LinearMap.ker φ) := OperatorChain.compression hT with hA
  set B : Module.End ℂ (PiLp 2 G) :=
    (e.toLinearEquiv.toLinearMap) ∘ₗ A ∘ₗ (e.symm.toLinearEquiv.toLinearMap) with hB
  have hBapp : ∀ y, B y = e (A (e.symm y)) := fun _ => rfl
  have hQB : ∀ (m : Fin K) (y : G m) (m' : Fin K),
      ‖(B (levelSingle m y)) m'‖ ≤ Q m' m * ‖y‖ := by
    intro m y m'
    rw [hBapp]
    exact hQ m y m'
  -- conjugation intertwines the powers
  have key : ∀ (p : ℕ) (x : LinearMap.ker φ), e ((A ^ p) x) = (B ^ p) (e x) := by
    intro p
    induction p with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        have h1 : (A ^ (n + 1)) x = (A ^ n) (A x) := by rw [pow_succ]; rfl
        have h2 : (B ^ (n + 1)) (e x) = (B ^ n) (B (e x)) := by rw [pow_succ]; rfl
        rw [h1, h2, ih (A x), hBapp]
        simp
  have hpow : ∀ p : ℕ, ∀ x : LinearMap.ker φ,
      ‖((OperatorChain.compression hT) ^ p) x‖ ≤ (dimConst K * c ^ p) * ‖x‖ := by
    intro p x
    have h1 : ‖(A ^ p) x‖ = ‖(B ^ p) (e x)‖ := by rw [← key p x]; exact (e.norm_map _).symm
    have h2 := norm_pow_le_dimConst_mul hK B Q hQB hQ0 c hc p (e x)
    rw [e.norm_map] at h2
    rw [← hA]
    rw [h1]
    exact h2
  have hmu : ∀ p : ℕ, ‖μ‖ ^ p ≤ dimConst K * c ^ p := fun p =>
    OperatorChain.norm_eigenvalue_le_of_compression_pow_bound hT p _ (hpow p) hμ hv0 hv
  -- `C_K^{1/p} → 1`, done as a contradiction so that no limit API is needed
  by_contra hcon
  push_neg at hcon
  have hc0 : (0 : ℝ) ≤ c :=
    le_trans (Finset.sum_nonneg fun b _ => mul_nonneg (hQ0 ⟨0, hK⟩ b) (by positivity))
      (hc ⟨0, hK⟩)
  have hmu0 : (0 : ℝ) < ‖μ‖ := lt_of_le_of_lt hc0 hcon
  have hd : (0 : ℝ) < dimConst K := dimConst_pos hK
  have ht1 : c / ‖μ‖ < 1 := (div_lt_one hmu0).mpr hcon
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hd) ht1
  have hpos : (0 : ℝ) < ‖μ‖ ^ n := pow_pos hmu0 n
  have h2 : (1 : ℝ) ≤ dimConst K * (c / ‖μ‖) ^ n := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos, one_mul]
    exact hmu n
  have h3 : dimConst K * (c / ‖μ‖) ^ n < 1 := by
    have := mul_lt_mul_of_pos_left hn hd
    rwa [mul_inv_cancel₀ (ne_of_gt hd)] at this
  linarith

/-!
### The adjoint bridge (THEOREM.md I.2) - and the orientation trap it closes

**Self-adversarial finding, recorded.** `norm_eigenvalue_le_cert` above is stated for the block
matrix of *the operator it is applied to*, namely the compression `A = T|_V`. `THEOREM.md`
defines `Q[a,b] := ||P_a U_k P_b||` for `U = T^T`, and `cert(k) := max_a sum_b Q[a,b] 2^{a-b}`.
Those are **transposes of each other**: `||P_a A P_b|| = ||(P_a A P_b)^*|| = ||P_b U_V P_a||`, so
the block matrix of `A` is `Q^T`, and a weighted *row* sum of `Q^T` is a weighted *column* sum of
`Q`. Feeding `THEOREM.md`'s `Q` to `norm_eigenvalue_le_cert` unchanged would therefore bound
`|lambda_2|` by the weighted **column**-sum of `Q` - a different number from `cert(k)`, and one
the paper never estimates.

This is exactly the step `THEOREM.md` I.2 takes and the reason it takes it:

> **I.2 (adjoint and Gelfand).** `A = P_V T P_V` on `V`, so `A^* = P_V U P_V =: U_V` with
> `U = T^T`, and `rho(A) = rho(U_V)`.

The paper crosses that bridge with `rho(A) = rho(U_V)`. The two theorems below cross it without
any spectral radius: from `<A x, y> = <x, U y>` alone (which is what `A^* = U_V` means), a power
bound on `U` transfers verbatim to `A`, by one Cauchy-Schwarz. So `norm_eigenvalue_le_cert_adjoint`
below is the version that consumes `THEOREM.md`'s `Q` in `THEOREM.md`'s orientation.
-/

section AdjointBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open RCLike

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-- `<A x, y> = <x, U y>` propagates to all powers: `<A^p x, y> = <x, U^p y>`. This is
`(A^p)^* = (A^*)^p`, stated without ever forming an adjoint. -/
theorem inner_pow_adjoint (A U : Module.End ℂ H) (hadj : ∀ x y, ⟪A x, y⟫ = ⟪x, U y⟫) :
    ∀ (p : ℕ) (x y : H), ⟪(A ^ p) x, y⟫ = ⟪x, (U ^ p) y⟫ := by
  intro p
  induction p with
  | zero => intro x y; simp
  | succ n ih =>
      intro x y
      have h1 : (A ^ (n + 1)) x = (A ^ n) (A x) := by rw [pow_succ]; rfl
      have h2 : (U ^ (n + 1)) y = U ((U ^ n) y) := by rw [pow_succ']; rfl
      rw [h1, h2, ih (A x) y, hadj x ((U ^ n) y)]

/-- **I.2, the adjoint bridge, without spectral radius.** If `A^* = U` then any bound on `U^p`
is a bound on `A^p`, with the same constant.

Proof: `‖A^p x‖² = re <A^p x, A^p x> = re <x, U^p (A^p x)> ≤ ‖x‖ ‖U^p (A^p x)‖ ≤ C ‖x‖ ‖A^p x‖`. -/
theorem norm_pow_le_of_adjoint_bound (A U : Module.End ℂ H) (hadj : ∀ x y, ⟪A x, y⟫ = ⟪x, U y⟫)
    (p : ℕ) (C : ℝ) (hC : ∀ y, ‖(U ^ p) y‖ ≤ C * ‖y‖) (x : H) : ‖(A ^ p) x‖ ≤ C * ‖x‖ := by
  rcases eq_or_lt_of_le (norm_nonneg ((A ^ p) x)) with h0 | hpos
  · have hC0 : 0 ≤ C * ‖x‖ := by
      rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hxpos
      · rw [← hx0, mul_zero]
      · nlinarith [hC x, norm_nonneg ((U ^ p) x)]
    rw [← h0]; exact hC0
  · have hsq : ‖(A ^ p) x‖ ^ 2 = re ⟪x, (U ^ p) ((A ^ p) x)⟫ := by
      rw [← inner_pow_adjoint A U hadj p x ((A ^ p) x)]
      exact (inner_self_eq_norm_sq _).symm
    have hCS : re ⟪x, (U ^ p) ((A ^ p) x)⟫ ≤ ‖x‖ * ‖(U ^ p) ((A ^ p) x)‖ :=
      re_inner_le_norm x _
    have hb : ‖(U ^ p) ((A ^ p) x)‖ ≤ C * ‖(A ^ p) x‖ := hC _
    have : ‖(A ^ p) x‖ ^ 2 ≤ (C * ‖x‖) * ‖(A ^ p) x‖ := by
      calc ‖(A ^ p) x‖ ^ 2 = re ⟪x, (U ^ p) ((A ^ p) x)⟫ := hsq
        _ ≤ ‖x‖ * ‖(U ^ p) ((A ^ p) x)‖ := hCS
        _ ≤ ‖x‖ * (C * ‖(A ^ p) x‖) := by
            exact mul_le_mul_of_nonneg_left hb (norm_nonneg x)
        _ = (C * ‖x‖) * ‖(A ^ p) x‖ := by ring
    nlinarith [this, hpos]

end AdjointBridge

section CompositionAdjoint

variable {K : ℕ} {G : Fin K → Type*} [∀ m, NormedAddCommGroup (G m)] [∀ m, NormedSpace ℂ (G m)]

/-- **THEOREM.md Part I, in `THEOREM.md`'s own orientation: `|lambda_2(T)| <= cert(k)`.**

Identical to `norm_eigenvalue_le_cert` except that the block bounds `hQ` are those of `U`, the
adjoint (Koopman) partner of the compression `A = T|_V`, related to it by `hadj`. `Q[m',m]` is
then literally `THEOREM.md`'s `||P_{m'} U_V P_m||` and `c` is literally
`cert = max_a sum_b Q[a,b] 2^{a-b}`. -/
theorem norm_eigenvalue_le_cert_adjoint {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] {φ : F →ₗ[ℂ] ℂ} {T : Module.End ℂ F} (hT : φ ∘ₗ T = φ) (hK : 0 < K)
    (U : Module.End ℂ (LinearMap.ker φ))
    -- `hadj` says exactly `A^* = U`; on a finite-dimensional `ker φ` it is satisfied by
    -- `U := ContinuousLinearMap.adjoint A`, so this hypothesis is never an obstruction.
    (hadj : ∀ x y : LinearMap.ker φ,
      @inner ℂ _ _ ((OperatorChain.compression hT) x) y = @inner ℂ _ _ x (U y))
    (e : (LinearMap.ker φ) ≃ₗᵢ[ℂ] PiLp 2 G)
    (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (hQ : ∀ (m : Fin K) (y : G m) (m' : Fin K),
      ‖(e (U (e.symm (levelSingle m y)))) m'‖ ≤ Q m' m * ‖y‖)
    (c : ℝ) (hc : ∀ a : Fin K, ∑ b, Q a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) ≤ c)
    {μ : ℂ} (hμ : μ ≠ 1) {v : F} (hv0 : v ≠ 0) (hv : T v = μ • v) :
    ‖μ‖ ≤ c := by
  classical
  set A : Module.End ℂ (LinearMap.ker φ) := OperatorChain.compression hT with hA
  set B : Module.End ℂ (PiLp 2 G) :=
    (e.toLinearEquiv.toLinearMap) ∘ₗ U ∘ₗ (e.symm.toLinearEquiv.toLinearMap) with hB
  have hBapp : ∀ y, B y = e (U (e.symm y)) := fun _ => rfl
  have hQB : ∀ (m : Fin K) (y : G m) (m' : Fin K),
      ‖(B (levelSingle m y)) m'‖ ≤ Q m' m * ‖y‖ := by
    intro m y m'; rw [hBapp]; exact hQ m y m'
  have key : ∀ (p : ℕ) (x : LinearMap.ker φ), e ((U ^ p) x) = (B ^ p) (e x) := by
    intro p
    induction p with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        have h1 : (U ^ (n + 1)) x = (U ^ n) (U x) := by rw [pow_succ]; rfl
        have h2 : (B ^ (n + 1)) (e x) = (B ^ n) (B (e x)) := by rw [pow_succ]; rfl
        rw [h1, h2, ih (U x), hBapp]
        simp
  -- bound on `U^p` from §2-§5
  have hUpow : ∀ p : ℕ, ∀ x : LinearMap.ker φ, ‖(U ^ p) x‖ ≤ (dimConst K * c ^ p) * ‖x‖ := by
    intro p x
    have h1 : ‖(U ^ p) x‖ = ‖(B ^ p) (e x)‖ := by rw [← key p x]; exact (e.norm_map _).symm
    have h2 := norm_pow_le_dimConst_mul hK B Q hQB hQ0 c hc p (e x)
    rw [e.norm_map] at h2
    rw [h1]; exact h2
  -- transfer to `A = T|_V` through the adjoint relation (THEOREM.md I.2)
  have hpow : ∀ p : ℕ, ∀ x : LinearMap.ker φ,
      ‖((OperatorChain.compression hT) ^ p) x‖ ≤ (dimConst K * c ^ p) * ‖x‖ := by
    intro p x
    rw [← hA]
    exact norm_pow_le_of_adjoint_bound A U hadj p _ (hUpow p) x
  have hmu : ∀ p : ℕ, ‖μ‖ ^ p ≤ dimConst K * c ^ p := fun p =>
    OperatorChain.norm_eigenvalue_le_of_compression_pow_bound hT p _ (hpow p) hμ hv0 hv
  by_contra hcon
  push_neg at hcon
  have hc0 : (0 : ℝ) ≤ c :=
    le_trans (Finset.sum_nonneg fun b _ => mul_nonneg (hQ0 ⟨0, hK⟩ b) (by positivity))
      (hc ⟨0, hK⟩)
  have hmu0 : (0 : ℝ) < ‖μ‖ := lt_of_le_of_lt hc0 hcon
  have hd : (0 : ℝ) < dimConst K := dimConst_pos hK
  have ht1 : c / ‖μ‖ < 1 := (div_lt_one hmu0).mpr hcon
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hd) ht1
  have hpos : (0 : ℝ) < ‖μ‖ ^ n := pow_pos hmu0 n
  have h2 : (1 : ℝ) ≤ dimConst K * (c / ‖μ‖) ^ n := by
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos, one_mul]
    exact hmu n
  have h3 : dimConst K * (c / ‖μ‖) ^ n < 1 := by
    have := mul_lt_mul_of_pos_left hn hd
    rwa [mul_inv_cancel₀ (ne_of_gt hd)] at this
  linarith

end CompositionAdjoint

end Composition

/-!
## Section 7: calibration at `K = 2` (standing gate 2)

An abstract file with no instantiation is not evidence that its hypotheses are satisfiable.
This section pins the chain to an explicit `2 x 2` nonnegative `Q` and an explicit operator, and
checks the general theorems against a value computed by hand.

```
Q = [[1/4, 1/2],
     [0  , 1/4]]

cert:  row 0:  1/4 * 2^(0-0) + 1/2 * 2^(0-1)  =  1/4 + 1/4  =  1/2
       row 1:  0   * 2^(1-0) + 1/4 * 2^(1-1)  =  0   + 1/4  =  1/4      so c = 1/2

Q^2  = [[1/16, 1/4],
        [0   , 1/16]]                         (by hand: (Q^2)[0,1] = 1/4*1/2 + 1/2*1/4 = 1/4)

x = (1,1),  D = max_b 2^b x_b = 2

Q^2 x = (1/16 + 1/4, 1/16) = (5/16, 1/16)     <- the hand-computed reference value

I.4 power bound at p = 2:   2^a (Q^2 x)_a  <=  c^2 D  =  1/4 * 2  =  1/2
   a = 0:  1 * 5/16 = 0.3125  <=  0.5     (slack 0.1875)
   a = 1:  2 * 1/16 = 0.125   <=  0.5     (slack 0.375)
```

**Anti-vacuity note (the failure mode this gate exists to catch), graded honestly.**

* `calib_hand_value` and `calib_slack` are pure arithmetic. `norm_num` alone discharges them.
  They are **not evidence**; they are the reference value the general bound is checked against.
* `calib_weighted_bound` is *also* arithmetically decidable in principle - the numbers are
  concrete. What makes it worth having is not its statement but its **proof**, which runs through
  `weighted_mulVec_pow_le` and therefore forces `Qcal_nonneg`, `Qcal_cert`, `xcal_nonneg` and
  `xcal_weight` to be genuinely satisfied. A general theorem with unsatisfiable hypotheses could
  not be instantiated at all. Grade: satisfiability witness, not independent evidence.
* `calib_operator_bound` is the one piece here that `norm_num`, `simp`, `decide` and `omega`
  cannot touch: it bounds `‖B² g‖` for an **arbitrary** `g` in an infinite-cardinality space, with
  an irrational constant `√2 · 4 · (1/2)²`. Its only possible proof is the abstract chain (a) →
  (b) → (c) → (d). Grade: real evidence that §2-§6 is non-vacuous on the operator side.

**Orientation discrimination (the referee's question (ii)).** The calibration is not
convention-blind: `Qcal` is deliberately non-symmetric, and the transposed reading gives
different numbers at every step. With `Qcalᵀ = [[1/4,0],[1/2,1/4]]` one gets
`(Qcalᵀ)² x = (1/16, 5/16)` instead of `(5/16, 1/16)`, and weighted row sums `(1/4, 5/4)` instead
of `(1/2, 1/4)`, i.e. `c = 5/4 > 1` instead of `c = 1/2`. So if the `mulVec` orientation or the
`Q^p` convention below were transposed, `calib_weighted_bound` would be **false**, not merely
differently-worded. Independently cross-checked against an exact-rational enumeration
(`python`, `fractions.Fraction`): `Q² x = (5/16, 1/16)`, `c = 1/2`, `D = 2`, bound `c²D = 1/2`,
actual `(5/16, 1/8)` - matching the Lean statements term for term.
-/

section Calibration

open Matrix

/-- The calibration matrix: nonnegative, strictly upper-triangular decay, `cert = 1/2`. -/
noncomputable def Qcal : Matrix (Fin 2) (Fin 2) ℝ := !![1/4, 1/2; 0, 1/4]

/-- The calibration vector `x = (1,1)`. -/
noncomputable def xcal : Fin 2 → ℝ := ![1, 1]

theorem Qcal_nonneg : ∀ i j, 0 ≤ Qcal i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Qcal]

theorem Qcal_cert : ∀ a : Fin 2, ∑ b, Qcal a b * ((2 : ℝ) ^ (a : ℕ) / 2 ^ (b : ℕ)) ≤ 1 / 2 := by
  intro a
  fin_cases a <;> simp [Qcal, Fin.sum_univ_two] <;> norm_num

theorem xcal_nonneg : ∀ i, 0 ≤ xcal i := by
  intro i; fin_cases i <;> simp [xcal]

theorem xcal_weight : ∀ b : Fin 2, (2 : ℝ) ^ (b : ℕ) * xcal b ≤ 2 := by
  intro b; fin_cases b <;> simp [xcal]

/-- **Hand-computed reference value.** `Q^2 x = (5/16, 1/16)`.

This is arithmetic only and proves nothing on its own - it is the number the general bound is
checked against. -/
theorem calib_hand_value : (Qcal ^ 2) *ᵥ xcal = ![5 / 16, 1 / 16] := by
  rw [pow_two]
  ext i
  fin_cases i <;>
    simp [Qcal, xcal, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

/-- **The general theorem, instantiated.** The proof runs entirely through
`weighted_mulVec_pow_le`; it does not compute `Q^2 x`. -/
theorem calib_weighted_bound :
    ∀ a : Fin 2, (2 : ℝ) ^ (a : ℕ) * ((Qcal ^ 2) *ᵥ xcal) a ≤ 1 / 2 := by
  intro a
  have h := weighted_mulVec_pow_le Qcal Qcal_nonneg (1 / 2) Qcal_cert xcal_nonneg
    (D := 2) xcal_weight 2 a
  calc (2 : ℝ) ^ (a : ℕ) * ((Qcal ^ 2) *ᵥ xcal) a ≤ (1 / 2 : ℝ) ^ 2 * 2 := h
    _ = 1 / 2 := by norm_num

/-- The bound is **not tight**, i.e. not vacuously an equality: at row `0` the general bound
gives `1/2` while the true value is `5/16`. Both facts are needed - correctness (the bound
holds) and non-degeneracy (it is not `x ≤ x`). -/
theorem calib_slack : ((Qcal ^ 2) *ᵥ xcal) 0 < 1 / 2 := by
  rw [calib_hand_value]; norm_num

/-! ### The operator side: an explicit `B` whose block norms are exactly `Qcal`

`G m := ℂ` for both levels, and `B` is the `Qcal`-action. This exhibits a non-trivial
inhabitant of the `hQ` hypothesis of `levelSplit` / `norm_pow_le_dimConst_mul`, so the abstract
chain of §2-§6 is shown to be non-vacuous on the operator side too, not only on the matrix side.
-/

/-- The `Qcal`-action on the decomposed space `⨁_{m<2} ℂ`. -/
noncomputable def Bcal : Module.End ℂ (PiLp 2 (fun _ : Fin 2 => ℂ)) where
  toFun g := WithLp.toLp 2 (fun m' => ∑ m, (Qcal m' m : ℂ) * g m)
  map_add' g h := by
    ext m'
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a g := by
    ext m'
    simp
    ring

theorem Bcal_apply (g : PiLp 2 (fun _ : Fin 2 => ℂ)) (m' : Fin 2) :
    (Bcal g) m' = ∑ m, (Qcal m' m : ℂ) * g m := rfl

/-- The block bounds of `Bcal` are exactly `Qcal` - the `hQ` hypothesis, satisfied. -/
theorem Bcal_block (m : Fin 2) (y : ℂ) (m' : Fin 2) :
    ‖(Bcal (levelSingle m y)) m'‖ ≤ Qcal m' m * ‖y‖ := by
  have h : (Bcal (levelSingle (G := fun _ : Fin 2 => ℂ) m y)) m' = (Qcal m' m : ℂ) * y := by
    rw [Bcal_apply]
    simp [levelSingle, Finset.sum_ite_eq, eq_comm]
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Qcal_nonneg m' m)]

/-- **The full chain, instantiated.** `‖B² g‖ ≤ C_2 · (1/2)² · ‖g‖` with `C_2 = √2 · 4`.

The proof is a single application of `norm_pow_le_dimConst_mul`, which internally uses (a), (b),
(c) and (d). It cannot be discharged by `norm_num`, `simp` or `omega`. -/
theorem calib_operator_bound (g : PiLp 2 (fun _ : Fin 2 => ℂ)) :
    ‖(Bcal ^ 2) g‖ ≤ Real.sqrt 2 * 4 * (1 / 2 : ℝ) ^ 2 * ‖g‖ := by
  have h := norm_pow_le_dimConst_mul (by norm_num) Bcal Qcal Bcal_block Qcal_nonneg
    (1 / 2) Qcal_cert 2 g
  have hd : dimConst 2 = Real.sqrt 2 * 4 := by
    rw [dimConst]; norm_num
  rwa [hd] at h

end Calibration

end LevelMajorisation
