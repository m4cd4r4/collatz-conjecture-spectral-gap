/-
# L13: `hQupper` reduced to a single named residue — the clean within-level bound

## SCOPE DECLARED UP FRONT: **E1**, and E1 only.

Two scopes were offered:

* **E1** — assemble `hQupper` from the *clean* bound taken as a hypothesis, so that the clean
  bound replaces `hQupper` as the single named residue.
* **E2** — E1 **plus** a proof of the clean bound, closing `hQupper` outright.

**This file lands E1. `hQupper` is NOT discharged _by this file_.** (STATUS 2026-08-03: it is
discharged by `GramIdentity.lean`, which proves this file's (CLEAN) hypothesis outright. The
scope statement below remains true OF THIS FILE and is left standing as the audit trail.)
`ManifestInstance.gap_certificate_concrete`
still has an undischarged hypothesis; what changes is *which* hypothesis, and §6 records exactly
where the clean bound stalls. Nothing below should be read as "`hQupper` is closed" — it is not.

--------------------------------------------------------------------------------
## §0. What E1 is, precisely
--------------------------------------------------------------------------------

`ManifestInstance.facts_of_hQupper` takes as its sole hypothesis, for `a < b`:

```
Qmat k a b ≤ s^(b-a) + s^(a+1) * Assembly.levelVec (gcVec …) b        (hQupper)
```

with `Qmat k a b = ‖P_a ∘ U_full ∘ P_b‖` the operator norm of a level block of the **full**
`U = (T_k)ᵀ`. `DefectSplit.U_split` splits `U_full = U_clean + D` with `D` the rank-one
`e_{r*} ⊗ c*`, so the triangle inequality for operator norms gives

```
‖P_a U_full P_b‖ ≤ ‖P_a U_clean P_b‖ + ‖P_a D P_b‖.
```

The **second** term is already exactly the second summand of `hQupper`, from two theorems that
already exist:

* `DefectSplit.norm_P_single` — `‖P_a e_r‖ = Assembly.s^(a+1)` for **every** `r`;
* `ManifestInstance.levelVec_gcVec` — `Assembly.levelVec (gcVec …) b = ‖P_b c*‖`.

§3 below proves `‖P_a D P_b‖ ≤ s^(a+1) · ‖P_b c*‖` from those, for **all** `a, b` — note this
needs no ordering hypothesis at all, unlike `DefectSplit.norm_P_U_P_le`, which is about the full
`U` and therefore has to kill the clean part with `b ≤ a` first. That asymmetry is the whole
reason the same rank-one estimate is available in the `a < b` regime.

The **first** term is the entire residue. §4 states it as a hypothesis

```
hclean : ∀ a b, a < b → ‖cleanBlockCLM k a b‖ ≤ Assembly.s ^ (b - a)                (CLEAN)
```

and §5 delivers `THEOREM.md`'s boxed conclusion for the concrete `T_k` conditional on (CLEAN)
and nothing else.

### Why this is a strictly better statement of the same debt

`hQupper` mixes three things: the clean operator, the defect operator, and the identification
of `levelVec gc` with `‖P_b c*‖`. Two of the three are now theorems. (CLEAN) is a statement
about `U_clean` alone — no defect, no `gc`, no `Q` — which is what `HALFSHIFT_S4_LEMMA_A_PROOF.md`
actually proves on paper. The debt is the same size mathematically and strictly smaller in
surface area.

### A withdrawn warning, recorded so it is not re-inherited

An earlier note in this track flagged that `hQupper`'s numerical slack shrinks by a factor of
exactly `4` per `k`, always at the top corner `(K-2, K-1)` with `d = 1`, and inferred that a
formalisation "cannot afford a lossy estimate". **That inference is wrong and is withdrawn**
(by the orchestrator, and independently confirmed by §1's measurements here). The triangle
route is exact: the margin *is* the triangle inequality's own slack, so it yields the bound
however thin the margin gets. Nothing below is contorted to chase tightness.

--------------------------------------------------------------------------------
## §1. Numerical calibration — run BEFORE any proving, from `TransferOperator.Tcount`
--------------------------------------------------------------------------------

Rebuilt independently in Python from `Tcount`'s own definition
(`syracuse(r + m·2^k) mod 2^k` over the lift window), target-first `T[u,r]`, `U = Tᵀ`, row
`idx (rstar k)` zeroed, `P_a` from the characters `χ_ξ(s) = w^{ξ(2s+1)}/√N`. Scripts live in
the session scratchpad, not the repo.

| `k` | `‖F*F − I‖` | `max_{a<b} \|‖P_a U_clean P_b‖ − 2^{-(b-a)/2}\|` | `max_{a,b} \|‖P_a D P_b‖ − ‖P_a e_{r*}‖·‖P_b c*‖\|` | min slack in `hQupper` | argmin |
|---|---|---|---|---|---|
| 4 | `1.1e-15` | `3.3e-16` | `3.3e-16` | `2.175e-02` | `(1,2)` |
| 5 | `1.2e-14` | `9.3e-15` | `4.8e-15` | `5.503e-03` | `(2,3)` |
| 6 | `8.3e-14` | `1.0e-13` | `2.7e-14` | `1.380e-03` | `(3,4)` |
| 7 | `1.0e-13` | `1.3e-13` | `3.9e-14` | `3.452e-04` | `(4,5)` |
| 8 | `9.7e-13` | `1.3e-12` | `3.2e-13` | `8.631e-05` | `(5,6)` |

Three facts this fixes, all of them used below:

1. **The clean bound is an EQUALITY**, `‖P_a U_clean P_b‖ = 2^{-(b-a)/2}`, not merely `≤`
   (column 3, agreeing with the orchestrator's independent `4.9e-14 / 6.6e-13 / 6.2e-12` at
   `k = 6, 8, 10`). Only `≤` is used below, and (CLEAN) is stated as `≤`; the equality is
   recorded because it says the residue is *sharp*, so no slack can be recovered there.
2. **The rank-one factorisation `‖P_a D P_b‖ = ‖P_a e_{r*}‖ · ‖P_b c*‖` is exact** at every
   `(a,b)` — including `a < b` — and `‖P_a e_{r*}‖ = s^{a+1}` (column 4 folds both checks).
   §3 proves the `≤` half, which is all that is needed.
3. **The assembled `hQupper` holds with the slack the orchestrator measured**: `+5.503e-3` at
   `k = 5`, decaying by a factor of exactly `4` per `k`, and the argmin is `(K-2, K-1)` — i.e.
   `d = 1` — at every `k` (column 6 against `K = k-1`). The thin corner is real; §0 records why
   it does not matter.

`k = 4` is included deliberately: it is where an index error is off by `~10^-1` rather than
`~10^-3` (`OperatorBlock` §0.1's corrected note on the guard weakening in `k`).

--------------------------------------------------------------------------------
## §2. Orientation
--------------------------------------------------------------------------------

Unchanged and load-bearing: target-first `T[u,r]`, `U = Tᵀ`, `U_clean` zeroes the **row**
`idx (rstar k)` of `U`, which is the `r*` **column** of `T`. `Qmat k a b` has `a` the target
level and `b` the source level. `cleanBlockCLM k a b` below is `P_a ∘ U_clean ∘ P_b` in that
same order, so it composes with `Qmat` without a transpose anywhere. Mutation M3 in §7 is the
shot at this.

Sorry-free, no `native_decide`. Mutation table §7, axiom audit §8.
-/

import ManifestInstance

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace CleanBlock

open Finset GapCertificate LemmaA CountingLemmas CollisionBound TransferOperator
open CharacterBasis BlockVanishing OperatorBlock DefectSplit ManifestInstance

/-!
--------------------------------------------------------------------------------
## §3. The two blocks, and the defect block's bound
--------------------------------------------------------------------------------
-/

/-- The **clean** level block `P_a U_clean P_b`, as a linear map. Same shape as
`ManifestInstance.blockOp`, with `Uendfull` replaced by its clean part `Uend`. -/
noncomputable def cleanBlockOp (k a b : ℕ) : Fsp k →ₗ[ℂ] Fsp k :=
  (P k a).comp ((Uend k).comp (P k b))

/-- The same as a continuous linear map, so that it has an operator norm. -/
noncomputable def cleanBlockCLM (k a b : ℕ) : Fsp k →L[ℂ] Fsp k :=
  LinearMap.toContinuousLinearMap (cleanBlockOp k a b)

@[simp] theorem cleanBlockCLM_apply (k a b : ℕ) (x : Fsp k) :
    cleanBlockCLM k a b x = P k a (Uend k (P k b x)) := rfl

/-- **The defect block's bound.** `‖P_a D P_b x‖ ≤ s^{a+1} · ‖P_b c*‖ · ‖P_b x‖`.

Two things to notice. First, there is **no ordering hypothesis on `a` and `b`** — `D` is
rank one whatever the levels are, so this is available in the `a < b` regime that
`DefectSplit.norm_P_U_P_le` (about the FULL `U`) cannot reach. Second, the two factors are
already theorems: `norm_P_single` supplies `s^{a+1}` for every `r`, and Cauchy-Schwarz against
`P_b` self-adjoint + idempotent supplies `‖P_b c*‖`. §1 column 4 measures this as an
**equality**; only `≤` is used. -/
theorem norm_P_D_P_le {k a b : ℕ} (hk : 1 ≤ k) (ha : a + 2 ≤ k) (x : Fsp k) :
    ‖P k a (Dend k (P k b x))‖
      ≤ Assembly.s ^ (a + 1) * ‖P k b (cvecE k)‖ * ‖P k b x‖ := by
  have hcoef : (@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)
      = @inner ℂ _ _ (P k b (cvecE k)) (P k b x) := by
    rw [P_selfadjoint hk b, P_idem hk]
  have hCS : ‖(@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)‖
      ≤ ‖P k b (cvecE k)‖ * ‖P k b x‖ := by
    rw [hcoef]; exact norm_inner_le_norm _ _
  rw [Dend_apply_eq hk, map_smul, norm_smul, norm_P_single ha]
  calc ‖(@inner ℂ _ _ (cvecE k) (P k b x) : ℂ)‖ * Assembly.s ^ (a + 1)
      ≤ (‖P k b (cvecE k)‖ * ‖P k b x‖) * Assembly.s ^ (a + 1) :=
        mul_le_mul_of_nonneg_right hCS (pow_nonneg Assembly.s_pos.le _)
    _ = Assembly.s ^ (a + 1) * ‖P k b (cvecE k)‖ * ‖P k b x‖ := by ring

/-!
--------------------------------------------------------------------------------
## §4. **THE REDUCTION**: `Q[a,b] ≤ ‖clean block‖ + s^{a+1}·‖P_b c*‖`
--------------------------------------------------------------------------------

The triangle inequality, applied pointwise and then promoted to operator norms with
`ContinuousLinearMap.opNorm_le_bound`. This holds for **all** `a, b` in range; the `a < b`
hypothesis appears only in §5, where it is used to invoke (CLEAN).
-/

/-- The splitting of a level block into clean part plus defect part, pointwise. -/
theorem block_split {k a b : ℕ} (hk : 1 ≤ k) (x : Fsp k) :
    blockCLM k a b x = P k a (Uend k (P k b x)) + P k a (Dend k (P k b x)) := by
  show P k a (Uendfull k (P k b x)) = _
  rw [Uendfull_split hk (P k b x), map_add]

/-- **THE REDUCTION.** For every `a, b` in the level range, `Q[a,b]` is at most the operator
norm of the clean block plus the exact rank-one defect term of `hQupper`.

The second summand is *literally* `hQupper`'s second summand once `levelVec_gcVec` rewrites it
(§5); nothing is estimated there. So the only inequality with any slack in it is the triangle
inequality itself, and the only unknown is `‖cleanBlockCLM‖`. -/
theorem Qmat_le_clean_add {k : ℕ} (hk : 2 ≤ k) (a b : Fin (k - 1)) :
    Qmat k a b ≤ ‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖
      + Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖ := by
  have hk1 : 1 ≤ k := by omega
  have ha : (a : ℕ) + 2 ≤ k := by have := a.isLt; omega
  refine ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (s_pow_norm_nonneg _ _)) fun x => ?_
  have htri : ‖blockCLM k (a : ℕ) (b : ℕ) x‖
      ≤ ‖P k (a : ℕ) (Uend k (P k (b : ℕ) x))‖
        + ‖P k (a : ℕ) (Dend k (P k (b : ℕ) x))‖ := by
    rw [block_split hk1 x]; exact norm_add_le _ _
  have hclean : ‖P k (a : ℕ) (Uend k (P k (b : ℕ) x))‖
      ≤ ‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖ * ‖x‖ :=
    (cleanBlockCLM k (a : ℕ) (b : ℕ)).le_opNorm x
  have hdef : ‖P k (a : ℕ) (Dend k (P k (b : ℕ) x))‖
      ≤ Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖ * ‖x‖ :=
    le_trans (norm_P_D_P_le hk1 ha x)
      (mul_le_mul_of_nonneg_left (norm_P_le hk1 (b : ℕ) x) (s_pow_norm_nonneg _ _))
  calc ‖blockCLM k (a : ℕ) (b : ℕ) x‖
      ≤ ‖P k (a : ℕ) (Uend k (P k (b : ℕ) x))‖
        + ‖P k (a : ℕ) (Dend k (P k (b : ℕ) x))‖ := htri
    _ ≤ ‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖ * ‖x‖
        + Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖ * ‖x‖ :=
        add_le_add hclean hdef
    _ = (‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖
        + Assembly.s ^ ((a : ℕ) + 1) * ‖P k (b : ℕ) (cvecE k)‖) * ‖x‖ := by ring

/-!
--------------------------------------------------------------------------------
## §5. `hQupper` from (CLEAN), and the certificate
--------------------------------------------------------------------------------

The named residue, in one place:

> **(CLEAN)** `‖P_a U_clean P_b‖ ≤ Assembly.s ^ (b - a)` for `a < b`.

This is `HALFSHIFT_S4_LEMMA_A_PROOF.md`'s Lemma A upper part — the within-level isometry
`B*B = 2^{-d} I` with `d = b - a`, whose ingredients are HALFSHIFT **Sections 1 (SB), 3 (S4)
and 4 (owner count)**. It is **not** Sections 1-2, and it does **not** come from CU; several
documents in this corpus mis-cite it, and that mis-citation is not propagated here.
-/

/-- **`hQupper`, derived from (CLEAN).** Exactly the hypothesis
`ManifestInstance.facts_of_hQupper` takes, now a consequence of a statement about `U_clean`
alone. -/
theorem hQupper_of_clean {k : ℕ} (hk : 3 ≤ k)
    (hclean : ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      ‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ))) :
    ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      Qmat k a b ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ))
        + Assembly.s ^ ((a : ℕ) + 1) * Assembly.levelVec (gcVec (two_le hk)) (b : ℕ) := by
  intro a b hab
  rw [levelVec_gcVec (two_le hk) b.isLt]
  have hc := hclean a b hab
  have hred := Qmat_le_clean_add (two_le hk) a b
  linarith

/-- **The manifest, with (CLEAN) as its single hypothesis.** Compare
`ManifestInstance.facts_of_hQupper`, which takes `hQupper` itself. -/
theorem facts_of_clean {k : ℕ} (hk : 3 ≤ k)
    (hclean : ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      ‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ))) :
    Assembly.LemmaAFacts k (k - 1) (onesCov k) (Tend k) (elev (two_le hk))
      (Uop (one_le hk)) (Qmat k) (gcVec (two_le hk)) :=
  facts_of_hQupper hk (hQupper_of_clean hk hclean)

/-- **`THEOREM.md`'s boxed conclusion for the concrete `T_k`, conditional on (CLEAN) alone.**

Every eigenvalue of the Syracuse transfer operator other than `1` has modulus at most
`2^{-3/2} + 2^{-1}`, uniformly in `k ≥ 3`.

**This does NOT close `hQupper`** — it replaces one hypothesis by another. The hypothesis is
strictly cleaner (a statement about `U_clean` with no `Q`, no defect and no `gc` in it), and it
is the exact statement `HALFSHIFT` proves on paper, but it is a hypothesis. -/
theorem gap_certificate_of_clean {k : ℕ} (hk : 3 ≤ k)
    (hclean : ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      ‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ)))
    {μ : ℂ} (hμ : μ ≠ 1) {x : Fsp k} (hx0 : x ≠ 0) (hx : Tend k x = μ • x) :
    ‖μ‖ ≤ envelope Assembly.s 3 :=
  Assembly.gap_certificate (facts_of_clean hk hclean) hμ hx0 hx

/-- The same with the numeral. -/
theorem gap_certificate_of_clean_numeral {k : ℕ} (hk : 3 ≤ k)
    (hclean : ∀ a b : Fin (k - 1), (a : ℕ) < (b : ℕ) →
      ‖cleanBlockCLM k (a : ℕ) (b : ℕ)‖ ≤ Assembly.s ^ ((b : ℕ) - (a : ℕ)))
    {μ : ℂ} (hμ : μ ≠ 1) {x : Fsp k} (hx0 : x ≠ 0) (hx : Tend k x = μ • x) :
    ‖μ‖ < 0.853554 :=
  Assembly.gap_certificate_numeral (facts_of_clean hk hclean) hμ hx0 hx

/-!
--------------------------------------------------------------------------------
## §6. What is NOT discharged, and exactly where the clean bound stalls
--------------------------------------------------------------------------------

**`hQupper` is OPEN _as of this file_.** `ManifestInstance.gap_certificate_concrete` still
carries an undischarged hypothesis; this file changes which one. Do not read §5 as closing
anything.

**STATUS UPDATE 2026-08-03 (F3): (CLEAN) is now a theorem, `GramIdentity.clean_bound`, so
`gap_certificate_of_clean` has an unconditional form, `GramIdentity.gap_certificate_unconditional`.**
The four "missing" items listed below were built as L14 (owner count), L15 (disjoint
ownership), and F3 (the upper-block entry theorem + the Gram identity + the norm). Item 4's
prediction that a within-level block `B` must be defined and its adjoint formed turned out
to be avoidable: F3 forms no adjoint at all. The rest of this section is accurate as a
record of what was open when it was written.

The residue is now (CLEAN), and nothing else. A read of `HALFSHIFT_S4_LEMMA_A_PROOF.md`
§§1/3/4 and `STEP4_BLOCK_FORMULA_FOUNDATION.md` against this Lean development, done as part of
this task, locates the stall precisely. The paper chain is

```
SB bijection (§1) → S1 phase rewrite → valuation table → A_j = w^{ξ·3⁻¹}·Sodd(α_j, k−j)
  → S4 dead band (§3) → S5 survivor rule (only j = d survives, |ĥ| = 2^{k−d−1})
  → S6/S7 owner count (each η of level b has exactly 2^d owners ξ of level a)
  → S8 disjoint ownership (each ξ has a unique owner η)
  → B*B = 2^{−d}·I  →  ‖B‖₂ = 2^{−d/2}.
```

**The first six steps are already formalised in this repo.** In order:
`CountingLemmas.sb_bijective` / `sb_image_eq` (SB), `BlockVanishing.phase_congr` (S1),
`LemmaA.valuation_below` / `valuation_above` / `valuation_at` (the table),
`BlockVanishing.shell_character_sum` (the `A_j` closed form, multiplicity one),
`LemmaA.Sodd_eq_zero_iff` + `Sodd_full` + `norm_Sodd_full` (S4, including the FULL branch that
supplies `2^{k−d−1}`), and `LemmaA.survivor_dead_band` — whose hypothesis is `a < b`, i.e. it
is already the **upper** variant, unlike `CharacterBasis.survivor_dead_band_lower` which L8
built for `a ≥ b`. `OperatorBlock.inner_chiVec_Uend` supplies the normalisation
`⟪χ_ξ, U_clean χ_η⟫ = (1/N)·cleanEntry k η ξ`, i.e. `B[ξ,η]`.

**Four things are missing, and they are what a follow-on task must build:**

1. **The upper-block entry theorem.** No `a < b` analogue of `BlockVanishing.masked_entry_vanishes`
   exists: `cleanEntry k η ξ = w^{ξu}·(unit of modulus 2^{k−d−1})` when
   `α_d ∈ {0, 2^{k−1}}`, and `0` otherwise. Every ingredient above is present; this is assembly
   in a direction nobody has assembled.
2. **The owner count (S6/S7).** `#{ξ ∈ levelSet k a : 2^{k−1} ∣ alphaJ η ξ u (b−a)} = 2^{b−a}`.
   Not formalised anywhere — `BlockVanishing.lean` says so in its own header.
   `CountingLemmas.residue_class_card` and `three_mul_add_existsUnique` are the raw material.
3. **Disjoint ownership (S8).** For fixed `ξ` of level `a`, at most one `η < 2^{k−1}` of level
   `b` satisfies `2^{k−1} ∣ alphaJ η ξ u d`. Not formalised. This is what makes the Gram matrix
   *diagonal*; without it the entry theorem gives no operator bound at all.
4. **`B*B = 2^{−d}·I`, and the passage from it to the operator norm.** No within-level block
   `B` is defined anywhere in this development — `blockOp`/`cleanBlockOp` act on the whole
   space, not between level subspaces — its adjoint is not formed, and the isometry is not
   stated. `CharacterBasis.gram*` is the right pattern but is about the identity, not `U_clean`.

**Three traps recorded so the next task does not walk into them:**

* **Do not attempt a rank-one argument.** `STEP4` states it explicitly: the upper blocks have
  rank `d_b = 2^{k−2−b}` (full source), **not** rank one, so `‖·‖₂ = ‖·‖_F` is false here and
  any such attack produces wrong dimension factors. The correct reading is
  `Q_norm = √(Q_mass)`, *not* `√(d_b · Q_mass)`.
* **Do not reach for `LinearMap.adjoint`.** L12 exhausted a 400k `synthInstance` budget and then
  a 1M `isDefEq` budget on the adjoint over a `Submodule` of `EuclideanSpace`. Hand-build the
  compression, as `ManifestInstance` §5 does.
* **Do not restate (CLEAN) for the full `U`.** `‖P_a U_full P_b‖ ≤ 2^{−(b−a)/2}` is numerically
  **FALSE** — the defect leaks a positive excess (`+1.4e-4` at `k = 8` per HALFSHIFT). It is
  exact only for `U_clean`, which is why §4 splits before bounding rather than after.

**And the bound is sharp, so no slack is recoverable.** §1 measures `‖P_a U_clean P_b‖` as
*equal* to `2^{-(b-a)/2}` to `1.3e-12`. A cruder route that loses any constant will fail: the
assembled `hQupper` slack at the binding corner is `+8.6e-5` at `k = 8` and falls by `4×` per
`k`, so the clean factor must be `2^{-(b-a)/2}` on the nose, not `C · 2^{-(b-a)/2}` for any
`C > 1`. This is the one place the thin-corner observation *does* bite — not on the triangle
inequality (§0), but on any attempt to prove (CLEAN) lossily.

**A citation correction this file does not propagate.** Several documents in this corpus route
ingredient (ii) through Sections 1-2 or through CU. Neither is right: CU is used only for the
Gauss collapse that *defines* `U_clean`, and the within-level isometry is SB (§1) + S4 (§3) +
the owner count (§4). `HALFSHIFT` §5 additionally records that the S1→S2 seam — once its only
flagged deductive risk — was closed by the shell bijection in June 2026, so the paper chain has
no known gap; the gap is entirely one of formalisation.

**Also not claimed here:** that `gc ≠ 0` (L12 correctly declined to assert it, and nothing in
this file changes that), and any statement whatsoever about Collatz cycles. `Assembly.lean`'s
standing gate 1 is unchanged: every construction here is available verbatim for the `3x-1`
operator, which has real cycles and passes the same certificate.

--------------------------------------------------------------------------------
## §7. Mutation tests (failure mode 1: a theorem a tactic closes on its own)
--------------------------------------------------------------------------------

Seven single-token mutations were applied to the load-bearing statements and the build was run
on each. **All seven failed to compile.** The build was restored and re-run green afterwards.

| # | mutation | result |
|---|---|---|
| M1 | `norm_P_D_P_le`: `Assembly.s ^ (a+1)` → `Assembly.s ^ (a+2)` (the level exponent) | fails |
| M2 | `norm_P_D_P_le`: `‖P k b (cvecE k)‖` → `‖P k a (cvecE k)‖` (the wrong level of `c*`) | fails |
| M3 | `cleanBlockOp`: `(P k a).comp ((Uend k).comp (P k b))` → `(P k b).comp ((Uend k).comp (P k a))` (the orientation trap) | fails |
| M4 | `block_split`: `Uend k … + Dend k …` → `Uend k … - Dend k …` | fails |
| M5 | `Qmat_le_clean_add`: drop `‖cleanBlockCLM …‖` from the RHS | fails |
| M6 | `hQupper_of_clean`: `Assembly.s ^ ((b:ℕ) - (a:ℕ))` → `Assembly.s ^ ((a:ℕ) - (b:ℕ))` | fails |
| M7 | `hQupper_of_clean`: hypothesis `(a:ℕ) < (b:ℕ)` → `(b:ℕ) < (a:ℕ)` (the regime) | fails |

M3, M6 and M7 are three independent shots at the orientation trap that has already cost this
project a defect. M5 is the one that would matter most if it passed: it is the check that the
clean term is genuinely load-bearing in the reduction rather than decoration.

--------------------------------------------------------------------------------
## §8. Satisfiability (failure mode 3: a vacuous hypothesis block)
--------------------------------------------------------------------------------
-/

/-- `k = 6, a = 1, b = 3` satisfies every hypothesis of §3-§5 simultaneously, and the regime
`a < b` is the one (CLEAN) is about. -/
theorem hyp_satisfiable_clean : 3 ≤ 6 ∧ 2 ≤ 6 ∧ 1 + 2 ≤ 6 ∧ (1 : ℕ) < 3 := by norm_num

/-- The index range is inhabited at `k = 6`: `(1, 3) : Fin 5 × Fin 5` with `1 < 3`, so §5's
quantifier is not vacuous. -/
example : ((⟨1, by norm_num⟩ : Fin (6 - 1)) : ℕ) < ((⟨3, by norm_num⟩ : Fin (6 - 1)) : ℕ) := by
  norm_num

/-- The reduction, instantiated at `k = 6, a = 1, b = 3` — inside the `a < b` regime, where
`Qmat`'s lower-triangle theorem `Qmat_lower_eq` does **not** apply. -/
example : Qmat 6 ⟨1, by norm_num⟩ ⟨3, by norm_num⟩
    ≤ ‖cleanBlockCLM 6 1 3‖ + Assembly.s ^ 2 * ‖P 6 3 (cvecE 6)‖ :=
  Qmat_le_clean_add (by norm_num) ⟨1, by norm_num⟩ ⟨3, by norm_num⟩

/-- The defect block's bound at a concrete point. -/
example (x : Fsp 6) :
    ‖P 6 1 (Dend 6 (P 6 3 x))‖ ≤ Assembly.s ^ 2 * ‖P 6 3 (cvecE 6)‖ * ‖P 6 3 x‖ :=
  norm_P_D_P_le (by norm_num) (by norm_num) x

/-- The level sets at both ends of that instance are inhabited (`ξ = 2` has `v₂ = 1`,
`ξ = 8` has `v₂ = 3`), so neither `P` in it is the zero projection. -/
example : (⟨2, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 1 :=
  mem_levelSet_mod.2 (by norm_num)

example : (⟨8, by norm_num⟩ : Fin (2 ^ (6 - 1))) ∈ levelSet 6 3 :=
  mem_levelSet_mod.2 (by norm_num)

/-- **(CLEAN) is not self-evidently vacuous either**: at `k = 6` the pairs `a < b` in range are
ten in number, and the bound it asserts at the binding corner `(3, 4)` is `s^1`, a number
strictly between `0` and `1`. -/
example : (0 : ℝ) < Assembly.s ^ (4 - 3) ∧ Assembly.s ^ (4 - 3) < 1 := by
  constructor
  · exact pow_pos Assembly.s_pos _
  · rw [pow_one, Assembly.s, show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-!
--------------------------------------------------------------------------------
## §9. Axiom audit
--------------------------------------------------------------------------------

Every exported declaration must use a SUBSET of `{propext, Classical.choice, Quot.sound}`.
-/

#print axioms cleanBlockCLM_apply
#print axioms norm_P_D_P_le
#print axioms block_split
#print axioms Qmat_le_clean_add
#print axioms hQupper_of_clean
#print axioms facts_of_clean
#print axioms gap_certificate_of_clean
#print axioms gap_certificate_of_clean_numeral
#print axioms hyp_satisfiable_clean

end CleanBlock
