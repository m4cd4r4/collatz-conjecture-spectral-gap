# The uniform spectral gap, consolidated: statement and full proof chain

Written 2026-07-05 (Fable review session). This document is the single self-contained statement of
what this repository proves, including the spectral reduction that earlier documents cited but did
not write out (the acknowledged open item (a) of [LEMMA_C_PROOF.md](LEMMA_C_PROOF.md)), and a
simplified assembly that closes the certificate from Lemmas A and B alone, with a better constant
than the Lemma C route. Reproduce the numerics with `python fable_assembly_check.py`.

> **Scope (read first).** This is a theorem about the mod-`2^k` transfer operator of the Syracuse
> map - a Markov model. It does **not** eliminate Collatz cycles: the `3x-1` operator passes the
> identical certificate yet `3x-1` has real cycles ([CYCLE_CLAIM_REFUTED.md](CYCLE_CLAIM_REFUTED.md)).
> It is not a proof of any part of the Collatz conjecture.

## The theorem

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

Inputs: Lemma A ([HALFSHIFT_S4_LEMMA_A_PROOF.md](HALFSHIFT_S4_LEMMA_A_PROOF.md)), Lemma B
([LEMMA_B_PROOF.md](LEMMA_B_PROOF.md)), and the foundation facts R1-R3
([STEP4_BLOCK_FORMULA_FOUNDATION.md](STEP4_BLOCK_FORMULA_FOUNDATION.md)), all proved elementarily
for all `k`. Lemma C ([LEMMA_C_PROOF.md](LEMMA_C_PROOF.md)) is used only for the sharper constant.

## Setup

States: odd residues `r` mod `2^k`, `N = 2^{k-1}`. The chain from `r` moves to
`Syr(r + m 2^k) mod 2^k` with `m` uniform on `[0, 2^k)`; `T_k[s', s]` is that transition
probability, and `U := T_k^T` is the expectation (Koopman) operator,
`(U g)(r) = E_m[ g(Syr(r + m 2^k)) ]`.

Characters: `chi_xi(r) = w^{xi r}/sqrt(N)`, `w = e^{2 pi i/2^k}`, `xi in [0, 2^{k-1})`. On odd
arguments `chi_{xi + 2^{k-1}} = -chi_xi`, so this index range is exactly one representative per
line; the `chi_xi` are orthonormal (S4 with `m = k`: `<chi_xi, chi_eta> = Sodd(eta-xi, k)/N = 0`
for `xi != eta` in range, since `0 <= v2(eta - xi) <= k-2` there). `chi_0` is the constant
(Perron) mode. Level of `xi != 0`: `m := v2(xi) in {0, ..., k-2}`; `P_m` projects onto
`W_m := span{chi_xi : v2(xi) = m}`. The mean-zero space is `V = W_0 + ... + W_{k-2}`,
an orthogonal decomposition.

## Part I - the spectral reduction `|lambda_2| <= rho(Q) <= cert(k)`

**Warning fixed here (referee find, 2026-07-05).** Earlier write-ups asserted `T_k` is doubly
stochastic with uniform stationary distribution, and used `T_r^p = T_k^p - (1/N)J`. Both are
FALSE: columns of `T` sum to 1 exactly, but row sums deviate (`||T1 - 1||_2 ~ 0.76 * 2^{-k/2}`,
another face of the `r*` defect), so the stationary distribution is only approximately uniform
and `TJ != J`. The chain below is the corrected, one-sided derivation; nothing in it uses
uniformity of the stationary distribution.

**I.1 (Perron split).** `T := T_k` is column-stochastic: `1^T T = 1^T`, hence `rho(T) = 1` and
the mean-zero space `V = ker(1^T) = 1^perp` is `T`-invariant (`1^T (Tf) = 1^T f = 0`). In a basis
adapted to `C^N = span(1) (+) V`, `T` is block-triangular, `T = [[1, 0], [d, A]]` with
`A = T|_V` (the off-diagonal `d` is the `V`-component of `T1`, nonzero here). The characteristic
polynomial factors, so `spec(T) = {1} u spec(A)` as multisets, and
```
  |lambda_2(T)|  <=  rho(A).
```

**I.2 (adjoint and Gelfand).** `A = P_V T P_V` on `V`, so `A^* = P_V U P_V =: U_V` with
`U = T^T`, and `rho(A) = rho(U_V)`. (`V` need not be `U`-invariant - `U_V` is the compression,
which is all that is used.) By Gelfand, for every `p`,
```
  rho(U_V) <= || U_V^p ||_2^{1/p} ,
```
valid for any matrix - no normality or diagonalisability input (this is what makes the route
immune to the `kappa ~ 10^k` non-normality that broke the older perturbative argument).

**I.3 (level majorisation).** For `g in V` write the level-energy vector `a(g)_m := ||P_m g||_2`.
Since `P_{m'} P_V = P_{m'}`, the triangle inequality and the definition of `Q = Q_k` give
```
  ||P_{m'} U_V g||  =  ||P_{m'} U g||  <=  sum_m Q[m',m] a(g)_m  =  (Q a(g))_{m'} ,
```
i.e. `a(U_V g) <= Q a(g)` entrywise. `Q` is nonnegative, so this iterates:
`a(U_V^p g) <= Q^p a(g)`. The levels are orthogonal and exhaust `V`, so
```
  ||U_V^p g||_2 = ||a(U_V^p g)||_2 <= ||Q^p||_2 ||g||_2 ,
```
hence `rho(A) = rho(U_V) <= lim_p ||Q^p||^{1/p} = rho(Q)`, and with I.1,
`|lambda_2(T)| <= rho(Q)`.

**I.4 (weighted row sum).** `Q` is nonnegative, so for the diagonal similarity
`S = diag(2^0, ..., 2^{k-2})`:
```
  rho(Q) = rho(S Q S^{-1}) <= ||S Q S^{-1}||_inf = max_a sum_b Q[a,b] 2^{a-b} = cert(k).
```

## Part II - the block structure (the proved lemmas, recalled)

- **Splitting (Coset-Uniformity).** `U = U_clean + D`: for the `2^{k-1} - 1` rows `r` with
  `v(r) := v2(3r+1) < k`, CU collapses the fiber average to the masked phase
  `(U chi_eta)(r) = [v(r) <= v2(eta)] w^{eta (3r+1)/2^{v(r)}}`; the unique remaining row
  `r* = -3^{-1} mod 2^k` carries the rank-1 defect `D = e_{r*} c^*`, `c` its fiber distribution.
  ([HALFSHIFT_S4_LEMMA_A_PROOF.md](HALFSHIFT_S4_LEMMA_A_PROOF.md) Sections 1-2, foundation R1/R2.)
- **Lemma A (exact upper cascade).** `||P_a U_clean P_b||_2 = 2^{-(b-a)/2}` for `a < b`, and
  `P_a U_clean P_b = 0` for `a >= b`. So by the triangle inequality, for ALL `a, b`:
  ```
    Q[a,b]  <=  2^{-(b-a)/2} [b > a]  +  u_a v_b ,
  ```
  with `u_a := ||P_a e_{r*}|| = 2^{-(a+1)/2}` (R3) and `v_b := ||P_b c||`.
- **Lemma B (defect mass).** `sum_b v_b^2 <= ||c||^2 = coll(k)/4^k <= 3 * 2^{-k}`, i.e.
  `||v|| <= sqrt(3) 2^{-k/2}`, from the collision bound `coll(k) <= 3 * 2^k`.

## Part III - the assembly (truncation-aware; Lemmas A + B suffice)

Fix a row `a` and set `e := k - a in {2, ..., k}`. Summing the defect over ALL `b` absorbs the
upper leak (no separate estimate needed), and the clean upper series **truncates at the top**:
`b <= k-2` means `d = b - a <= e - 2`. Hence
```
  R_a := sum_b Q[a,b] 2^{a-b}
       <= sum_{d=1}^{e-2} 2^{-3d/2}   +   u_a 2^a * sum_{b=0}^{k-2} v_b 2^{-b} .
```
For the defect factor, Cauchy-Schwarz and Lemma B give (this needs no information about the
`v_b` profile):
```
  sum_{b=0}^{k-2} v_b 2^{-b}  <=  ||v|| * sqrt( sum_{b>=0} 4^{-b} )  <=  sqrt(3) 2^{-k/2} * 2/sqrt(3)
                              =   2^{1-k/2} ,
```
and `u_a 2^a = 2^{(a-1)/2}`, so the defect term is `<= 2^{(a-1)/2} 2^{1-k/2} = 2^{-(e-1)/2}`.
Therefore
```
  R_a  <=  f(e)  :=  sum_{d=1}^{e-2} 2^{-3d/2}  +  2^{-(e-1)/2} .
```
`f(2) = 0.7071`, `f(3) = 2^{-3/2} + 2^{-1} = 0.85355`, `f(4) = 0.8321`, `f(5) = 0.7727`, and
`f` decreases monotonically to `G_up = 0.5469` afterwards: the two terms trade off, and the
maximum over `e >= 2` is
```
  cert(k)  =  max_a R_a  <=  max_{e>=2} f(e)  =  f(3)  =  2^{-3/2} + 2^{-1}  =  0.853553...
```
for every `k >= 3`, with no small-`k` exceptions and no leak bookkeeping. With Part I this proves
the Theorem.   ∎

**Correction to [UFULL_ASSEMBLY_PROOF.md](UFULL_ASSEMBLY_PROOF.md) Remark 2.** That remark argues
the L2 route fails ("`G_up + 0.707 = 1.25 > 1`") and concludes the per-level decay (Lemma C) is
necessary. The evaluation adds the FULL series `G_up` to the top row's defect bound - but at the
top row the upper cascade is EMPTY (`b <= k-2` leaves no `b > a` when `a = k-2`). Row-wise, the
upper part is the truncated series `sum_{d <= e-2}`, and the correct envelope is `f(e)` above,
whose maximum is `0.8536 < 1`. So Lemmas A + B alone close the certificate; Lemma C is a genuine
sharpening, not a necessity.

**Sharpness remark (numerical adversary, 2026-07-05).** The envelope `f(e)` is asymptotically
sharp at the bottom row `a = 0` (`e = k`): both `R_0` and `f(k)` converge to `G_up = 0.5469` from
above, with margin `~2^{-k/2}` (0.0148 at k=12). This is the Cauchy-Schwarz step being
asymptotically efficient there, not a fragility - the inequality is derived, and the row that sets
the CONSTANT is `e = 3`, where the measured margin is large (`R ~ 0.63` vs `f(3) = 0.854`).
Verified k=3..13, both parities, no violations of any ingredient (rank-1 separability exact to
8e-17; upper-leak triangle slack 16x-400x conservative; `||c|| 2^{k/2}` peaks at 1.6202, k=4).

**The Lemma C refinement.** Feeding `v_b <= (3/4) 2^{-b} 2^{-k/2}` (Lemma C) through the same
truncated envelope replaces the defect term by `2^{(a-1)/2} 2^{-k/2} = 2^{-(e+1)/2}`:
```
  cert(k) <= max_{e>=2} [ sum_{d=1}^{e-2} 2^{-3d/2} + 2^{-(e+1)/2} ]  =  0.65597...   (max at e = 4),
```
close to the measured `~0.6345` and a factor-`sqrt 2` sharpening of the defect term over
Cauchy-Schwarz alone.

## Verification

```
python fable_assembly_check.py    # per-row R_a <= f(k-a) against dense build_T, k=3..13;
                                  # u_a exactness; ||c|| 2^{k/2} <= sqrt(3); Q[a,b] = u_a v_b (a>=b)
python verify_assembly.py         # the Lemma C route numbers (cert ~0.6345, rho ~0.566)
python audit_halfshift_s4.py      # CU, S4, and the Lemma A isometry to machine precision
```

## Lean formalisation (elementary core)

[lean/GapCertificate.lean](lean/GapCertificate.lean) - sorry-free, Mathlib v4.27.0
(`cd lean && lake exe cache get && lake build`). Machine-checked (2026-07-05):

- the shared divisibility engine, FACT 1 (Lemma B) and SB injectivity (Lemma A's S1);
- the Coset-Uniformity affine step (`cu_valuation_frozen`, `cu_syracuse_affine`);
- the envelope `f(e) <= f(3) = 2^{-3/2} + 1/2 < 1` (`envelope_max`, `envelope_lt_one`);
- the Cauchy-Schwarz defect bound (`defect_sum_bound`) and the abstract row-sum
  assembly of Part III (`assembly_row_bound`, `certificate_lt_one`).

Not yet formalised: the operator chain of Part I (Perron split, majorisation,
Gelfand), the CU fiber COUNT, SB surjectivity/cardinality, Lemma B's shell counting.

## Honest scope (restated)

The theorem is about mixing of the mod-`2^k` Markov model. The averaging over `2^k` lifts that
defines `T_k` erases deterministic orbit structure, so the spectral gap says nothing about cycles
(`3x-1` control: same certificate, real cycles) and nothing about divergent trajectories. What
stands is an elementary, explicit, all-`k` spectral gap for a natural family of arithmetic
transfer operators, with every ingredient - CU, SB, S4, Lemma A, Lemma B, Lemma C/H, and the
assembly above - at the level of finite 2-group arithmetic and one application of Cauchy-Schwarz.
