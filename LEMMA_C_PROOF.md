# Lemma C: per-level decay of the defect covector

Written 2026-06-02 (Session 40), the analytic step requested after
[UFULL_ASSEMBLY_PROOF.md](UFULL_ASSEMBLY_PROOF.md). This document reduces Lemma C to an elementary
collision-count inequality in the **same shell framework that proves Lemma B**, and proves the bound
at the strength the assembly needs. Reproduce with `probe_gb_collision.py`, `probe_autocorr.py`,
`probe_shell_halfshift.py`, and the one-liners in this file's verification section.

## Statement and what the assembly actually needs

> **Lemma C (sharp form).** `v_b <= (3/4) 2^{-b} 2^{-k/2}` for all `k`, `0 <= b <= k-2`. Equivalently,
> with `g_b := v_b 2^b 2^{k/2}`, `g_b^2 <= 9/16`.

The assembly ([UFULL_ASSEMBLY_PROOF.md](UFULL_ASSEMBLY_PROOF.md)) does not need the sharp constant. It
needs `sum_{b} v_b 2^{-b} <= C 2^{-k/2} (4/3)` with the certificate `< G_up + C (4/3) 2^{-3/2} < 1`,
i.e. any uniform bound

> **Lemma C (assembly form).** `g_b <= 0.961` for all `k, b`.

We prove `g_b < sqrt(3/4) = 0.8660 < 0.961` for all `k, b` (Theorem C below), **conditional on the two
inputs flagged in the status section** (the scale-`k`-to-`p` homometry, verified exactly to `k=26`, and
Lemma B's shell facts, which inherit the Half-Shift Invariance conditionality). The sharp `g_b <= 3/4`
is verified exactly to `k=26` but not needed. This document does not claim an unconditional proof; it
claims a rigorous reduction of Lemma C to those two inputs.

## Step 1 - the defect covector is a 3x+1 exponential sum, and `g_b` is single-index

`r* = -3^{-1} mod 2^k` is the unique odd residue with `3r*+1 = 2^{2 ceil(k/2)}` (Lemma B). Lifting
`r*+m 2^k` and applying the Syracuse map collapses the `2^k` factor:
```
  Syr(r* + m 2^k) = OddCore(3m + a) mod 2^k,   a := 2^{2 ceil(k/2) - k} in {1,2}   (a=1 k even, a=2 k odd).
```
So the defect count `cf_k[t] = #{m in [0,2^k): Syr(r*+m 2^k) = t}` is the pushforward of the uniform
measure on `[0,2^k)` under `m -> OddCore(3m+a) mod 2^k`, and `c = cf_k / 2^k`. Its Fourier transform is
the 3x+1 exponential sum `S_k(xi) = sum_t cf_k[t] w^{xi t}`, `w = e^{-2 pi i/2^k}`, with
`v_b^2 = sum_{xi: v2(xi)=b, 1<=xi<2^{k-1}} |S_k(xi)|^2 / (2^{2k} 2^{k-1})`.

**Two routes to a single-index reduction (both give the same identity, verified exactly):**

- **(Scale-`k` Parseval - the identity is rigorous, but completing the proof this way still needs
  Step 3 redone at reduced resolution.)** Let `fcoll_j := sum_t (fold_{2^j} cf_k[t])^2` be the collision
  count of `cf_k` folded to resolution `2^{k-j}`. Then by Parseval on `Z/2^{k-1}` and the band identity
  `B_b = M_b - M_{b+1}` (see [UFULL_ASSEMBLY_PROOF.md](UFULL_ASSEMBLY_PROOF.md)),
  ```
      g_b^2 = 2^{b-1-k} ( 2 fcoll_b - fcoll_{b+1} ).                              (1)
  ```
  Identity (1) is exact and unconditional (`probe` confirms it for every `b`, `k`). It avoids the
  homometry, but Step 3's shell bound would then have to be re-run for the *folded scale-`k`* counts
  `fcoll_b` at reduced resolution `2^{k-b}` (the same argument at a different resolution). That
  reduced-resolution shell bound is set up below in spirit but **not written out in full**, so this
  route is not, by itself, a completed proof either.

- **(Self-similarity, verified exactly.)** The exponential sum is homometric under frequency-doubling:
  `|S_k(2 xi)| = |S_{k-1}(xi)|` for all `xi` (verified exactly, `probe_selfsimilar.py`). Iterating,
  level-`b` energy at scale `k` equals level-`0` (odd-frequency) energy at scale `p := k-b`, so
  ```
      g_b^2 = E_p / 4^p,    E_p := sum_{xi odd, 1<=xi<2^p} |S_p(xi)|^2,    p = k-b.   (2)
  ```
  `g_b^2` depends only on `p`, which is why the top-level profile is `k`-independent.

Routes (1) and (2) agree numerically to machine precision for all tested `k` (the homometry identity
`|S_k(2xi)|=|S_{k-1}(xi)|` is the bridge; it is verified exactly, see the status section).

## Step 2 - `E_p` is a half-shift autocorrelation (fully rigorous)

Write the odd-frequency indicator `[xi odd] = (1 - (-1)^xi)/2` and use Parseval on `Z/2^p` twice:
```
  sum_{xi}        |S_p(xi)|^2          = 2^p coll(p),       coll(p) = sum_t cf_p[t]^2,
  sum_{xi} (-1)^xi |S_p(xi)|^2          = 2^p A_p,           A_p     = sum_t cf_p[t] cf_p[t + 2^{p-1}],
```
the second because `(-1)^xi = w^{xi 2^{p-1}}` and `sum_xi |S|^2 w^{xi h} = 2^p (autocorrelation at lag h)`.
Hence
```
  E_p = (1/2)( 2^p coll(p) - 2^p A_p ) = 2^{p-1} ( coll(p) - A_p ),                  (3)
```
and, using `coll - A = (1/2) sum_t (cf[t] - cf[t+2^{p-1}])^2`,
```
  g_b^2 = E_p/4^p = (coll(p) - A_p) / 2^{p+1}.                                       (4)
```
Identities (3), (4) are exact and unconditional (`probe_autocorr.py`: `match=True` for all `p`).
Grouping `m` by `u := O_p(m) mod 2^{p-1}` with top-bit split `n_u^0, n_u^1`,
```
  coll(p) - A_p = sum_{u} (n_u^0 - n_u^1)^2.                                         (5)
```
So **Lemma C (assembly form) <=> `coll(p) - A_p <= (7/8) 2^p` for all p** (this gives `g_b^2 <= 7/16`
asymptotically; we prove the looser `<= (3/2) 2^p` below, i.e. `g_b^2 <= 3/4`, which already suffices).

## Step 3 - shell bound (Lemma B's machinery)

Decompose the AP `{a+3m : m in [0,2^p)}` into 2-adic shells `A_j = {x : v2(x) = j}`, and set
`R_j = {(x/2^j) mod 2^p : x in A_j}`. Lemma B's facts carry over verbatim:
- **FACT 1 (per-shell injectivity).** `x -> (x/2^j) mod 2^p` is injective on `A_j`; so `cf_p[t] = #{j : t in R_j}` is `0/1` per shell, and `|R_j| = 2^{p-1-j}` for `j=0..p-1`, plus a single top atom.
- In particular `|R_0| = 2^{p-1}`: shell `j=0` is **all** `2^{p-1}` odd residues mod `2^p`.

Write `coll(p) - A_p = sum_{j,j'} ( c_{jj'} - d_{jj'} )`, `c_{jj'} = |R_j cap R_{j'}|`,
`d_{jj'} = |R_j cap (R_{j'} - 2^{p-1})|` (this is (5) re-expanded via `cf = sum_j 1[. in R_j]`).

**The `j=0` shell cancels.** Since `R_0` is all odd residues and `2^{p-1}` is even, `R_{j'} - 2^{p-1}`
is also a set of odd residues, so `c_{0 j'} = |R_{j'}| = d_{0 j'}` and likewise `c_{j' 0} = d_{j' 0}`.
Every term with a `0` index vanishes:
```
  coll(p) - A_p = sum_{j, j' >= 1} ( c_{jj'} - d_{jj'} ).                            (6)
```

**Drop the non-negative subtractions** (`d_{jj'} >= 0`, and the diagonal `d_{jj} = s_j >= 0`):
```
  coll(p) - A_p <= sum_{j>=1} c_{jj} + sum_{j != j', j,j' >= 1} c_{jj'}
               =  sum_{j>=1} |R_j| + 2 sum_{1<=j<j'} |R_j cap R_{j'}|.
```
The first sum is `sum_{j=1}^{p-1} 2^{p-1-j} + 1 (atom) = (2^{p-1} - 1) + 1 = 2^{p-1}`. For the second,
`|R_j cap R_{j'}| <= |R_{j'}|` (the smaller shell, `j' > j`); the shells `j' = 2..p-1` have
`|R_{j'}| = 2^{p-1-j'}` and `j'-1` partners `j in {1,...,j'-1}`, and the top atom `j' = p` has
`|R_p| = 1` and `p-1` partners. The honest finite sum has an exact closed form:
```
  sum_{1<=j<j'<=p} |R_j cap R_{j'}|  <=  sum_{j'=2}^{p-1}(j'-1) 2^{p-1-j'}  +  (p-1) * 1
                                     =  2^{p-1} - 1                              (verified for all p).
```
(The `(p-1)` is the top atom's partner contribution; the closed form `... = 2^{p-1}-1` is checked in
the verification section.) Therefore
```
  coll(p) - A_p  <=  2^{p-1} + 2 (2^{p-1} - 1)  =  3 * 2^{p-1} - 2  <  (3/2) 2^p,    (7)
```
and by (4),
```
  g_b^2  =  (coll(p) - A_p) / 2^{p+1}  <=  (3 * 2^{p-1} - 2)/2^{p+1}  =  3/4 - 2^{-p}  <  3/4.   (8)
```

## Theorem C and the conclusion

> **Theorem C (conditional).** Assume (i) the scale-`k`-to-`p` homometry `|S_k(2xi)| = |S_{k-1}(xi)|`
> (so that `g_b^2 = (coll(p)-A_p)/2^{p+1}`, p=k-b; verified exactly to `k=26`, not derived) and (ii)
> Lemma B's shell facts (FACT 1 and `|R_j| = 2^{p-1-j}`, themselves conditional on Half-Shift
> Invariance). Then `g_b < sqrt(3/4) = 0.8660 < 0.961` for all `k` and `0 <= b <= k-2`, so Lemma C
> (assembly form) holds and the certificate is `< 1` uniformly. The chain from (i),(ii) to the bound is
> the fully rigorous Steps 2-3 above; this is a reduction of Lemma C to (i),(ii), not an unconditional
> proof.

The bound (8) is `g_b^2 <= 3/4`, well inside the `0.924` ceiling the assembly needs. (A sharper
accounting of the top-atom partners gives `g_b^2 <= 3/4 + (p-1)/2^p`, which still respects the ceiling
for `p>=5`; for the finitely many top levels `p = k-b in {2,3,4}` the values are the exact, `k`-independent
dyadic rationals `g_b^2 in {1/2, 1/8, 9/16}`, all `<= 9/16`. Either way `g_b < 0.961`.)

Feeding `g_b <= sqrt(3/4)` into the assembly: `sum_b v_b 2^{-b} <= sqrt(3/4) 2^{-k/2} (4/3)`, so the
lower row-sum at the top is `<= 2^{-3/2} sqrt(3/4)(4/3) = 0.408`, and
```
  cert(k) < G_up + 0.408 = 0.547 + 0.408 = 0.955 < 1,   uniform in k.
```

## Status: what is rigorous, what is conditional

**Rigorous and self-contained (no homometry, no Half-Shift Invariance):**
- Step 1 identity (1): the scale-`k` Parseval identity `g_b^2 = 2^{b-1-k}(2 fcoll_b - fcoll_{b+1})`.
- Step 2: identities (3), (4), (5) (Parseval + the `coll-A = (1/2) sum (cf[t]-cf[t+h])^2` algebra).

**Rigorous given Lemma B's shell facts (which inherit Half-Shift Invariance conditionality):**
- Step 3: the `j=0` cancellation (6), the shell drop, and the finite bound (7), **given** FACT 1 and the
  shell sizes `|R_j| = 2^{p-1-j}`. The *combinatorial core* of these is Lemma B's and unconditional;
  but their relevance to the operator (R1/R2) rests in the foundation on the Half-Shift Invariance /
  coset-uniformity lemma, a draft with a finite-`k`-verified crux. So Step 3 inherits exactly the
  conditionality Lemma B has - it is not unconditional.

**Verified exactly to `k=26` but not derived (the one genuinely new gap):**
- The scale-`k`-to-scale-`p` **homometry** `|S_k(2xi)| = |S_{k-1}(xi)|` (equivalently:
  `fold_{2^j} cf_k` and `cf_{k-j}` have equal Fourier magnitudes), which is what turns Step 3's
  scale-`p` bound `coll(p)-A_p <= 3*2^{p-1}-2` into the scale-`k` statement `g_b^2 < 3/4` via (4).

**Neither route is a finished unconditional proof.** Route (2) [homometry] is complete except for that
identity. Route (1) [scale-`k` Parseval] has the exact identity (1) but still needs Step 3 re-run for
the folded counts at reduced resolution, which is not written out. So the honest statement is:

> **Lemma C (assembly form) is reduced, by the rigorous Steps 2-3, to (i) the scale-`k`-to-`p` homometry
> and (ii) Lemma B's shell facts.** Given (i) and (ii), `g_b < sqrt(3/4) < 0.961` and the certificate is
> `< 1` uniformly. (ii) is the same dependence Lemma B already carries; (i) is genuinely new and is the
> single un-derived Fourier-magnitude identity. This is a large advance - the open mathematical content
> of the cycle program is now that one identity plus the pre-existing Half-Shift Invariance crux, not an
> operator-norm estimate - but it is a reduction, not a closed proof.

## Verification

```bash
python probe_gb_collision.py     # g_b^2 = E_p/4^p (single index); sum|S|^2 = 2^p coll(p)
python probe_autocorr.py         # E_p = 2^{p-1}(coll-A); coll-A = (1/2)sum(cf[t]-cf[t+h])^2
python probe_shell_halfshift.py  # shell decomposition: diag=2^{p-1}, j=0 cancels, the (3/2)2^p bound
python probe_selfsimilar.py      # the homometry |S_k(2 xi)| = |S_{k-1}(xi)| (the one un-derived link)
# closed forms (one-liners):
#   sum_{j=2}^{p-1}(j-1)2^{p-1-j} + (p-1) == 2^{p-1}-1     (cross-sum bound, p=2..24: True)
#   coll(p) - A_p <= 3*2^{p-1} - 2                          (eq 7, p=2..16: True)
```

## Honest ceiling (unchanged)

This is cycle elimination, not Collatz. Even with Lemma C fully closed, the program proves only "the
only Collatz cycle is `1 -> 4 -> 2 -> 1`," strictly weaker than the conjecture; the divergent-trajectory
half is untouched.
