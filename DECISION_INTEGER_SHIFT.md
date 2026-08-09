# Representation decision: how `3x - 1` gets a Lean certificate

**Status: DECISION, not a proof.** Nothing below is formalised yet. The evidence is
`calibrate_integer_shift.py` (exit 0) plus gate G5 of `calibrate_general_shift.py`.
Date: 2026-08-09.

## The problem

`ShiftedOperator.lean` proves `gap_certificate_shifted` for `3x + c` with **`c : ℕ`**,
`c` odd, `c < 2^k`, `k ≥ 3`. `syracuseS` takes `c : ℕ`, so the development cannot
*state* `3x - 1`, let alone prove anything about it. The project's most transferable
claim - that `3x - 1` passes the identical certificate and yet **has** cycles, so
"spectral gap ⟹ no cycles" is false - therefore still rests on Python
(`CYCLE_CLAIM_REFUTED.md`, `probe_cycle_link.py`).

Note the c = 2^k − 1 trap, already recorded in `ShiftedOperator.lean` §4: `-1` and
`2^k - 1` agree mod `2^k` but `oddPart` does **not** factor through the residue, so the
substitute is a genuinely different operator. Only a real integer shift closes this.

## What the calibration measured

| Gate | Result |
|---|---|
| I1 | `r*_c` unique and odd at integer `c`. Sign of `c` is irrelevant - 3 is invertible mod `2^k` either way. **Nothing to redo.** |
| I2 | The offset trichotomy `A_c ∈ {1,2,3}` is **FALSE** at negative `c`. Size bound permits `{-2,…,3}`; measured set is `{-1,0,1,2,3}`, k = 3..12. |
| I2 | **`A_c = 0` occurs**, at exactly `c = -3t` for odd `t < 2^k` (closed-form prediction confirmed, not just observed). There `oddPart(A_c + 3m)` is undefined at `m = 0`. Smallest instance `c = -3`. |
| I3 | The link theorem survives verbatim at negative and zero-crossing `A_c`, on the fibre minus the single undefined entry. `oddPart(2^k X) = oddPart(X)` is sign-agnostic. 0 mismatches over 523,917 compared pairs, k = 3..9. |
| I4 | `coll_c ≤ 3·2^k` still holds, and still depends on `c` only through `A_c`. |
| I5 | `c = -1` passes all four spectral gates at k = 4..8 (cert 0.578–0.606, clean block norms exact to 6.5e-13, rank D = 1, ‖D‖ ≤ √3·2^{-k/2}). Called from `calibrate_general_shift.py` directly so the two scripts cannot drift. |

**The load-bearing finding:** `A_{-1}` is **1 at odd `k` and 2 at even `k`** - it
alternates, it is not constant. Both values are offset classes the `c : ℕ` development
has already proved. **`3x - 1` never meets `A_c ≤ 0`.** So the degenerate case that
negative shifts introduce is real, and it is not on the path to `3x - 1`.

## The decision: route (a′), a *scoped* integer reparametrisation

The brief offered two routes. Neither is taken as written.

* **(a) Full `c : ℤ` reparametrisation** - `syracuseS`, `rstarS`, `shellS`, `sbMapS`,
  `apAS`, `cfS`, `collS`, `TcountS` all move to `ℤ`. Correct but overpriced: it forces
  the `A_c ≤ 0` and `A_c = 0` cases into scope, and those are exactly the cases `3x - 1`
  does not need. It also trades `ℕ` truncated subtraction for `Int.emod` sign
  conventions, which is a different trap, not a smaller one.
* **(b) Define `syracuseM n := oddPart (3n - 1)` over `ℕ`** - smallest, but proves one
  map rather than a family and duplicates the ~4560-line chain a third time. The chain
  has now been written three times; a fourth copy is the wrong direction.

**Chosen: (a′).** Move the shift argument to `c : ℤ`, and **supply the offset as a
hypothesis rather than deriving it from `c < 2^k`**:

```
hA : 1 ≤ apAS c k ∧ apAS c k ≤ 3
```

At `c : ℕ`, `c < 2^k`, that hypothesis is a theorem (the existing size argument, B1). At
`c = -1` it is discharged by one new arithmetic lemma. Everything downstream of the
offset - the link theorem, Lemma B, Lemma A, the assembly - is sign-agnostic by I3/I4
and transfers unchanged.

**Why this and not (a):** it buys the whole integer family that anyone would actually
want, while leaving `A_c ≤ 0` explicitly out of scope as a stated hypothesis instead of
a silently-missing case. Route (a) would have to prove or dispatch `A_c = 0`, where the
AP model genuinely degenerates - work with no bearing on `3x - 1`.

**Why this and not (b):** the cost difference is one hypothesis threaded through
existing statements versus a third transcription of the chain.

### The one new arithmetic lemma

`r*_{-1}` has a closed form, visible in the I2 probe table (3, 11, 11, 43, 43, 171, 171,
683, 683, 2731):

```
r*_{-1}(k) = (2^k + 1)/3      for odd k,   giving apAS (-1) k = 1
r*_{-1}(k) = (2^{k+1} + 1)/3  for even k,  giving apAS (-1) k = 2
```

That is the entire `3x - 1`-specific content. Everything else is inherited.

## What this does NOT do

1. It does not make `3x - 1` proved. This is a decision plus a calibration; the Lean is
   a separate multi-session job, in the order operator → defect residue → link theorem →
   Lemma B → Lemma A → assembly.
2. It **resurrects no cycle conclusion**. A certificate holding across a family of
   shifts, several of which *have* cycles, makes "spectral gap ⟹ no cycles" false for
   **more** maps. If the integer version lands, `CYCLE_CLAIM_REFUTED.md` gets *stronger*,
   not weaker.
3. `Assembly.LemmaAFacts` stays non-parametric and is not instantiated here; route
   through `LevelMajorisation.norm_eigenvalue_le_cert_adjoint`, as `certS_le` does.
4. `hL2`/`hParseval` remains open, at `c = 1` and at every shift.
5. `A_c ≤ 0` - including the degenerate `A_c = 0` at `c = -3t` - is **deliberately out of
   scope** under this decision, and is recorded here so a later session does not mistake
   its absence for an oversight.
