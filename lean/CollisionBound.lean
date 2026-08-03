/-
# CollisionBound.lean -- Lemma B's combinatorial core: `coll(k) ≤ 3·2^k`

Task L4 of `OPUS_TASK_PLAN_2026-08-02.md`. Source of truth:
`LEMMA_B_PROOF.md` (the 2026-06-01 unconditional write-up, with the 2026-07-05
top-atom finding and the 2026-08-03 T6.1 correction banner).

This file discharges the hypothesis `hL2` that `GapCertificate.defect_sum_bound`
and `GapCertificate.certificate_lt_one` currently *assume*, modulo one explicitly
named Parseval link (see §8) which is an instance of the level-decomposition
machinery, not new content. Nothing here is axiomatised.

--------------------------------------------------------------------------------
## §0. THE FROZEN DEFINITION (quoted from LEMMA_B_PROOF.md before any proof)
--------------------------------------------------------------------------------

`LEMMA_B_PROOF.md`, lines 79-91, verbatim:

> The defect covector is `c[s] = (1/2^k) #{m in Z/2^k : Syr(r* + m 2^k) = 2s+1 (mod 2^k)}`.
> Writing `cf[t] = #{m : Syr(r*+m 2^k) = t}` (so `c = cf / 2^k` reindexed onto odd
> residues),
> ```
>     ||c||^2 = sum_s c[s]^2 = (1/4^k) sum_t cf[t]^2 = coll / 4^k,
>     coll := sum_t cf[t]^2.
> ```
> Hence `||c|| = sqrt(coll) / 2^k`, and Lemma B reduces to:
> ```
>     coll(k) <= 3 * 2^k    for all k.                                     [the whole content]
> ```

and lines 97-106, the model identity this file *proves* rather than assumes:

> The fibre value is `Syr(r* + m 2^k) = oddpart(3(r*+m 2^k)+1) (mod 2^k)`. Since `r*` is
> the unique odd residue with `v2(3r*+1) = 2 ceil(k/2)`, we have `3r*+1 = 2^{2 ceil(k/2)}`,
> so
> ```
>     3(r* + m 2^k) + 1 = 2^{2 ceil(k/2)} + 3m 2^k = 2^k (a + 3m),
>     a := 2^{2 ceil(k/2) - k} in {1, 2}
> ```
> Hence `Syr(r* + m 2^k) = oddpart(a + 3m) (mod 2^k)`.

The Lean rendering, fixed here and never widened afterwards:

```
cf   k t = #{ m < 2^k : oddPart (a k + 3 m) % 2^k = t }        -- `cf`
coll k   = Σ_{t < 2^k} (cf k t)^2                              -- `coll`
```

`m` ranges over `range (2^k)` = a full set of residues mod `2^k`; `t` ranges over
`range (2^k)`, which is exhaustive because every `fibVal` is a residue mod `2^k`.
**No narrowing** relative to the document: the sum is over *all* `t`, the fibre is
the *full* fibre, and `oddPart` is the true 2-adic odd part.

The link to the ACTUAL Syracuse map is proved, not assumed, in `syracuse_defect_fibre`
(§2): `syracuse (rstar k + m * 2^k) % 2^k = fibVal k m`, where `rstar k` is the true
defect residue `r* = -3⁻¹ mod 2^k` (`rstar_spec`, `rstar_odd`, `rstar_lt`,
`rstar_defect`). So `coll` counts collisions of the genuine Syracuse fibre over the
genuine `r*`, not of a convenient proxy. (This is failure mode (2) that L2 and L3
each caught once -- the right-looking theorem about the wrong object. The AP model
is a *theorem* here, `syracuse_defect_fibre`, not a definition.)

--------------------------------------------------------------------------------
## §0.1 MODEL SCOPE (standing gate 1): this lemma DISTINGUISHES 3x+1 from 3x-1
--------------------------------------------------------------------------------

`coll(k)` is the collision count of the defect fibre at `r* = -3⁻¹ mod 2^k`, i.e.
the *unique* odd residue at which `v2(3r+1) ≥ k`. That residue is defined by the
`+1`. The `3x-1` control map has its own defect residue `r*' = +3⁻¹ mod 2^k` (the
unique odd `r` with `v2(3r-1) ≥ k`), a different number, giving a different
arithmetic progression `a' + 3m` with a different `a'` and hence a different
collision count.

Per the T3.1 number-referee digest, the defect fibre is *exactly* where the two maps
genuinely differ: the naive negation conjugacy `x ↦ -x` intertwines the clean
(strictly-upper) parts of the two operators but FAILS at the defect row. So unlike
almost every other statement in this development -- which is sign-agnostic and
therefore carries no cycle content (see `CYCLE_CLAIM_REFUTED.md`) -- the collision
bound is a genuinely model-distinguishing statement about `3x+1`.

Two honest caveats, so the gate is passed non-vacuously and not over-claimed:

* The *numeric value* `coll(k)` differs between the two models; the *bound*
  `≤ 3·2^k` is proved here only for `3x+1`. The proof method (mod-3 class + interval
  width) would transfer, but that is not proved here and is not claimed.
* Distinguishing the models at the defect fibre does NOT resurrect any cycle
  conclusion. `3x-1` passes the same *certificate* (`cert(k) ≤ 0.8536`) and has real
  cycles, so certificate ⇒ no-cycles is false and stays withdrawn. This file is
  operator theory, full stop.

--------------------------------------------------------------------------------
## §0.2 CALIBRATION (standing gate 2) -- Python enumeration, k = 3..14
--------------------------------------------------------------------------------

Brute enumeration written for this task (`coll_enum.py`, `plan_check.py`,
scratchpad), computing `coll` BOTH from the true Syracuse fibre
`oddpart(3(r*+m·2^k)+1) mod 2^k` and from the document's AP model
`oddpart(a+3m) mod 2^k`. The two columns agree at every `k` tested -- an independent
check of `syracuse_defect_fibre` below.

```
  k  coll_true coll_model      3*2^k   margin   coll/2^k  ||c||*2^(k/2)   diag    cross   diag+2cross
  3         18         18         24        6    2.25000       1.500000       8        5        18
  4         42         42         48        6    2.62500       1.620185      16       13        42
  5         80         80         96       16    2.50000       1.581139      32       24        80
  6        166        166        192       26    2.59375       1.610512      64       51       166
  7        328        328        384       56    2.56250       1.600781     128      100       328
  8        662        662        768      106    2.58594       1.608085     256      203       662
  9       1320       1320       1536      216    2.57812       1.605654     512      404      1320
 10       2646       2646       3072      426    2.58398       1.607478    1024      811      2646
 11       5288       5288       6144      856    2.58203       1.606870    2048     1620      5288
 12      10582      10582      12288     1706    2.58350       1.607326    4096     3243     10582
 13      21160      21160      24576     3416    2.58301       1.607174    8192     6484     21160
 14      42326      42326      49152     6826    2.58337       1.607288   16384    12971     42326
```

Three known-quantity reproductions, none of them circular:

1. **The `1.6202` sharpness peak.** `THEOREM.md`'s sharpness remark reports a peak
   `‖c‖·2^{k/2} = 1.6202` at `k = 4`. Enumeration: the maximum over the whole table
   is `1.620185` at `k = 4`, and `1.620185² = 2.625000 = 42/16 = coll(4)/2^4`
   exactly. (`1.6202² = 2.625048`, the rounding of the same number.) REPRODUCED.
2. **The even-`k` closed form.** `LEMMA_B_PROOF.md` line 177 gives
   `coll = (31·2^k + 8)/12` for even `k` with values `166, 662, 2646, 10582` at
   `k = 6,8,10,12`; and `80, 328, 1320, 5288, 21160` for odd `k = 5,7,9,11,13`.
   Every one of those ten numbers is reproduced. REPRODUCED.
3. **The asymptotic ratio.** `coll(k)/2^k → 31/12 = 2.58333`, so
   `‖c‖·2^{k/2} → sqrt(31/12) = 1.607275`; the table converges to `1.607288` at
   `k = 14`. REPRODUCED.

The bound `coll(k) ≤ 3·2^k` holds at every tested `k` with margin, the smallest
relative margin being at `k = 4` (`42` vs `48`, 12.5% slack). No kill criterion
fired; the enumeration agrees with the document's literal definition.

**GRADE (witness vs evidence, following `LevelMajorisation.lean` §7).** The table
above is *external evidence*: it is produced by independently written Python from
the mathematical definition, not by re-running the Lean proof, and it reproduces
three quantities (`1.6202`, the ten closed-form values, `31/12`) that were published
in the repo BEFORE this task existed. It is therefore genuine corroboration, not a
tautology.

The `#eval` block in §9 is a *different and weaker* artifact and is graded
separately there: it is a satisfiability witness (the Lean `coll` is not vacuous and
computes the same integers), NOT independent evidence, because it evaluates the very
definition the theorem is about. It is deliberately NOT dressed up as a theorem --
a `theorem coll_calibration : coll 4 = 42 := by decide` would be provable by
`decide` alone and would read as a proved cross-check while proving nothing beyond
what `#eval` already shows. That trap (L3 caught one in itself) is avoided by not
stating it.

--------------------------------------------------------------------------------
## §0.3 ABSURD-HEIGHT LINE (standing gate 4)
--------------------------------------------------------------------------------

At `k = 10^9`: `coll(10^9) ≤ 3·2^(10^9)`, hence `‖c‖² ≤ 3·2^(-10^9)`, a number below
`10^(-3·10^8)`. Nothing in `coll_le` depends on `k` beyond `3 ≤ k` -- the constant
`3` is uniform, which is the entire content. As always in this development, such
smallness is a statement about the *operator*, and carries no cycle inference
whatsoever (`CYCLE_CLAIM_REFUTED.md`).

--------------------------------------------------------------------------------
## §0.4 THE PROOF, AND WHERE THE TOP ATOM IS HANDLED
--------------------------------------------------------------------------------

`LEMMA_B_PROOF.md` lines 113-172 decompose the AP `x = a + 3m`, `m < 2^k`, by 2-adic
valuation into shells `A_j = {x : v2 x = j}` for `j = 0..k-1`, "plus a single top
atom `x ≡ 0 (mod 2^k)`". The top atom is NOT an ordinary shell and the document's
cross-term series must be extended to infinity to absorb it (the 2026-07-05 Fable
review, Finding 3, lines 168-170).

This formalisation makes the atom a first-class shell rather than an afterthought.
`sh k m` (§3) is `k` exactly when `2^k ∣ a + 3m`, and `v2 (a+3m)` otherwise -- so
`sh` is a total function `range (2^k) → range (k+1)` and every `m` lies in exactly
one of `k+1` shells, atom included. Then:

* `shell_card_lt` : `|{m : sh k m = j}| = 2^(k-1-j)` for `j < k`   (ordinary shells)
* `shell_card_top`: `|{m : sh k m = k}| = 1`                        (THE TOP ATOM)
* `sum_sh`        : `Σ_{m < 2^k} sh k m = 2^k - 1`                  (both, together)

`sum_sh` is where the atom is paid for, and it is paid for *exactly*, not by a series
tail: `Σ_{j<k} j·2^(k-1-j) = 2^k - k - 1` (`geom_weighted`), plus the atom's own
contribution `k·1 = k`, giving `2^k - 1` on the nose. The document's
`Σ_{j'≥k} j'·2^(k-1-j') = k+1 ≥ k` slack argument is therefore *replaced* by an exact
identity here, not reproduced. Numerically: at `k = 3` the document's finite series
`Σ_{j<k} j·2^(k-1-j) = 4` is genuinely SMALLER than the true cross count `5`, so the
top atom is load-bearing and dropping it would break the bound at small `k` -- the
2026-07-05 finding is correct and this file does not silently drop the atom.

Collision pairs (`collPairs`, §5) split by comparing shells:

* equal shells  → `E`, forced to the diagonal by FACT 1 (`fact1_shell`), so `|E| = 2^k`
* `sh m < sh m'` → `L`, and `|L| ≤ Σ_{m'} sh k m' = 2^k - 1` because for each `m'` the
  colliding partners in strictly lower shells inject into `range (sh k m')` (FACT 1
  again: at most one partner per shell)
* `sh m > sh m'` → `G`, in bijection with `L` by swapping

giving `coll = |E| + 2|L| ≤ 2^k + 2(2^k - 1) = 3·2^k - 2 ≤ 3·2^k`. This is the
document's `diag + 2·cross` split (lines 152-172) with `diag = 2^k` exact and
`cross ≤ 2^k - 1`; the document states `cross ≤ 2^k`, so the Lean bound is very
slightly *stronger* (by `2`), never weaker. Enumeration confirms both:
`coll = diag + 2·cross` exactly at every tested `k`, `diag = 2^k` at every `k`,
`cross ≤ 2^k - 1` at every `k`.

FACT 1 itself is NOT reproved: it is `GapCertificate.fact1_injective`, imported.

--------------------------------------------------------------------------------
## §0.5 WHAT IS PROVED HERE, IN ONE LINE
--------------------------------------------------------------------------------

`coll_le : 3 ≤ k → coll k ≤ 3 * 2^k`, and its Real corollary
`defect_norm_sq_le : (coll k : ℝ)/4^k ≤ 3 * s^(2k)` for `s² = 1/2` -- exactly the
right-hand side of `GapCertificate.defect_sum_bound`'s `hL2`. See §8 for precisely
which hypothesis remains, and why it is not axiomatised.
-/
import CountingLemmas

namespace CollisionBound

open Finset GapCertificate CountingLemmas

/-!
--------------------------------------------------------------------------------
## §1. The defect residue `r*` and the arithmetic progression `a + 3m`
--------------------------------------------------------------------------------
-/

/-- `ek k = 2⌈k/2⌉`, the exact 2-adic valuation of `3r* + 1`
(`LEMMA_B_PROOF.md` line 98). -/
def ek (k : ℕ) : ℕ := 2 * ((k + 1) / 2)

theorem le_ek (k : ℕ) : k ≤ ek k := by unfold ek; omega

theorem ek_le (k : ℕ) : ek k ≤ k + 1 := by unfold ek; omega

/-- `a := 2^(2⌈k/2⌉ - k) ∈ {1, 2}` (`LEMMA_B_PROOF.md` line 102). -/
def apA (k : ℕ) : ℕ := 2 ^ (ek k - k)

theorem apA_pos (k : ℕ) : 0 < apA k := Nat.two_pow_pos _

/-- `a ∈ {1, 2}`: `1` for even `k`, `2` for odd `k`. -/
theorem apA_eq (k : ℕ) : apA k = 1 ∨ apA k = 2 := by
  unfold apA ek
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · left
    have : 2 * ((k + 1) / 2) - k = 0 := by omega
    rw [this]; norm_num
  · right
    have : 2 * ((k + 1) / 2) - k = 1 := by omega
    rw [this]; norm_num

theorem apA_spec (k : ℕ) : 2 ^ k * apA k = 2 ^ ek k := by
  unfold apA
  rw [← pow_add]
  congr 1
  have := le_ek k
  omega

/-- The defect residue `r* = -3⁻¹ mod 2^k`, in the closed form
`(2^(2⌈k/2⌉) - 1)/3` forced by `3r* + 1 = 2^(2⌈k/2⌉)`. -/
def rstar (k : ℕ) : ℕ := (2 ^ ek k - 1) / 3

theorem two_pow_ek_mod_three (k : ℕ) : 2 ^ ek k % 3 = 1 := by
  unfold ek
  rw [pow_mul]
  simp [Nat.pow_mod]

/-- **`3r* + 1 = 2^(2⌈k/2⌉)`** -- the defining property (`LEMMA_B_PROOF.md` line 98). -/
theorem rstar_spec (k : ℕ) : 3 * rstar k + 1 = 2 ^ ek k := by
  have h1 := two_pow_ek_mod_three k
  have h2 : 1 ≤ 2 ^ ek k := Nat.one_le_two_pow
  unfold rstar
  omega

/-- `r*` is odd (so the Syracuse map takes its odd branch on every lift). -/
theorem rstar_odd {k : ℕ} (hk : 1 ≤ k) : rstar k % 2 = 1 := by
  have h1 := rstar_spec k
  have h2 : 2 ^ ek k % 2 = 0 := by
    have : (2 : ℕ) ∣ 2 ^ ek k := dvd_pow_self 2 (by have := le_ek k; omega)
    omega
  omega

/-- `r* < 2^k`: it really is a residue mod `2^k`. -/
theorem rstar_lt {k : ℕ} (hk : 1 ≤ k) : rstar k < 2 ^ k := by
  have h1 := rstar_spec k
  have h2 : (2 : ℕ) ^ ek k ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by norm_num) (ek_le k)
  have h3 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  omega

/-- **`r*` is the defect residue**: `2^k ∣ 3r* + 1`, i.e. `k ≤ v2 (3r*+1)`. This is
the `CountingLemmas.defectSet` membership condition, so `rstar k` is *the* element of
`CountingLemmas.defectSet k` (which `CountingLemmas.defect_card` proves is a
singleton). -/
theorem rstar_defect {k : ℕ} (hk : 1 ≤ k) : (3 * rstar k + 1) % 2 ^ k = 0 := by
  rw [rstar_spec k, ← apA_spec k]
  simp [Nat.mul_mod_right]

/-- **`rstar k` IS the `r*` of `CountingLemmas`.** It is a member of
`CountingLemmas.defectSet k`, which `CountingLemmas.defect_card` proves is a
singleton. So there is no room for a different-`r*` reading of `coll`. -/
theorem rstar_mem_defectSet {k : ℕ} (hk : 1 ≤ k) : rstar k ∈ defectSet k := by
  refine mem_filter.mpr ⟨mem_range.mpr (rstar_lt hk), ?_, rstar_odd hk, ?_⟩
  · have := rstar_odd hk; omega
  · exact defect_iff.mpr (rstar_defect hk)

/-- **UNIQUENESS.** Any odd `r < 2^k` with `2^k ∣ 3r+1` equals `rstar k`. Together
with `rstar_mem_defectSet` this pins `rstar k` as *the* defect residue
`r* = -3⁻¹ mod 2^k`, not merely *a* residue with that property. -/
theorem eq_rstar {k r : ℕ} (hk : 1 ≤ k) (hr : r < 2 ^ k) (hodd : r % 2 = 1)
    (hdef : (3 * r + 1) % 2 ^ k = 0) : r = rstar k := by
  have hmem : r ∈ defectSet k :=
    mem_filter.mpr ⟨mem_range.mpr hr, by omega, hodd, defect_iff.mpr hdef⟩
  exact Finset.card_le_one.mp (le_of_eq (defect_card hk)) r hmem _ (rstar_mem_defectSet hk)

/-- The AP term `x_m = a + 3m` (`LEMMA_B_PROOF.md` line 106). -/
def apTerm (k m : ℕ) : ℕ := apA k + 3 * m

theorem apTerm_pos (k m : ℕ) : 0 < apTerm k m := by
  unfold apTerm; have := apA_pos k; omega

theorem apTerm_ne_zero (k m : ℕ) : apTerm k m ≠ 0 := (apTerm_pos k m).ne'

/-!
--------------------------------------------------------------------------------
## §2. The odd part, and the identification with the true Syracuse fibre
--------------------------------------------------------------------------------
-/

/-- `oddPart n = n / 2^(v2 n)`. -/
def oddPart (n : ℕ) : ℕ := n / 2 ^ v2 n

theorem two_pow_mul_oddPart {n : ℕ} (hn : n ≠ 0) : 2 ^ v2 n * oddPart n = n :=
  Nat.mul_div_cancel' (pow_v2_dvd n hn)

theorem v2_two_pow_mul {c n : ℕ} (hn : n ≠ 0) : v2 (2 ^ c * n) = c + v2 n := by
  unfold v2
  rw [padicValNat.mul (by positivity) hn, padicValNat.prime_pow]

theorem oddPart_two_pow_mul {c n : ℕ} (hn : n ≠ 0) :
    oddPart (2 ^ c * n) = oddPart n := by
  unfold oddPart
  rw [v2_two_pow_mul (c := c) hn, pow_add]
  exact Nat.mul_div_mul_left _ _ (Nat.two_pow_pos c)

/-- **The fibre value**: `fibVal k m = oddpart(a + 3m) mod 2^k`. -/
def fibVal (k m : ℕ) : ℕ := oddPart (apTerm k m) % 2 ^ k

theorem fibVal_lt (k m : ℕ) : fibVal k m < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

/-- **THE MODEL IDENTITY, PROVED.** `Syr(r* + m·2^k) ≡ oddpart(a + 3m) (mod 2^k)`.

`LEMMA_B_PROOF.md` line 105 states this and cross-checks it numerically
(`lemmaB_fact1_rigorous.py`, column `=syr?`). Here it is a theorem, so `coll` below
counts collisions of the genuine Syracuse map on the genuine defect fibre. -/
theorem syracuse_defect_fibre {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    syracuse (rstar k + m * 2 ^ k) % 2 ^ k = fibVal k m := by
  have hlift_odd : (rstar k + m * 2 ^ k) % 2 = 1 := by
    have h2 : (2 : ℕ) ∣ m * 2 ^ k := (dvd_pow_self 2 (by omega : k ≠ 0)).mul_left m
    have := rstar_odd hk
    omega
  have h3n : 3 * (rstar k + m * 2 ^ k) + 1 = 2 ^ k * apTerm k m := by
    calc 3 * (rstar k + m * 2 ^ k) + 1 = (3 * rstar k + 1) + 3 * m * 2 ^ k := by ring
      _ = 2 ^ ek k + 3 * m * 2 ^ k := by rw [rstar_spec k]
      _ = 2 ^ k * apA k + 2 ^ k * (3 * m) := by rw [← apA_spec k]; ring
      _ = 2 ^ k * apTerm k m := by unfold apTerm; ring
  unfold syracuse
  rw [if_neg (by omega)]
  show (3 * (rstar k + m * 2 ^ k) + 1) / 2 ^ v2 (3 * (rstar k + m * 2 ^ k) + 1) % 2 ^ k
      = fibVal k m
  rw [h3n]
  show oddPart (2 ^ k * apTerm k m) % 2 ^ k = fibVal k m
  rw [oddPart_two_pow_mul (apTerm_ne_zero k m)]
  rfl

/-!
--------------------------------------------------------------------------------
## §3. `coll(k)`: the frozen definition
--------------------------------------------------------------------------------
-/

/-- `cf k t = #{m < 2^k : Syr(r* + m·2^k) ≡ t (mod 2^k)}` (`LEMMA_B_PROOF.md`
line 80, via `syracuse_defect_fibre`). -/
def cf (k t : ℕ) : ℕ := ((range (2 ^ k)).filter (fun m => fibVal k m = t)).card

/-- **`coll(k) := Σ_t cf[t]²`** (`LEMMA_B_PROOF.md` line 84). The sum over
`t < 2^k` is exhaustive: `fibVal` is always a residue mod `2^k`. -/
def coll (k : ℕ) : ℕ := ∑ t ∈ range (2 ^ k), (cf k t) ^ 2

/-- The shell index. `sh k m = k` exactly on the TOP ATOM `2^k ∣ a + 3m`; otherwise
it is the 2-adic valuation `v2 (a + 3m)`. Total function into `{0,...,k}`. -/
def sh (k m : ℕ) : ℕ := if apTerm k m % 2 ^ k = 0 then k else v2 (apTerm k m)

theorem sh_le (k m : ℕ) : sh k m ≤ k := by
  unfold sh
  split
  · exact le_rfl
  · rename_i hne
    by_contra hcon
    push_neg at hcon
    have hdvd : 2 ^ k ∣ apTerm k m :=
      dvd_trans (pow_dvd_pow 2 (by omega)) (pow_v2_dvd _ (apTerm_ne_zero k m))
    obtain ⟨c, hc⟩ := hdvd
    exact hne (by simp [hc, Nat.mul_mod_right])

/-- Below the top, `sh` is the valuation, characterised as a residue condition. -/
theorem sh_eq_iff_lt {k j m : ℕ} (hj : j < k) :
    sh k m = j ↔ apTerm k m % 2 ^ (j + 1) = 2 ^ j := by
  unfold sh
  split
  · rename_i htop
    have hdvd : 2 ^ (j + 1) ∣ apTerm k m :=
      dvd_trans (pow_dvd_pow 2 (by omega)) (Nat.dvd_of_mod_eq_zero htop)
    obtain ⟨c, hc⟩ := hdvd
    have h0 : apTerm k m % 2 ^ (j + 1) = 0 := by simp [hc, Nat.mul_mod_right]
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    constructor
    · intro h; omega
    · intro h; omega
  · exact v2_eq_iff_mod (apTerm_ne_zero k m)

/-- The top shell is exactly the divisibility condition. -/
theorem sh_eq_top_iff {k m : ℕ} (hk : 1 ≤ k) :
    sh k m = k ↔ apTerm k m % 2 ^ k = 0 := by
  unfold sh
  split
  · rename_i h; simp [h]
  · rename_i hne
    constructor
    · intro h
      exfalso
      have hdvd : 2 ^ k ∣ apTerm k m := by
        have hd := pow_v2_dvd (apTerm k m) (apTerm_ne_zero k m)
        rwa [h] at hd
      obtain ⟨c, hc⟩ := hdvd
      exact hne (by simp [hc, Nat.mul_mod_right])
    · intro h; exact absurd h hne

/-!
--------------------------------------------------------------------------------
## §4. Shell cardinalities (the equidistribution of `a + 3m` mod `2^(j+1)`)
--------------------------------------------------------------------------------

Both counts come from `CountingLemmas`' two counting primitives -- `residue_class_card`
and `three_mul_add_existsUnique` -- with no new number theory.
-/

/-- The shell condition, rewritten as a residue class in `m`. -/
private theorem shell_as_class {k M c : ℕ} (hMk : M ≤ k) (hc : c < 2 ^ M) :
    ∃ r < 2 ^ M,
      (range (2 ^ k)).filter (fun m => apTerm k m % 2 ^ M = c)
        = (range (2 ^ k)).filter (fun m => m % 2 ^ M = r) := by
  obtain ⟨r, ⟨hr, hrc⟩, _⟩ := three_mul_add_existsUnique M (apA k) hc
  refine ⟨r, hr, ?_⟩
  ext m
  simp only [mem_filter, mem_range, and_congr_right_iff]
  intro _
  constructor
  · intro h
    have h1 : (3 * (m % 2 ^ M) + apA k) % 2 ^ M = c := by
      rw [three_mul_add_mod_mod]
      unfold apTerm at h
      rw [← h]; ring_nf
    exact three_mul_add_inj (Nat.mod_lt _ (Nat.two_pow_pos M)) hr (by rw [h1, hrc])
  · intro h
    have h1 : (3 * (m % 2 ^ M) + apA k) % 2 ^ M = c := by rw [h, hrc]
    rw [three_mul_add_mod_mod] at h1
    unfold apTerm
    rw [← h1]; ring_nf

/-- **ORDINARY SHELL CARDINALITY.** `|{m < 2^k : sh k m = j}| = 2^(k-1-j)` for
`j < k`. This is `LEMMA_B_PROOF.md` line 117's `|A_j| = 2^{k-1-j}`. -/
theorem shell_card_lt {k j : ℕ} (hj : j < k) :
    ((range (2 ^ k)).filter (fun m => sh k m = j)).card = 2 ^ (k - 1 - j) := by
  have hset : (range (2 ^ k)).filter (fun m => sh k m = j)
      = (range (2 ^ k)).filter (fun m => apTerm k m % 2 ^ (j + 1) = 2 ^ j) := by
    apply filter_congr
    intro m _
    simpa using sh_eq_iff_lt (m := m) hj
  rw [hset]
  obtain ⟨r, hr, hcl⟩ := shell_as_class (k := k) (M := j + 1) (c := 2 ^ j)
    (by omega) (by exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  rw [hcl, residue_class_card (by omega) hr]
  congr 1
  omega

/-- **TOP ATOM CARDINALITY.** `|{m < 2^k : sh k m = k}| = 1`: the single atom
`x ≡ 0 (mod 2^k)` of `LEMMA_B_PROOF.md` line 117. -/
theorem shell_card_top {k : ℕ} (hk : 1 ≤ k) :
    ((range (2 ^ k)).filter (fun m => sh k m = k)).card = 1 := by
  have hset : (range (2 ^ k)).filter (fun m => sh k m = k)
      = (range (2 ^ k)).filter (fun m => apTerm k m % 2 ^ k = 0) := by
    apply filter_congr
    intro m _
    simpa using sh_eq_top_iff (m := m) hk
  rw [hset]
  obtain ⟨r, hr, hcl⟩ := shell_as_class (k := k) (M := k) (c := 0) le_rfl
    (Nat.two_pow_pos k)
  rw [hcl, residue_class_card le_rfl hr]
  simp

/-- Every `m` lands in one of the `k+1` shells `0,...,k`. -/
theorem sh_mem_range (k m : ℕ) : sh k m ∈ range (k + 1) := by
  simp only [mem_range]
  have := sh_le k m
  omega

/-- **The weighted geometric identity.** `Σ_{j<k} j·2^(k-1-j) + k + 1 = 2^k`.
Equivalently `Σ_{j<k} j·2^(k-1-j) = 2^k - k - 1` -- the exact finite form of the
document's series (whose infinite extension to `2^k` was the 2026-07-05 top-atom
patch; here the atom's own `k` is added exactly instead). -/
theorem geom_weighted (k : ℕ) : (∑ j ∈ range k, j * 2 ^ (k - 1 - j)) + k + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ j ∈ range (n + 1), j * 2 ^ (n + 1 - 1 - j)
        = (∑ j ∈ range n, j * 2 ^ (n - j)) + n := by
      rw [Finset.sum_range_succ]
      simp
    have hdouble : ∑ j ∈ range n, j * 2 ^ (n - j) = 2 * ∑ j ∈ range n, j * 2 ^ (n - 1 - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [mem_range] at hj
      have : n - j = (n - 1 - j) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [hsplit, hdouble, pow_succ]
    omega

/-- **THE SHELL SUM, atom included.** `Σ_{m < 2^k} sh k m = 2^k - 1`.

`= Σ_{j<k} j·2^(k-1-j)  +  k·1  =  (2^k - k - 1) + k`. The second summand is the top
atom's contribution; it is exactly what the document's infinite-series slack was
covering. -/
theorem sum_sh {k : ℕ} (hk : 1 ≤ k) :
    (∑ m ∈ range (2 ^ k), sh k m) + 1 = 2 ^ k := by
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := range (2 ^ k)) (t := range (k + 1)) (g := sh k) (f := sh k)
    (fun m _ => sh_mem_range k m)
  have hinner : ∀ j ∈ range (k + 1),
      (∑ m ∈ (range (2 ^ k)).filter (fun m => sh k m = j), sh k m)
        = j * ((range (2 ^ k)).filter (fun m => sh k m = j)).card := by
    intro j _
    rw [Finset.sum_congr rfl (fun m hm => (mem_filter.mp hm).2)]
    simp [mul_comm]
  rw [← hfib, Finset.sum_congr rfl hinner, Finset.sum_range_succ]
  rw [shell_card_top hk]
  have hcards : ∀ j ∈ range k,
      j * ((range (2 ^ k)).filter (fun m => sh k m = j)).card = j * 2 ^ (k - 1 - j) := by
    intro j hj
    simp only [mem_range] at hj
    rw [shell_card_lt hj]
  rw [Finset.sum_congr rfl hcards]
  have := geom_weighted k
  omega

/-!
--------------------------------------------------------------------------------
## §5. FACT 1 in shell form
--------------------------------------------------------------------------------
-/

/-- **FACT 1 (per-shell injectivity), shell form.** Two lift indices in the *same*
ordinary shell with the same fibre value are equal.

`LEMMA_B_PROOF.md` lines 122-136. The engine is `GapCertificate.fact1_injective`,
imported and not reproved: `(I) u - u' = 2^k s`, `(II) 3 ∣ s`, `(R) |x - x'| < 3·2^k`,
so `2^j|s| < 3` and `s = 0`. -/
theorem fact1_shell {k j m m' : ℕ} (hj : j < k) (hm : m < 2 ^ k) (hm' : m' < 2 ^ k)
    (h1 : sh k m = j) (h2 : sh k m' = j) (hf : fibVal k m = fibVal k m') : m = m' := by
  -- Below the top, `sh` is the valuation, so both AP terms factor as `2^j * u`.
  have hv : v2 (apTerm k m) = j := by
    unfold sh at h1
    split at h1
    · omega
    · exact h1
  have hv' : v2 (apTerm k m') = j := by
    unfold sh at h2
    split at h2
    · omega
    · exact h2
  have hx : apTerm k m = 2 ^ j * oddPart (apTerm k m) := by
    rw [← hv]; exact (two_pow_mul_oddPart (apTerm_ne_zero k m)).symm
  have hx' : apTerm k m' = 2 ^ j * oddPart (apTerm k m') := by
    rw [← hv']; exact (two_pow_mul_oddPart (apTerm_ne_zero k m')).symm
  -- The fibre values agreeing is `2^k ∣ u - u'`.
  have hmod : oddPart (apTerm k m) % 2 ^ k = oddPart (apTerm k m') % 2 ^ k := hf
  have hdvd : (2 : ℤ) ^ k ∣ (oddPart (apTerm k m) : ℤ) - (oddPart (apTerm k m') : ℤ) := by
    have : Nat.ModEq (2 ^ k) (oddPart (apTerm k m')) (oddPart (apTerm k m)) := hmod.symm
    have h := (Nat.modEq_iff_dvd).1 this
    push_cast at h
    exact h
  -- Apply the imported engine over ℤ.
  have hZ : (m : ℤ) = (m' : ℤ) := by
    refine fact1_injective (k := k) (j := j) (a := (apA k : ℤ))
      (u := (oddPart (apTerm k m) : ℤ)) (u' := (oddPart (apTerm k m') : ℤ))
      (by positivity) (by exact_mod_cast hm) (by positivity) (by exact_mod_cast hm')
      ?_ ?_ hdvd
    · have := hx; unfold apTerm at this; exact_mod_cast this
    · have := hx'; unfold apTerm at this; exact_mod_cast this
  exact_mod_cast hZ

/-- FACT 1 extended over the TOP ATOM: the top shell has one element, so the same
conclusion holds there for free. Together with `fact1_shell` this says the fibre map
is injective on every shell, atom included. -/
theorem fact1_all {k m m' : ℕ} (hk : 1 ≤ k) (hm : m < 2 ^ k) (hm' : m' < 2 ^ k)
    (hsh : sh k m = sh k m') (hf : fibVal k m = fibVal k m') : m = m' := by
  rcases Nat.lt_or_ge (sh k m) k with hlt | hge
  · exact fact1_shell hlt hm hm' rfl hsh.symm hf
  · have hmk : sh k m = k := le_antisymm (sh_le k m) hge
    have hm'k : sh k m' = k := hsh ▸ hmk
    have hcard := shell_card_top (k := k) hk
    have hmem : m ∈ (range (2 ^ k)).filter (fun x => sh k x = k) :=
      mem_filter.mpr ⟨mem_range.mpr hm, hmk⟩
    have hmem' : m' ∈ (range (2 ^ k)).filter (fun x => sh k x = k) :=
      mem_filter.mpr ⟨mem_range.mpr hm', hm'k⟩
    exact Finset.card_le_one.mp (le_of_eq hcard) m hmem m' hmem'

/-!
--------------------------------------------------------------------------------
## §6. The collision pair set and the diag / cross split
--------------------------------------------------------------------------------
-/

/-- The collision pairs `{(m,m') ∈ [0,2^k)² : fibVal m = fibVal m'}`. -/
def collPairs (k : ℕ) : Finset (ℕ × ℕ) :=
  ((range (2 ^ k)) ×ˢ (range (2 ^ k))).filter (fun p => fibVal k p.1 = fibVal k p.2)

/-- Membership in `collPairs`, unfolded once and for all. -/
theorem mem_collPairs {k : ℕ} {p : ℕ × ℕ} :
    p ∈ collPairs k ↔ p.1 < 2 ^ k ∧ p.2 < 2 ^ k ∧ fibVal k p.1 = fibVal k p.2 := by
  simp only [collPairs, mem_filter, Finset.mem_product, mem_range, and_assoc]

/-- `coll = |collPairs|`: the `Σ_t cf[t]²` definition equals the pair count. -/
theorem coll_eq_card (k : ℕ) : coll k = (collPairs k).card := by
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => fibVal k p.1)
      (↑(collPairs k) : Set (ℕ × ℕ)) (↑(range (2 ^ k)) : Set ℕ) := by
    intro p _
    simp only [Finset.mem_coe, mem_range]
    exact fibVal_lt k p.1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  unfold coll
  apply Finset.sum_congr rfl
  intro t _
  have hfib : (collPairs k).filter (fun p => fibVal k p.1 = t)
      = ((range (2 ^ k)).filter (fun m => fibVal k m = t))
        ×ˢ ((range (2 ^ k)).filter (fun m => fibVal k m = t)) := by
    ext p
    simp only [mem_filter, mem_collPairs, Finset.mem_product, mem_range]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨h1, h4⟩, h2, by rw [← h3, h4]⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3, by rw [h2, h4]⟩, h2⟩
  rw [hfib, Finset.card_product]
  unfold cf
  ring

/-- The equal-shell part. -/
def Eset (k : ℕ) : Finset (ℕ × ℕ) := (collPairs k).filter (fun p => sh k p.1 = sh k p.2)

/-- The strictly-lower part `sh m < sh m'`. -/
def Lset (k : ℕ) : Finset (ℕ × ℕ) := (collPairs k).filter (fun p => sh k p.1 < sh k p.2)

/-- The strictly-upper part `sh m > sh m'`. -/
def Gset (k : ℕ) : Finset (ℕ × ℕ) := (collPairs k).filter (fun p => sh k p.2 < sh k p.1)

theorem mem_Lset {k : ℕ} {p : ℕ × ℕ} :
    p ∈ Lset k ↔ (p.1 < 2 ^ k ∧ p.2 < 2 ^ k ∧ fibVal k p.1 = fibVal k p.2)
      ∧ sh k p.1 < sh k p.2 := by
  simp only [Lset, mem_filter, mem_collPairs]

theorem mem_Gset {k : ℕ} {p : ℕ × ℕ} :
    p ∈ Gset k ↔ (p.1 < 2 ^ k ∧ p.2 < 2 ^ k ∧ fibVal k p.1 = fibVal k p.2)
      ∧ sh k p.2 < sh k p.1 := by
  simp only [Gset, mem_filter, mem_collPairs]

theorem mem_Eset {k : ℕ} {p : ℕ × ℕ} :
    p ∈ Eset k ↔ (p.1 < 2 ^ k ∧ p.2 < 2 ^ k ∧ fibVal k p.1 = fibVal k p.2)
      ∧ sh k p.1 = sh k p.2 := by
  simp only [Eset, mem_filter, mem_collPairs]

theorem card_split (k : ℕ) :
    (collPairs k).card = (Eset k).card + (Lset k).card + (Gset k).card := by
  classical
  have h1 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := collPairs k) (p := fun p => sh k p.1 = sh k p.2)
  have h2 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (collPairs k).filter (fun p => ¬ sh k p.1 = sh k p.2))
    (p := fun p => sh k p.1 < sh k p.2)
  have hL : ((collPairs k).filter (fun p => ¬ sh k p.1 = sh k p.2)).filter
      (fun p => sh k p.1 < sh k p.2) = Lset k := by
    unfold Lset
    rw [Finset.filter_filter]
    apply filter_congr
    intro p _
    omega
  have hG : ((collPairs k).filter (fun p => ¬ sh k p.1 = sh k p.2)).filter
      (fun p => ¬ sh k p.1 < sh k p.2) = Gset k := by
    unfold Gset
    rw [Finset.filter_filter]
    apply filter_congr
    intro p _
    omega
  rw [hL, hG] at h2
  unfold Eset
  omega

/-- **DIAGONAL (exact).** `|E| = 2^k`: by FACT 1 (atom included) the equal-shell
collision pairs are exactly the diagonal. `LEMMA_B_PROOF.md` line 158's
`diag = (2^k - 1) + 1 = 2^k`. -/
theorem card_Eset {k : ℕ} (hk : 1 ≤ k) : (Eset k).card = 2 ^ k := by
  have hinj : Function.Injective (fun m : ℕ => (m, m)) := by
    intro a b h
    exact congrArg Prod.fst h
  have hset : Eset k = (range (2 ^ k)).image (fun m => (m, m)) := by
    ext ⟨a, b⟩
    simp only [mem_Eset, mem_image, mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨a, h1, rfl, fact1_all hk h1 h2 h4 h3⟩
    · rintro ⟨m, hm, rfl, rfl⟩
      exact ⟨⟨hm, hm, rfl⟩, rfl⟩
  rw [hset, Finset.card_image_of_injective _ hinj, card_range]

/-- `|G| = |L|` by the swap involution. -/
theorem card_Gset_eq (k : ℕ) : (Gset k).card = (Lset k).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.2, p.1)) := by
    intro a b h
    have h1 : a.2 = b.2 := congrArg Prod.fst h
    have h2 : a.1 = b.1 := congrArg Prod.snd h
    exact Prod.ext h2 h1
  have hset : Gset k = (Lset k).image (fun p : ℕ × ℕ => (p.2, p.1)) := by
    ext ⟨a, b⟩
    simp only [mem_Gset, mem_image, mem_Lset, Prod.exists, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨b, a, ⟨⟨h2, h1, h3.symm⟩, h4⟩, rfl, rfl⟩
    · rintro ⟨x, y, ⟨⟨h1, h2, h3⟩, h4⟩, rfl, rfl⟩
      exact ⟨⟨h2, h1, h3.symm⟩, h4⟩
  rw [hset, Finset.card_image_of_injective _ hinj]

/-- **CROSS (bound).** For each `m'`, the strictly-lower colliding partners inject
into `range (sh k m')` via `sh` -- at most one per shell, by FACT 1. -/
theorem fibre_L_card_le {k m' : ℕ} (hk : 1 ≤ k) :
    ((Lset k).filter (fun p => p.2 = m')).card ≤ sh k m' := by
  have hcard : (range (sh k m')).card = sh k m' := card_range _
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => sh k p.1)
  · intro p hp
    simp only [Finset.mem_coe, mem_filter, mem_Lset] at hp
    simp only [Finset.mem_coe, mem_range]
    rw [← hp.2]
    exact hp.1.2
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, mem_filter, mem_Lset] at hp hq
    have hp2 : p.2 = m' := hp.2
    have hq2 : q.2 = m' := hq.2
    have hjk : sh k p.1 < k := lt_of_lt_of_le hp.1.2 (sh_le k p.2)
    have hfp : fibVal k p.1 = fibVal k q.1 := by
      rw [hp.1.1.2.2, hq.1.1.2.2, hp2, hq2]
    have h1 : p.1 = q.1 := fact1_shell hjk hp.1.1.1 hq.1.1.1 rfl hpq.symm hfp
    have h2 : p.2 = q.2 := by rw [hp2, hq2]
    exact Prod.ext h1 h2

theorem card_Lset_le {k : ℕ} (hk : 1 ≤ k) : (Lset k).card + 1 ≤ 2 ^ k := by
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.2)
      (↑(Lset k) : Set (ℕ × ℕ)) (↑(range (2 ^ k)) : Set ℕ) := by
    intro p hp
    simp only [Finset.mem_coe, mem_Lset] at hp
    simp only [Finset.mem_coe, mem_range]
    exact hp.1.2.1
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  have hle : ∑ m' ∈ range (2 ^ k), ((Lset k).filter (fun p => p.2 = m')).card
      ≤ ∑ m' ∈ range (2 ^ k), sh k m' :=
    Finset.sum_le_sum (fun m' _ => fibre_L_card_le hk)
  have := sum_sh hk
  omega


/-!
--------------------------------------------------------------------------------
## §7. THE COLLISION BOUND
--------------------------------------------------------------------------------
-/

/-- **THE COLLISION BOUND (sharpened form).** `coll(k) ≤ 3·2^k - 2` for `k ≥ 1`.

`diag = 2^k` exactly + `2·cross ≤ 2·(2^k - 1)`. `LEMMA_B_PROOF.md` line 172 states
`cross ≤ 2^k`; the exact top-atom accounting here gives `cross ≤ 2^k - 1`, so this is
two better and never weaker. -/
theorem coll_le_sharp {k : ℕ} (hk : 1 ≤ k) : coll k + 2 ≤ 3 * 2 ^ k := by
  rw [coll_eq_card, card_split, card_Gset_eq, card_Eset hk]
  have := card_Lset_le hk
  omega

/-- **THE COLLISION BOUND, as stated in `LEMMA_B_PROOF.md` line 90:**

> `coll(k) <= 3 * 2^k    for all k.                                     [the whole content]`

Stated for `k ≥ 3` to match the certificate's range; `coll_le_sharp` gives it for
every `k ≥ 1`. -/
theorem coll_le {k : ℕ} (hk : 3 ≤ k) : coll k ≤ 3 * 2 ^ k := by
  have := coll_le_sharp (k := k) (by omega)
  omega

/-!
--------------------------------------------------------------------------------
## §8. THE BRIDGE TO `hL2` -- and exactly what remains assumed
--------------------------------------------------------------------------------

`GapCertificate.defect_sum_bound` and `certificate_lt_one` take

```
hL2 : ∑ b ∈ range K, (v b)^2 ≤ 3 * s^(2*k)
```

as a hypothesis, with `v b = ‖P_b c‖` and `s² = 1/2`. `LEMMA_B_PROOF.md` line 63:

> And `||v||^2 = sum_b v_b^2 = ||c||^2 - 1/N <= ||c||^2`: the level sum runs over
> `b = 0..k-2` and omits the Perron direction `xi = 0` [...] The omitted term only
> strengthens the bound.

together with line 83, `||c||^2 = coll / 4^k`. So the chain is

```
   ∑_b v_b²  ≤  ‖c‖²  =  coll(k)/4^k   ≤   3·2^k/4^k  =  3·2^(-k)  =  3·s^(2k).
   \________________________________/      \_________________________________/
        Parseval over levels (L2)                    PROVED HERE
```

`defect_norm_sq_le` below proves the right-hand half unconditionally. The left-hand
half -- `∑_b ‖P_b c‖² ≤ ‖c‖² = coll/4^k` -- is Parseval/Bessel for the level
decomposition, i.e. an *instance of L2's machinery on a concrete vector*, not new
content and not this task's object. It is therefore carried as a **single named
hypothesis** `hParseval` in `hL2_of_parseval`, NOT axiomatised and NOT `sorry`ed.

**STATUS: `hL2` is CONDITIONAL on one named hypothesis.** Discharging `hParseval`
requires the concrete level-projection `P_b` on `ℓ²(Z/2^k)` and `c` as an actual
vector -- objects that do not yet exist in this Lean development (L2's
`LevelMajorisation.lean` is abstract in the projections). That is the remaining gap,
and it is a Bessel inequality, not a counting fact.
-/

/-- **The Real-valued form of the collision bound**, in exactly the shape
`GapCertificate.defect_sum_bound`'s `hL2` wants on the right. Unconditional. -/
theorem defect_norm_sq_le {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2) {k : ℕ} (hk : 3 ≤ k) :
    (coll k : ℝ) / 4 ^ k ≤ 3 * s ^ (2 * k) := by
  have hcoll : (coll k : ℝ) ≤ 3 * 2 ^ k := by exact_mod_cast coll_le hk
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hs2k : s ^ (2 * k) = (1 / 2 : ℝ) ^ k := by rw [pow_mul, hsq]
  have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  rw [hs2k, h4, div_le_iff₀ (by positivity)]
  have key : 3 * ((1 / 2 : ℝ) ^ k) * (2 ^ k * 2 ^ k) = 3 * 2 ^ k := by
    rw [div_pow, one_pow]
    field_simp
  rw [key]
  exact hcoll

/-- **`hL2`, conditional on the one named Parseval hypothesis.**

`hParseval` is `∑_b ‖P_b c‖² ≤ ‖c‖² = coll(k)/4^k` -- Bessel for the level
decomposition (L2's territory, see §8). Everything to its right is proved here. -/
theorem hL2_of_parseval {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2) {k K : ℕ} (hk : 3 ≤ k)
    {v : ℕ → ℝ}
    (hParseval : ∑ b ∈ range K, (v b) ^ 2 ≤ (coll k : ℝ) / 4 ^ k) :
    ∑ b ∈ range K, (v b) ^ 2 ≤ 3 * s ^ (2 * k) :=
  le_trans hParseval (defect_norm_sq_le hs hsq hk)

/-- **The composed conclusion**: with the Parseval link, the defect row bound that
`GapCertificate.assembly_row_bound` consumes follows from the collision count. This
is the exact statement `defect_sum_bound` produces, now with `hL2` traced back to
`coll_le` rather than assumed. -/
theorem defect_sum_bound_of_collision {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2)
    {k K : ℕ} (hk : 3 ≤ k) {v : ℕ → ℝ} (hv : ∀ b, 0 ≤ v b)
    (hParseval : ∑ b ∈ range K, (v b) ^ 2 ≤ (coll k : ℝ) / 4 ^ k) :
    ∑ b ∈ range K, v b * ((1 : ℝ) / 2) ^ b ≤ 2 * s ^ k :=
  defect_sum_bound hs hv (hL2_of_parseval hs hsq hk hParseval)

/-!
--------------------------------------------------------------------------------
## §9. Calibration witness (GRADED: witness, NOT evidence)
--------------------------------------------------------------------------------

`coll` is computable, so these evaluate the very definition §7's theorem is about.
That makes them a **satisfiability witness** -- proof that the Lean `coll` is not
vacuous and produces the same integers as the Python enumeration and the document's
published closed form -- and NOT independent evidence. The independent evidence is
the externally written Python table in §0.2, which reproduces `1.6202`, the ten
closed-form values, and `31/12`, all published before this task.

Deliberately NOT stated as theorems: `coll 4 = 42` is closable by `decide`/`native_decide`
alone, which would read as a proved cross-check while proving nothing.

Expected output (matching §0.2 exactly):
```
#eval coll 3   -- 18     ≤  24
#eval coll 4   -- 42     ≤  48     ← the 1.6202 peak: 42/16 = 2.625 = 1.620185²
#eval coll 5   -- 80     ≤  96
#eval coll 6   -- 166    ≤ 192     ← (31·2^6 + 8)/12 = 166, LEMMA_B_PROOF.md line 177
#eval coll 7   -- 328    ≤ 384
#eval coll 8   -- 662    ≤ 768     ← (31·2^8 + 8)/12 = 662
```
-/

/-- The AP model side, for eval: the fibre value list. -/
def fibValList (k : ℕ) : List ℕ := (List.range (2 ^ k)).map (fibVal k)

/-- The shell index list, for eval: confirms the shell cardinalities `2^(k-1-j)`
and the single top atom at index `k`. -/
def shList (k : ℕ) : List ℕ := (List.range (2 ^ k)).map (sh k)

#eval coll 3   -- expected 18   (bound 24)
#eval coll 4   -- expected 42   (bound 48)   <- the 1.6202 peak: 42/16 = 2.625
#eval coll 5   -- expected 80   (bound 96)
#eval coll 6   -- expected 166  (bound 192)  <- (31*2^6 + 8)/12 = 166
#eval coll 7   -- expected 328  (bound 384)
#eval coll 8   -- expected 662  (bound 768)  <- (31*2^8 + 8)/12 = 662
#eval (shList 5).sum          -- expected 31 = 2^5 - 1, matching `sum_sh`
#eval (shList 6).sum          -- expected 63 = 2^6 - 1
#eval rstar 4                 -- expected 5,  3*5+1  = 16 = 2^4
#eval rstar 5                 -- expected 21, 3*21+1 = 64 = 2^6 = 2^(2*ceil(5/2))
#eval apA 4                   -- expected 1 (k even)
#eval apA 5                   -- expected 2 (k odd)
#eval (List.range 6).map (fun j => ((List.range (2^6)).filter (fun m => sh 6 m == j)).length)
                              -- expected [32, 16, 8, 4, 2, 1]  = 2^(6-1-j)
#eval ((List.range (2^6)).filter (fun m => sh 6 m == 6)).length
                              -- expected 1  = THE TOP ATOM
#eval ((Eset 3).card, (Lset 3).card, (Gset 3).card)   -- expected (8, 5, 5);  8+5+5 = 18 = coll 3
#eval ((Eset 4).card, (Lset 4).card, (Gset 4).card)   -- expected (16, 13, 13); = 42 = coll 4
-- Non-vacuity: `Lset` is NON-EMPTY at every k tested, so `card_Lset_le` and
-- `fibre_L_card_le` are real inequalities, not bounds on an empty set.

/-!
### Axiom audit

`#print axioms` on every exported declaration of this namespace. Expected, for all
of them: `[propext, Classical.choice, Quot.sound]` -- the three Lean/Mathlib standard
axioms and nothing else. No `sorryAx`, no project-specific axiom.
-/

#print axioms CollisionBound.ek
#print axioms CollisionBound.le_ek
#print axioms CollisionBound.ek_le
#print axioms CollisionBound.apA
#print axioms CollisionBound.apA_pos
#print axioms CollisionBound.apA_eq
#print axioms CollisionBound.apA_spec
#print axioms CollisionBound.rstar
#print axioms CollisionBound.two_pow_ek_mod_three
#print axioms CollisionBound.rstar_spec
#print axioms CollisionBound.rstar_odd
#print axioms CollisionBound.rstar_lt
#print axioms CollisionBound.rstar_defect
#print axioms CollisionBound.rstar_mem_defectSet
#print axioms CollisionBound.eq_rstar
#print axioms CollisionBound.apTerm
#print axioms CollisionBound.apTerm_pos
#print axioms CollisionBound.apTerm_ne_zero
#print axioms CollisionBound.oddPart
#print axioms CollisionBound.two_pow_mul_oddPart
#print axioms CollisionBound.v2_two_pow_mul
#print axioms CollisionBound.oddPart_two_pow_mul
#print axioms CollisionBound.fibVal
#print axioms CollisionBound.fibVal_lt
#print axioms CollisionBound.syracuse_defect_fibre
#print axioms CollisionBound.cf
#print axioms CollisionBound.coll
#print axioms CollisionBound.sh
#print axioms CollisionBound.sh_le
#print axioms CollisionBound.sh_eq_iff_lt
#print axioms CollisionBound.sh_eq_top_iff
#print axioms CollisionBound.shell_card_lt
#print axioms CollisionBound.shell_card_top
#print axioms CollisionBound.sh_mem_range
#print axioms CollisionBound.geom_weighted
#print axioms CollisionBound.sum_sh
#print axioms CollisionBound.fact1_shell
#print axioms CollisionBound.fact1_all
#print axioms CollisionBound.collPairs
#print axioms CollisionBound.mem_collPairs
#print axioms CollisionBound.coll_eq_card
#print axioms CollisionBound.Eset
#print axioms CollisionBound.Lset
#print axioms CollisionBound.Gset
#print axioms CollisionBound.mem_Lset
#print axioms CollisionBound.mem_Gset
#print axioms CollisionBound.mem_Eset
#print axioms CollisionBound.card_split
#print axioms CollisionBound.card_Eset
#print axioms CollisionBound.card_Gset_eq
#print axioms CollisionBound.fibre_L_card_le
#print axioms CollisionBound.card_Lset_le
#print axioms CollisionBound.coll_le_sharp
#print axioms CollisionBound.coll_le
#print axioms CollisionBound.defect_norm_sq_le
#print axioms CollisionBound.hL2_of_parseval
#print axioms CollisionBound.defect_sum_bound_of_collision
#print axioms CollisionBound.fibValList
#print axioms CollisionBound.shList


/-!
--------------------------------------------------------------------------------
## §10. SELF-ADVERSARIAL PASS (recorded findings)
--------------------------------------------------------------------------------

Run against this file and against `LEMMA_B_PROOF.md`, with the two failure modes
this project hit in the last day held explicitly in view.

### F1. REFEREE FINDING AGAINST `LEMMA_B_PROOF.md` lines 163-166 (minor, non-fatal)

The document displays

```
    cross <= sum_{j'=0}^{k-1} j' * 2^{k-1-j'}
          <= 2^{k-1} * sum_{j'>=0} j' 2^{-j'}  =  2^{k-1} * 2  =  2^k.
```

**The FIRST inequality is false at small `k`.** Enumeration: at `k = 3` the finite sum
is `4` while the true `cross` is `5`; at `k = 4` it is `11` against a true `13`. The
reason is exactly the top atom: `cross` counts pairs involving the atom, but the sum's
range `j' = 0..k-1` excludes it. The prose immediately after (lines 168-170, the
2026-07-05 Fable review Finding 3) repairs the *conclusion* by extending the series to
infinity, but the displayed intermediate line is left standing as written and is wrong
as a standalone statement. This is a presentation defect, not a mathematical one: the
final `cross ≤ 2^k` is true (verified `k = 3..14`).

The correct finite form, proved here as `card_Lset_le`, is

```
    cross ≤ (Σ_{j'<k} j'·2^(k-1-j'))  +  k  =  (2^k - k - 1) + k  =  2^k - 1,
```

which is exact accounting rather than series slack, and is one better than the
document's `2^k`. Consequently `coll_le_sharp` gives `coll ≤ 3·2^k - 2`, two better
than the document's `3·2^k`. Recommended doc edit: replace the first line of the
display with the `+ k` form and delete the infinite-series step.

### F2. Wrong-object check (the L2/L3 failure mode)

Asked: is `coll` here the collision count of the *Syracuse* fibre at the *defect*
residue, or of a convenient proxy?

* `rstar_mem_defectSet` + `eq_rstar` prove `rstar k` is THE element of
  `CountingLemmas.defectSet k` (odd, `< 2^k`, `2^k ∣ 3r+1`), which
  `CountingLemmas.defect_card` proves is a singleton. Not *a* residue with the
  property -- *the* one.
* `syracuse_defect_fibre` proves `syracuse (rstar k + m·2^k) % 2^k = fibVal k m` using
  `GapCertificate.syracuse` itself. The AP model `a + 3m` is therefore a THEOREM here,
  not a definitional shortcut. This is the specific trap L3 fell into (CU proved for
  the multiplication map rather than the Syracuse map) and it is closed.
* `cf` sums over `t ∈ range (2^k)` with `fibVal_lt` guaranteeing exhaustiveness, and
  `m` over a full residue system `range (2^k)`. No narrowing of the collision
  definition -- a narrower `coll` would make the theorem true but not the cited one.

### F3. Provable-by-`decide` check (the L3 self-catch)

No theorem in this file is closable by `decide`, `omega`, `simp` or `norm_num` alone.
The two candidates were considered and deliberately NOT stated:

* `coll 4 = 42` -- would be `decide`-closable and would masquerade as a cross-check.
  Left as `#eval` and graded in §9 as a satisfiability witness only.
* a `coll k ≤ 3·2^k` "consistency" restatement at fixed small `k` -- same problem.

The `#eval` outputs are labelled with their expected values so a drift is visible, and
the real corroboration is the externally written Python of §0.2.

### F4. Vacuity check on every inequality

* `card_Lset_le` and `fibre_L_card_le` bound a set that is non-empty at every tested
  `k` (`(Lset 3).card = 5`, `(Lset 4).card = 13`, evaluated in §9), so neither is a
  bound on an empty set.
* `card_Eset` is an EQUALITY (`= 2^k`), not a bound, so it cannot be vacuous.
* `card_split` is an identity.
* `hL2_of_parseval`'s hypothesis is satisfiable (trivially by `v ≡ 0`, and by Bessel
  for the true `v`), so the conditional corollary is not vacuously true.

### F5. Where the top atom could still have been dropped, and was not

Three places, all checked: `sh_le` (the atom is inside the codomain `{0..k}`),
`shell_card_top` (its cardinality is proved `= 1`, not assumed), `sum_sh` (its `k·1`
contribution is added explicitly, and `geom_weighted` supplies the exact `2^k - k - 1`
for the ordinary shells so the total is `2^k - 1` on the nose). `fact1_all` covers the
atom separately from `fact1_shell`, since `GapCertificate.fact1_injective` needs a
common finite `j` and the atom's members need not share one -- there is only one of
them, which is why the case closes.

### F6. What remains unclosed

`hParseval` (§8): `Σ_b ‖P_b c‖² ≤ ‖c‖² = coll(k)/4^k`. Bessel for the level
decomposition on a concrete vector. Not axiomatised, not `sorry`ed -- carried as a
named hypothesis on `hL2_of_parseval` and `defect_sum_bound_of_collision`. It needs
concrete `P_b` and `c`, which no file in this development has yet; `LevelMajorisation`
is abstract in the projections. That is an L2/L5 integration task, not a counting one.
-/

end CollisionBound
