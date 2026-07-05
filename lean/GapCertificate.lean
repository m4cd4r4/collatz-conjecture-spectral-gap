/-
# Uniform Spectral Gap Certificate - elementary core (Lean 4 formalisation)

Formalises the elementary 2-adic core of the uniform-spectral-gap certificate
(THEOREM.md in the public collatz-cycle-certificate repo, 2026-07-05):

* `eq_of_two_pow_dvd_three_mul_sub` - the shared engine: 2^N | 3(m-m') + small range => m = m'.
* `fact1_injective`   - Lemma B FACT 1: per-shell injectivity of the defect fiber.
* `sb_injective`      - the Shell-Bijection SB is injective on a shell.
* `cu_valuation_frozen`, `cu_syracuse_affine` - the Coset-Uniformity affine step:
  on the fiber x + m*2^K the 2-adic valuation of 3n+1 is frozen and Syr is affine in m.
* `envelope_max`, `envelope_lt_one` - the assembly envelope f(e) <= f(3) = 2^{-3/2}+2^{-1} < 1.

Everything here is sorry-free and elementary. NOT formalised here (paper proof in
THEOREM.md Part I, corrected 2026-07-05): the operator-norm chain (Perron split via
V = ker(1^T), level majorisation on the compression P_V U P_V, Gelfand, weighted row sum).

Honest scope: these lemmas support a spectral-gap theorem for the mod-2^k transfer
operator. They do NOT bear on Collatz cycles (see CYCLE_CLAIM_REFUTED.md: the 3x-1
operator passes the identical certificate yet 3x-1 has cycles).
-/

import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace GapCertificate

/-!
## Section 0: Standalone definitions

(In the development repo these live in `Basic.lean`; inlined here so this file
builds on bare Mathlib v4.27.0: `lake exe cache get && lake build`.)
-/

/-- The 2-adic valuation. -/
def v2 (n : ℕ) : ℕ := padicValNat 2 n

/-- `v2` of an odd number is 0. -/
theorem v2_odd_mod (n : ℕ) (h : n % 2 = 1) : v2 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (by omega)

/-- `2^(v2 n)` divides `n`. -/
theorem pow_v2_dvd (n : ℕ) (_ : n ≠ 0) : 2 ^ v2 n ∣ n :=
  pow_padicValNat_dvd

/-- The Syracuse map: `T(n) = (3n+1) / 2^{v2(3n+1)}` for odd `n`. -/
def syracuse (n : ℕ) : ℕ :=
  if n % 2 = 0 then n
  else
    let m := 3 * n + 1
    m / (2 ^ v2 m)

/-!
## Section 1: The shared divisibility engine

Both FACT 1 and SB injectivity reduce to: if `2^N` divides `3*(m - m')` and
`|m - m'| < 2^N`, then `m = m'` (using only that 3 is odd).
-/

/-- If `2^N ∣ 3*(m - m')` and `m, m'` lie in a window of width `2^N`, then `m = m'`. -/
theorem eq_of_two_pow_dvd_three_mul_sub {N : ℕ} {m m' : ℤ}
    (hdvd : (2 : ℤ) ^ N ∣ 3 * (m - m'))
    (hlt : |m - m'| < 2 ^ N) : m = m' := by
  have hcop : IsCoprime ((2 : ℤ) ^ N) 3 := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]
    norm_num
  have hdvd' : (2 : ℤ) ^ N ∣ (m - m') := by
    have h := hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
    exact h
  have := Int.eq_zero_of_abs_lt_dvd hdvd' hlt
  linarith

/-!
## Section 2: Lemma B, FACT 1 (per-shell injectivity)

The defect fiber at `r*` is the arithmetic progression `x = a + 3m`, `m ∈ [0, 2^k)`.
Within the shell `v2(x) = j`, write `x = 2^j * u`. If two odd parts agree mod `2^k`,
the AP terms coincide. (In the write-up this used a mod-3 argument; parametrised by
`m` it reduces to the shared engine, with no mod-3 step at all.)
-/

/-- **FACT 1.** On the AP `a + 3m`, `m ∈ [0, 2^k)`, if `a + 3m = 2^j u` and
`a + 3m' = 2^j u'` with `u ≡ u' (mod 2^k)`, then `m = m'`. Hence
`x ↦ (x / 2^j) mod 2^k` is injective on each shell, and the fiber counts are 0/1
per shell. -/
theorem fact1_injective {k j : ℕ} {a m m' u u' : ℤ}
    (hm0 : 0 ≤ m) (hmk : m < 2 ^ k) (hm'0 : 0 ≤ m') (hm'k : m' < 2 ^ k)
    (hx : a + 3 * m = 2 ^ j * u) (hx' : a + 3 * m' = 2 ^ j * u')
    (hu : (2 : ℤ) ^ k ∣ u - u') : m = m' := by
  obtain ⟨s, hs⟩ := hu
  have key : 3 * (m - m') = 2 ^ (j + k) * s := by
    have h1 : 3 * (m - m') = 2 ^ j * (u - u') := by linear_combination hx - hx'
    rw [h1, hs, pow_add]
    ring
  apply eq_of_two_pow_dvd_three_mul_sub (N := j + k)
  · exact ⟨s, key⟩
  · have h2 : (2 : ℤ) ^ k ≤ 2 ^ (j + k) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    rw [abs_lt]
    constructor <;> linarith

/-!
## Section 3: The Shell-Bijection SB (injectivity)

`ψ(r) = (3r+1)/2^j mod 2^{k-j}` is injective on the shell
`S_j = { r odd, 0 < r < 2^k, v2(3r+1) = j }`. Same engine.
-/

/-- **SB, injectivity.** If `3r+1 = 2^j q`, `3r'+1 = 2^j q'` with
`q ≡ q' (mod 2^{k-j})`, `j ≤ k`, and `r, r' ∈ [0, 2^k)`, then `r = r'`. -/
theorem sb_injective {k j : ℕ} (hjk : j ≤ k) {r r' q q' : ℤ}
    (hr0 : 0 ≤ r) (hrk : r < 2 ^ k) (hr'0 : 0 ≤ r') (hr'k : r' < 2 ^ k)
    (hq : 3 * r + 1 = 2 ^ j * q) (hq' : 3 * r' + 1 = 2 ^ j * q')
    (hcong : (2 : ℤ) ^ (k - j) ∣ q - q') : r = r' := by
  obtain ⟨s, hs⟩ := hcong
  have key : 3 * (r - r') = 2 ^ k * s := by
    have h1 : 3 * (r - r') = 2 ^ j * (q - q') := by linear_combination hq - hq'
    have h2 : (2 : ℤ) ^ j * 2 ^ (k - j) = 2 ^ k := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1, hs, ← mul_assoc, h2]
  apply eq_of_two_pow_dvd_three_mul_sub (N := k)
  · exact ⟨s, key⟩
  · rw [abs_lt]
    constructor <;> linarith

/-!
## Section 4: Coset-Uniformity, the affine step

For odd `x` with `v := v2(3x+1) < K`, every lift `n = x + m*2^K` has the SAME
valuation `v2(3n+1) = v`, and `Syr(n) = q0 + 3m*2^{K-v}` where `q0 = (3x+1)/2^v`.
This is CU's step (a): the valuation is frozen and the Syracuse image is affine
in the lift index. (The uniform-fiber count, CU step (b), is the image/kernel
count of multiplication by `3*2^{K-v}` on `Z/2^K`.)
-/

/-- Auxiliary: `v2 (2^v * o) = v` for odd `o`. -/
theorem v2_two_pow_mul_odd (v o : ℕ) (ho : o % 2 = 1) : v2 (2 ^ v * o) = v := by
  have ho0 : o ≠ 0 := by
    rintro rfl
    simp at ho
  unfold v2
  rw [padicValNat.mul (by positivity) ho0]
  have h1 : padicValNat 2 (2 ^ v) = v := by
    rw [padicValNat.prime_pow]
  have h2 : padicValNat 2 o = 0 := v2_odd_mod o ho
  omega

/-- The odd part `q0 = (3x+1)/2^v` is odd. -/
theorem odd_part_odd (x : ℕ) (hx : x % 2 = 1) :
    ((3 * x + 1) / 2 ^ v2 (3 * x + 1)) % 2 = 1 := by
  set n := 3 * x + 1 with hn
  have hn0 : n ≠ 0 := by omega
  have hdvd : 2 ^ v2 n ∣ n := pow_v2_dvd n hn0
  have hfac : n = 2 ^ v2 n * (n / 2 ^ v2 n) := (Nat.mul_div_cancel' hdvd).symm
  by_contra hodd
  have heven : 2 ∣ n / 2 ^ v2 n := by omega
  obtain ⟨c, hc⟩ := heven
  have hstep : 2 ^ (v2 n + 1) ∣ n := by
    refine ⟨c, ?_⟩
    calc n = 2 ^ v2 n * (n / 2 ^ v2 n) := hfac
      _ = 2 ^ v2 n * (2 * c) := by rw [hc]
      _ = 2 ^ (v2 n + 1) * c := by rw [pow_succ]; ring
  exact pow_succ_padicValNat_not_dvd hn0 hstep

/-- The decomposition `3(x + m*2^K) + 1 = 2^v * (q0 + 3m*2^{K-v})` with the
bracket odd, for odd `x`, `v = v2(3x+1) < K`. -/
theorem cu_decomposition (x m K : ℕ) (hx : x % 2 = 1) (hK : v2 (3 * x + 1) < K) :
    3 * (x + m * 2 ^ K) + 1 =
      2 ^ v2 (3 * x + 1) *
        ((3 * x + 1) / 2 ^ v2 (3 * x + 1) + 3 * m * 2 ^ (K - v2 (3 * x + 1))) ∧
    ((3 * x + 1) / 2 ^ v2 (3 * x + 1) + 3 * m * 2 ^ (K - v2 (3 * x + 1))) % 2 = 1 := by
  set v := v2 (3 * x + 1) with hv
  set q0 := (3 * x + 1) / 2 ^ v with hq0
  have hn0 : 3 * x + 1 ≠ 0 := by omega
  have hdvd : 2 ^ v ∣ 3 * x + 1 := pow_v2_dvd _ hn0
  have hfac : 3 * x + 1 = 2 ^ v * q0 := (Nat.mul_div_cancel' hdvd).symm
  have hKv : v ≤ K := le_of_lt hK
  have hpow : 2 ^ K = 2 ^ v * 2 ^ (K - v) := by
    rw [← pow_add]
    congr 1
    omega
  have hsplit : 3 * (x + m * 2 ^ K) + 1 = 2 ^ v * (q0 + 3 * m * 2 ^ (K - v)) := by
    calc 3 * (x + m * 2 ^ K) + 1
        = (3 * x + 1) + 3 * m * 2 ^ K := by ring
      _ = 2 ^ v * q0 + 3 * m * (2 ^ v * 2 ^ (K - v)) := by rw [hfac, hpow]
      _ = 2 ^ v * (q0 + 3 * m * 2 ^ (K - v)) := by ring
  refine ⟨hsplit, ?_⟩
  have hq0odd : q0 % 2 = 1 := odd_part_odd x hx
  have heven : (2 : ℕ) ∣ 3 * m * 2 ^ (K - v) :=
    (dvd_pow_self 2 (by omega : K - v ≠ 0)).mul_left (3 * m)
  omega

/-- **CU, valuation frozen.** `v2(3(x + m*2^K) + 1) = v2(3x+1)` whenever `x` is odd
and `v2(3x+1) < K`. -/
theorem cu_valuation_frozen (x m K : ℕ) (hx : x % 2 = 1) (hK : v2 (3 * x + 1) < K) :
    v2 (3 * (x + m * 2 ^ K) + 1) = v2 (3 * x + 1) := by
  obtain ⟨hsplit, hodd⟩ := cu_decomposition x m K hx hK
  rw [hsplit]
  exact v2_two_pow_mul_odd _ _ hodd

/-- **CU, Syracuse affine in the lift.** For odd `x` with `v2(3x+1) < K`,
`Syr(x + m*2^K) = (3x+1)/2^v + 3m*2^{K-v}`. -/
theorem cu_syracuse_affine (x m K : ℕ) (hx : x % 2 = 1) (hK : v2 (3 * x + 1) < K) :
    syracuse (x + m * 2 ^ K) =
      (3 * x + 1) / 2 ^ v2 (3 * x + 1) + 3 * m * 2 ^ (K - v2 (3 * x + 1)) := by
  obtain ⟨hsplit, hodd⟩ := cu_decomposition x m K hx hK
  have hK1 : 1 ≤ K := by omega
  have hlift_odd : (x + m * 2 ^ K) % 2 = 1 := by
    have h2 : (2 : ℕ) ∣ m * 2 ^ K := (dvd_pow_self 2 (by omega : K ≠ 0)).mul_left m
    omega
  unfold syracuse
  rw [if_neg (by omega)]
  show (3 * (x + m * 2 ^ K) + 1) / 2 ^ v2 (3 * (x + m * 2 ^ K) + 1) = _
  rw [cu_valuation_frozen x m K hx hK, hsplit,
    Nat.mul_div_cancel_left _ (by positivity : (0:ℕ) < 2 ^ v2 (3 * x + 1))]

/-!
## Section 5: The assembly envelope

`f(e) = Σ_{d=1}^{e-2} s^{3d} + s^{e-1}` with `s = 2^{-1/2}` is the per-row bound of
the certificate (upper cascade truncated at the top + Cauchy-Schwarz defect term).
Its maximum over `e ≥ 2` is `f(3) = s^3 + s^2 = 2^{-3/2} + 1/2 = 0.8536 < 1`.

We prove it for any `s` with `0 < s` and `s^2 = 1/2` (i.e. `s = 1/√2`), then
instantiate. Key facts: `s < 3/4` (so the difference `f(e+1) - f(e) =
s^{e-1}(s^{2(e-1)} + s - 1)` is `≤ 0` for `e ≥ 3`) and `s < 1` (so `f(3) < 1`).
-/

/-- The envelope: `f e = Σ_{d ∈ [1, e-2]} s^(3d) + s^(e-1)` (natural-number `e ≥ 2`). -/
noncomputable def envelope (s : ℝ) (e : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 (e - 2), s ^ (3 * d)) + s ^ (e - 1)

/-- `s = 1/√2` satisfies the two numeric facts we need. -/
theorem sqrt_half_facts :
    (0 < (Real.sqrt 2)⁻¹) ∧ ((Real.sqrt 2)⁻¹ ^ 2 = 1 / 2) := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · positivity
  · rw [inv_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
    norm_num

/-- With `0 < s`, `s^2 = 1/2`: `s < 3/4`. -/
theorem s_lt_three_quarters {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2) :
    s < 3 / 4 := by
  nlinarith [sq_nonneg (s - 3/4), sq_nonneg s]

/-- With `0 < s`, `s^2 = 1/2`: `s < 1`. -/
theorem s_lt_one {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2) : s < 1 := by
  nlinarith [sq_nonneg (s - 1)]

/-- One-step decrease: for `e ≥ 3`, `f(e+1) ≤ f(e)`. -/
theorem envelope_step {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2)
    {e : ℕ} (he : 3 ≤ e) : envelope s (e + 1) ≤ envelope s e := by
  have hs1 : s < 1 := s_lt_one hs hsq
  have hs34 : s < 3 / 4 := s_lt_three_quarters hs hsq
  unfold envelope
  have hsum : ∑ d ∈ Finset.Icc 1 (e + 1 - 2), s ^ (3 * d)
      = (∑ d ∈ Finset.Icc 1 (e - 2), s ^ (3 * d)) + s ^ (3 * (e - 1)) := by
    have h1 : e + 1 - 2 = (e - 2) + 1 := by omega
    have h2 : (e - 2) + 1 = e - 1 := by omega
    rw [h1, Finset.sum_Icc_succ_top (by omega : 1 ≤ (e - 2) + 1), h2]
  rw [hsum]
  -- goal: sum + s^(3(e-1)) + s^e ≤ sum + s^(e-1)
  have hkey : s ^ (3 * (e - 1)) + s ^ (e + 1 - 1) ≤ s ^ (e - 1) := by
    have he1 : e + 1 - 1 = (e - 1) + 1 := by omega
    have h3e : 3 * (e - 1) = (e - 1) + 2 * (e - 1) := by ring
    rw [he1, h3e, pow_add, pow_succ]
    have hfactor : s ^ (e - 1) * s ^ (2 * (e - 1)) + s ^ (e - 1) * s
        = s ^ (e - 1) * (s ^ (2 * (e - 1)) + s) := by ring
    rw [hfactor]
    have hpe : (0:ℝ) < s ^ (e - 1) := pow_pos hs _
    have hbound : s ^ (2 * (e - 1)) + s ≤ 1 := by
      have h2e : s ^ (2 * (e - 1)) ≤ s ^ 4 := by
        apply pow_le_pow_of_le_one (le_of_lt hs) (le_of_lt hs1)
        omega
      have hs4 : s ^ 4 = 1 / 4 := by
        have : s ^ 4 = (s ^ 2) ^ 2 := by ring
        rw [this, hsq]
        norm_num
      nlinarith
    calc s ^ (e - 1) * (s ^ (2 * (e - 1)) + s) ≤ s ^ (e - 1) * 1 :=
          mul_le_mul_of_nonneg_left hbound (le_of_lt hpe)
      _ = s ^ (e - 1) := mul_one _
  linarith

/-- The two endpoint values: `f(2) = s` and `f(3) = s^3 + s^2`. -/
theorem envelope_two (s : ℝ) : envelope s 2 = s := by
  unfold envelope
  have h : Finset.Icc 1 (2 - 2) = (∅ : Finset ℕ) := by
    apply Finset.Icc_eq_empty
    omega
  rw [h]
  simp

theorem envelope_three (s : ℝ) : envelope s 3 = s ^ 3 + s ^ 2 := by
  unfold envelope
  have h : Finset.Icc 1 (3 - 2) = ({1} : Finset ℕ) := rfl
  rw [h]
  simp

/-- `f(2) ≤ f(3)`: since `s^3 + s^2 = s/2 + 1/2` and `s ≤ 1`. -/
theorem envelope_two_le_three {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2) :
    envelope s 2 ≤ envelope s 3 := by
  rw [envelope_two, envelope_three]
  have h3 : s ^ 3 = s * (1 / 2) := by
    have h : s ^ 3 = s * s ^ 2 := by ring
    rw [h, hsq]
  have h1 : s < 1 := s_lt_one hs hsq
  rw [h3, hsq]
  linarith

/-- For all `e ≥ 3`, `f(e) ≤ f(3)` (downward monotone past the peak). -/
theorem envelope_ge_three_le {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2) :
    ∀ e, 3 ≤ e → envelope s e ≤ envelope s 3 := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (envelope_step hs hsq hn) ih

/-- **Envelope maximum.** For all `e ≥ 2`, `f(e) ≤ f(3)`. -/
theorem envelope_max {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2)
    {e : ℕ} (he : 2 ≤ e) : envelope s e ≤ envelope s 3 := by
  rcases Nat.lt_or_ge e 3 with h | h
  · have he2 : e = 2 := by omega
    rw [he2]
    exact envelope_two_le_three hs hsq
  · exact envelope_ge_three_le hs hsq e h

/-- **The certificate constant.** `f(3) = s^3 + s^2 = 2^{-3/2} + 1/2 < 1`. -/
theorem envelope_lt_one {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2) :
    envelope s 3 < 1 := by
  have hs1 : s < 1 := s_lt_one hs hsq
  rw [envelope_three]
  have h3 : s ^ 3 = s * (1 / 2) := by
    have h : s ^ 3 = s * s ^ 2 := by ring
    rw [h, hsq]
  rw [h3, hsq]
  linarith

/-- **The theorem's constant, concretely:** with `s = 1/√2`, every row bound
`f(e)`, `e ≥ 2`, is at most `f(3) = 2^{-3/2} + 1/2 < 1`. -/
theorem certificate_envelope_bound {e : ℕ} (he : 2 ≤ e) :
    envelope (Real.sqrt 2)⁻¹ e ≤ envelope (Real.sqrt 2)⁻¹ 3 ∧
    envelope (Real.sqrt 2)⁻¹ 3 < 1 := by
  obtain ⟨hs, hsq⟩ := sqrt_half_facts
  exact ⟨envelope_max hs hsq he, envelope_lt_one hs hsq⟩

/-!
## Section 6: The Cauchy-Schwarz defect bound

Lemma B delivers `Σ_b v_b² ≤ 3·2^{-k}`. The assembly needs
`Σ_b v_b·2^{-b} ≤ 2·2^{-k/2}` - one Cauchy-Schwarz against the geometric
weight, with `Σ_b 4^{-b} < 4/3`. No information about the `v_b` profile is used.
-/

/-- Geometric tail: `Σ_{b<K} (1/4)^b ≤ 4/3`. -/
theorem quarter_geom_sum_le (K : ℕ) :
    ∑ b ∈ Finset.range K, ((1 : ℝ) / 4) ^ b ≤ 4 / 3 := by
  have h := geom_sum_eq (by norm_num : ((1 : ℝ) / 4) ≠ 1) K
  rw [h]
  have hpow : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ K := by positivity
  have hne : ((1 : ℝ) / 4 - 1) ≠ 0 := by norm_num
  rw [div_le_iff_of_neg (by norm_num : ((1 : ℝ) / 4 - 1) < 0)]
  linarith

/-- **The defect bound.** If `Σ_{b<K} v_b² ≤ 3·s^{2k}` (Lemma B, with
`s^{2k} = 2^{-k}`), then `Σ_{b<K} v_b·(1/2)^b ≤ 2·s^k`. -/
theorem defect_sum_bound {s : ℝ} (hs : 0 < s) {k K : ℕ}
    {v : ℕ → ℝ} (hv : ∀ b, 0 ≤ v b)
    (hL2 : ∑ b ∈ Finset.range K, (v b) ^ 2 ≤ 3 * s ^ (2 * k)) :
    ∑ b ∈ Finset.range K, v b * ((1 : ℝ) / 2) ^ b ≤ 2 * s ^ k := by
  set L := ∑ b ∈ Finset.range K, v b * ((1 : ℝ) / 2) ^ b with hL
  have hL0 : 0 ≤ L := by
    apply Finset.sum_nonneg
    intro b _
    have : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ b := by positivity
    exact mul_nonneg (hv b) this
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range K) v
    (fun b => ((1 : ℝ) / 2) ^ b)
  have hgeom : ∑ b ∈ Finset.range K, (((1 : ℝ) / 2) ^ b) ^ 2 ≤ 4 / 3 := by
    have hb : ∀ b : ℕ, (((1 : ℝ) / 2) ^ b) ^ 2 = ((1 : ℝ) / 4) ^ b := by
      intro b
      rw [← pow_mul, mul_comm b 2, pow_mul]
      norm_num
    calc ∑ b ∈ Finset.range K, (((1 : ℝ) / 2) ^ b) ^ 2
        = ∑ b ∈ Finset.range K, ((1 : ℝ) / 4) ^ b := by
          apply Finset.sum_congr rfl
          intro b _
          exact hb b
      _ ≤ 4 / 3 := quarter_geom_sum_le K
  have hs2k : (0 : ℝ) ≤ s ^ (2 * k) := by positivity
  have hLsq : L ^ 2 ≤ (2 * s ^ k) ^ 2 := by
    have h1 : L ^ 2 ≤ (∑ b ∈ Finset.range K, (v b) ^ 2) *
        (∑ b ∈ Finset.range K, (((1 : ℝ) / 2) ^ b) ^ 2) := hCS
    have hsum2_nonneg : (0 : ℝ) ≤ ∑ b ∈ Finset.range K, (v b) ^ 2 := by
      apply Finset.sum_nonneg
      intro b _
      positivity
    have h2 : (∑ b ∈ Finset.range K, (v b) ^ 2) *
        (∑ b ∈ Finset.range K, (((1 : ℝ) / 2) ^ b) ^ 2)
        ≤ (3 * s ^ (2 * k)) * (4 / 3) := by
      apply mul_le_mul hL2 hgeom
      · apply Finset.sum_nonneg
        intro b _
        positivity
      · positivity
    have h3 : (3 * s ^ (2 * k)) * (4 / 3) = (2 * s ^ k) ^ 2 := by
      have : s ^ (2 * k) = (s ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [this]
      ring
    calc L ^ 2 ≤ _ := h1
      _ ≤ (3 * s ^ (2 * k)) * (4 / 3) := h2
      _ = (2 * s ^ k) ^ 2 := h3
  have hR0 : (0 : ℝ) ≤ 2 * s ^ k := by positivity
  nlinarith [hLsq, hL0, hR0]

/-!
## Section 7: The assembly row bound

The abstract form of THEOREM.md Part III. Row `a` of the certificate, with
`e := k - a ≥ 2` and weights `w b = 2^a · (1/2)^b = 2^{a-b}`:

* upper entries (`a < b ≤ k-2`) are bounded by the clean cascade plus defect:
  `Q b ≤ s^{b-a} + s^{a+1}·v b`  (Lemma A + triangle inequality, `u_a = s^{a+1}`);
* lower+diagonal entries (`b ≤ a`) are pure defect: `Q b ≤ s^{a+1}·v b`  (R1);
* the defect covector satisfies `Σ v_b² ≤ 3·s^{2k}`  (Lemma B).

Conclusion: the weighted row sum is at most the envelope `f(k-a)`, hence at most
`f(3) = 0.8536 < 1` by `envelope_max`. Key identity (no real exponents needed):
`s^{a+1}·2^{a+1}·s^k = (2s²)^{a+1}·s^{e-1} = s^{e-1}`.
-/

/-- **The assembly (abstract row bound).** -/
theorem assembly_row_bound {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2)
    {k a : ℕ} (ha : a + 2 ≤ k) {Q v : ℕ → ℝ} (hv : ∀ b, 0 ≤ v b)
    (hQupper : ∀ b, a < b → Q b ≤ s ^ (b - a) + s ^ (a + 1) * v b)
    (hQlower : ∀ b, b ≤ a → Q b ≤ s ^ (a + 1) * v b)
    (hL2 : ∑ b ∈ Finset.range (k - 1), (v b) ^ 2 ≤ 3 * s ^ (2 * k)) :
    ∑ b ∈ Finset.range (k - 1), Q b * ((2 : ℝ) ^ a * ((1 : ℝ) / 2) ^ b)
      ≤ envelope s (k - a) := by
  set w : ℕ → ℝ := fun b => (2 : ℝ) ^ a * ((1 : ℝ) / 2) ^ b with hw
  have hw0 : ∀ b, 0 ≤ w b := fun b => by positivity
  -- Per-term bound: Q b · w b ≤ clean b + defect b, where clean is 0 for b ≤ a.
  set clean : ℕ → ℝ := fun b => if a < b then s ^ (b - a) * w b else 0 with hclean
  set defect : ℕ → ℝ := fun b => s ^ (a + 1) * v b * w b with hdefect
  have hterm : ∀ b, Q b * w b ≤ clean b + defect b := by
    intro b
    by_cases hab : a < b
    · have h1 := hQupper b hab
      have h2 : Q b * w b ≤ (s ^ (b - a) + s ^ (a + 1) * v b) * w b :=
        mul_le_mul_of_nonneg_right h1 (hw0 b)
      simp only [hclean, hdefect, if_pos hab]
      calc Q b * w b ≤ (s ^ (b - a) + s ^ (a + 1) * v b) * w b := h2
        _ = s ^ (b - a) * w b + s ^ (a + 1) * v b * w b := by ring
    · have h1 := hQlower b (by omega)
      have h2 : Q b * w b ≤ (s ^ (a + 1) * v b) * w b :=
        mul_le_mul_of_nonneg_right h1 (hw0 b)
      simp only [hclean, hdefect, if_neg hab]
      calc Q b * w b ≤ s ^ (a + 1) * v b * w b := h2
        _ = 0 + s ^ (a + 1) * v b * w b := by ring
  have hsum1 : ∑ b ∈ Finset.range (k - 1), Q b * w b
      ≤ (∑ b ∈ Finset.range (k - 1), clean b) +
        (∑ b ∈ Finset.range (k - 1), defect b) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun b _ => hterm b
  -- (1) The clean part equals the truncated cascade Σ_{d ∈ [1, e-2]} s^{3d}.
  have hclean_eval : ∑ b ∈ Finset.range (k - 1), clean b
      = ∑ d ∈ Finset.Icc 1 (k - a - 2), s ^ (3 * d) := by
    have hsplit : (∑ b ∈ Finset.Ico 0 (a + 1), clean b) +
        (∑ b ∈ Finset.Ico (a + 1) (k - 1), clean b)
        = ∑ b ∈ Finset.Ico 0 (k - 1), clean b :=
      Finset.sum_Ico_consecutive _ (by omega) (by omega)
    rw [Finset.range_eq_Ico, ← hsplit]
    have hzero : ∑ b ∈ Finset.Ico 0 (a + 1), clean b = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      simp only [Finset.mem_Ico] at hb
      simp only [hclean, if_neg (by omega : ¬ a < b)]
    rw [hzero, zero_add]
    have hIco : ∑ b ∈ Finset.Ico (a + 1) (k - 1), clean b
        = ∑ i ∈ Finset.range (k - 1 - (a + 1)), clean (a + 1 + i) := by
      rw [Finset.sum_Ico_eq_sum_range]
    rw [hIco]
    have hterm2 : ∀ i, clean (a + 1 + i) = s ^ (3 * (i + 1)) := by
      intro i
      simp only [hclean, if_pos (by omega : a < a + 1 + i), hw]
      have h1 : a + 1 + i - a = i + 1 := by omega
      have h2 : (2 : ℝ) ^ a * ((1 : ℝ) / 2) ^ (a + 1 + i) = ((1 : ℝ) / 2) ^ (i + 1) := by
        have hsplit2 : a + 1 + i = a + (i + 1) := by omega
        rw [hsplit2, pow_add]
        have hcancel : (2 : ℝ) ^ a * ((1 : ℝ) / 2) ^ a = 1 := by
          rw [← mul_pow]
          norm_num
        calc (2 : ℝ) ^ a * (((1 : ℝ) / 2) ^ a * ((1 : ℝ) / 2) ^ (i + 1))
            = ((2 : ℝ) ^ a * ((1 : ℝ) / 2) ^ a) * ((1 : ℝ) / 2) ^ (i + 1) := by ring
          _ = ((1 : ℝ) / 2) ^ (i + 1) := by rw [hcancel, one_mul]
      rw [h1, h2, ← hsq]
      calc s ^ (i + 1) * (s ^ 2) ^ (i + 1) = (s * s ^ 2) ^ (i + 1) := by
            rw [mul_pow]
        _ = (s ^ 3) ^ (i + 1) := by ring_nf
        _ = s ^ (3 * (i + 1)) := by rw [← pow_mul]
    have hcount : k - 1 - (a + 1) = k - a - 2 := by omega
    rw [hcount]
    have hicc : ∑ d ∈ Finset.Icc 1 (k - a - 2), s ^ (3 * d)
        = ∑ i ∈ Finset.range (k - a - 2), s ^ (3 * (1 + i)) := by
      have hset : Finset.Icc 1 (k - a - 2) = Finset.Ico 1 (k - a - 2 + 1) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hset, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
    rw [hicc]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm2 i]
    congr 1
    omega
  -- (2) The defect part is ≤ s^{e-1} via Cauchy-Schwarz and (2s²)^{a+1} = 1.
  have hdefect_eval : ∑ b ∈ Finset.range (k - 1), defect b ≤ s ^ (k - a - 1) := by
    have hpull : ∑ b ∈ Finset.range (k - 1), defect b
        = (s ^ (a + 1) * (2 : ℝ) ^ a) *
          ∑ b ∈ Finset.range (k - 1), v b * ((1 : ℝ) / 2) ^ b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [hdefect, hw]
      ring
    rw [hpull]
    have hCS := defect_sum_bound hs hv hL2
    have hconst : (0 : ℝ) ≤ s ^ (a + 1) * (2 : ℝ) ^ a := by positivity
    calc (s ^ (a + 1) * (2 : ℝ) ^ a) *
          ∑ b ∈ Finset.range (k - 1), v b * ((1 : ℝ) / 2) ^ b
        ≤ (s ^ (a + 1) * (2 : ℝ) ^ a) * (2 * s ^ k) :=
          mul_le_mul_of_nonneg_left hCS hconst
      _ = ((2 : ℝ) * s ^ 2) ^ (a + 1) * s ^ (k - a - 1) := by
          have hk : k = (a + 1) + (k - a - 1) := by omega
          have hsk : s ^ k = s ^ (a + 1) * s ^ (k - a - 1) := by
            rw [← pow_add, ← hk]
          rw [hsk, mul_pow]
          have h2a : (2 : ℝ) ^ (a + 1) = 2 * (2 : ℝ) ^ a := by
            rw [pow_succ]
            ring
          rw [h2a]
          have hs2 : (s ^ 2) ^ (a + 1) = s ^ (a + 1) * s ^ (a + 1) := by
            rw [← pow_mul]
            rw [show 2 * (a + 1) = (a + 1) + (a + 1) by ring, pow_add]
          rw [hs2]
          ring
      _ = s ^ (k - a - 1) := by
          have h1 : (2 : ℝ) * s ^ 2 = 1 := by rw [hsq]; norm_num
          rw [h1, one_pow, one_mul]
  -- Combine.
  have hfinal : ∑ b ∈ Finset.range (k - 1), Q b * w b
      ≤ (∑ d ∈ Finset.Icc 1 (k - a - 2), s ^ (3 * d)) + s ^ (k - a - 1) := by
    calc ∑ b ∈ Finset.range (k - 1), Q b * w b
        ≤ _ + _ := hsum1
      _ ≤ (∑ d ∈ Finset.Icc 1 (k - a - 2), s ^ (3 * d)) + s ^ (k - a - 1) := by
          rw [hclean_eval]
          exact add_le_add le_rfl hdefect_eval
  have henv : envelope s (k - a)
      = (∑ d ∈ Finset.Icc 1 (k - a - 2), s ^ (3 * d)) + s ^ (k - a - 1) := by
    unfold envelope
    congr 1
  exact henv ▸ hfinal

/-- **The certificate, assembled.** Under the three lemma inputs, every weighted
row sum is `< 1`: `Σ_b Q b · 2^{a-b} ≤ f(k-a) ≤ f(3) = 2^{-3/2} + 1/2 < 1`. -/
theorem certificate_lt_one {s : ℝ} (hs : 0 < s) (hsq : s ^ 2 = 1 / 2)
    {k a : ℕ} (ha : a + 2 ≤ k) {Q v : ℕ → ℝ} (hv : ∀ b, 0 ≤ v b)
    (hQupper : ∀ b, a < b → Q b ≤ s ^ (b - a) + s ^ (a + 1) * v b)
    (hQlower : ∀ b, b ≤ a → Q b ≤ s ^ (a + 1) * v b)
    (hL2 : ∑ b ∈ Finset.range (k - 1), (v b) ^ 2 ≤ 3 * s ^ (2 * k)) :
    ∑ b ∈ Finset.range (k - 1), Q b * ((2 : ℝ) ^ a * ((1 : ℝ) / 2) ^ b) < 1 := by
  have h1 := assembly_row_bound hs hsq ha hv hQupper hQlower hL2
  have h2 : envelope s (k - a) ≤ envelope s 3 :=
    envelope_max hs hsq (by omega : 2 ≤ k - a)
  have h3 : envelope s 3 < 1 := envelope_lt_one hs hsq
  linarith

end GapCertificate
