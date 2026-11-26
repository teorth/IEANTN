/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Vecchi
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import IEANTN.Nodes.FKS2NuAsymp.v1.Conclusions

/-!
# Solution: `FKS2NuAsymp.v1`

Proves both conclusions of `FKS2NuAsymp.v1`:
1. `nu_asymp_e30_le`: `FKS2Numerics.v1.nuAsympE30 ≤ IEANTN.margin 0 * 6.3381e-7`.
2. `nu_asymp_e30_gt`: `¬ FKS2Numerics.v1.nu_asymp_e30_le` (i.e. `nuAsympE30 > 6.3376e-7`).

All bounds use pure Mathlib (`Real.exp_bound`, `Real.sum_le_exp_of_nonneg`,
`Real.log_two_gt_d9`, `Real.log_two_lt_d9`) with explicit short-rational repeated squaring.
-/

open Real Finset

namespace FKS2NuAsymp.v1.Dev

/-! ### Elementary Taylor bounds for `Real.exp` on `[0, 1]` -/

private lemma exp_le_poly5 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 100 := by
  have hb := Real.exp_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1) (n := 5) (by norm_num)
  rw [abs_of_nonneg h0] at hb
  have hle := (abs_le.mp hb).2
  simp [Finset.sum_range_succ, Nat.factorial] at hle
  linarith

private lemma exp_le_poly7 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 +
      x ^ 6 / 720 + x ^ 7 / 4410 := by
  have hb := Real.exp_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1) (n := 7) (by norm_num)
  rw [abs_of_nonneg h0] at hb
  have hle := (abs_le.mp hb).2
  simp [Finset.sum_range_succ, Nat.factorial] at hle
  linarith

private lemma exp_le_poly9 {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 +
      x ^ 6 / 720 + x ^ 7 / 5040 + x ^ 8 / 40320 + x ^ 9 / 326592 := by
  have hb := Real.exp_bound (x := x) (by rw [abs_of_nonneg h0]; exact h1) (n := 9) (by norm_num)
  rw [abs_of_nonneg h0] at hb
  have hle := (abs_le.mp hb).2
  simp [Finset.sum_range_succ, Nat.factorial] at hle
  linarith

private lemma poly9_le_exp {x : ℝ} (h0 : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 +
      x ^ 6 / 720 + x ^ 7 / 5040 + x ^ 8 / 40320 ≤ exp x := by
  have h := Real.sum_le_exp_of_nonneg h0 9
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-! ### Repeated-squaring helpers -/

private lemma pow_two_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  pow_le_pow_left₀ ha hab 2

private lemma exp_pow_8_le {x b0 b1 b2 b3 : ℝ}
    (h0 : exp x ≤ b0) (h1 : b0 ^ 2 ≤ b1) (h2 : b1 ^ 2 ≤ b2) (h3 : b2 ^ 2 ≤ b3) :
    exp (8 * x) ≤ b3 := by
  have hp : exp (8 * x) = (((exp x) ^ 2) ^ 2) ^ 2 := by
    rw [show (8 : ℝ) * x = (8 : ℕ) * x by norm_num, exp_nat_mul]
    ring
  rw [hp]
  have s1 : (exp x) ^ 2 ≤ b1 := (pow_two_le (exp_pos x).le h0).trans h1
  have s2 : ((exp x) ^ 2) ^ 2 ≤ b2 := (pow_two_le (by positivity) s1).trans h2
  exact (pow_two_le (by positivity) s2).trans h3

private lemma exp_pow_16_le {x b0 b1 b2 b3 b4 : ℝ}
    (h0 : exp x ≤ b0) (h1 : b0 ^ 2 ≤ b1) (h2 : b1 ^ 2 ≤ b2) (h3 : b2 ^ 2 ≤ b3)
    (h4 : b3 ^ 2 ≤ b4) : exp (16 * x) ≤ b4 := by
  have hp : exp (16 * x) = ((((exp x) ^ 2) ^ 2) ^ 2) ^ 2 := by
    rw [show (16 : ℝ) * x = (16 : ℕ) * x by norm_num, exp_nat_mul]
    ring
  rw [hp]
  have s1 : (exp x) ^ 2 ≤ b1 := (pow_two_le (exp_pos x).le h0).trans h1
  have s2 : ((exp x) ^ 2) ^ 2 ≤ b2 := (pow_two_le (by positivity) s1).trans h2
  have s3 : (((exp x) ^ 2) ^ 2) ^ 2 ≤ b3 := (pow_two_le (by positivity) s2).trans h3
  exact (pow_two_le (by positivity) s3).trans h4

private lemma exp_pow_32_le {x b0 b1 b2 b3 b4 b5 : ℝ}
    (h0 : exp x ≤ b0) (h1 : b0 ^ 2 ≤ b1) (h2 : b1 ^ 2 ≤ b2) (h3 : b2 ^ 2 ≤ b3)
    (h4 : b3 ^ 2 ≤ b4) (h5 : b4 ^ 2 ≤ b5) : exp (32 * x) ≤ b5 := by
  have hp : exp (32 * x) = (((((exp x) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
    rw [show (32 : ℝ) * x = (32 : ℕ) * x by norm_num, exp_nat_mul]
    ring
  rw [hp]
  have s1 : (exp x) ^ 2 ≤ b1 := (pow_two_le (exp_pos x).le h0).trans h1
  have s2 : ((exp x) ^ 2) ^ 2 ≤ b2 := (pow_two_le (by positivity) s1).trans h2
  have s3 : (((exp x) ^ 2) ^ 2) ^ 2 ≤ b3 := (pow_two_le (by positivity) s2).trans h3
  have s4 : ((((exp x) ^ 2) ^ 2) ^ 2) ^ 2 ≤ b4 := (pow_two_le (by positivity) s3).trans h4
  exact (pow_two_le (by positivity) s4).trans h5

private lemma exp_pow_32_ge {x b0 b1 b2 b3 b4 b5 : ℝ}
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4)
    (h0 : b0 ≤ exp x) (h1 : b1 ≤ b0 ^ 2) (h2 : b2 ≤ b1 ^ 2) (h3 : b3 ≤ b2 ^ 2)
    (h4 : b4 ≤ b3 ^ 2) (h5 : b5 ≤ b4 ^ 2) : b5 ≤ exp (32 * x) := by
  have hp : exp (32 * x) = (((((exp x) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
    rw [show (32 : ℝ) * x = (32 : ℕ) * x by norm_num, exp_nat_mul]
    ring
  rw [hp]
  have s1 : b1 ≤ (exp x) ^ 2 := h1.trans (pow_two_le hb0 h0)
  have s2 : b2 ≤ ((exp x) ^ 2) ^ 2 := h2.trans (pow_two_le hb1 s1)
  have s3 : b3 ≤ (((exp x) ^ 2) ^ 2) ^ 2 := h3.trans (pow_two_le hb2 s2)
  have s4 : b4 ≤ ((((exp x) ^ 2) ^ 2) ^ 2) ^ 2 := h4.trans (pow_two_le hb3 s3)
  exact h5.trans (pow_two_le hb4 s4)

private lemma exp_pow_64_le {x b0 b1 b2 b3 b4 b5 b6 : ℝ}
    (h0 : exp x ≤ b0) (h1 : b0 ^ 2 ≤ b1) (h2 : b1 ^ 2 ≤ b2) (h3 : b2 ^ 2 ≤ b3)
    (h4 : b3 ^ 2 ≤ b4) (h5 : b4 ^ 2 ≤ b5) (h6 : b5 ^ 2 ≤ b6) : exp (64 * x) ≤ b6 := by
  have hp : exp (64 * x) = ((((((exp x) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
    rw [show (64 : ℝ) * x = (64 : ℕ) * x by norm_num, exp_nat_mul]
    ring
  rw [hp]
  have s1 : (exp x) ^ 2 ≤ b1 := (pow_two_le (exp_pos x).le h0).trans h1
  have s2 : ((exp x) ^ 2) ^ 2 ≤ b2 := (pow_two_le (by positivity) s1).trans h2
  have s3 : (((exp x) ^ 2) ^ 2) ^ 2 ≤ b3 := (pow_two_le (by positivity) s2).trans h3
  have s4 : ((((exp x) ^ 2) ^ 2) ^ 2) ^ 2 ≤ b4 := (pow_two_le (by positivity) s3).trans h4
  have s5 : (((((exp x) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 ≤ b5 := (pow_two_le (by positivity) s4).trans h5
  exact (pow_two_le (by positivity) s5).trans h6

private lemma exp_pow_64_ge {x b0 b1 b2 b3 b4 b5 b6 : ℝ}
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4) (hb5 : 0 ≤ b5)
    (h0 : b0 ≤ exp x) (h1 : b1 ≤ b0 ^ 2) (h2 : b2 ≤ b1 ^ 2) (h3 : b3 ≤ b2 ^ 2)
    (h4 : b4 ≤ b3 ^ 2) (h5 : b5 ≤ b4 ^ 2) (h6 : b6 ≤ b5 ^ 2) : b6 ≤ exp (64 * x) := by
  have hp : exp (64 * x) = ((((((exp x) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
    rw [show (64 : ℝ) * x = (64 : ℕ) * x by norm_num, exp_nat_mul]
    ring
  rw [hp]
  have s1 : b1 ≤ (exp x) ^ 2 := h1.trans (pow_two_le hb0 h0)
  have s2 : b2 ≤ ((exp x) ^ 2) ^ 2 := h2.trans (pow_two_le hb1 s1)
  have s3 : b3 ≤ (((exp x) ^ 2) ^ 2) ^ 2 := h3.trans (pow_two_le hb2 s2)
  have s4 : b4 ≤ ((((exp x) ^ 2) ^ 2) ^ 2) ^ 2 := h4.trans (pow_two_le hb3 s3)
  have s5 : b5 ≤ (((((exp x) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := h5.trans (pow_two_le hb4 s4)
  exact h6.trans (pow_two_le hb5 s5)

/-! ### Algebraic rewrite of `FKS2Numerics.v1.nuAsympE30` -/

private lemma nuAsympE30_eq :
    FKS2Numerics.v1.nuAsympE30 =
      (5.5666305 / 121.096) * sqrt (5.5666305 / 30) *
        (exp (15 - 2 * sqrt (30 / 5.5666305)))⁻¹ *
        ((1 + 1.93378e-8) + BKLNW.v1.a₂ 30 * (exp 5)⁻¹) := by
  unfold FKS2Numerics.v1.nuAsympE30
  have h32 : ((5.5666305 : ℝ) / 30) ^ ((3 : ℝ) / 2) =
      (5.5666305 / 30) * sqrt (5.5666305 / 30) := by
    have hpos : (0 : ℝ) < 5.5666305 / 30 := by norm_num
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, rpow_add hpos, rpow_one, ← sqrt_eq_rpow]
  have he15 : (exp 30) ^ (-(1 : ℝ) / 2) = exp (-15) := by
    rw [← exp_mul]
    norm_num
  have he20 : (exp 30) ^ (-(2 : ℝ) / 3) = exp (-15) * exp (-5) := by
    rw [← exp_mul, ← exp_add]
    norm_num
  have heinv : exp (2 * sqrt (30 / 5.5666305)) * exp (-15) =
      (exp (15 - 2 * sqrt (30 / 5.5666305)))⁻¹ := by
    rw [← exp_add, ← exp_neg]
    congr 1
    ring
  rw [h32, he15, he20, ← exp_neg 5]
  calc
    1 / 121.096 * (5.5666305 / 30 * sqrt (5.5666305 / 30)) * exp (2 * sqrt (30 / 5.5666305)) *
        ((1 + 1.93378e-8) * 30 * exp (-15) + BKLNW.v1.a₂ 30 * 30 * (exp (-15) * exp (-5)))
      = (5.5666305 / 121.096) * sqrt (5.5666305 / 30) *
          (exp (2 * sqrt (30 / 5.5666305)) * exp (-15)) *
          ((1 + 1.93378e-8) + BKLNW.v1.a₂ 30 * exp (-5)) := by ring
    _ = _ := by rw [heinv]

/-! ### Square-root and exponential enclosures -/

private lemma sqrt_R_div_30_bounds :
    (0.4307602001 : ℝ) ≤ sqrt (5.5666305 / 30) ∧ sqrt (5.5666305 / 30) ≤ 0.4307602002 := by
  refine ⟨?_, ?_⟩
  · rw [le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [sqrt_le_left (by norm_num)]
    norm_num

private lemma sqrt_30_div_R_bounds :
    (2.3214772389 : ℝ) ≤ sqrt (30 / 5.5666305) ∧ sqrt (30 / 5.5666305) ≤ 2.3214772390 := by
  refine ⟨?_, ?_⟩
  · rw [le_sqrt (by norm_num) (by norm_num)]
    norm_num
  · rw [sqrt_le_left (by norm_num)]
    norm_num

private lemma exp_y_bounds :
    (31478.041271 : ℝ) ≤ exp (15 - 2 * sqrt (30 / 5.5666305)) ∧
      exp (15 - 2 * sqrt (30 / 5.5666305)) ≤ 31478.043756 := by
  obtain ⟨hs_lo, hs_hi⟩ := sqrt_30_div_R_bounds
  have hy_lo : (10.357045522 : ℝ) ≤ 15 - 2 * sqrt (30 / 5.5666305) := by linarith
  have hy_hi : 15 - 2 * sqrt (30 / 5.5666305) ≤ 10.3570455222 := by linarith
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ (exp_le_exp.mpr hy_lo)
    have h64 : (10.357045522 : ℝ) = 64 * (10.357045522 / 64) := by ring
    rw [h64]
    refine exp_pow_64_ge (b0 := 1.1756589939) (b1 := 1.3821740699) (b2 := 1.910405159)
      (b3 := 3.64964787) (b4 := 13.3199295) (b5 := 177.420521)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact (by norm_num : (1.1756589939 : ℝ) ≤ _).trans (poly9_le_exp (by norm_num))
  · refine (exp_le_exp.mpr hy_hi).trans ?_
    have h64 : (10.3570455222 : ℝ) = 64 * (10.3570455222 / 64) := by ring
    rw [h64]
    refine exp_pow_64_le (b0 := 1.175658994) (b1 := 1.3821740702) (b2 := 1.910405161)
      (b3 := 3.64964788) (b4 := 13.3199297) (b5 := 177.420528)
      ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact (exp_le_poly9 (by norm_num) (by norm_num)).trans (by norm_num)

private lemma exp_5_bounds :
    (148.4131525 : ℝ) ≤ exp 5 ∧ exp 5 ≤ 148.41318004 := by
  have h5 : (5 : ℝ) = 32 * (5 / 32) := by ring
  rw [h5]
  refine ⟨?_, ?_⟩
  · refine exp_pow_32_ge (b0 := 1.1691184461) (b1 := 1.36683794) (b2 := 1.86824595)
      (b3 := 3.49034292) (b4 := 12.18249369)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact (by norm_num : (1.1691184461 : ℝ) ≤ _).trans (poly9_le_exp (by norm_num))
  · refine exp_pow_32_le (b0 := 1.1691184462) (b1 := 1.36683795) (b2 := 1.86824599)
      (b3 := 3.49034308) (b4 := 12.18249482)
      ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact (exp_le_poly9 (by norm_num) (by norm_num)).trans (by norm_num)

private lemma exp_5_div_2_le : exp (5 / 2) ≤ 12.18249482 := by
  have h : (5 : ℝ) / 2 = 16 * (5 / 32) := by ring
  rw [h]
  refine exp_pow_16_le (b0 := 1.1691184462) (b1 := 1.36683795) (b2 := 1.86824599)
    (b3 := 3.49034308) ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (exp_le_poly9 (by norm_num) (by norm_num)).trans (by norm_num)

private lemma exp_4_le : exp 4 ≤ 54.598415 := by
  have h : (4 : ℝ) = 16 * (1 / 4) := by ring
  rw [h]
  refine exp_pow_16_le (b0 := 1.2840255) (b1 := 1.648722) (b2 := 2.718285) (b3 := 7.389074)
    ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (exp_le_poly7 (by norm_num) (by norm_num)).trans (by norm_num)

private lemma exp_40_div_7_le : exp (40 / 7) ≤ 303.171128 := by
  have h : (40 : ℝ) / 7 = 32 * (5 / 28) := by ring
  rw [h]
  refine exp_pow_32_le (b0 := 1.1955083) (b1 := 1.429241) (b2 := 2.04273) (b3 := 4.172746)
    (b4 := 17.41181) ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (exp_le_poly7 (by norm_num) (by norm_num)).trans (by norm_num)

private lemma exp_25_div_4_le : exp (25 / 4) ≤ 518.019285 := by
  have h : (25 : ℝ) / 4 = 32 * (25 / 128) := by ring
  rw [h]
  refine exp_pow_32_le (b0 := 1.2156909) (b1 := 1.477905) (b2 := 2.184204) (b3 := 4.770748)
    (b4 := 22.760037) ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (exp_le_poly7 (by norm_num) (by norm_num)).trans (by norm_num)

/-! ### Exact index `⌊30 / log 2⌋₊ = 43` and dominance `f (2^44) ≤ f (exp 30)` -/

private lemma floor_30_div_log_two : ⌊(30 : ℝ) / log 2⌋₊ = 43 := by
  have hlog_pos : 0 < log 2 := log_pos (by norm_num)
  rw [Nat.floor_eq_iff (div_nonneg (by norm_num) hlog_pos.le)]
  constructor
  · rw [le_div_iff₀ hlog_pos]
    have hlt := log_two_lt_d9
    norm_num at hlt ⊢
    linarith
  · rw [div_lt_iff₀ hlog_pos]
    have hgt := log_two_gt_d9
    norm_num at hgt ⊢
    linarith

private lemma f_exp30_eq :
    BKLNW.v1.f (exp 30) = ∑ k ∈ Icc (3 : ℕ) 43, exp (30 * ((1 : ℝ) / (k : ℝ) - 1 / 3)) := by
  unfold BKLNW.v1.f
  rw [log_exp, floor_30_div_log_two]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← exp_mul]

private lemma f_2pow44_eq :
    BKLNW.v1.f ((2 : ℝ) ^ (44 : ℕ)) =
      ∑ k ∈ Icc (3 : ℕ) 44, ((2 : ℝ) ^ (44 : ℕ)) ^ ((1 : ℝ) / (k : ℝ) - 1 / 3) := by
  unfold BKLNW.v1.f
  have hlog : log ((2 : ℝ) ^ (44 : ℕ)) / log 2 = 44 := by
    rw [log_pow]
    have hne : log 2 ≠ 0 := (log_pos (by norm_num)).ne'
    field_simp
    norm_cast
  rw [hlog, show ⌊(44 : ℝ)⌋₊ = 44 by norm_num]

private lemma exp30_le_2pow44 : exp 30 ≤ (2 : ℝ) ^ (44 : ℕ) := by
  have hlog : (30 : ℝ) ≤ 44 * log 2 := by linarith [log_two_gt_d9]
  have hpow : (2 : ℝ) ^ (44 : ℕ) = exp (44 * log 2) := by
    rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hpow]
  exact exp_le_exp.mpr hlog

private lemma sum_Icc_split {a b c : ℕ} (hab : a ≤ b) (hbc : b < c) (g : ℕ → ℝ) :
    ∑ k ∈ Icc a c, g k = (∑ k ∈ Icc a b, g k) + ∑ k ∈ Icc (b + 1) c, g k := by
  have hunion : Icc a c = Icc a b ∪ Icc (b + 1) c := by
    ext k
    simp only [mem_Icc, mem_union]
    omega
  have hdisj : Disjoint (Icc a b) (Icc (b + 1) c) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [mem_Icc] at hk1 hk2
    omega
  rw [hunion, Finset.sum_union hdisj]

private lemma sum_Icc_succ_top' {a b : ℕ} (hab : a ≤ b + 1) (g : ℕ → ℝ) :
    ∑ k ∈ Icc a (b + 1), g k = (∑ k ∈ Icc a b, g k) + g (b + 1) := by
  by_cases h : a ≤ b
  · rw [sum_Icc_split h (Nat.lt_succ_self b), Icc_self, sum_singleton]
  · have heq : a = b + 1 := by omega
    subst heq
    have hempty : Icc (b + 1) b = ∅ := by
      ext k
      simp only [mem_Icc, notMem_empty, iff_false]
      omega
    rw [hempty, sum_empty, zero_add, Icc_self, sum_singleton]

private lemma f_2pow44_le_f_exp30 :
    BKLNW.v1.f ((2 : ℝ) ^ (44 : ℕ)) ≤ BKLNW.v1.f (exp 30) := by
  rw [f_2pow44_eq]
  have hf30 : BKLNW.v1.f (exp 30) =
      ∑ k ∈ Icc (3 : ℕ) 43, (exp 30) ^ ((1 : ℝ) / (k : ℝ) - 1 / 3) := by
    unfold BKLNW.v1.f
    rw [log_exp, floor_30_div_log_two]
  rw [hf30]
  rw [sum_Icc_succ_top' (a := 3) (b := 43) (by omega)]
  have hmem4 : (4 : ℕ) ∈ Icc (3 : ℕ) 43 := mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← Finset.add_sum_erase _ _ hmem4, ← Finset.add_sum_erase _ _ hmem4]
  have hrest :
      ∑ k ∈ (Icc (3 : ℕ) 43).erase 4, ((2 : ℝ) ^ (44 : ℕ)) ^ ((1 : ℝ) / (k : ℝ) - 1 / 3) ≤
        ∑ k ∈ (Icc (3 : ℕ) 43).erase 4, (exp 30) ^ ((1 : ℝ) / (k : ℝ) - 1 / 3) := by
    refine sum_le_sum fun k hk ↦ ?_
    have hk3 : (3 : ℕ) ≤ k := (mem_Icc.mp (mem_of_mem_erase hk)).1
    have hexp_nonpos : (1 : ℝ) / (k : ℝ) - 1 / 3 ≤ 0 := by
      have hk3' : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
      have h1 : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) hk3'
      linarith
    exact rpow_le_rpow_of_nonpos (exp_pos 30) exp30_le_2pow44 hexp_nonpos
  -- Show the k = 4 and k = 44 terms for 2^44 together are bounded by the k = 4 term for exp 30.
  have h44_term : ((2 : ℝ) ^ (44 : ℕ)) ^ ((1 : ℝ) / (44 : ℝ) - 1 / 3) ≤ 1 / 8192 := by
    have hpow : ((2 : ℝ) ^ (44 : ℕ)) ^ ((1 : ℝ) / (44 : ℝ) - 1 / 3) =
        (2 : ℝ) ^ (-(41 : ℝ) / 3) := by
      rw [← rpow_natCast, ← rpow_mul (by norm_num)]
      congr 1
      norm_num
    rw [hpow]
    have hle : (2 : ℝ) ^ (-(41 : ℝ) / 3) ≤ (2 : ℝ) ^ (-(13 : ℝ)) :=
      rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    refine hle.trans ?_
    rw [show (-(13 : ℝ)) = (-13 : ℤ) by norm_num, rpow_intCast]
    norm_num
  have h4_term : ((2 : ℝ) ^ (44 : ℕ)) ^ ((1 : ℝ) / (4 : ℝ) - 1 / 3) ≤ 0.079 := by
    have hpow : ((2 : ℝ) ^ (44 : ℕ)) ^ ((1 : ℝ) / (4 : ℝ) - 1 / 3) =
        (2 : ℝ) ^ (-(11 : ℝ) / 3) := by
      rw [← rpow_natCast, ← rpow_mul (by norm_num)]
      congr 1
      norm_num
    rw [hpow]
    have hcube : ((2 : ℝ) ^ (-(11 : ℝ) / 3)) ^ (3 : ℕ) ≤ (0.079 : ℝ) ^ (3 : ℕ) := by
      rw [← rpow_natCast, ← rpow_mul (by norm_num)]
      rw [show (-(11 : ℝ) / 3) * (3 : ℕ) = (-11 : ℤ) by norm_num, rpow_intCast]
      norm_num
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hcube
  have h4_e30 : (0.082 : ℝ) ≤ (exp 30) ^ ((1 : ℝ) / (4 : ℝ) - 1 / 3) := by
    rw [← exp_mul, show (30 : ℝ) * ((1 : ℝ) / (4 : ℝ) - 1 / 3) = -(5 / 2) by norm_num, exp_neg]
    have hinv : (12.18249482 : ℝ)⁻¹ ≤ (exp (5 / 2))⁻¹ :=
      inv_anti₀ (exp_pos _) exp_5_div_2_le
    exact (by norm_num : (0.082 : ℝ) ≤ (12.18249482 : ℝ)⁻¹).trans hinv
  linarith

private lemma a₂_30_eq :
    BKLNW.v1.a₂ 30 = (1 + 1.93378e-8) * BKLNW.v1.f (exp 30) := by
  unfold BKLNW.v1.a₂
  rw [floor_30_div_log_two, max_eq_left f_2pow44_le_f_exp30]

/-! ### Part 1: Lower bound on `f (exp 30)` and refutation of `FKS2Numerics.v1.nu_asymp_e30_le` -/

private lemma f_exp30_ge : (1.112367 : ℝ) ≤ BKLNW.v1.f (exp 30) := by
  rw [f_exp30_eq]
  have hsub : Icc (3 : ℕ) 8 ⊆ Icc 3 43 := Icc_subset_Icc_right (by omega)
  have hsum :
      ∑ k ∈ Icc (3 : ℕ) 8, exp (30 * ((1 : ℝ) / (k : ℝ) - 1 / 3)) ≤
        ∑ k ∈ Icc (3 : ℕ) 43, exp (30 * ((1 : ℝ) / (k : ℝ) - 1 / 3)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ (exp_pos _).le
  refine le_trans ?_ hsum
  have hexp :
      ∑ k ∈ Icc (3 : ℕ) 8, exp (30 * ((1 : ℝ) / (k : ℝ) - 1 / 3)) =
        exp (30 * ((1 : ℝ) / (3 : ℕ) - 1 / 3)) + exp (30 * ((1 : ℝ) / (4 : ℕ) - 1 / 3)) +
        exp (30 * ((1 : ℝ) / (5 : ℕ) - 1 / 3)) + exp (30 * ((1 : ℝ) / (6 : ℕ) - 1 / 3)) +
        exp (30 * ((1 : ℝ) / (7 : ℕ) - 1 / 3)) + exp (30 * ((1 : ℝ) / (8 : ℕ) - 1 / 3)) := by
    rw [sum_Icc_succ_top' (a := 3) (b := 7) (by omega),
      sum_Icc_succ_top' (a := 3) (b := 6) (by omega),
      sum_Icc_succ_top' (a := 3) (b := 5) (by omega),
      sum_Icc_succ_top' (a := 3) (b := 4) (by omega),
      sum_Icc_succ_top' (a := 3) (b := 3) (by omega),
      Icc_self, sum_singleton]
  rw [hexp]
  have h3 : exp (30 * ((1 : ℝ) / (3 : ℕ) - 1 / 3)) = 1 := by norm_num
  have h4 : (12.18249482 : ℝ)⁻¹ ≤ exp (30 * ((1 : ℝ) / (4 : ℕ) - 1 / 3)) := by
    rw [show (30 : ℝ) * ((1 : ℝ) / (4 : ℕ) - 1 / 3) = -(5 / 2) by norm_num, exp_neg]
    exact inv_anti₀ (exp_pos _) exp_5_div_2_le
  have h5 : (54.598415 : ℝ)⁻¹ ≤ exp (30 * ((1 : ℝ) / (5 : ℕ) - 1 / 3)) := by
    rw [show (30 : ℝ) * ((1 : ℝ) / (5 : ℕ) - 1 / 3) = -4 by norm_num, exp_neg]
    exact inv_anti₀ (exp_pos _) exp_4_le
  have h6 : (148.41318004 : ℝ)⁻¹ ≤ exp (30 * ((1 : ℝ) / (6 : ℕ) - 1 / 3)) := by
    rw [show (30 : ℝ) * ((1 : ℝ) / (6 : ℕ) - 1 / 3) = -5 by norm_num, exp_neg]
    exact inv_anti₀ (exp_pos _) exp_5_bounds.2
  have h7 : (303.171128 : ℝ)⁻¹ ≤ exp (30 * ((1 : ℝ) / (7 : ℕ) - 1 / 3)) := by
    rw [show (30 : ℝ) * ((1 : ℝ) / (7 : ℕ) - 1 / 3) = -(40 / 7) by norm_num, exp_neg]
    exact inv_anti₀ (exp_pos _) exp_40_div_7_le
  have h8 : (518.019285 : ℝ)⁻¹ ≤ exp (30 * ((1 : ℝ) / (8 : ℕ) - 1 / 3)) := by
    rw [show (30 : ℝ) * ((1 : ℝ) / (8 : ℕ) - 1 / 3) = -(25 / 4) by norm_num, exp_neg]
    exact inv_anti₀ (exp_pos _) exp_25_div_4_le
  linarith

theorem nu_asymp_e30_gt : FKS2NuAsymp.v1.nu_asymp_e30_gt := by
  unfold FKS2NuAsymp.v1.nu_asymp_e30_gt FKS2Numerics.v1.nu_asymp_e30_le
  simp only [IEANTN.margin, pow_zero, one_mul, not_le]
  rw [nuAsympE30_eq, a₂_30_eq]
  have hs1 : (0.4307602001 : ℝ) ≤ sqrt (5.5666305 / 30) := sqrt_R_div_30_bounds.1
  have hey : (31478.043756 : ℝ)⁻¹ ≤ (exp (15 - 2 * sqrt (30 / 5.5666305)))⁻¹ :=
    inv_anti₀ (exp_pos _) exp_y_bounds.2
  have he5 : (148.41318004 : ℝ)⁻¹ ≤ (exp 5)⁻¹ :=
    inv_anti₀ (exp_pos _) exp_5_bounds.2
  have hf : (1.112367 : ℝ) ≤ BKLNW.v1.f (exp 30) := f_exp30_ge
  have hinner :
      (1 + 1.93378e-8 : ℝ) + (1 + 1.93378e-8) * 1.112367 * (148.41318004 : ℝ)⁻¹ ≤
        (1 + 1.93378e-8) + (1 + 1.93378e-8) * BKLNW.v1.f (exp 30) * (exp 5)⁻¹ := by
    gcongr
  have hpref :
      (5.5666305 / 121.096 : ℝ) * 0.4307602001 * (31478.043756 : ℝ)⁻¹ ≤
        (5.5666305 / 121.096) * sqrt (5.5666305 / 30) *
          (exp (15 - 2 * sqrt (30 / 5.5666305)))⁻¹ := by
    gcongr
  have hprod :
      ((5.5666305 / 121.096 : ℝ) * 0.4307602001 * (31478.043756 : ℝ)⁻¹) *
        ((1 + 1.93378e-8) + (1 + 1.93378e-8) * 1.112367 * (148.41318004 : ℝ)⁻¹) ≤
      ((5.5666305 / 121.096) * sqrt (5.5666305 / 30) *
        (exp (15 - 2 * sqrt (30 / 5.5666305)))⁻¹) *
        ((1 + 1.93378e-8) + (1 + 1.93378e-8) * BKLNW.v1.f (exp 30) * (exp 5)⁻¹) :=
    mul_le_mul hpref hinner (by positivity) (by positivity)
  have hnum :
      (6.3376e-7 : ℝ) <
        ((5.5666305 / 121.096 : ℝ) * 0.4307602001 * (31478.043756 : ℝ)⁻¹) *
          ((1 + 1.93378e-8) + (1 + 1.93378e-8) * 1.112367 * (148.41318004 : ℝ)⁻¹) := by
    norm_num
  exact hnum.trans_le hprod

/-! ### Part 2: Upper bound on `f (exp 30)` and corrected bound `nuAsympE30 ≤ 6.3381e-7` -/

private lemma exp_30_div_le_16 (k : ℕ) (hk : 4 ≤ k) {b0 b1 b2 b3 b4 : ℝ}
    (h0 : 1 + (30 / (16 * (k : ℝ))) + (30 / (16 * (k : ℝ))) ^ 2 / 2 +
          (30 / (16 * (k : ℝ))) ^ 3 / 6 + (30 / (16 * (k : ℝ))) ^ 4 / 24 +
          (30 / (16 * (k : ℝ))) ^ 5 / 120 + (30 / (16 * (k : ℝ))) ^ 6 / 720 +
          (30 / (16 * (k : ℝ))) ^ 7 / 4410 ≤ b0)
    (h1 : b0 ^ 2 ≤ b1) (h2 : b1 ^ 2 ≤ b2) (h3 : b2 ^ 2 ≤ b3) (h4 : b3 ^ 2 ≤ b4) :
    exp (30 / (k : ℝ)) ≤ b4 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hle1 : (30 : ℝ) / (16 * (k : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have heq : (30 : ℝ) / (k : ℝ) = 16 * (30 / (16 * (k : ℝ))) := by field_simp
  rw [heq]
  exact exp_pow_16_le ((exp_le_poly7 (by positivity) hle1).trans h0) h1 h2 h3 h4

private lemma exp_30_div_le_8 (k : ℕ) (hk : 4 ≤ k) {b0 b1 b2 b3 : ℝ}
    (h0 : 1 + (30 / (8 * (k : ℝ))) + (30 / (8 * (k : ℝ))) ^ 2 / 2 +
          (30 / (8 * (k : ℝ))) ^ 3 / 6 + (30 / (8 * (k : ℝ))) ^ 4 / 24 +
          (30 / (8 * (k : ℝ))) ^ 5 / 100 ≤ b0)
    (h1 : b0 ^ 2 ≤ b1) (h2 : b1 ^ 2 ≤ b2) (h3 : b2 ^ 2 ≤ b3) :
    exp (30 / (k : ℝ)) ≤ b3 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hle1 : (30 : ℝ) / (8 * (k : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have heq : (30 : ℝ) / (k : ℝ) = 8 * (30 / (8 * (k : ℝ))) := by field_simp
  rw [heq]
  exact exp_pow_8_le ((exp_le_poly5 (by positivity) hle1).trans h0) h1 h2 h3

private lemma sum_Icc_exp_30_div_le {a b : ℕ} {B : ℝ} (ha : 0 < a)
    (hB : exp (30 / (a : ℝ)) ≤ B) :
    ∑ k ∈ Icc a b, exp (30 / (k : ℝ)) ≤ ((Icc a b).card : ℝ) * B := by
  calc
    ∑ k ∈ Icc a b, exp (30 / (k : ℝ))
      ≤ ∑ _k ∈ Icc a b, B := by
        refine sum_le_sum fun k hk ↦ ?_
        have hak : (a : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
        refine (exp_le_exp.mpr ?_).trans hB
        exact div_le_div_of_nonneg_left (by norm_num) ha0 hak
    _ = ((Icc a b).card : ℝ) * B := by simp

private lemma sum_4_43_exp_30_div_le :
    ∑ k ∈ Icc (4 : ℕ) 43, exp (30 / (k : ℝ)) ≤ 2669.15 := by
  have hsplit :
      ∑ k ∈ Icc (4 : ℕ) 43, exp (30 / (k : ℝ)) =
        (∑ k ∈ Icc (4 : ℕ) 23, exp (30 / (k : ℝ))) +
        (∑ k ∈ Icc (24 : ℕ) 25, exp (30 / (k : ℝ))) +
        (∑ k ∈ Icc (26 : ℕ) 28, exp (30 / (k : ℝ))) +
        (∑ k ∈ Icc (29 : ℕ) 32, exp (30 / (k : ℝ))) +
        (∑ k ∈ Icc (33 : ℕ) 37, exp (30 / (k : ℝ))) +
        (∑ k ∈ Icc (38 : ℕ) 43, exp (30 / (k : ℝ))) := by
    rw [sum_Icc_split (a := 4) (b := 23) (c := 43) (by omega) (by omega),
      sum_Icc_split (a := 24) (b := 25) (c := 43) (by omega) (by omega),
      sum_Icc_split (a := 26) (b := 28) (c := 43) (by omega) (by omega),
      sum_Icc_split (a := 29) (b := 32) (c := 43) (by omega) (by omega),
      sum_Icc_split (a := 33) (b := 37) (c := 43) (by omega) (by omega)]
    ring
  rw [hsplit]
  have h4 : exp (30 / (4 : ℕ)) ≤ 1808.12 :=
    exp_30_div_le_16 4 (by omega) (b0 := 1.597996) (b1 := 2.5536) (b2 := 6.52088)
      (b3 := 42.52188) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 : exp (30 / (5 : ℕ)) ≤ 403.45 :=
    exp_30_div_le_16 5 (by omega) (b0 := 1.454992) (b1 := 2.11701) (b2 := 4.48174)
      (b3 := 20.086) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 : exp (30 / (6 : ℕ)) ≤ 148.42 :=
    exp_30_div_le_16 6 (by omega) (b0 := 1.366838) (b1 := 1.86825) (b2 := 3.49036)
      (b3 := 12.18262) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h7 : exp (30 / (7 : ℕ)) ≤ 72.66 :=
    exp_30_div_le_16 7 (by omega) (b0 := 1.307161) (b1 := 1.70867) (b2 := 2.91956)
      (b3 := 8.52384) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h8 : exp (30 / (8 : ℕ)) ≤ 42.53 :=
    exp_30_div_le_16 8 (by omega) (b0 := 1.264119) (b1 := 1.598) (b2 := 2.55361)
      (b3 := 6.52093) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h9 : exp (30 / (9 : ℕ)) ≤ 28.04 :=
    exp_30_div_le_16 9 (by omega) (b0 := 1.231624) (b1 := 1.5169) (b2 := 2.30099)
      (b3 := 5.29456) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h10 : exp (30 / (10 : ℕ)) ≤ 20.1 :=
    exp_30_div_le_8 10 (by omega) (b0 := 1.455) (b1 := 2.1171) (b2 := 4.4822)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 : exp (30 / (11 : ℕ)) ≤ 15.3 :=
    exp_30_div_le_8 11 (by omega) (b0 := 1.40624) (b1 := 1.9776) (b2 := 3.911)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h12 : exp (30 / (12 : ℕ)) ≤ 12.19 :=
    exp_30_div_le_8 12 (by omega) (b0 := 1.36685) (b1 := 1.8683) (b2 := 3.4906)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 : exp (30 / (13 : ℕ)) ≤ 10.06 :=
    exp_30_div_le_8 13 (by omega) (b0 := 1.33438) (b1 := 1.7806) (b2 := 3.1706)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h14 : exp (30 / (14 : ℕ)) ≤ 8.53 :=
    exp_30_div_le_8 14 (by omega) (b0 := 1.30717) (b1 := 1.7087) (b2 := 2.9197)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h15 : exp (30 / (15 : ℕ)) ≤ 7.4 :=
    exp_30_div_le_8 15 (by omega) (b0 := 1.28403) (b1 := 1.6488) (b2 := 2.7186)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h16 : exp (30 / (16 : ℕ)) ≤ 6.53 :=
    exp_30_div_le_8 16 (by omega) (b0 := 1.26412) (b1 := 1.598) (b2 := 2.5537)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h17 : exp (30 / (17 : ℕ)) ≤ 5.85 :=
    exp_30_div_le_8 17 (by omega) (b0 := 1.24682) (b1 := 1.5546) (b2 := 2.4168)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h18 : exp (30 / (18 : ℕ)) ≤ 5.3 :=
    exp_30_div_le_8 18 (by omega) (b0 := 1.23163) (b1 := 1.517) (b2 := 2.3013)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h19 : exp (30 / (19 : ℕ)) ≤ 4.86 :=
    exp_30_div_le_8 19 (by omega) (b0 := 1.2182) (b1 := 1.4841) (b2 := 2.2026)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h20 : exp (30 / (20 : ℕ)) ≤ 4.49 :=
    exp_30_div_le_8 20 (by omega) (b0 := 1.20624) (b1 := 1.4551) (b2 := 2.1174)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h21 : exp (30 / (21 : ℕ)) ≤ 4.18 :=
    exp_30_div_le_8 21 (by omega) (b0 := 1.19551) (b1 := 1.4293) (b2 := 2.0429)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h22 : exp (30 / (22 : ℕ)) ≤ 3.92 :=
    exp_30_div_le_8 22 (by omega) (b0 := 1.18585) (b1 := 1.4063) (b2 := 1.9777)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h23 : exp (30 / (23 : ℕ)) ≤ 3.69 :=
    exp_30_div_le_8 23 (by omega) (b0 := 1.17709) (b1 := 1.3856) (b2 := 1.9199)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb24 : ∑ k ∈ Icc (24 : ℕ) 25, exp (30 / (k : ℝ)) ≤ 2 * 3.5 := by
    simpa using sum_Icc_exp_30_div_le (a := 24) (b := 25) (by omega)
      (exp_30_div_le_8 24 (by omega) (b0 := 1.16912) (b1 := 1.3669) (b2 := 1.8685)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hb26 : ∑ k ∈ Icc (26 : ℕ) 28, exp (30 / (k : ℝ)) ≤ 3 * 3.18 := by
    simpa using sum_Icc_exp_30_div_le (a := 26) (b := 28) (by omega)
      (exp_30_div_le_8 26 (by omega) (b0 := 1.15516) (b1 := 1.3344) (b2 := 1.7807)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hb29 : ∑ k ∈ Icc (29 : ℕ) 32, exp (30 / (k : ℝ)) ≤ 4 * 2.82 := by
    simpa using sum_Icc_exp_30_div_le (a := 29) (b := 32) (by omega)
      (exp_30_div_le_8 29 (by omega) (b0 := 1.13805) (b1 := 1.2952) (b2 := 1.6776)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hb33 : ∑ k ∈ Icc (33 : ℕ) 37, exp (30 / (k : ℝ)) ≤ 5 * 2.49 := by
    simpa using sum_Icc_exp_30_div_le (a := 33) (b := 37) (by omega)
      (exp_30_div_le_8 33 (by omega) (b0 := 1.12035) (b1 := 1.2552) (b2 := 1.5756)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hb38 : ∑ k ∈ Icc (38 : ℕ) 43, exp (30 / (k : ℝ)) ≤ 6 * 2.21 := by
    simpa using sum_Icc_exp_30_div_le (a := 38) (b := 43) (by omega)
      (exp_30_div_le_8 38 (by omega) (b0 := 1.10372) (b1 := 1.2182) (b2 := 1.4841)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hhead :
      ∑ k ∈ Icc (4 : ℕ) 23, exp (30 / (k : ℝ)) =
        exp (30 / (4 : ℕ)) + exp (30 / (5 : ℕ)) + exp (30 / (6 : ℕ)) + exp (30 / (7 : ℕ)) +
        exp (30 / (8 : ℕ)) + exp (30 / (9 : ℕ)) + exp (30 / (10 : ℕ)) + exp (30 / (11 : ℕ)) +
        exp (30 / (12 : ℕ)) + exp (30 / (13 : ℕ)) + exp (30 / (14 : ℕ)) + exp (30 / (15 : ℕ)) +
        exp (30 / (16 : ℕ)) + exp (30 / (17 : ℕ)) + exp (30 / (18 : ℕ)) + exp (30 / (19 : ℕ)) +
        exp (30 / (20 : ℕ)) + exp (30 / (21 : ℕ)) + exp (30 / (22 : ℕ)) + exp (30 / (23 : ℕ)) := by
    rw [sum_Icc_succ_top' (a := 4) (b := 22) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 21) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 20) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 19) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 18) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 17) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 16) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 15) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 14) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 13) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 12) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 11) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 10) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 9) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 8) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 7) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 6) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 5) (by omega),
      sum_Icc_succ_top' (a := 4) (b := 4) (by omega),
      Icc_self, sum_singleton]
  rw [hhead]
  linarith

private lemma f_exp30_le :
    BKLNW.v1.f (exp 30) ≤ 1 + 2669.15 * ((148.4131525 : ℝ) ^ 2)⁻¹ := by
  rw [f_exp30_eq]
  rw [sum_Icc_split (a := 3) (b := 3) (c := 43) (by omega) (by omega), Icc_self, sum_singleton]
  have hfirst : exp (30 * ((1 : ℝ) / (3 : ℕ) - 1 / 3)) = 1 := by norm_num
  rw [hfirst]
  have hfac :
      ∑ k ∈ Icc (4 : ℕ) 43, exp (30 * ((1 : ℝ) / (k : ℝ) - 1 / 3)) =
        (∑ k ∈ Icc (4 : ℕ) 43, exp (30 / (k : ℝ))) * ((exp 5) ^ 2)⁻¹ := by
    rw [Finset.sum_mul]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← exp_nat_mul, ← exp_neg, ← exp_add]
    congr 1
    ring
  rw [hfac]
  have he10 : ((exp 5) ^ 2)⁻¹ ≤ ((148.4131525 : ℝ) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_two_le (by norm_num) exp_5_bounds.1)
  have hsum_nonneg : 0 ≤ ∑ k ∈ Icc (4 : ℕ) 43, exp (30 / (k : ℝ)) :=
    Finset.sum_nonneg fun _ _ ↦ (exp_pos _).le
  have hmul :
      (∑ k ∈ Icc (4 : ℕ) 43, exp (30 / (k : ℝ))) * ((exp 5) ^ 2)⁻¹ ≤
        2669.15 * ((148.4131525 : ℝ) ^ 2)⁻¹ :=
    mul_le_mul sum_4_43_exp_30_div_le he10 (by positivity) (by norm_num)
  linarith

theorem nu_asymp_e30_le : FKS2NuAsymp.v1.nu_asymp_e30_le := by
  unfold FKS2NuAsymp.v1.nu_asymp_e30_le
  simp only [IEANTN.margin, pow_zero, one_mul]
  rw [nuAsympE30_eq, a₂_30_eq]
  have hs1 : sqrt (5.5666305 / 30) ≤ 0.4307602002 := sqrt_R_div_30_bounds.2
  have hey : (exp (15 - 2 * sqrt (30 / 5.5666305)))⁻¹ ≤ (31478.041271 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) exp_y_bounds.1
  have he5 : (exp 5)⁻¹ ≤ (148.4131525 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) exp_5_bounds.1
  have hf : BKLNW.v1.f (exp 30) ≤ 1 + 2669.15 * ((148.4131525 : ℝ) ^ 2)⁻¹ := f_exp30_le
  have hf_nonneg : 0 ≤ BKLNW.v1.f (exp 30) := by
    rw [f_exp30_eq]
    exact Finset.sum_nonneg fun _ _ ↦ (exp_pos _).le
  have hinner :
      (1 + 1.93378e-8) + (1 + 1.93378e-8) * BKLNW.v1.f (exp 30) * (exp 5)⁻¹ ≤
        (1 + 1.93378e-8) +
          (1 + 1.93378e-8) * (1 + 2669.15 * ((148.4131525 : ℝ) ^ 2)⁻¹) *
            (148.4131525 : ℝ)⁻¹ := by
    gcongr
  have hpref :
      (5.5666305 / 121.096) * sqrt (5.5666305 / 30) *
          (exp (15 - 2 * sqrt (30 / 5.5666305)))⁻¹ ≤
        (5.5666305 / 121.096) * 0.4307602002 * (31478.041271 : ℝ)⁻¹ := by
    gcongr
  have hprod :
      ((5.5666305 / 121.096) * sqrt (5.5666305 / 30) *
          (exp (15 - 2 * sqrt (30 / 5.5666305)))⁻¹) *
        ((1 + 1.93378e-8) + (1 + 1.93378e-8) * BKLNW.v1.f (exp 30) * (exp 5)⁻¹) ≤
      ((5.5666305 / 121.096) * 0.4307602002 * (31478.041271 : ℝ)⁻¹) *
        ((1 + 1.93378e-8) +
          (1 + 1.93378e-8) * (1 + 2669.15 * ((148.4131525 : ℝ) ^ 2)⁻¹) *
            (148.4131525 : ℝ)⁻¹) :=
    mul_le_mul hpref hinner (by positivity) (by positivity)
  have hnum :
      ((5.5666305 / 121.096 : ℝ) * 0.4307602002 * (31478.041271 : ℝ)⁻¹) *
        ((1 + 1.93378e-8) +
          (1 + 1.93378e-8) * (1 + 2669.15 * ((148.4131525 : ℝ) ^ 2)⁻¹) *
            (148.4131525 : ℝ)⁻¹) ≤
      6.3381e-7 := by
    norm_num
  exact hprod.trans hnum

end FKS2NuAsymp.v1.Dev

theorem FKS2NuAsymp.v1.challenge_nu_asymp_e30_le : FKS2NuAsymp.v1.nu_asymp_e30_le :=
  FKS2NuAsymp.v1.Dev.nu_asymp_e30_le

theorem FKS2NuAsymp.v1.challenge_nu_asymp_e30_gt : FKS2NuAsymp.v1.nu_asymp_e30_gt :=
  FKS2NuAsymp.v1.Dev.nu_asymp_e30_gt
