/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section9Limit
import IEANTN.Nodes.PlattTrudgian.v1.Conclusions
import IEANTN.Nodes.Buthe.v1.Conclusions

/-!
# Corollary 1.3, the `ψ` display: the numerics

`|ψ(x) − x| ≤ (π/(3·10¹²)) x + 113.67 √x` for every `x ≥ 1`, from Corollary 1.2 at Platt and
Trudgian's height. The delicate part is `C_T ≤ 113.67`: at `T = 3 · 10¹² + 5` the true value is
`113.66888`, a margin of `1.1 · 10⁻³`, which pins `log(T/2π)` to about `1.3 · 10⁻⁴` and so needs
six significant digits of `log T` and `log 2π`. That is what this file supplies, from ten-term
Taylor bounds for `exp` on `[0,1]` and `e²⁸`.

Why `T = 3 · 10¹² + 5` rather than the exact verified height: Corollary 1.2 gives `π/(T−1)`, and
turning that into `π/(3·10¹²)` needs `T ≥ 3·10¹² + 1`, with a little more to pay for the main
factor `(π/T) coth(π/T) − 1 ≤ (π/T)²`. Five units is enough, and keeping `T` as small as possible
keeps `C_T` as small as possible.
-/

open Complex Filter Topology Set MeasureTheory

namespace CH2Section9

/-! ### Ten-term Taylor bounds for `exp` on `[0,1]` -/

theorem exp_le_taylor {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720
      + x ^ 7 / 5040 + x ^ 8 / 40320 + x ^ 9 / 362880 + x ^ 10 * 11 / 36288000 := by
  have h := Real.exp_bound' h0 h1 (n := 10) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

theorem exp_ge_taylor {x : ℝ} (h0 : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040
      + x ^ 8 / 40320 + x ^ 9 / 362880 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg h0 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

theorem exp_28_lb : (1.4462570e12 : ℝ) ≤ Real.exp 28 := by
  have h := (CH2Section7A.exp_nat_bounds 28).1
  simp only [Nat.cast_ofNat] at h
  calc (1.4462570e12 : ℝ) ≤ (2.7182818283 : ℝ) ^ 28 := by norm_num
    _ ≤ Real.exp 28 := h

theorem exp_28_ub : Real.exp 28 ≤ 1.4462572e12 := by
  have h := (CH2Section7A.exp_nat_bounds 28).2
  simp only [Nat.cast_ofNat] at h
  calc Real.exp 28 ≤ (2.7182818286 : ℝ) ^ 28 := h
    _ ≤ 1.4462572e12 := by norm_num

/-! ### `log 2π` and `log(3·10¹² + 5)` to six digits -/

theorem log_two_pi_lb : (1.83787 : ℝ) ≤ Real.log (2 * Real.pi) := by
  have hπ := Real.pi_gt_d6
  rw [Real.le_log_iff_exp_le (by positivity), show (1.83787 : ℝ) = 1 + 0.83787 by norm_num,
    Real.exp_add]
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h3 : Real.exp 0.83787 ≤ 2.31144 :=
    (exp_le_taylor (x := 0.83787) (by norm_num) (by norm_num)).trans (by norm_num)
  calc Real.exp 1 * Real.exp 0.83787 ≤ 2.7182818286 * 2.31144 :=
        mul_le_mul h1 h3 (Real.exp_pos _).le (by norm_num)
    _ ≤ 2 * Real.pi := by nlinarith

theorem log_two_pi_ub : Real.log (2 * Real.pi) ≤ 1.8379 := by
  have hπ := Real.pi_lt_d6
  rw [Real.log_le_iff_le_exp (by positivity), show (1.8379 : ℝ) = 1 + 0.8379 by norm_num,
    Real.exp_add]
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h3 : (2.31150 : ℝ) ≤ Real.exp 0.8379 :=
    le_trans (by norm_num) (exp_ge_taylor (x := 0.8379) (by norm_num))
  calc 2 * Real.pi ≤ 2.7182818283 * 2.31150 := by nlinarith
    _ ≤ Real.exp 1 * Real.exp 0.8379 := mul_le_mul h1 h3 (by norm_num) (Real.exp_pos _).le

theorem log_T_ub : Real.log (3 * 10 ^ 12 + 5) ≤ 28.7297 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (28.7297 : ℝ) = 28 + 0.7297 by norm_num,
    Real.exp_add]
  have h3 : (2.07445 : ℝ) ≤ Real.exp 0.7297 :=
    le_trans (by norm_num) (exp_ge_taylor (x := 0.7297) (by norm_num))
  calc (3 * 10 ^ 12 + 5 : ℝ) ≤ 1.4462570e12 * 2.07445 := by norm_num
    _ ≤ Real.exp 28 * Real.exp 0.7297 :=
        mul_le_mul exp_28_lb h3 (by norm_num) (Real.exp_pos _).le

theorem log_T_lb : (28.7296 : ℝ) ≤ Real.log (3 * 10 ^ 12 + 5) := by
  rw [Real.le_log_iff_exp_le (by norm_num), show (28.7296 : ℝ) = 28 + 0.7296 by norm_num,
    Real.exp_add]
  have h3 : Real.exp 0.7296 ≤ 2.07426 :=
    (exp_le_taylor (x := 0.7296) (by norm_num) (by norm_num)).trans (by norm_num)
  calc Real.exp 28 * Real.exp 0.7296 ≤ 1.4462572e12 * 2.07426 :=
        mul_le_mul exp_28_ub h3 (Real.exp_pos _).le (by norm_num)
    _ ≤ 3 * 10 ^ 12 + 5 := by norm_num

/-! ### `C_T` at the two heights used -/

theorem CT_le_big : CH2.v1.CT (3 * 10 ^ 12 + 5) ≤ 113.67 := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hπ : (0 : ℝ) < Real.pi := by linarith
  rw [CH2.v1.CT]
  set y : ℝ := Real.log ((3 * 10 ^ 12 + 5) / (2 * Real.pi)) with hy
  have hyeq : y = Real.log (3 * 10 ^ 12 + 5) - Real.log (2 * Real.pi) := by
    rw [hy, Real.log_div (by norm_num) (by positivity)]
  have hylo : (26.8917 : ℝ) ≤ y := by
    rw [hyeq]; linarith [log_T_lb, log_two_pi_ub]
  have hyhi : y ≤ 26.89183 := by
    rw [hyeq]; linarith [log_T_ub, log_two_pi_lb]
  have h1 : 1 / (2 * Real.pi) * y ^ (2 : ℕ) ≤ 115.09633 := by
    have hy2 : y ^ (2 : ℕ) ≤ 723.17053 := by nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : (1.42664 : ℝ) ≤ 1 / (6 * Real.pi) * y := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

theorem log_ten_ub : Real.log 10 ≤ 2.3026 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (2.3026 : ℝ) = 2 + 0.3026 by norm_num,
    Real.exp_add]
  have h2 := (CH2Section7A.exp_nat_bounds 2).1
  simp only [Nat.cast_ofNat] at h2
  have h4 : (1.35336 : ℝ) ≤ Real.exp 0.3026 :=
    le_trans (by norm_num) (exp_ge_taylor (x := 0.3026) (by norm_num))
  calc (10 : ℝ) ≤ 7.3890560 * 1.35336 := by norm_num
    _ ≤ Real.exp 2 * Real.exp 0.3026 := by
        refine mul_le_mul ?_ h4 (by norm_num) (Real.exp_pos _).le
        calc (7.3890560 : ℝ) ≤ (2.7182818283 : ℝ) ^ 2 := by norm_num
          _ ≤ Real.exp 2 := h2

theorem CT_le_small : CH2.v1.CT (10 ^ 7) ≤ 82 := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hπ : (0 : ℝ) < Real.pi := by linarith
  rw [CH2.v1.CT]
  set y : ℝ := Real.log ((10 ^ 7 : ℝ) / (2 * Real.pi)) with hy
  have hyeq : y = Real.log ((10 : ℝ) ^ 7) - Real.log (2 * Real.pi) := by
    rw [hy, Real.log_div (by norm_num) (by positivity)]
  have hl7 : Real.log ((10 : ℝ) ^ 7) ≤ 16.1182 := by
    rw [Real.log_pow]
    push_cast
    linarith [log_ten_ub]
  have hyhi : y ≤ 14.3 := by
    rw [hyeq]; linarith [log_two_pi_lb]
  have hylo : (0 : ℝ) ≤ y := by
    rw [hy]
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h1 : 1 / (2 * Real.pi) * y ^ (2 : ℕ) ≤ 33 := by
    have hy2 : y ^ (2 : ℕ) ≤ 204.49 := by nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : (0 : ℝ) ≤ 1 / (6 * Real.pi) * y := by positivity
  linarith

/-! ### The main factor -/

theorem mainFactor_eq_ycoth {T : ℝ} (hT : 0 < T) :
    CH2.v1.mainFactor T = ycoth (Real.pi / T) := by
  have hπ := Real.pi_pos
  have hu : 0 < Real.pi / T := by positivity
  have hs : Real.sinh (Real.pi / T) ≠ 0 := (Real.sinh_pos_iff.mpr hu).ne'
  have hc : Real.cosh (Real.pi / T) ≠ 0 := (Real.cosh_pos _).ne'
  rw [CH2.v1.mainFactor, Real.tanh_eq_sinh_div_cosh, ycoth]
  field_simp

theorem mainFactor_bounds {T : ℝ} (hT : Real.pi ≤ T) :
    1 ≤ CH2.v1.mainFactor T ∧ CH2.v1.mainFactor T ≤ 1 + (Real.pi / T) ^ 2 := by
  have hπ := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hu : 0 < Real.pi / T := by positivity
  have hu1 : Real.pi / T ≤ 1 := by rw [div_le_one hT0]; exact hT
  rw [mainFactor_eq_ycoth hT0]
  exact ⟨one_le_ycoth hu, (ycoth_le_cosh hu).trans (cosh_le_one_add_sq hu.le hu1)⟩

/-! ### Corollary 1.2, with the main factor removed -/

theorem psi_of_cor12 (hcor : CH2.v1.corollary_1_2_psi)
    (hRH : PlattTrudgian.v1.rh_up_to_exact) {T x B : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T)
    (hTle : T ≤ 3000175332800) (hx : max T ((10 : ℝ) ^ 9) < x) (hCT : CH2.v1.CT T ≤ B) :
    |Chebyshev.psi x - x| ≤ (Real.pi / (T - 1) + (Real.pi / T) ^ 2) * x + B * Real.sqrt x := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have hx0 : (0 : ℝ) < x := lt_trans (by positivity) (lt_of_le_of_lt (le_max_right _ _) hx)
  have hs0 : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h := hcor T x hT (RH_mono hTle hRH) hx
  obtain ⟨hmf1, hmf2⟩ := mainFactor_bounds (show Real.pi ≤ T by
    linarith [Real.pi_lt_four, show (4 : ℝ) ≤ 10 ^ 7 by norm_num])
  have hsplit : |Chebyshev.psi x - x|
      ≤ |Chebyshev.psi x - x * CH2.v1.mainFactor T| + x * (CH2.v1.mainFactor T - 1) := by
    have e : Chebyshev.psi x - x
        = (Chebyshev.psi x - x * CH2.v1.mainFactor T) + x * (CH2.v1.mainFactor T - 1) := by ring
    calc |Chebyshev.psi x - x|
        ≤ |Chebyshev.psi x - x * CH2.v1.mainFactor T| + |x * (CH2.v1.mainFactor T - 1)| := by
          rw [e]; exact abs_add_le _ _
      _ = _ := by
          rw [abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ x * (CH2.v1.mainFactor T - 1))]
  have hcorr : x * (CH2.v1.mainFactor T - 1) ≤ (Real.pi / T) ^ 2 * x := by nlinarith
  have hB : CH2.v1.CT T * Real.sqrt x ≤ B * Real.sqrt x :=
    mul_le_mul_of_nonneg_right hCT hs0
  nlinarith [h, hsplit, hcorr, hB]

/-! ### The three ranges -/

theorem cor13_large (hcor : CH2.v1.corollary_1_2_psi) (hRH : PlattTrudgian.v1.rh_up_to_exact)
    {x : ℝ} (hx : 3 * 10 ^ 12 + 5 < x) :
    |Chebyshev.psi x - x| ≤ Real.pi / (3 * 10 ^ 12) * x + 113.67 * Real.sqrt x := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hπ : (0 : ℝ) < Real.pi := by linarith
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 3 * 10 ^ 12 by norm_num]
  have h := psi_of_cor12 hcor hRH (T := 3 * 10 ^ 12 + 5) (by norm_num) (by norm_num)
    (by rw [max_eq_left (by norm_num)]; exact hx) CT_le_big
  have hcoef : Real.pi / (3 * 10 ^ 12 + 5 - 1) + (Real.pi / (3 * 10 ^ 12 + 5)) ^ 2
      ≤ Real.pi / (3 * 10 ^ 12) := by
    rw [div_add' _ _ _ (by norm_num), div_le_div_iff₀ (by norm_num) (by norm_num)]
    ring_nf
    nlinarith [sq_nonneg Real.pi]
  nlinarith [h, hcoef, hx0.le]

theorem cor13_mid (hcor : CH2.v1.corollary_1_2_psi) (hRH : PlattTrudgian.v1.rh_up_to_exact)
    {x : ℝ} (hx1 : (10 : ℝ) ^ 9 < x) (hx2 : x ≤ 3 * 10 ^ 12 + 5) :
    |Chebyshev.psi x - x| ≤ Real.pi / (3 * 10 ^ 12) * x + 113.67 * Real.sqrt x := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hπ : (0 : ℝ) < Real.pi := by linarith
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 9 by norm_num]
  have h := psi_of_cor12 hcor hRH (T := (10 : ℝ) ^ 7) le_rfl (by norm_num)
    (by rw [max_eq_right (by norm_num)]; exact hx1) CT_le_small
  have hs : Real.sqrt x ≤ 1.74e6 := by
    rw [show (1.74e6 : ℝ) = Real.sqrt (1.74e6 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxs : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
  -- the excess coefficient, times `x`, fits inside the `√x` slack
  have hcoef : (Real.pi / ((10 : ℝ) ^ 7 - 1) + (Real.pi / (10 : ℝ) ^ 7) ^ 2) * x
      ≤ Real.pi / (3 * 10 ^ 12) * x + 31.67 * Real.sqrt x := by
    have hle : Real.pi / ((10 : ℝ) ^ 7 - 1) + (Real.pi / (10 : ℝ) ^ 7) ^ 2 ≤ 3.2e-7 := by
      rw [div_add' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]
      nlinarith
    have h1 : (Real.pi / ((10 : ℝ) ^ 7 - 1) + (Real.pi / (10 : ℝ) ^ 7) ^ 2) * x ≤ 3.2e-7 * x :=
      mul_le_mul_of_nonneg_right hle hx0.le
    have h2 : (3.2e-7 : ℝ) * x ≤ 31.67 * Real.sqrt x := by
      have hkey : 0 ≤ Real.sqrt x * (31.67 - 3.2e-7 * Real.sqrt x) :=
        mul_nonneg hs0.le (by linarith)
      nlinarith [hxs]
    have h3 : (0 : ℝ) ≤ Real.pi / (3 * 10 ^ 12) * x := by positivity
    linarith
  nlinarith [h, hcoef]

theorem psi_le_of_small {x : ℝ} (hx : x ≤ 11) : Chebyshev.psi x ≤ 31 := by
  rw [Chebyshev.psi]
  have hcard : (Finset.Ioc 0 ⌊x⌋₊).card ≤ 11 := by
    rcases le_or_gt x 0 with h | h
    · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h one_pos)]
    · have : ⌊x⌋₊ ≤ 11 := Nat.floor_le_of_le hx |>.trans (by norm_num)
      simpa using this
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 2.8 := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    have hn11 : (n : ℝ) ≤ 16 := by
      have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hn).2
      have h2 : (⌊x⌋₊ : ℝ) ≤ 11 := by
        rcases le_or_gt x 0 with h | h
        · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h one_pos)]
        · exact_mod_cast Nat.floor_le_of_le hx |>.trans (by norm_num)
      have : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      linarith
    calc Real.log (n : ℝ) ≤ Real.log 16 := Real.log_le_log hnpos hn11
      _ = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
          push_cast
          ring
      _ ≤ 2.8 := by linarith [Real.log_two_lt_d9]
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ)
      ≤ ∑ _n ∈ Finset.Ioc 0 ⌊x⌋₊, (2.8 : ℝ) := Finset.sum_le_sum hterm
    _ = (Finset.Ioc 0 ⌊x⌋₊).card * 2.8 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 11 * 2.8 := by
        have : ((Finset.Ioc 0 ⌊x⌋₊).card : ℝ) ≤ 11 := by exact_mod_cast hcard
        nlinarith
    _ ≤ 31 := by norm_num

theorem cor13_small {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 11) :
    |Chebyshev.psi x - x| ≤ Real.pi / (3 * 10 ^ 12) * x + 113.67 * Real.sqrt x := by
  have hπ := Real.pi_pos
  have h1 : Chebyshev.psi x ≤ 31 := psi_le_of_small hx2
  have h2 : (0 : ℝ) ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  have hs : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hx1
  have habs : |Chebyshev.psi x - x| ≤ 31 := by
    rw [abs_le]
    constructor <;> linarith
  have : (0 : ℝ) ≤ Real.pi / (3 * 10 ^ 12) * x := by positivity
  nlinarith

theorem cor13_buthe (hbuthe : Buthe.v1.theorem_2_psi) {x : ℝ} (hx1 : 11 < x)
    (hx2 : x ≤ (10 : ℝ) ^ 9) :
    |Chebyshev.psi x - x| ≤ Real.pi / (3 * 10 ^ 12) * x + 113.67 * Real.sqrt x := by
  have hπ := Real.pi_pos
  have hx0 : (0 : ℝ) < x := by linarith
  have h := hbuthe x hx1 (by nlinarith [show (10 : ℝ) ^ 9 ≤ 10 ^ 19 by norm_num])
  rw [abs_sub_comm] at h
  have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have : (0 : ℝ) ≤ Real.pi / (3 * 10 ^ 12) * x := by positivity
  nlinarith

/-! ### Corollary 1.3, the `ψ` display -/

theorem corollary_1_3_psi (hcor : CH2.v1.corollary_1_2_psi)
    (hRH : PlattTrudgian.v1.rh_up_to_exact) (hbuthe : Buthe.v1.theorem_2_psi) :
    CH2.v1.corollary_1_3_psi := by
  intro x hx
  rcases le_or_gt x 11 with h1 | h1
  · exact cor13_small hx h1
  rcases le_or_gt x ((10 : ℝ) ^ 9) with h2 | h2
  · exact cor13_buthe hbuthe h1 h2
  rcases le_or_gt x (3 * 10 ^ 12 + 5) with h3 | h3
  · exact cor13_mid hcor hRH h2 h3
  · exact cor13_large hcor hRH h3

end CH2Section9
