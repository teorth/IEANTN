/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.Chebyshev

open Real Finsupp Finset Chebyshev
open ArithmeticFunction hiding log
namespace RS12Factorial

/-- A positive weighted-floor certificate controls a short multiplicative interval of psi. -/
theorem psi_diff_le_weighted {w : ℕ →₀ ℝ} {a x : ℝ} (ha : 1 ≤ a) (hx : 0 < x)
    (hpos : ∀ y ≥ 0, 0 ≤ Chebyshev.E w y)
    (hfirst : ∀ y ∈ Set.Ico 1 a, 1 ≤ Chebyshev.E w y) :
    ψ x - ψ (x / a) ≤ w.sum (fun m b ↦ b * Chebyshev.T (x / m)) := by
  unfold Chebyshev.psi
  rw [Chebyshev.T.weighted_eq_sum, ← Ioc_eq_Icc]
  have hsub : Ioc 0 ⌊x / a⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le ha
  rw [← sum_sdiff_eq_sub hsub, ← sum_sdiff hsub]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_)
    (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg (hpos _ (div_nonneg hx.le (by positivity))))
  have hn' := hn
  simp only [Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le] at hn'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn'.1.1
  have hnle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hn'.1.2
  have hsmall : x / a < n := (Nat.floor_lt (div_nonneg hx.le (by linarith))).mp (hn'.2 hn'.1.1)
  have he := hfirst (x / n) ⟨(one_le_div hnpos).mpr hnle,
    (div_lt_iff₀ hnpos).mpr (by nlinarith [(div_lt_iff₀ (by linarith : 0 < a)).mp hsmall])⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (vonMangoldt_nonneg (n := n))

/-- A uniform elementary error for small factorial arguments. -/
private theorem T_small_error {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    |Chebyshev.T y - (y * log y - y + 1)| ≤ 1 := by
  have ht : Chebyshev.T y = 0 := by
    by_cases heq : y = 1
    · simp [heq, Chebyshev.T]
    · have hfl : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (lt_of_le_of_ne hy1 heq)
      simp [Chebyshev.T, hfl]
  rw [ht, zero_sub, abs_neg, abs_le]
  have hl : log y ≤ 0 := Real.log_nonpos hy.le hy1
  have hm : y * log y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy.le hl
  have hg : 0 ≤ y * log y - y + 1 := by
    have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
    rw [Real.log_inv] at hi
    have hh := mul_le_mul_of_nonneg_left hi hy.le
    rw [mul_sub, mul_inv_cancel₀ hy.ne', mul_one] at hh
    nlinarith
  constructor <;> linarith

end RS12Factorial
