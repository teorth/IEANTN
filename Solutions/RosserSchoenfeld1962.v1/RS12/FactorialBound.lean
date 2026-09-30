/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.Period

open Real Finsupp Finset Chebyshev
namespace RS12Factorial

noncomputable def slope (cs : List (ℕ × ℤ)) : ℝ :=
  - (cs.map (fun dw => (dw.2 : ℝ) / 1000000 * log dw.1 / dw.1)).sum

def weightSum (cs : List (ℕ × ℤ)) : ℤ := (cs.map Prod.snd).sum

def weightAbsSum (cs : List (ℕ × ℤ)) : ℤ := (cs.map (fun dw => |dw.2|)).sum

/-- A single weighted factorial term, with its error measured at x. -/
private theorem weighted_T_term {x : ℝ} (hx : 1 ≤ x) {m : ℕ} (hm : 0 < m)
    (hmx : (m : ℝ) ≤ x) (b : ℝ) :
    b * Chebyshev.T (x / m) ≤
      (b / m) * (x * log x - x) - (b * log m / m) * x + b + |b| * log x := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : 1 ≤ x / m := (one_le_div hmp).mpr hmx
  have hb := Chebyshev.U_bound.lemma_2 (x / m) hy
  have hlog : log (x / m) ≤ log x := Real.log_le_log (by positivity)
    (div_le_self (by linarith) (by exact_mod_cast hm))
  have herr : b * Chebyshev.e (x / m) ≤ |b| * log x := by
    calc
      _ ≤ |b * Chebyshev.e (x / m)| := le_abs_self _
      _ = |b| * |Chebyshev.e (x / m)| := abs_mul _ _
      _ ≤ |b| * log x := mul_le_mul_of_nonneg_left (hb.trans hlog) (abs_nonneg _)
  rw [Chebyshev.e] at herr
  rw [Real.log_div (by linarith : x ≠ 0) hmp.ne'] at herr
  linear_combination herr

/-- Cancellation removes the x log x term; the remaining constants are finite sums. -/
theorem weighted_T_upper (cs : List (ℕ × ℤ)) {x : ℝ} (hx : 1 ≤ x)
    (hs : ∀ dw ∈ cs, 0 < dw.1 ∧ (dw.1 : ℝ) ≤ x)
    (hc : (cs.map (fun dw => (dw.2 : ℝ) / 1000000 / dw.1)).sum = 0) :
    (realWeights cs).sum (fun m b => b * Chebyshev.T (x / m)) ≤
      slope cs * x + (weightSum cs : ℝ) / 1000000 +
        ((weightAbsSum cs : ℝ) / 1000000) * log x := by
  rw [realWeights_sum]
  have hb := List.sum_le_sum (l := cs) (fun dw hd => weighted_T_term hx (hs dw hd).1
    (hs dw hd).2 ((dw.2 : ℝ) / 1000000))
  have heq : (cs.map (fun dw =>
      ((dw.2 : ℝ) / 1000000 / dw.1) * (x * log x - x) -
      ((dw.2 : ℝ) / 1000000 * log dw.1 / dw.1) * x +
      (dw.2 : ℝ) / 1000000 + |(dw.2 : ℝ) / 1000000| * log x)).sum =
      (cs.map (fun dw => (dw.2 : ℝ) / 1000000 / dw.1)).sum * (x * log x - x) +
      slope cs * x + (weightSum cs : ℝ) / 1000000 +
        ((weightAbsSum cs : ℝ) / 1000000) * log x := by
    clear hc hs hb
    induction cs with
    | nil => simp [slope, weightSum, weightAbsSum]
    | cons dw cs ih =>
      simp only [List.map_cons, List.sum_cons, slope, weightSum, weightAbsSum,
        Int.cast_add, Int.cast_abs] at *
      rw [ih]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1000000)]
      ring
  rw [heq, hc, zero_mul, zero_add] at hb
  exact hb

end RS12Factorial
