import Mathlib

/-!
# Small numerical facts about `exp` and `log` (copies of the `MajorArcs.Cor713` helpers, to keep the
`Explicit/` zero-free-region files independent of `MajorArcs`)
-/

namespace TernaryGoldbach.Explicit

theorem exp_ge_taylor' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i / i.factorial ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx n

theorem exp_nat_ge' (k : ℕ) : (2.7182818283 : ℝ) ^ k ≤ Real.exp k := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k

theorem exp_split_ge' (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (2.7182818283 : ℝ) ^ k * ∑ i ∈ Finset.range n, u ^ i / i.factorial ≤ Real.exp (k + u) := by
  rw [Real.exp_add]
  exact mul_le_mul (exp_nat_ge' k) (exp_ge_taylor' hu n) (Finset.sum_nonneg fun i _ => by positivity)
    (Real.exp_pos _).le

theorem log_le_of_le_exp'' {x c : ℝ} (hx : 0 < x) (h : x ≤ Real.exp c) : Real.log x ≤ c :=
  (Real.log_le_iff_le_exp hx).2 h

theorem log9201_le' : Real.log 9201 ≤ 9.2 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 9 (u := 0.2) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem neg_log0355_le' : -Real.log 0.355 ≤ 1.0357 := by
  rw [← Real.log_inv]
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 1 (u := 0.0357) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log22_le' : Real.log 22 ≤ 3.0911 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 3 (u := 0.0911) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

theorem log1375_le' : Real.log 13.75 ≤ 2.6211 := by
  refine log_le_of_le_exp'' (by norm_num) ?_
  have h := exp_split_ge' 2 (u := 0.6211) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith

end TernaryGoldbach.Explicit
