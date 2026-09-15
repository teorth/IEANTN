/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section7Adar
import IEANTN.Nodes.PlattZeroSum.v1.Conclusions

/-!
# Section 7: `lem:salmon` and `prop:vihuela`

`lem:salmon` handles the zeros with `0 < γ ≤ t₀` by the classical weight (`cor:thonny`, eq. `demoscen`);
`prop:vihuela` splits at `t₀ = 2·10⁴`, uses `PlattZeroSum.v1` below and `lem:adar` above, and concludes

`(2π/T) ∑_{0 < γ ≤ T} |ω⁺_{T,σ}(ρ) + ξ θ_{T,1}(ρ) i| ≤ (1/2π) log²(T/2π) - (1.001/6π) log(T/2π)`

for `T ≥ 10⁷`, `0 ≤ σ < 1`, `|ξ| ≤ 1`, RH up to `T` and no zero ordinate at `T`.

The paper states `1.01/6π` for `|σ - 1/2| ≤ 100`; Section 9 needs only `σ ∈ [0, 1]` and uses the
extra `0.01/6π` for terms of size `10⁻⁴`, so `1.001` is what is proved. Its margin at `T = 10⁷` is
about `0.017`, growing with `T`.
-/

open Real MeasureTheory Set

namespace CH2Section7A

open CH2Section7 CH2Section7T

/-! ### Numbers -/

theorem exp_small_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 * 4 / 18 := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  norm_num at h ⊢
  linarith

theorem exp_small_ge {x : ℝ} (h0 : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg h0 5
  simpa [Finset.sum_range_succ, Nat.factorial] using h

theorem exp_nat_bounds (n : ℕ) :
    (2.7182818283 : ℝ) ^ n ≤ Real.exp n ∧ Real.exp n ≤ (2.7182818286 : ℝ) ^ n := by
  rw [← Real.exp_one_pow]
  exact ⟨pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n,
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n⟩

theorem log_t0_bounds : (8.064 : ℝ) ≤ Real.log (20000 / (2 * Real.pi)) ∧
    Real.log (20000 / (2 * Real.pi)) ≤ 8.07 := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hpos : (0 : ℝ) < 20000 / (2 * Real.pi) := by positivity
  constructor
  · rw [Real.le_log_iff_exp_le hpos, show (8.064 : ℝ) = (8 : ℕ) + 0.064 by norm_num, Real.exp_add]
    have h8 := (exp_nat_bounds 8).2
    have hs := exp_small_le (x := 0.064) (by norm_num) (by norm_num)
    rw [le_div_iff₀ (by positivity)]
    have h8' : Real.exp ((8 : ℕ) : ℝ) ≤ 2980.96 := by norm_num at h8 ⊢; linarith
    have hs' : Real.exp 0.064 ≤ 1.06611 := by norm_num at hs ⊢; linarith
    have : Real.exp ((8 : ℕ) : ℝ) * Real.exp 0.064 ≤ 2980.96 * 1.06611 :=
      mul_le_mul h8' hs' (Real.exp_pos _).le (by norm_num)
    nlinarith
  · rw [Real.log_le_iff_le_exp hpos, show (8.07 : ℝ) = (8 : ℕ) + 0.07 by norm_num, Real.exp_add]
    have h8 := (exp_nat_bounds 8).1
    have hs := exp_small_ge (x := 0.07) (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    have h8' : (2980.95 : ℝ) ≤ Real.exp ((8 : ℕ) : ℝ) := by norm_num at h8 ⊢; linarith
    have hs' : (1.0725 : ℝ) ≤ Real.exp 0.07 := by norm_num at hs ⊢; linarith
    have : (2980.95 : ℝ) * 1.0725 ≤ Real.exp ((8 : ℕ) : ℝ) * Real.exp 0.07 :=
      mul_le_mul h8' hs' (by norm_num) (Real.exp_pos _).le
    nlinarith

theorem log_T0_le : Real.log ((10 : ℝ) ^ 7 / (2 * Real.pi)) ≤ 14.3 := by
  have hπ1 := Real.pi_gt_d6
  have hpos : (0 : ℝ) < (10 : ℝ) ^ 7 / (2 * Real.pi) := by positivity
  rw [Real.log_le_iff_le_exp hpos, show (14.3 : ℝ) = (14 : ℕ) + 0.3 by norm_num, Real.exp_add]
  have h14 := (exp_nat_bounds 14).1
  have hs := exp_small_ge (x := 0.3) (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  have h14' : (1202604 : ℝ) ≤ Real.exp ((14 : ℕ) : ℝ) := by norm_num at h14 ⊢; linarith
  have hs' : (1.3498 : ℝ) ≤ Real.exp 0.3 := by norm_num at hs ⊢; linarith
  have : (1202604 : ℝ) * 1.3498 ≤ Real.exp ((14 : ℕ) : ℝ) * Real.exp 0.3 :=
    mul_le_mul h14' hs' (by norm_num) (Real.exp_pos _).le
  nlinarith

theorem log_20000_le : Real.log 20000 ≤ 9.92 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (9.92 : ℝ) = (9 : ℕ) + 0.92 by norm_num, Real.exp_add]
  have h9 := (exp_nat_bounds 9).1
  have hs := exp_small_ge (x := 0.92) (by norm_num)
  have h9' : (8103 : ℝ) ≤ Real.exp ((9 : ℕ) : ℝ) := by norm_num at h9 ⊢; linarith
  have hs' : (2.5 : ℝ) ≤ Real.exp 0.92 := by norm_num at hs ⊢; linarith
  have : (8103 : ℝ) * 2.5 ≤ Real.exp ((9 : ℕ) : ℝ) * Real.exp 0.92 :=
    mul_le_mul h9' hs' (by norm_num) (Real.exp_pos _).le
  linarith

theorem log_500_le : Real.log 500 ≤ 6.22 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (6.22 : ℝ) = (6 : ℕ) + 0.22 by norm_num, Real.exp_add]
  have h6 := (exp_nat_bounds 6).1
  have hs := exp_small_ge (x := 0.22) (by norm_num)
  have h6' : (403.4 : ℝ) ≤ Real.exp ((6 : ℕ) : ℝ) := by norm_num at h6 ⊢; linarith
  have hs' : (1.246 : ℝ) ≤ Real.exp 0.22 := by norm_num at hs ⊢; linarith
  have : (403.4 : ℝ) * 1.246 ≤ Real.exp ((6 : ℕ) : ℝ) * Real.exp 0.22 :=
    mul_le_mul h6' hs' (by norm_num) (Real.exp_pos _).le
  linarith

end CH2Section7A
