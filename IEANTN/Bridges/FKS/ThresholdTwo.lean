/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcos Adriano
-/
import IEANTN.Nodes.FKS.v1.Conclusions
import IEANTN.Nodes.FKS.v2.Conclusions
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Bridge: `FKS.v1.psi_classical_bound` already holds from `x₀ = 2`

`FKS.v1.psi_classical_bound` states the admissible classical bound
`Eψ x ≤ 121.096 (log x / R)^{3/2} exp(−2 √(log x / R))`, `R = 5.5666305`, for `x ≥ e³⁰`, as `FKS2`
quotes it in its proof of Corollary 14. `FKS2`'s remark on admissible asymptotic bounds quotes the
same four parameters with `x₀ = 2`, and so does PrimeNumberTheoremAnd (issue #52, discrepancy 1).

The two thresholds say the same thing. On `[2, e³⁰]` the right-hand side never drops below
`2.627…` (its minimum, at `x = 2`), and Mathlib's Chebyshev bound `ψ x ≤ log 4 · x + 2 √x log x`
already gives `Eψ x ≤ 2` there. So the `x₀ = 2` form follows from the `x₀ = e³⁰` one with no
further input — the argument `FKS2` itself gives for `Eθ` right after quoting the bound.

The lower bound on the right-hand side is done on five pieces of `s = √(log x / R)`, which runs
over `[0.352, 2.3216]`, each with `s³ ≥ a³` and `exp (−2s) ≥ (1 − 2b/n)ⁿ` at the right end `b`;
the tightest piece, next to `x = 2`, clears `2` by 4.6%.
-/

namespace IEANTN.Bridges.FKS

open IEANTN Real

/-- `log x ≤ (4/5) √x` for `x > 0`: `log √x ≤ √x / e`, and `2 / e < 4 / 5`. -/
lemma log_le_four_fifths_sqrt {x : ℝ} (hx : 0 < x) : log x ≤ 4 / 5 * √x := by
  have hs : 0 < √x := sqrt_pos.mpr hx
  have he : 0 < exp 1 := exp_pos 1
  have h1 : log (√x / exp 1) ≤ √x / exp 1 - 1 := log_le_sub_one_of_pos (div_pos hs he)
  rw [log_div hs.ne' he.ne', log_exp, log_sqrt hx.le] at h1
  have he' : (5 : ℝ) / 2 ≤ exp 1 := by have := exp_one_gt_d9; linarith
  have h2 : √x / exp 1 ≤ 2 / 5 * √x := by
    rw [div_le_iff₀ he]
    nlinarith
  linarith

/-- Mathlib's Chebyshev bound gives `Eψ x ≤ 2` for every `x ≥ 2`. -/
lemma Eψ_le_two {x : ℝ} (hx : 2 ≤ x) : Eψ x ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hψ := Chebyshev.psi_le hx1
  have hψ0 := Chebyshev.psi_nonneg x
  have hlog := log_le_four_fifths_sqrt hx0
  have hlog4 : log 4 < 1.3863 := by
    have h4 : log 4 = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
      push_cast
      ring
    have := log_two_lt_d9
    linarith
  have hsx : √x * √x = x := mul_self_sqrt hx0.le
  have hs0 : 0 ≤ √x := sqrt_nonneg x
  have h4x : log 4 * x ≤ 1.3863 * x := by nlinarith
  have hmid : 2 * √x * log x ≤ 2 * √x * (4 / 5 * √x) := by gcongr
  have hup : Chebyshev.psi x ≤ 3 * x := by nlinarith
  unfold Eψ
  rw [div_le_iff₀ hx0, abs_le]
  constructor <;> linarith

/-- `(1 + y / n) ^ n ≤ exp y` whenever `1 + y / n ≥ 0`. -/
lemma one_add_div_pow_le_exp {y : ℝ} {n : ℕ} (hn : 0 < n) (hy : 0 ≤ 1 + y / n) :
    (1 + y / n) ^ n ≤ exp y := by
  have h := add_one_le_exp (y / n)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc (1 + y / n) ^ n ≤ exp (y / n) ^ n := pow_le_pow_left₀ hy (by linarith) n
    _ = exp y := by rw [← exp_nat_mul]; congr 1; field_simp

/-- The classical bound's right-hand side stays above `2` on `[2, e³⁰]`. -/
lemma two_le_admissibleBound {x : ℝ} (hx : 2 ≤ x) (hx30 : x ≤ exp 30) :
    2 ≤ admissibleBound 121.096 (3 / 2) 2 5.5666305 x := by
  have hx0 : 0 < x := by linarith
  have hl2 : log 2 ≤ log x := log_le_log (by norm_num) hx
  have hl30 : log x ≤ 30 := by
    have := log_le_log hx0 hx30
    rwa [log_exp] at this
  have hlog2 := log_two_gt_d9
  unfold admissibleBound
  set t := log x / 5.5666305 with ht
  have ht_lo : 0.1245 ≤ t := by rw [ht, le_div_iff₀ (by norm_num)]; linarith
  have ht_hi : t ≤ 5.3894 := by rw [ht, div_le_iff₀ (by norm_num)]; linarith
  have ht0 : 0 ≤ t := by linarith
  set s := t ^ ((1 : ℝ) / 2) with hs
  have hs0 : 0 ≤ s := rpow_nonneg ht0 _
  have hs2 : s ^ 2 = t := by
    rw [hs, ← rpow_natCast, ← rpow_mul ht0]
    norm_num
  have ht32 : t ^ ((3 : ℝ) / 2) = s ^ 3 := by
    rw [hs, ← rpow_natCast, ← rpow_mul ht0]
    norm_num
  have hs_lo : 0.352 ≤ s := by nlinarith
  have hs_hi : s ≤ 2.3216 := by nlinarith
  rw [ht32]
  -- one piece: `s ∈ [a, b]`, with `s³ ≥ a³` and `exp (-2 s) ≥ exp (-2 b) ≥ (1 - 2 b / n) ^ n`
  have piece : ∀ (a b : ℝ) (n : ℕ), 0 < n → a ≤ s → s ≤ b → 0 ≤ a → 0 ≤ 1 + -2 * b / n →
      2 ≤ 121.096 * a ^ 3 * (1 + -2 * b / n) ^ n → 2 ≤ 121.096 * s ^ 3 * exp (-2 * s) := by
    intro a b n hn has hsb ha hy hnum
    have h1 : a ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ ha has 3
    have h2 : (1 + -2 * b / n) ^ n ≤ exp (-2 * b) := one_add_div_pow_le_exp hn hy
    have h3 : exp (-2 * b) ≤ exp (-2 * s) := exp_le_exp.mpr (by linarith)
    have h4 : 0 ≤ (1 + -2 * b / n) ^ n := pow_nonneg hy n
    have h5 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
    calc (2 : ℝ) ≤ 121.096 * a ^ 3 * (1 + -2 * b / n) ^ n := hnum
      _ ≤ 121.096 * s ^ 3 * (1 + -2 * b / n) ^ n := by gcongr
      _ ≤ 121.096 * s ^ 3 * exp (-2 * s) := by gcongr; exact h2.trans h3
  rcases le_or_gt s 0.45 with h1 | h1
  · exact piece 0.352 0.45 16 (by norm_num) hs_lo h1 (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt s 0.65 with h2 | h2
  · exact piece 0.45 0.65 16 (by norm_num) h1.le h2 (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt s 1 with h3 | h3
  · exact piece 0.65 1 16 (by norm_num) h2.le h3 (by norm_num) (by norm_num) (by norm_num)
  rcases le_or_gt s 1.6 with h4 | h4
  · exact piece 1 1.6 16 (by norm_num) h3.le h4 (by norm_num) (by norm_num) (by norm_num)
  · exact piece 1.6 2.3216 32 (by norm_num) h4.le hs_hi (by norm_num) (by norm_num) (by norm_num)

/-- **The bridge.** `FKS.v1.psi_classical_bound`, stated from `x₀ = e³⁰`, implies
`FKS.v2.psi_classical_bound`, the same bound from `x₀ = 2` -- the threshold `FKS2`'s remark and
PrimeNumberTheoremAnd quote. The two node statements are therefore equivalent, since the `x₀ = 2`
form gives the `x₀ = e³⁰` one by `exp 30 ≥ 2`. -/
theorem psi_classical_bound_from_two (h : FKS.v1.psi_classical_bound) :
    FKS.v2.psi_classical_bound := by
  intro x hx
  by_cases hx30 : exp 30 ≤ x
  · exact h x hx30
  · exact (Eψ_le_two hx).trans (two_le_admissibleBound hx (not_le.mp hx30).le)

end IEANTN.Bridges.FKS
