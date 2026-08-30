/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.DudekPlatt.v2.Conclusions
import IEANTN.Nodes.DudekPlatt.v3.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v2.Conclusions

/-!
# Solution: `DudekPlatt.v2`

Ramanujan's inequality above `exp(3915)`, from the repaired criterion and one numerical input.

Both arrive as hypotheses, which is what `DudekPlatt.v2`'s two imports mean:

* `DudekPlatt.v3.criterion` — the repaired Lemma 2.1, itself `lean-comparator` verified;
* `DudekPlattNumerics.v2.pi_two_sided_pnt` — the two-sided estimate for `π` at
  `PrimeNumberTheoremAnd`'s literal constants `M = 1426`, `m = −1194`, above `exp(3914)`.

All that is left is to instantiate the criterion at those constants and discharge its threshold
condition, which is the only real work here and is done in `threshold` below.

## The threshold condition is not a formality

`criterion` assumes `εUpper Mₐ x − εLower mₐ xₐ x < log x` above the threshold. At these constants
it holds, clearing by about `0.4989` at `log x = 3915`. At `DudekPlattNumerics.v1`'s constants —
Dudek and Platt's own — **the same condition fails** at the threshold their paper prints, by
`0.887`. So this is a place where the repair genuinely bites, and where a solution that assumed
rather than proved would have been wrong one node over.

The bound below is deliberately crude: every `c/(log x)^k` with `c > 0` is bounded by its value at
`log x = 3915`, and every subtracted term is simply dropped. That gives `3914.6`-ish against a
threshold of `3915`, which is enough, and it avoids any argument about how the two tails interact.
-/

open Real IEANTN DudekPlatt.v3

namespace DudekPlattV2Sol

/-- The criterion's threshold condition, at `M = 1426`, `m = −1194`, `xₐ = exp 3914`.

Proved by bounding each positive reciprocal power at `log x = 3915` and discarding the negative
ones, which is the same shape as `PrimeNumberTheoremAnd`'s `epsilon_bound`. -/
lemma threshold (x : ℝ) (hx : Real.exp 3915 < x) :
    εUpper 1426 x - εLower (-1194) (Real.exp 3914) x < Real.log x := by
  have hL : (3915 : ℝ) < Real.log x := by
    have h := Real.log_lt_log (by positivity) hx
    simpa using h
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hxa : Real.log (Real.exp 3914) = 3914 := Real.log_exp _
  -- `m = -1194` is negative, so `εLower` takes the repaired branch.
  -- `m = -1194 < 0`, so `εLower` reduces to the repaired branch `εNeg`.
  rw [show εLower (-1194) (Real.exp 3914) x = εNeg (-1194) (Real.exp 3914) x from
    by simp [εLower]]
  simp only [εUpper, εNeg, hxa]
  -- Every positive term is largest at `log x = 3915`.
  have key : ∀ c : ℝ, ∀ k : ℕ, 0 ≤ c → c / Real.log x ^ k ≤ c / 3915 ^ k := by
    intro c k hc
    exact div_le_div_of_nonneg_left hc (by positivity)
      (pow_le_pow_left₀ (by norm_num) hL.le k)
  have h1 : (2 * 1426 + 132 : ℝ) / Real.log x ≤ (2 * 1426 + 132) / 3915 := by
    simpa using key (2 * 1426 + 132) 1 (by norm_num)
  have h2 : (4 * 1426 + 288 : ℝ) / Real.log x ^ 2 ≤ (4 * 1426 + 288) / 3915 ^ 2 :=
    key _ 2 (by norm_num)
  have h3 : (12 * 1426 + 576 : ℝ) / Real.log x ^ 3 ≤ (12 * 1426 + 576) / 3915 ^ 3 :=
    key _ 3 (by norm_num)
  have h4 : (48 * 1426 : ℝ) / Real.log x ^ 4 ≤ (48 * 1426) / 3915 ^ 4 :=
    key _ 4 (by norm_num)
  have h5 : ((1426 : ℝ) ^ 2) / Real.log x ^ 5 ≤ ((1426 : ℝ) ^ 2) / 3915 ^ 5 :=
    key _ 5 (by norm_num)
  -- Every subtracted term is non-negative, so dropping it only weakens the bound.
  have n1 : (0 : ℝ) ≤ 364 / Real.log x := by positivity
  have n2 : (0 : ℝ) ≤ 381 / Real.log x ^ 2 := by positivity
  have n3 : (0 : ℝ) ≤ 238 / Real.log x ^ 3 := by positivity
  have n4 : (0 : ℝ) ≤ 97 / Real.log x ^ 4 := by positivity
  have n5 : (0 : ℝ) ≤ 30 / Real.log x ^ 5 := by positivity
  have n6 : (0 : ℝ) ≤ 8 / Real.log x ^ 6 := by positivity
  -- The repair's factor, bounded so the whole estimate stays linear in the reciprocal powers.
  -- `(1 + 1/3914)^6 = 1.00153...`, so this product is `-1195.8315...`.
  have hc : ((1 : ℝ) + 1 / 3914) ^ 6 * (-1194) ≥ -1195.9 := by norm_num
  -- Crude total: 72 + 2852 - 206 + 1195.9 + 0.7626 = 3914.663 < 3915 < log x.
  linarith [hL, h1, h2, h3, h4, h5, n1, n2, n3, n4, n5, n6, hc]

end DudekPlattV2Sol

theorem DudekPlatt.v2.challenge_ramanujan_inequality_3915
    (dudekplatt_v3_criterion : DudekPlatt.v3.criterion)
    (dudekplattnumerics_v2_pi_two_sided_pnt : DudekPlattNumerics.v2.pi_two_sided_pnt) :
    DudekPlatt.v2.ramanujan_inequality_3915 := by
  intro x hx
  have hxa1 : (1 : ℝ) < Real.exp 3914 := by
    have := Real.add_one_le_exp (3914 : ℝ)
    linarith
  have hexa : Real.exp 1 * Real.exp 3914 = Real.exp 3915 := by
    rw [← Real.exp_add]; norm_num
  -- `margin 0 = 1`, so the numerical input says exactly what it appears to.
  have hnum := dudekplattnumerics_v2_pi_two_sided_pnt
  simp only [DudekPlattNumerics.v2.pi_two_sided_pnt, IEANTN.margin, pow_zero, one_mul]
    at hnum
  refine dudekplatt_v3_criterion (-1194) 1426 (Real.exp 3914) (Real.exp 3915) hxa1
    ?_ ?_ ?_ ?_ x hx
  · intro y hy
    -- `-1194 * y / L^6` and `1194 * (y / L^6)` are equal but are different atoms to `linarith`.
    have e : DudekPlatt.v3.mainTerm y + (-1194) * y / Real.log y ^ (6 : ℕ)
        = DudekPlattNumerics.v2.mainTerm y - 1194 * (y / Real.log y ^ (6 : ℕ)) := by
      simp only [DudekPlatt.v3.mainTerm, DudekPlattNumerics.v2.mainTerm]
      ring
    rw [e]
    exact (hnum y hy).1
  · intro y hy
    rw [hexa] at hy
    have e : DudekPlatt.v3.mainTerm y + 1426 * y / Real.log y ^ (6 : ℕ)
        = DudekPlattNumerics.v2.mainTerm y + 1426 * (y / Real.log y ^ (6 : ℕ)) := by
      simp only [DudekPlatt.v3.mainTerm, DudekPlattNumerics.v2.mainTerm]
      ring
    rw [e]
    exact (hnum y (lt_trans (Real.exp_lt_exp.mpr (by norm_num)) hy)).2
  · exact le_of_eq hexa
  · intro y hy
    exact DudekPlattV2Sol.threshold y hy
