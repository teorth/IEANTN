/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions
import IEANTN.Nodes.DudekPlatt.v4.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v3.Conclusions

/-!
# Solution: `DudekPlatt.v4`

Ramanujan's inequality above `exp(9401)`, from the repaired criterion and the two-sided `π`
estimate at Dudek and Platt's own footnote 1 parameters.

Both arrive as hypotheses, which is what `DudekPlatt.v4`'s two imports mean:

* `DudekPlatt.v3.criterion` — the repaired Lemma 2.1, itself `lean-comparator` verified;
* `DudekPlattNumerics.v3.pi_two_sided_footnote` — the two-sided estimate for `π` at the paper's
  footnote-improved constants `M = 3250.488`, `m = −3010.333`, above `exp(9400)`.

All that is left is to instantiate the criterion at those constants and discharge its threshold
condition, which is the only real work here and is done in `threshold` below. This file follows
`Solutions/DudekPlatt.v2/Solution.lean`'s pattern line for line, substituting the new node names
and constants.

## The threshold condition, and how much room it has

`criterion` assumes `εUpper Mₐ x − εLower mₐ xₐ x < log x` above the threshold. At these constants
it holds with **substantial** room: the crude bound proved below reaches about `9379.94` against a
threshold of `9401`, i.e. roughly `21` units of slack — much more than `DudekPlatt.v2`'s own
`0.4989` at its threshold, and in sharp contrast to the same condition **failing** at
`DudekPlattNumerics.v1`'s parameters at `DudekPlatt.v1`'s printed threshold (documented on that
node, short by about `0.89`). The large margin here is exactly what lets `x₀ = exp(9401)` recover
issue #63's `exp(9658)` target with `257` log-units to spare, without needing to optimize `xₐ`,
`Mₐ` or `mₐ` any further.

The bound below is deliberately crude, in the same shape as `.v2`'s: every `c/(log x)^k` with
`c > 0` in `εUpper` is bounded by its value at `log x = 9401`, and every non-negative tail term of
`εNeg` is simply dropped. -/

open Real IEANTN DudekPlatt.v3

namespace DudekPlattV4Sol

/-- The criterion's threshold condition, at `M = 3250.488`, `m = −3010.333`, `xₐ = exp 9400`.

Proved by bounding each positive reciprocal power at `log x = 9401` and discarding the negative
ones, the same shape as `PrimeNumberTheoremAnd`'s `epsilon_bound` and `DudekPlatt.v2`'s own
`threshold`. -/
lemma threshold (x : ℝ) (hx : Real.exp 9401 < x) :
    εUpper 3250.488 x - εLower (-3010.333) (Real.exp 9400) x < Real.log x := by
  have hL : (9401 : ℝ) < Real.log x := by
    have h := Real.log_lt_log (by positivity) hx
    simpa using h
  have hL0 : (0 : ℝ) < Real.log x := by linarith
  have hxa : Real.log (Real.exp 9400) = 9400 := Real.log_exp _
  -- `m = -3010.333` is negative, so `εLower` takes the repaired branch. `-3010.333` is a decimal
  -- (`OfScientific`) literal rather than a plain integer, so plain `simp` cannot decide its sign
  -- the way it can for `.v2`'s `-1194`; `norm_num` is needed to close `¬ (0:ℝ) ≤ -3010.333`.
  have hLower : εLower (-3010.333 : ℝ) (Real.exp 9400) x
      = εNeg (-3010.333) (Real.exp 9400) x := by
    unfold εLower
    exact if_neg (by norm_num : ¬ (0 : ℝ) ≤ -3010.333)
  rw [hLower]
  simp only [εUpper, εNeg, hxa]
  -- Every positive term is largest at `log x = 9401`.
  have key : ∀ c : ℝ, ∀ k : ℕ, 0 ≤ c → c / Real.log x ^ k ≤ c / 9401 ^ k := by
    intro c k hc
    exact div_le_div_of_nonneg_left hc (by positivity)
      (pow_le_pow_left₀ (by norm_num) hL.le k)
  have h1 : (2 * 3250.488 + 132 : ℝ) / Real.log x ≤ (2 * 3250.488 + 132) / 9401 := by
    simpa using key (2 * 3250.488 + 132) 1 (by norm_num)
  have h2 : (4 * 3250.488 + 288 : ℝ) / Real.log x ^ 2 ≤ (4 * 3250.488 + 288) / 9401 ^ 2 :=
    key _ 2 (by norm_num)
  have h3 : (12 * 3250.488 + 576 : ℝ) / Real.log x ^ 3 ≤ (12 * 3250.488 + 576) / 9401 ^ 3 :=
    key _ 3 (by norm_num)
  have h4 : (48 * 3250.488 : ℝ) / Real.log x ^ 4 ≤ (48 * 3250.488) / 9401 ^ 4 :=
    key _ 4 (by norm_num)
  have h5 : ((3250.488 : ℝ) ^ 2) / Real.log x ^ 5 ≤ ((3250.488 : ℝ) ^ 2) / 9401 ^ 5 :=
    key _ 5 (by norm_num)
  -- Every subtracted term is non-negative, so dropping it only weakens the bound.
  have n1 : (0 : ℝ) ≤ 364 / Real.log x := by positivity
  have n2 : (0 : ℝ) ≤ 381 / Real.log x ^ 2 := by positivity
  have n3 : (0 : ℝ) ≤ 238 / Real.log x ^ 3 := by positivity
  have n4 : (0 : ℝ) ≤ 97 / Real.log x ^ 4 := by positivity
  have n5 : (0 : ℝ) ≤ 30 / Real.log x ^ 5 := by positivity
  have n6 : (0 : ℝ) ≤ 8 / Real.log x ^ 6 := by positivity
  -- The repair's factor, bounded so the whole estimate stays linear in the reciprocal powers.
  -- `(1 + 1/9400)^6 = 1.000638...`, so this product is `-3012.255...`.
  have hc : ((1 : ℝ) + 1 / 9400) ^ 6 * (-3010.333) ≥ -3012.26 := by norm_num
  -- Crude total: 72 + 6500.976 - 206 + 3012.26 + (tail bounds) ≈ 9379.94 < 9401 < log x.
  linarith [hL, h1, h2, h3, h4, h5, n1, n2, n3, n4, n5, n6, hc]

end DudekPlattV4Sol

theorem DudekPlatt.v4.challenge_ramanujan_inequality_9401
    (dudekplatt_v3_criterion : DudekPlatt.v3.criterion)
    (dudekplattnumerics_v3_pi_two_sided_footnote : DudekPlattNumerics.v3.pi_two_sided_footnote) :
    DudekPlatt.v4.ramanujan_inequality_9401 := by
  intro x hx
  have hxa1 : (1 : ℝ) < Real.exp 9400 := by
    have := Real.add_one_le_exp (9400 : ℝ)
    linarith
  have hexa : Real.exp 1 * Real.exp 9400 = Real.exp 9401 := by
    rw [← Real.exp_add]; norm_num
  -- `margin 0 = 1`, so the numerical input says exactly what it appears to.
  have hnum := dudekplattnumerics_v3_pi_two_sided_footnote
  simp only [DudekPlattNumerics.v3.pi_two_sided_footnote, IEANTN.margin, pow_zero, one_mul]
    at hnum
  refine dudekplatt_v3_criterion (-3010.333) 3250.488 (Real.exp 9400) (Real.exp 9401) hxa1
    ?_ ?_ ?_ ?_ x hx
  · intro y hy
    -- `-3010.333 * y / L^6` and `3010.333 * (y / L^6)` are equal but are different atoms to
    -- `linarith`.
    have e : DudekPlatt.v3.mainTerm y + (-3010.333) * y / Real.log y ^ (6 : ℕ)
        = DudekPlattNumerics.v3.mainTerm y - 3010.333 * (y / Real.log y ^ (6 : ℕ)) := by
      simp only [DudekPlatt.v3.mainTerm, DudekPlattNumerics.v3.mainTerm]
      ring
    rw [e]
    exact (hnum y hy).1
  · intro y hy
    rw [hexa] at hy
    have e : DudekPlatt.v3.mainTerm y + 3250.488 * y / Real.log y ^ (6 : ℕ)
        = DudekPlattNumerics.v3.mainTerm y + 3250.488 * (y / Real.log y ^ (6 : ℕ)) := by
      simp only [DudekPlatt.v3.mainTerm, DudekPlattNumerics.v3.mainTerm]
      ring
    rw [e]
    exact (hnum y (lt_trans (Real.exp_lt_exp.mpr (by norm_num)) hy)).2
  · exact le_of_eq hexa
  · intro y hy
    exact DudekPlattV4Sol.threshold y hy
