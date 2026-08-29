/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Bounds

/-!
# Solution: `DudekPlatt.v3`

Dudek and Platt's Lemma 2.1, repaired, proved.

The shape of the argument is theirs: bound `π(x)²` above and `(e x / log x) π(x/e)` below by the
same expression `x²(1/log²x + 2/log³x + 5/log⁴x + 16/log⁵x + …)` differing only in the sixth-order
coefficient and in the seventh-order term, then show the difference is negative. What the criterion
assumes — `εUpper Mₐ x − εLower mₐ xₐ x < log x` — is exactly what makes it so.

The repair lives in `Shifts.lean` and is used by `Bounds.lean`'s `ex_pi_gt_neg`: for negative `mₐ`,
which is the case every application needs, the term carrying `mₐ` must be bounded using
`(1 + 1/log xₐ)^6` rather than the truncation the paper reuses from the positive-coefficient terms.

The mathematics is `PrimeNumberTheoremAnd`'s `Ramanujan.criterion`; the vocabulary is this
repository's.

This conclusion **imports nothing** — every input arrives as a hypothesis — so this proof is its
whole justification, and it can be verified without waiting on any numerical input.
-/

open Real IEANTN DudekPlatt.v3

theorem DudekPlatt.v3.challenge_criterion : DudekPlatt.v3.criterion := by
  intro mₐ Mₐ xₐ x₀ hxₐ hlower hupper hx₀xₐ hcrit x hx
  simp only [mainTerm] at hlower hupper
  have hxexₐ : x > exp 1 * xₐ := lt_of_le_of_lt hx₀xₐ hx
  have hsq := DudekPlattSol.sq_pi_lt Mₐ (exp 1 * xₐ) hupper x hxexₐ
  have hlow := DudekPlattSol.ex_pi_gt mₐ xₐ hxₐ hlower x hxexₐ
  set U : ℝ := 1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 64 / log x ^ 6 +
    εUpper Mₐ x / log x ^ 7 with hU
  set L : ℝ := 1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
    εLower mₐ xₐ x / log x ^ 7 with hL
  have hx_gt_e : exp 1 < x := by
    have h1 : exp 1 < exp 1 * xₐ := by nlinarith [hxₐ, exp_pos (1 : ℝ)]
    exact lt_of_lt_of_le h1 (le_of_lt hxexₐ)
  have hlog_gt1 : 1 < log x := by
    simpa using log_lt_log (show (0 : ℝ) < exp 1 by positivity) hx_gt_e
  have hlog_pos : 0 < log x := by linarith
  have hnum_neg : εUpper Mₐ x - εLower mₐ xₐ x - log x < 0 := by linarith [hcrit x hx]
  have hden_pos : 0 < log x ^ 7 := by positivity
  have hlog_ne : log x ≠ 0 := ne_of_gt hlog_pos
  have hUL_eq : U - L = (εUpper Mₐ x - εLower mₐ xₐ x - log x) / log x ^ 7 := by
    rw [hU, hL]
    field_simp [hlog_ne]
    ring
  have hUL_neg : U - L < 0 := by
    rw [hUL_eq]; exact div_neg_of_neg_of_pos hnum_neg hden_pos
  have hU_lt_L : U < L := by linarith
  have hx_pos : 0 < x := lt_trans (exp_pos 1) hx_gt_e
  have hmul : x ^ 2 * U < x ^ 2 * L := by
    exact mul_lt_mul_of_pos_left hU_lt_L (by positivity)
  exact lt_trans hsq (lt_trans hmul hlow)
