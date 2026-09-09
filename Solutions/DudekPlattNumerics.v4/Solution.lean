/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors (AI-assisted)
-/
import CalculusAssembly
import Numerics
import IEANTN.Nodes.DudekPlattNumerics.v4.Conclusions
import IEANTN.Nodes.MT.v2.Conclusions

/-!
# Solution: `DudekPlattNumerics.v4`

The two-sided `π(x)` estimate at Dudek and Platt's own footnote 1 parameters, derived from one
explicit literature premise, `MT.v2.corollary_1` (Mossinghoff–Trudgian's §7 Corollary 1), rather
than a Python-checked certificate.

This file composes two independently-developed pieces, both already checked in their own
worktrees and reported clean (`#print axioms` exactly `[propext, Classical.choice, Quot.sound]`,
no `sorry`):

* `CalculusAssembly.lean` (imported via `Numerics`'s sibling `CalculusAssembly`) — the native
  theta-to-pi partial-summation identity, the elementary early-range bound, and the whole-range
  integral majorants, culminating in `DudekPlattNumerics.Calculus.pi_two_sided_from_certificates`,
  which takes six scalar/pointwise hypotheses and produces the two-sided estimate.
* `Numerics.lean` — `f_R`'s monotonicity, the two endpoint certificates, and a connector
  (`hpoint_proof`, `htail_proof`, `hD_proof`, `hI7_proof`, `hA_proof`, `hlog2_proof`) that supplies
  exactly those six hypotheses from an explicit Mossinghoff–Trudgian-Corollary-1-shaped `θ`-error
  hypothesis, at `K := 3600` throughout.

All that is left is the one step neither worker's file does: converting the *graph* hypothesis
`MT.v2.corollary_1` (stated in the network's `HasClassicalBound`/`Eθ` vocabulary, with the `1/4`
and `1/2` exponents as `Real.rpow`) into the *literal nested-square-root* shape both workers'
files use. That conversion, and the final `simpa` reconciling `DudekPlattNumerics.v4.mainTerm`
with `DudekPlattNumerics.Calculus.S5` (the same sum, spelled independently in each file per this
network's "repeat rather than import a node-local definition" convention), is the whole of what
this file adds. -/

open Real IEANTN DudekPlattNumerics.Calculus

namespace DudekPlattNumericsV4Sol

/-- `y ^ (1/4 : ℝ) = √√y` for `y ≥ 0`: the network's `admissibleBound`'s `rpow` exponent, in the
nested-square-root shape `f_R` and the two workers' files use. -/
theorem rpow_quarter_eq_sqrt_sqrt {y : ℝ} (hy : 0 ≤ y) :
    y ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt y) := by
  rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num, Real.rpow_mul hy, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow]

/-- `MT.v2.corollary_1`, converted from the network's `HasClassicalBound`/`Eθ` vocabulary (with
`Real.rpow` exponents `1/4`, `1/2`) into the literal nested-square-root shape the numerics and
calculus workers' files both use as `hMT`. Pure algebra: no new mathematics. Stated directly with
`DudekPlattNumerics.v4.Numerics.C`/`.R` (rather than their unfolded values) so it is usable
verbatim as that file's `hMT` hypothesis. -/
theorem hMT_of_corollary_1 (h : MT.v2.corollary_1) :
    ∀ x : ℝ, 149 ≤ x → |Chebyshev.theta x - x| ≤
      x * DudekPlattNumerics.v4.Numerics.C *
        Real.sqrt (Real.sqrt (Real.log x / DudekPlattNumerics.v4.Numerics.R)) *
        Real.exp (-Real.sqrt (Real.log x / DudekPlattNumerics.v4.Numerics.R)) := by
  intro x hx
  have hb : Eθ x ≤ admissibleBound (Real.sqrt (8 / (17 * Real.pi))) (1 / 4 : ℝ) 1
      (1263 / 200 : ℝ) x := h x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : (0 : ℝ) ≤ Real.log x / (1263 / 200 : ℝ) := by
    have hlogx : 0 ≤ Real.log x := by
      have h149 : (1 : ℝ) ≤ 149 := by norm_num
      exact Real.log_nonneg (h149.trans hx)
    positivity
  have hrw : admissibleBound (Real.sqrt (8 / (17 * Real.pi))) (1 / 4 : ℝ) 1
      (1263 / 200 : ℝ) x =
      DudekPlattNumerics.v4.Numerics.C *
        Real.sqrt (Real.sqrt (Real.log x / DudekPlattNumerics.v4.Numerics.R)) *
        Real.exp (-Real.sqrt (Real.log x / DudekPlattNumerics.v4.Numerics.R)) := by
    show Real.sqrt (8 / (17 * Real.pi)) * (Real.log x / (1263 / 200)) ^ (1 / 4 : ℝ) *
        Real.exp (-1 * (Real.log x / (1263 / 200)) ^ ((1 : ℝ) / 2)) = _
    unfold DudekPlattNumerics.v4.Numerics.C DudekPlattNumerics.v4.Numerics.R
    rw [rpow_quarter_eq_sqrt_sqrt hy0, ← Real.sqrt_eq_rpow, neg_one_mul]
  rw [hrw] at hb
  have hEθ : Eθ x = |Chebyshev.theta x - x| / x := rfl
  rw [hEθ, div_le_iff₀ hx0] at hb
  linarith [hb]

end DudekPlattNumericsV4Sol

theorem DudekPlattNumerics.v4.challenge_pi_two_sided_footnote
    (mt_v2_corollary_1 : MT.v2.corollary_1) :
    DudekPlattNumerics.v4.pi_two_sided_footnote := by
  intro x hx
  have hMT := DudekPlattNumericsV4Sol.hMT_of_corollary_1 mt_v2_corollary_1
  have hL : (9400 : ℝ) ≤ Real.log x := by
    have := Real.log_lt_log (Real.exp_pos _) hx
    simpa only [Real.log_exp] using this.le
  have h := pi_two_sided_from_certificates
    DudekPlattNumerics.v4.Numerics.hlog2_proof hx (K := 3600) (by norm_num)
    (DudekPlattNumerics.v4.Numerics.hpoint_proof hMT hx)
    (DudekPlattNumerics.v4.Numerics.htail_proof hMT hx)
    (DudekPlattNumerics.v4.Numerics.hD_proof hL)
    (DudekPlattNumerics.v4.Numerics.hI7_proof hL)
    (DudekPlattNumerics.v4.Numerics.hA_proof hL)
  simpa only [DudekPlattNumerics.v4.mainTerm, S5, IEANTN.margin, pow_zero, one_mul] using h
