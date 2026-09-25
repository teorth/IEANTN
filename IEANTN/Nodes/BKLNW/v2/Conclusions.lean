/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Nodes.BKLNWNumerics.v1.Tables

/-!
# Node `BKLNW.v2`

Pipeline form of Broadbent–Kadiri–Lumley–Ng–Wilk. `BKLNW.v1` keeps the paper's
four conclusions together. This version keeps the analytic Corollary 5.1 and
states the Table 8 tail bound as a consequence of the computation node
`BKLNWNumerics.v1`, so the table is an import rather than a second copy of the
data on this family.
-/

namespace BKLNW.v2

open IEANTN

/-- The auxiliary sum `f` of equation (2.4):
`f(x) = Σ_{k=3}^{⌊log x / log 2⌋} x^{1/k − 1/3}`. -/
noncomputable def f (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / (k : ℝ) - 1 / 3)

/-- The coefficient `a₂(b)` of equation (2.12), on the range where `α` is the explicit constant of
Corollary 2.1:
`a₂(b) = (1 + 1.93378·10⁻⁸) · max(f(e^b), f(2^{⌊b/log 2⌋+1}))`.

Displayed (2.12) is transcribed, not the stray `1.15177·10⁻⁸` in the proof. -/
noncomputable def a₂ (b : ℝ) : ℝ :=
  (1 + 1.93378e-8) * max (f (Real.exp b)) (f ((2 : ℝ) ^ (⌊b / Real.log 2⌋₊ + 1)))

/-- **Corollary 5.1**, on the range where its coefficients are explicit.

For `7 ≤ b ≤ 38 log 10` and every `x ≥ e^b`,
`ψ(x) − θ(x) < (1 + 1.93378·10⁻⁸) √x + a₂(b) x^{1/3}`. -/
def corollary_5_1 : Prop :=
  ∀ b : ℝ, 7 ≤ b → b ≤ 38 * Real.log 10 → ∀ x ≥ Real.exp b,
    Chebyshev.psi x - Chebyshev.theta x <
      (1 + 1.93378e-8) * x ^ ((1 : ℝ) / 2) + a₂ b * x ^ ((1 : ℝ) / 3)

/-- **Table 8 tail**, importing the consecutive-interval table from `BKLNWNumerics`.

For every entry `(b, ε)` of Table 8, `|ψ(x) − x| ≤ ε · x` for all `e^b ≤ x ≤ e^25000`.
This is `BKLNW.v1.table8_psi_bound_above`, now a pipeline step from the
consecutive-row claim plus that the tabulated `ε` decrease. -/
def table8_psi_bound_above : Prop :=
  ∀ p ∈ BKLNWNumerics.v1.table8, ∀ x : ℝ,
    Real.exp (p.1 : ℝ) ≤ x → x ≤ Real.exp 25000 → |Chebyshev.psi x - x| ≤ p.2 * x

end BKLNW.v2
