/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.CotangentSeries.v1.Conclusions

/-!
# Examples: `CotangentSeries.v1`

The statement is a `HasSum`, so convergence is part of what a consumer receives. Both
`z ≠ 0` and `‖z‖ < 1` have to be supplied: dropping either from the declaration makes this
example fail to elaborate.
-/

namespace CotangentSeries.v1

example (h : cot_series_zeta_values) {z : ℂ} (hz : z ≠ 0) (hball : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ 2 * riemannZeta (2 * (n : ℂ) + 2) * z ^ (2 * n + 1))
      (1 / z - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)) :=
  h z hz hball

end CotangentSeries.v1
