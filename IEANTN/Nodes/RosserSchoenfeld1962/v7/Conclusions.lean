/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import IEANTN.Vocabulary.PrimeCounting

/-! # Rosser–Schoenfeld 1962: Corollary 3, equation (3.9) -/

namespace RosserSchoenfeld1962.v7

/-- **Corollary 3, equation (3.9), p. 69.** For every real `x > 1`,
`0 < π(2x) - π(x) < 7x / (5 log x)`. The count includes the right endpoint.
This is the complete two-sided inequality; both inequalities are strict. -/
def equation_3_9 : Prop :=
  ∀ x : ℝ, 1 < x →
    0 < IEANTN.primeCounting (2 * x) - IEANTN.primeCounting x ∧
      IEANTN.primeCounting (2 * x) - IEANTN.primeCounting x < 7 * x / (5 * Real.log x)

end RosserSchoenfeld1962.v7
