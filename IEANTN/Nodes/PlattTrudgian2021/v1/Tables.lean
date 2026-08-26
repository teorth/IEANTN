/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Tables: `PlattTrudgian2021.v1`

Data from Platt and Trudgian, *The error term in the prime number theorem*,
Math. Comp. **90** (2021), no. 328, 871–881. Data only — what is claimed *about* it is in
`Conclusions.lean`.

Extracted from the typeset table rather than retyped.
-/

namespace PlattTrudgian2021.v1

/-- **Table 1**: rows `(X, A, B, C, ε₀)` of the paper's Theorem 1.

The printed table has six columns, `X σ A B C ε₀`. The `σ` column is omitted here: Theorem 1 says
"for each row `{X, A, B, C, ϵ₀}` from Table 1", so `σ` is not part of what is claimed — it is the
zero-density abscissa the authors optimised over to produce the row, and it takes the values `0.98`
for `X ≤ 4000` and `0.99` above. Recording it would suggest the statement depends on it.

Cross-checked against `FKS`, whose abstract says "for all `x ≥ exp(3 000)`,
`|ψ(x) − x| < 4.9678 · 10⁻¹⁵ x`. This compares to results of Platt and Trudgian (2021) who obtained
`4.51 · 10⁻¹³`" — which is exactly this table's `X = 3000` row. -/
def table1 : List (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  [
    (1000, 461.9, 1.52, 1.89, 1.20e-5),
    (2000, 411.4, 1.52, 1.89, 8.35e-10),
    (3000, 379.6, 1.52, 1.89, 4.51e-13),
    (4000, 356.3, 1.52, 1.89, 7.33e-16),
    (5000, 713.0, 1.51, 1.94, 9.77e-19),
    (6000, 611.6, 1.51, 1.94, 4.23e-21),
    (7000, 590.1, 1.51, 1.94, 3.09e-23),
    (8000, 570.5, 1.51, 1.94, 3.12e-25),
    (9000, 552.3, 1.51, 1.94, 4.11e-27),
    (10000, 535.4, 1.51, 1.94, 6.78e-29),
  ]

end PlattTrudgian2021.v1
