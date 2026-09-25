/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Mathlib.Data.Real.Basic

/-!
# Tables: `Buthe2016.v1`

Data from Büthe, *Estimating π(x) and related functions under partial RH assumptions*,
Math. Comp. **85** (2016), 2483–2498. Data only — what is claimed *about* it is in
`Conclusions.lean`.

These are the tabulated outputs of the paper's **Theorem 1**: for each row, `δ₀` is an upper bound
for `e^{αε}(ℰ₁ + ℰ₂ + ℰ₃)` at the printed parameters, and the theorem then gives
`|ψ(x) − x| ≤ δ₀ x` for all `x ≥ e^{αε} x₀`, assuming the Riemann hypothesis up to the printed
height `T` (with `ε = c/T`).

The general statement of Theorem 1 is parameterised by the Logan kernel and Bessel ratios, which
are not yet Vocabulary. The tables are the part a consumer can cite without that machinery, and
they are the "explicit bound of a different shape from Theorem 2" that the node had recorded as
unstated.
-/

namespace Buthe2016.v1

/-- **Table 1**: bounds under a verification to height at most `3.061 × 10¹⁰`.

Each triple is `(b, T, δ₀)` where the bound is claimed for `x ≥ e^b` if the Riemann hypothesis
holds up to height `T`. Extracted from the typeset table on arXiv:1410.7015. -/
def table1 : List (ℕ × ℝ × ℝ) :=
  [
    (45, 3.5e9, 1.11742e-8),
    (50, 3.061e10, 1.16465e-9),
    (55, 3.061e10, 2.88434e-10),
    (60, 3.061e10, 2.08162e-10),
    (65, 3.061e10, 1.96865e-10),
    (70, 3.061e10, 1.91910e-10),
    (80, 3.061e10, 1.84848e-10),
    (90, 3.061e10, 1.79330e-10),
    (100, 3.061e10, 1.75185e-10),
    (500, 3.061e10, 1.47067e-10),
    (1000, 3.061e10, 1.43770e-10),
    (3000, 3.061e10, 1.41594e-10)
  ]

/-- **Table 2**: bounds under a verification to height at most `2.445 × 10¹²`.

Same shape as `table1`. The paper attributes this height to Gourdon (2004); the network has no
node for that computation yet, so a consumer must supply the verification as a hypothesis. -/
def table2 : List (ℕ × ℝ × ℝ) :=
  [
    (55, 8.5e11, 1.12494e-10),
    (60, 2.445e12, 1.22147e-11),
    (65, 2.445e12, 3.57125e-12),
    (70, 2.445e12, 2.79233e-12),
    (75, 2.445e12, 2.70358e-12),
    (80, 2.445e12, 2.61079e-12),
    (90, 2.445e12, 2.52129e-12),
    (100, 2.445e12, 2.45229e-12),
    (500, 2.445e12, 1.99986e-12),
    (1000, 2.445e12, 1.94751e-12),
    (2000, 2.445e12, 1.92155e-12),
    (3000, 2.445e12, 1.91298e-12),
    (4000, 2.445e12, 1.90866e-12)
  ]

end Buthe2016.v1
