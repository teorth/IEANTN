/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary

/-!
# Node `MTY.v1`

Mossinghoff, Trudgian and Yang, *Explicit zero-free regions for the Riemann zeta-function*,
arXiv:2212.06867. Read from `Zerofree_MTY_v10_arXiv_TTsub.tex` in that source bundle.

Three explicit regions are stated, each as printed. Theorem Main2 (`48.1588`, "for sufficiently
large `|t|`") is not stated: the preprint gives no threshold, and inventing one would change the
claim. Only positive `t` is quantified, matching `ClassicalZeroFreeRegion`.
-/

namespace MTY.v1

open IEANTN

/-- **Theorem thmClassical.** No zeros of `ζ(σ + it)` for `|t| ≥ 2` and
`σ ≥ 1 - 1/(5.558691 log |t|)`.

The classical shape, so a consumer of `Kadiri2005.v1.zero_free_region` can be pointed here by a
bridge. Smaller `R` is stronger: `5.558691` improves Mossinghoff–Trudgian's `5.573412`. -/
def classical_zero_free_region : Prop :=
  ClassicalZeroFreeRegion 5.558691 2

/-- **Theorem Main.** No zeros of `ζ(σ + it)` for `|t| ≥ 3` and
`σ ≥ 1 - 1/(55.241 (log |t|)^{2/3} (log log |t|)^{1/3})`.

The preprint's closed inequality (`σ ≥`) is kept. `log log t` is only asked for `t ≥ 3`, where
`log t > 1`. -/
def korobov_vinogradov_region : Prop :=
  ∀ σ t : ℝ, 3 ≤ t →
    1 - 1 / (55.241 * (Real.log t) ^ ((2 : ℝ) / 3) * (Real.log (Real.log t)) ^ ((1 : ℝ) / 3)) ≤ σ →
    riemannZeta (σ + t * Complex.I) ≠ 0

/-- Height function in the intermediate region: `h(t) = (27/164) log |t| + 7.096`. -/
noncomputable def intermediateHeight (t : ℝ) : ℝ :=
  (27 / 164) * Real.log t + 7.096

/-- **Theorem thmIntZFR.** No zeros for `|t| ≥ exp(1000)` and
`σ > 1 - 0.05035 / h(t) + 0.0349 / h(t)²`, with `h` as above.

The preprint's inequality is strict (`σ >`). Stating `≥` would claim a boundary the theorem does
not give. -/
def intermediate_zero_free_region : Prop :=
  ∀ σ t : ℝ, Real.exp 1000 ≤ t →
    1 - 0.05035 / intermediateHeight t + 0.0349 / intermediateHeight t ^ 2 < σ →
    riemannZeta (σ + t * Complex.I) ≠ 0

end MTY.v1
