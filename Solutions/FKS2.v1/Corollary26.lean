/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Corollary23

/-!
# Corollary 26: `|π(x) − Li(x)| ≤ 0.4298 x / log x`

## Two routes, and this file takes the cheap one

The paper's proof of `cor:weak` is numerical throughout: the 25 prime intervals below `97`, then
Büthe's Theorem 2 on `[97, 10¹⁹]`, then its own numerical proposition with Table 4 above `10¹⁹`.

`PrimeNumberTheoremAnd` instead derives it from Corollary 23, and so does this file, because we need
Corollary 23 anyway and the residual is then **entirely elementary — no numerical input at all**:

* above `e`, the Table 6 row-2 curve `0.826 √u e^{-u}` in `u = √(log x/R)` never exceeds `0.413`,
  by `e^{-u} ≤ 1/(1+u)` and `2√u ≤ 1+u`. Its true supremum is `0.3543`, at `u = 1/2`;
* below `e`, `π(x) = 1` and `0 ≤ Li(x) ≤ 2`, so `|π − Li| ≤ 1`, and `log x/x ≤ 1/e` gives
  `Eπ(x) ≤ 1/e ≈ 0.3679`.

Both are in `Corollary22.lean` as `admissibleBound_row2_le` and `Epi_le_on_two_e`.

So this conclusion needs no `FKS2Numerics` claim of its own. Its imports are exactly Corollary 23's,
which is a change from what the node recorded: those were `Buthe`'s two conclusions, following the
paper's route rather than this one.
-/

namespace FKS2Sol

open Real IEANTN

/-- **Corollary 26**, the paper's headline numerical bound: `Eπ(x) ≤ 0.4298` for all `x ≥ 2`.

Split at `e`, and neither half needs a numerical input — the whole of the arithmetic is
`0.413 ≤ 0.4298` and `1/e ≤ 0.4298`. -/
theorem corollary_26
    (hpsi : FKS.v1.psi_classical_bound)
    (hbuthe : Buthe.v1.theorem_2_li_minus_pi)
    (hfloor : FKS2Numerics.v1.table6_row2_floor) :
    FKS2.v1.corollary_26 := by
  have h23 := corollary_23 hpsi hbuthe hfloor
  intro x hx
  by_cases hle : Real.exp 1 ≤ x
  · have h1e : (1 : ℝ) < Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact le_trans (h23 x hle) (admissibleBound_row2_le (lt_of_lt_of_le h1e hle))
  · exact Epi_le_on_two_e hx (lt_of_not_ge hle)

end FKS2Sol
