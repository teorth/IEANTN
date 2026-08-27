/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary

/-!
# Node `Brown1967.v1`

J. L. Brown, Jr., *On the error in reconstructing a non-bandlimited function by means of the
bandpass sampling theorem*, J. Math. Anal. Appl. **18** (1967), 75–84.

The aliasing bound `Platt2017` uses as its Theorem 4.4, to control the error from sampling the
completed zeta function on a lattice rather than reconstructing it exactly.

## Who proved what, which took some untangling

`Platt2017`'s Theorem 4.4 is attributed to "Weiss" and proved by "See for example [7]", [7] being
this paper. That phrasing is exact, and the situation behind it is worth recording.

* **Brown's §2 is titled "Weiss's theorem"**, and on p. 76 he writes "Weiss in [4] has shown that"
  followed by his equation (5): `|f(t) − Σ f(n/2W) g(t − n/2W)| ≤ (2/π) ∫_{2πW}^{∞} |F(ω)| dω`,
  under four hypotheses — absolute integrability, `F(ω) = F*(−ω)`, bounded variation, and the
  jump-discontinuity midpoint convention. **That is precisely `Platt2017`'s Theorem 4.4.** The
  hypotheses correspond one for one — Brown's `F(ω) = F*(−ω)` is exactly "`f` is real-valued" — and
  the constants agree once the Fourier convention is converted: Brown works in angular frequency
  with `f(t) = (1/2π) ∫ F(ω) e^{iωt} dω`, so `(2/π) ∫_{2πW}^{∞}` becomes Platt's `4 ∫_B^{∞}`.
* **Brown's [4] is an abstract.** P. Weiss, *An estimate of the error arising from misapplication
  of the sampling theorem*, Amer. Math. Soc. Notices **10** (1963), 351, Abstract No. 601-54. One
  page in the Notices, with no proof. So there is no published Weiss proof to cite, which is why
  Platt says "see for example" rather than naming an origin.
* **Brown's own Theorem 1 is strictly stronger**, and is proved here: assuming only
  `∫ |F(ω)| dω < ∞` — dropping bounded variation, the jump convention and realness — he obtains
  `|f(t) − Σ f(n/2W) g(t − n/2W)| ≤ (1/π) ∫_{|ω| > 2πW} |F(ω)| dω`, and shows the constant cannot
  be reduced. For real `f` the two bounds coincide, since `|F|` is then even.

So this is not folklore: the result a consumer should want is Brown's Theorem 1, which is refereed,
proved, and stronger than the form `Platt2017` uses.

## Why this node states nothing yet

Not for want of a source. Two obstacles, and the second is the interesting one.

1. Stating it needs Fourier-transform vocabulary that nothing else in this network uses. Mathlib
   has `Real.sinc`; the transform side would have to be written out as
   `f t = (1/(2π)) ∫ ω, F ω * exp (I t ω)` or assembled from Mathlib's API.
2. **The sum is a symmetric limit, not a `tsum`.** Brown's Lemma 3 proves uniform convergence of
   the partial sums `Σ_{−N}^{N}`, and nothing here gives unconditional summability over `ℤ`.
   Writing `∑' n : ℤ` would therefore assert something Brown does not prove, and — because `tsum`
   of a non-summable family is `0` — would silently become a *different and probably false* claim
   rather than a vacuous one. The right encoding is a `Filter.Tendsto` over `Finset.Icc (-N) N`.

Whoever states it should state **Theorem 1**, in that form, and may then note that Platt's
Theorem 4.4 follows for real `f`.
-/
