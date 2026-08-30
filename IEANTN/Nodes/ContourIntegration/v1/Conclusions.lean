/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Node `ContourIntegration.v1`

Textbook complex analysis that Mathlib happens not to have, stated once so that several nodes can
import it rather than each carrying its own copy.

This node belongs to no paper. It exists because `CH2.v4`'s contour shift needs the residue theorem
and there is nowhere in Mathlib to get it: as of the pin this node was written against,
`Mathlib/Analysis/Complex/` contains **no `residue`, no Cauchy theorem for cycles, and no homotopy
invariance of contour integrals**. What it does have is Cauchy on a rectangle
(`integral_boundary_rect_eq_zero_of_differentiableOn`) and invariance of a circle integral under a
change of radius across an annulus
(`circleIntegral_eq_of_differentiable_on_annulus_off_countable`, which holds for `f` itself and not
merely for `(z - c)⁻¹ • f`). The gap between those and the residue theorem is a rectangle with
finitely many holes, and that gap is what this node states.

Stating it here rather than inside `CH2.v4` is the point. It is not Chirre–Helfgott's mathematics,
it is not specific to their contour, and anything else in the network that shifts a contour past a
pole will want the same statement. It is also plausibly Mathlib material, in which case this node
becomes a place to record that it was wanted before it existed.

## Circle integrals rather than residues

There is no `residue` in Mathlib to state this with, and defining one here would mean choosing a
formulation — a limit, a Laurent coefficient, a contour integral — and committing every consumer to
it. So the statement uses `∮ ζ in C(ρ, r), f ζ` directly, which is `2πi` times the residue and
therefore removes the `2πi` from the identity as well.

The radius `r` is a parameter rather than existentially quantified, with the hypotheses forcing the
closed discs to be disjoint and to sit strictly inside the rectangle. That the value does not depend
on which such `r` is chosen is Mathlib's annulus invariance, so nothing is lost by fixing one; a
consumer that wants a different radius converts with that lemma rather than with a conclusion from
here.

## The shape of the left-hand side is Mathlib's, deliberately

The four-term boundary expression is copied from
`integral_boundary_rect_eq_zero_of_differentiableOn` — bottom, minus top, plus right, minus left —
so that a consumer holding a `DifferentiableOn` hypothesis can apply whichever of the two is
appropriate without reshaping anything. This conclusion is exactly that theorem with `= 0` replaced
by the sum over the singularities inside.
-/

namespace ContourIntegration.v1

open MeasureTheory intervalIntegral Complex

/-- **The residue theorem on a rectangle**, with residues written as circle integrals.

For `f` holomorphic on the closed rectangle with corners `z` and `w` except at the finitely many
points of `P`, the boundary integral equals the sum of the circle integrals of radius `r` about
those points.

The hypotheses on `r` say what they need to: each closed disc `C(ρ, r)` lies strictly inside the
rectangle, and any two of them are disjoint. Nothing here asserts that `P` is *all* of the
singularities — a consumer that omits one is supplying a false `DifferentiableOn` hypothesis rather
than obtaining a wrong conclusion, so the direction of that error is safe, but completeness of `P`
is the consumer's obligation.

Imports nothing: every input is universally quantified with its conditions as hypotheses.

**Junk-value note.** The boundary terms are `intervalIntegral`s and the circle integrals are
`circleIntegral`s, both of which are `0` on a non-integrable integrand. That cannot make this
statement vacuous, because holomorphy on the closed rectangle off `P` already forces continuity on
each boundary edge and on each circle, hence integrability there. It is the reason no separate
integrability hypothesis appears, and the reason one would have to be added if the holomorphy
hypothesis were ever weakened. -/
def residue_theorem_rectangle : Prop :=
  ∀ (z w : ℂ) (P : Finset ℂ) (r : ℝ) (f : ℂ → ℂ),
    z.re < w.re → z.im < w.im → 0 < r →
    (∀ ρ ∈ P, z.re < ρ.re - r ∧ ρ.re + r < w.re ∧ z.im < ρ.im - r ∧ ρ.im + r < w.im) →
    (∀ ρ ∈ P, ∀ σ ∈ P, ρ ≠ σ → 2 * r < dist ρ σ) →
    DifferentiableOn ℂ f ((Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) \ ↑P) →
      (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I))
        - (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I))
        + Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I))
        - Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))
        = ∑ ρ ∈ P, (∮ ζ in C(ρ, r), f ζ)

end ContourIntegration.v1
