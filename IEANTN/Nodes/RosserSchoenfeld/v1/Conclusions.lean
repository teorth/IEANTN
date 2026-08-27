/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary

/-!
# Node `RosserSchoenfeld.v1`

Rosser and Schoenfeld, *Sharper bounds for the Chebyshev functions `θ(x)` and `ψ(x)`*,
Math. Comp. **29** (1975), 243–269.

The classical source of explicit bounds on the Chebyshev functions, and the ancestor of every node
in this chain. Its Theorem 1 is the zero-free region that `Kadiri2005` starts from — "grâce au
résultat de Rosser, nous prenons tout d'abord `R = 9.645908801`" — and `FKBJ` cites the same
authors for `N(T)`.

## The shape is not `ClassicalZeroFreeRegion`, and that matters

Theorem 1 reads: there are no zeros of `ζ` in the region

`σ ≥ 1 − 1/(R log|t/17|)`,  `|t| ≥ 21`,  with `R = 9.645908801`.

Two differences from the network's usual shape. The denominator is `log|t/17|`, not `log|t|`, which
makes the region **wider**; and the threshold is `|t| ≥ 21`. Restating it directly as
`ClassicalZeroFreeRegion 9.645908801 3` would assert something on `3 ≤ t < 21` that the paper does
not prove.

So `zero_free_region` below is bespoke — this shape is used by this paper and nothing else — and
`zero_free_region_classical` is the ordinary form, obtained from it by a bridge rather than by
restating the paper. That is the honest way round: the paper's own claim is transcribed once, and
the weakening a consumer wants is a proof.

**The inequality is `≥`, not `>`.** An earlier note on this node said `>`, taken from extracted PDF
text; the rendered page shows `⩾`. The same extraction failure has now cost this project two wrong
transcriptions, and the rule that follows is in `docs/SOURCES.md`: read the source, or render the
page.

## What else to add

Whichever inequalities downstream nodes actually cite, one at a time. The paper contains a great
many. `FKBJ`'s Theorem 2.1 attributes an `N(T)` formula to Rosser, which is the next one with a
consumer waiting.
-/

namespace RosserSchoenfeld.v1

open IEANTN

/-- **Theorem 1, equation (1.27).** `ζ` has no zeroes with `Re s ≥ 1 − 1/(R log|Im s / 17|)` and
`Im s ≥ 21`, where `R = 9.645908801`.

Stated in the paper's own shape rather than the network's. The `log(t/17)` denominator is what
makes this region wider than the plain classical one, and the paper's introduction says so
explicitly — the result "improves Stechkin's Theorem 2 not only by having a smaller value for `R`
but also by the presence of the denominator 17".

Only positive `Im s` is quantified over, as elsewhere in the network; the paper's `|t| ≥ 21` form
follows by the symmetry of the zeroes about the real axis, which a consumer needing it must do. -/
def zero_free_region : Prop :=
  ∀ σ t : ℝ, 21 ≤ t → 1 - 1 / (9.645908801 * Real.log (t / 17)) ≤ σ →
    riemannZeta (σ + t * Complex.I) ≠ 0

/-- **Theorem 1, weakened to the network's usual shape**: the classical zero-free region holds with
`R = 9.645908801` above height `21`.

This is what `Kadiri2005` actually consumes — it uses `R` in the plain `1/(R log t)` form, at
heights past `3.3 · 10⁹`. It follows from `zero_free_region` because `log(t/17) ≤ log t`, so the
paper's region contains the plain one; the bridge in `IEANTN/Bridges/RosserSchoenfeld/` discharges
that, and it is why this conclusion is `bridged` rather than separately cited.

Note the threshold stays `21`, not `3`. Nothing here recovers the band `3 ≤ t < 21`. -/
def zero_free_region_classical : Prop :=
  ClassicalZeroFreeRegion 9.645908801 21

end RosserSchoenfeld.v1
