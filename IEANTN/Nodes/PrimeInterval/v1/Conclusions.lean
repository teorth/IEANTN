/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Vocabulary

/-!
# Node `PrimeInterval`

A **pipeline** node for issue #53: the shared argument by which a bound on the normalised error
term `Eθ` converts into a prime in a short interval. It imports nothing and consumes nothing that
is paper-specific, so a Lean proof is its whole justification — it is downstream-only, feeding on
whatever node states an `Eθ` bound (e.g. `FKS2`) rather than reproving one itself.

Source: `PrimeNumberTheoremAnd/IEANTN/PrimeInInterval.lean`, used as inspiration, not ported.
PNT+'s `HasPrimeInInterval` has the same proposition and endpoint convention. Specialising
`IEANTN.HasClassicalBound` to `IEANTN.Eθ` gives the same inequality shape as PNT+'s
`Eθ.classicalBound`; `Eθ` and `admissibleBound` use the same formulae and argument order. The
numerical-bound APIs differ: `IEANTN.HasNumericalBound` takes a constant `ε : ℝ`, whereas PNT+'s
`Eθ.numericalBound` takes `ε : ℝ → ℝ` and uses `ε x₀`.
-/

namespace PrimeInterval.v1

open Real

/-- The `θ` characterisation of a prime in a short interval: `(x, x + h]` contains a prime iff
Chebyshev's `θ` strictly increases across the interval.

This is what the other conclusions here are proved through: existence of a prime is not itself
analytic, but the jump in `θ` — a sum of `log p` over primes up to a point — is, and the two
statements coincide exactly. No hypothesis on `x` or `h` is needed: for `x < 0` or `h ≤ 0` both
sides are handled by `θ`'s definition on non-positive arguments and by `HasPrimeInInterval`'s own
strict inequality. -/
def theta_characterisation : Prop :=
  ∀ x h : ℝ, IEANTN.HasPrimeInInterval x h ↔ Chebyshev.theta (x + h) > Chebyshev.theta x

/-- The `Eθ` criterion: if the two endpoints' normalised errors are small enough relative to `h`,
there is a prime in `(x, x + h]`.

`Eθ x = |θ x - x| / x` is only well-behaved for `x > 0` (junk otherwise, since it divides by `x`),
so both `x` and `x + h` must be positive; `0 < h` is needed for `x + h > x` to be meaningful as an
interval at all. The bound `x * Eθ x + (x + h) * Eθ (x + h) < h` comes from writing
`θ x ≤ x + x * Eθ x` and `θ (x + h) ≥ (x + h) - (x + h) * Eθ (x + h)` and subtracting; see
`theta_characterisation`. -/
def eTheta_criterion : Prop :=
  ∀ x h : ℝ, 0 < x → 0 < h →
    x * IEANTN.Eθ x + (x + h) * IEANTN.Eθ (x + h) < h → IEANTN.HasPrimeInInterval x h

/-- The numerical-bound route: if `Eθ` is at most the constant `ε` throughout `[x₀, ∞)`,
`0 < h`, `x₀ ≤ x`, `0 < x` and `(2x + h) * ε < h`, there is a prime in `(x, x + h]`.

Immediate from `eTheta_criterion` once both `Eθ x` and `Eθ (x + h)` are bounded by the same `ε`,
which is exactly what `IEANTN.HasNumericalBound` gives once `x ≥ x₀`. Once `x` is at or beyond the
threshold where `admissibleBound` reaches its maximum and becomes antitone, the classical route
below freezes that bound at `x` to obtain this constant-bound hypothesis. -/
def numericalBound_hasPrimeInInterval : Prop :=
  ∀ x₀ x h ε : ℝ, IEANTN.HasNumericalBound IEANTN.Eθ ε x₀ → 0 < h → x₀ ≤ x → 0 < x →
    (2 * x + h) * ε < h → IEANTN.HasPrimeInInterval x h

/-- The classical-bound route, and the point of the node: `FKS2.v2.proposition_13` can produce
an `IEANTN.HasClassicalBound Eθ A B C R x₀`, and this consumes such a bound to certify a prime in a
short interval. This is the downstream composition the node is intended to expose.

The side conditions are load-bearing, not decoration. `x ≥ exp (R * (2 * B / C) ^ 2)` places `x`
at or beyond the maximum of `admissibleBound A B C R`; on that ray the bound is antitone because
its polynomial factor is overtaken by the exponential decay. Dropping the threshold makes the
conversion to a numerical bound at `x` invalid, not merely harder to prove. `0 < A, 0 < B, 0 < C,
0 < R` are the positivity hypotheses of that monotonicity argument; `0 < R` also keeps `log x / R`
positive once `x` is past the exponential threshold, so the `Real.rpow` bases are not negative. -/
def classicalBound_hasPrimeInInterval : Prop :=
  ∀ x₀ x h A B C R : ℝ,
    IEANTN.HasClassicalBound IEANTN.Eθ A B C R x₀ →
    0 < A → 0 < B → 0 < C → 0 < R → 0 < h → x₀ ≤ x → x ≥ Real.exp (R * (2 * B / C) ^ 2) →
    (2 * x + h) * IEANTN.admissibleBound A B C R x < h → IEANTN.HasPrimeInInterval x h

end PrimeInterval.v1
