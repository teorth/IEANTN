/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import IEANTN.Vocabulary.Numerics

/-!
# Node `ZetaLogDerivValues.v1`

**Numerical values of `ζ'/ζ` at a few real points, and the sign pattern of its Laurent coefficients
at `1`.**

Mathlib has `ζ'/ζ` and its Dirichlet series but not a single numerical value of either, and every
explicit contour argument needs some. Section 8 of Chirre–Helfgott alone reaches for four —
`ζ'/ζ(2)`, `ζ'/ζ(3/2)`, `ζ'/ζ(-1)` and `(ζ'/ζ)'(-1)` — in five separate places, together with one
structural fact of the same character: that the Laurent coefficients of `-ζ'/ζ` at `1` alternate in
sign.

## Why a node, and why this node

None of these is specific to a paper. Each value is a sum over `Λ(n) n^{-t}` or a coefficient of a
fixed Laurent expansion, and any explicit estimate that shifts a contour past `s = 1` or past the
trivial zeroes will want them. What makes them a *node* rather than solution lemmas is that Lean
cannot supply them from Mathlib at all: they are computations, and the computation is their
justification.

They are **not** on `ZetaLogDeriv.v1`, which states the functional equation and is verified.
Verification is all-or-nothing per node, so adding a conclusion there would invalidate a receipt
that has nothing to do with these values.

## What is deliberately absent

**The monotonicity `|ζ'/ζ(t)| ≤ |ζ'/ζ(2)|` for real `t ≥ 2` is not here**, and should not be. It
follows from Mathlib's `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` together with
`ArithmeticFunction.vonMangoldt_nonneg` and `LSeries.norm_term_le_of_re_le_re`, so it is ordinary
Lean work for whichever solution wants it. Only the *value* at the base point has to be imported.

Absent for the same reason: values of `ζ` itself, of `ζ'` alone, and the Stieltjes constants. Those
are different computations and belong wherever they are needed.

## The form of the numerical statements

Each value is stated as **a real number within a tolerance of a stated central value, equal to the
quantity** — `∃ c : ℝ, |c - v| ≤ margin 0 * 10⁻⁶ ∧ ζ'/ζ(p) = c` — rather than as a bound on `‖·‖`
or on `.re`.

Two reasons. Consumers need the sign as well as the size: `ζ'/ζ(-1)` is positive while the other
three are negative, and `lem:arles` and `lem:moruno` both use signs. And the existential carries
*"this quantity is real"* with it, which a norm bound does not.

**The tolerance form is what makes the `margin` site behave.** A two-sided bracket `A ≤ c ≤ B` would
need the margin applied in opposite ways on the two sides depending on the signs of `A` and `B`,
since raising a margin must always *widen*. `|c - v| ≤ margin n * ε` widens whatever the sign of
`v`, which is the property the site exists to have. See `IEANTN.margin`; at `n = 0` the factor is
`1`, so these say exactly what the computation says.

`10⁻⁶` is far wider than the computation's accuracy — every one of the four values is within
`4 × 10⁻⁷` of the stated centre — and far tighter than any known consumer needs.
-/

namespace ZetaLogDerivValues.v1

open IEANTN

/-- **`ζ'/ζ(2) = -0.5699609931…`.**

The base point for bounding `ζ'/ζ` on `[2, ∞)`: since `-ζ'/ζ(t) = ∑ Λ(n) n^{-t}` has non-negative
terms, `|ζ'/ζ(t)| ≤ |ζ'/ζ(2)|` for every real `t ≥ 2`. That reduction is Lean work rather than a
node fact; only this value has to be imported.

Carries a `margin 0` site — see `IEANTN.margin`.

Imports nothing: a bare numerical claim about a Mathlib constant. -/
noncomputable def logDeriv_two : Prop :=
  ∃ c : ℝ, |c - (-0.569961)| ≤ margin 0 * 1e-6 ∧
    deriv riemannZeta 2 / riemannZeta 2 = (c : ℂ)

/-- **`ζ'/ζ(3/2) = -1.5052353558…`.**

Chirre–Helfgott's `lem:adioso` carries `|ζ'/ζ(1+σ₀)|` for a free `σ₀ > 0` and `lem:hardin` uses it
at `σ₀ = 1/2`; `prop:titch96A` uses the same value as its `σ₊ = 3/2` term.

Carries a `margin 0` site. -/
noncomputable def logDeriv_three_halves : Prop :=
  ∃ c : ℝ, |c - (-1.505235)| ≤ margin 0 * 1e-6 ∧
    deriv riemannZeta (3 / 2) / riemannZeta (3 / 2) = (c : ℂ)

/-- **`ζ'/ζ(-1) = 1.9850537244…`**, the one positive value of the four.

`ζ(-1) = -1/12 ≠ 0`, so `ζ'/ζ` is analytic here and this is not a junk value. With
`deriv_logDeriv_neg_one` it fixes the constant `c = ζ'/ζ(-1) - 2(ζ'/ζ)'(-1) = 3.861024…` of
Chirre–Helfgott's `lem:arles`; on its own it fixes `Ã(-1) = -ζ'/ζ(-1) + 1/2 = -1.485053…`, the
constant `lem:moruno` bounds its integral by.

Carries a `margin 0` site. -/
noncomputable def logDeriv_neg_one : Prop :=
  ∃ c : ℝ, |c - 1.985054| ≤ margin 0 * 1e-6 ∧
    deriv riemannZeta (-1) / riemannZeta (-1) = (c : ℂ)

/-- **`(ζ'/ζ)'(-1) = -0.9379851995…`.**

The derivative *of the logarithmic derivative*, not of `ζ`. The quotient sits inside the outer
`deriv` so that there is no room to read it the other way — that is the transcription error this
statement is most exposed to.

Carries a `margin 0` site. -/
noncomputable def deriv_logDeriv_neg_one : Prop :=
  ∃ c : ℝ, |c - (-0.937985)| ≤ margin 0 * 1e-6 ∧
    deriv (fun s : ℂ ↦ deriv riemannZeta s / riemannZeta s) (-1) = (c : ℂ)

/-- **The Laurent coefficients of `-ζ'/ζ` at `1` alternate in sign.**

`-ζ'/ζ(s) = 1/(s-1) + ∑_{n≥0} (-1)^{n+1} aₙ (s-1)ⁿ` with every `aₙ > 0`. In particular `a₀ = γ`,
Euler's constant, since `-ζ'/ζ(s) - 1/(s-1) → -γ` as `s → 1`.

**The radius `3` is forced, not a convenience.** `-ζ'/ζ(s) - 1/(s-1)` is analytic on the open disc
`‖s-1‖ < 3`: the nearest non-trivial zero of `ζ` is at distance `14.13…`, so the binding constraint
is the trivial zero at `s = -2`, exactly `3` away, sitting on the boundary. The coefficients decay
like `3^{-(n+1)}`, which is that pole showing through.

`s ≠ 1` is a junk-value guard, not a restriction on the mathematics: the left-hand side extends
analytically to `1`, but `1/(s-1)` does not, and in Lean `1/0 = 0` would silently turn the claim at
`s = 1` into a different one.

Stated as a `HasSum` rather than an equation between `tsum`s, so convergence is part of the claim:
a `tsum` of a non-summable family is `0`, and an equation between two of those can hold vacuously.

**No `margin` site**: nothing here is a rounded numeral. The claim is a sign pattern, and a
multiplicative factor could not weaken it.

This is `lem:kalmynin` of Chirre–Helfgott, attributed there to A. Kalmynin. Its proof is an
interval-arithmetic computation — the maximum modulus principle applied to `|G| ≤ 1.396` over a box,
verified by bisection in Arb, with the first five coefficients computed separately — so it is a node
fact of the same kind as the values above rather than something a solution could derive. -/
def logDeriv_laurent_alternating : Prop :=
  ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
    ∀ s : ℂ, s ≠ 1 → ‖s - 1‖ < 3 →
      HasSum (fun n : ℕ ↦ (-1 : ℂ) ^ (n + 1) * (a n : ℂ) * (s - 1) ^ n)
        (-(deriv riemannZeta s / riemannZeta s) - 1 / (s - 1))

end ZetaLogDerivValues.v1
