/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Nodes.BKLNW.v1.Conclusions

/-!
# Node `FKS2Numerics.v1`

The finite numerical checks that `FKS2`'s corollaries rest on, separated from the analysis that
consumes them.

Same paper as `FKS2.v1` — Fiori, Kadiri and Swidinsky, *Sharper bounds for the error term in the
Prime Number Theorem* — but a different **kind** of claim, and that is the whole point of the
split. `FKS2.v1` carries analysis, justified by the paper's argument. This carries arithmetic on
bounded ranges, justified by a computation. Keeping them apart lets a consumer see which part of
its trust is analytic and which is a finite check somebody ran.

## Why this is its own node

Three reasons, in increasing order of how much they matter.

The evidence differs. A `numerical` justification records the outcome of a computation; a
`literature` one records an argument a referee read. Mixing them on one node makes the weaker of
the two invisible.

The `sorry`s go somewhere. `PrimeNumberTheoremAnd` threads these data through its FKS2 development
as deliberate holes — its own docstring notes that `#print axioms corollary_23_all` reports
`sorryAx` on their account. It has no choice: there is no import mechanism there. Here they become
**hypotheses**, so `FKS2.v1`'s solution can be free of `sorryAx` while resting on exactly the same
computations, stated where a reader can find them.

And it is what a pipelined `FKS2.v2` will need. A pipeline abstracts over the numerical input
rather than baking one paper's table into the argument; that is only possible if the input is a
separate importable claim to begin with.

## What is here, and what is not

Only what a stated `FKS2.v1` conclusion actually consumes. `FKS2.v1.corollary_23` states the
`[0.826, 0.25, 1.00, 1.000]` row of the paper's Table 6, which is its **row 2**, and the finite
check that row needs is the one below.

The paper's other Table 6 rows have their own floors, on their own windows, and its Table 7 has
another eleven; upstream states ten and twenty-five of them respectively. None is stated here,
because no conclusion in this network consumes one yet. Add them when something does — the shape
below is the pattern.

The two claims after it were added exactly that way. Proving `FKS2.v1.corollary_14` in Lean showed
that it rests on two finite checks nobody had recorded: the size of Proposition 13's multiplier at
`x₀ = e³⁰`, and the fact that the asymptotic bound stays above `1` below `e³⁰`. Neither was an
obstacle — they were previously invisible dependencies of a conclusion this network already
carried, and the port is what made them visible.

## One of these is not like the others

`table6_row2_floor` is arithmetic on a finite set: `π(x)` is a prime count. `nu_asymp_e30_le` is
likewise a closed-form real number compared against a constant.

`theta_asymp_ge_one_below_e30` is different in kind: it quantifies over a continuum, and it is
provable outright — `ε_θ,asymp(x) = A u³ e^{-2u}` in `u = √(log x / R)`, which rises to a maximum
at `u = 3/2` and so attains its minimum on `[2, e³⁰]` at an endpoint. Only the endpoint evaluation
is genuinely numerical. It sits here because that is where the paper puts it and because the
evaluation is still a computation, but it is the first candidate to be promoted to a proved
conclusion, and a reader should not mistake it for an irreducible finite check.
-/

namespace FKS2Numerics.v1

open IEANTN

/-- **Table 6, row 2: the small-`x` floor.**
`Eπ(x) ≤ 0.826 (log x / R)^{1/4} exp(−(log x / R)^{1/2})` for every `x` in `[e, e⁶]`, with
`R = 5.5666305`.

That window is `x ∈ [2.72, 403]`, where the paper "checks directly for particularly small `x`":
`π(x)` is an exact prime count and `Li(x) = ∫₂ˣ dt / log t` a certified quadrature, so the claim is
bounded arithmetic with no analytic content. It is what pins the `x₀ = e` threshold of
`FKS2.v1.corollary_23`; above the window the asymptotic bound carries the argument on its own.

Stated on `Set.Icc`, a closed window, matching upstream. Note this is a *floor* — a claim about
small `x` — not a tail bound, so it does not compose with anything above `e⁶` by monotonicity and
a consumer must not assume it does. -/
def table6_row2_floor : Prop :=
  ∀ x ∈ Set.Icc (Real.exp 1) (Real.exp 6),
    Eπ x ≤ admissibleBound 0.826 0.25 1 5.5666305 x

/-- Proposition 13's multiplier `ν_asymp` at `x₀ = e³⁰`, with the parameters `FKS2`'s Corollary 14
uses: `Aψ = 121.096`, `B = 3/2`, `C = 2`, `R = 5.5666305`, and the `ψ − θ` comparison coefficients
`a₁ = 1 + 1.93378·10⁻⁸` and `a₂ = a₂(30)` of `BKLNW`'s Corollary 5.1.

Written out rather than referring to the conversion formula, because a conclusion may not depend on
anything in a solution. `log(e³⁰) = 30` has been substituted, which is why no logarithm appears.

Note this is a *number*, not a claim: `BKLNW.v1.a₂` is a definition, so nothing here rests on
`BKLNW`'s corollary being true. -/
noncomputable def nuAsympE30 : ℝ :=
  (1 / 121.096) * (5.5666305 / 30) ^ ((3 : ℝ) / 2) *
      Real.exp (2 * Real.sqrt (30 / 5.5666305)) *
    ((1 + 1.93378e-8) * 30 * Real.exp 30 ^ (-(1 : ℝ) / 2)
      + BKLNW.v1.a₂ 30 * 30 * Real.exp 30 ^ (-(2 : ℝ) / 3))

/-- **The multiplier bound behind Corollary 14**: `ν_asymp(e³⁰) ≤ 6.3376·10⁻⁷`.

This is the paper's own displayed estimate, and it is what moves `A` from `121.096` to `121.0961`
and no further: `121.096 · (1 + 6.3376·10⁻⁷) < 121.0961`.

Evaluating it means evaluating `BKLNW.v1.a₂ 30`, hence `f(e³⁰)` and `f(2⁴⁴)` — sums of about forty
`rpow` terms each. A computation, not an argument. -/
def nu_asymp_e30_le : Prop :=
  nuAsympE30 ≤ 6.3376e-7

/-- **The small-range floor behind Corollary 14**: the asymptotic bound for `Eθ` is at least `1`
throughout `[2, e³⁰]`.

This is what lets `BKLNW`'s `Eθ(x) ≤ 1` cover the range below `e³⁰`, where Proposition 13 has
nothing to say because `FKS`'s bound starts at `e³⁰`. The paper records the minimum as about
`2.6271`, attained at `x = 2`, so the margin is wide.

See the module docstring: unlike the other two, this one is provable outright with more work. -/
def theta_asymp_ge_one_below_e30 : Prop :=
  ∀ x ∈ Set.Icc (2 : ℝ) (Real.exp 30),
    1 ≤ admissibleBound 121.0961 (3 / 2) 2 5.5666305 x

/-- **The mid-range behind Corollary 22**: the headline bound already holds on `[2, e²⁰⁰⁰⁰]`.

Above `e²⁰⁰⁰⁰` Corollary 22 is analysis — Theorem 3 applied to Corollary 14, with the multiplier
controlled by the Dawson estimate. Below it the paper proceeds differently: "the numerical results
obtainable from Theorem [prop_num_pi] may be interpolated as a step function to give a bound on
`E_π(x)` of the shape `ε_{π,asymp}(x)`", using the subdivisions of FKS's Lemmas 5.2 and 5.3. That
interpolation is a computation over a table, not an argument, so it is stated here.

`PrimeNumberTheoremAnd` does not have this either — it formalizes only the tail
(`corollary_22_tail`, from `exp 20000` onward). So this is the genuinely missing piece, in both
developments. -/
def corollary_22_mid_range : Prop :=
  ∀ x ∈ Set.Icc (2 : ℝ) (Real.exp 20000),
    Eπ x ≤ admissibleBound 9.2211 (3 / 2) 0.84768363 1 x

end FKS2Numerics.v1
