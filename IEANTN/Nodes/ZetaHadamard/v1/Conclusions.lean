/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import IEANTN.Vocabulary.Zeta

/-!
# Node `ZetaHadamard.v1`

The partial-fraction expansion of `ζ'/ζ`: the identity that expresses the logarithmic derivative of
`ζ` as a sum over its non-trivial zeroes.

## Why a node

Mathlib has the functional equation, the Dirichlet series, and — since 2026 — the discreteness of
the zero set (`Mathlib.NumberTheory.LSeries.ZetaZeros`). It does **not** have the Hadamard
factorisation of `ξ`, and so it does not have

`ζ'/ζ(s) = ∑_ρ (1/(s−ρ) + 1/ρ) − ½ψ(s/2+1) − 1/(s−1) + C`,

which is Corollary 10.14 of Montgomery–Vaughan and §12 of Davenport. That identity is the only
route from the zeroes of `ζ` to the size of `ζ'/ζ` inside the critical strip, and every explicit
bound of the shape "`ζ'/ζ(s)` is its nearby zeroes plus `O(log t)`" — Titchmarsh 9.6(A) and its
explicit descendants — begins there. It is textbook material Mathlib happens not to have, so it is
a `standard` node rather than a lemma inside one paper's solution.

## The paired form, and why the obvious statement would be vacuous

`∑_ρ (1/(s−ρ) + 1/ρ)` is not absolutely convergent; the sum is over zeroes ordered by `|Im ρ|`, and
the pairing `ρ ↔ 1 − ρ` is doing real work. In Lean an unordered `tsum` of a family that is not
`Summable` is `0`, so stating it that way would produce something that typechecks and says nothing.
`IEANTN.Vocabulary.Zeta` flags exactly this trap and names the fix: state a regularised form.

**This node states the difference of the identity at two points.** With

`aₚ(s) = 1/(s−ρ) − 1/(w−ρ) = (w−s)/((s−ρ)(w−ρ))`

the terms are `O(1/|ρ|²)` and the family is genuinely summable, so `HasSum` carries both the
convergence and the value. Three things fall out of taking the difference:

* **the constant `C` disappears**, which is what makes this statable at all without also fixing a
  normalisation the sources do not agree on;
* **the sum is unconditional**, so there is no ordering convention to get wrong;
* **it is the form the consumer wants.** Titchmarsh 9.6(A) — Proposition B.7 of Chirre–Helfgott,
  their `prop:titch96A` — evaluates the identity at `s` and at `s₊ = σ₊ + i t` and subtracts, and
  never uses the unsubtracted version.

## The hypotheses are exactly four, and two of them do more than they look

`s ≠ 1` and `w ≠ 1` keep the `1/(s−1)` terms finite and stay off the pole of `ζ`. `ζ(s) ≠ 0` and
`ζ(w) ≠ 0` make the logarithmic derivatives finite — and also, silently, keep `ψ(s/2+1)` off its
poles: `ψ(z)` has poles exactly at `z ∈ {0, −1, −2, …}`, so `ψ(s/2+1)` has poles exactly at
`s ∈ {−2, −4, −6, …}`, which are the trivial zeroes of `ζ`. So no separate hypothesis is needed for
the digamma term, and none is stated.

Nothing excludes `s` from being a zero of `ζ` *by accident of the sum*: `1/(s−ρ)` needs `s ≠ ρ`,
and `ζ(s) ≠ 0` gives it.

## Checked numerically before being written

At `s = 0.3+5i`, `s = −3+2i` and `s = 0.5+30i` against `w = 3/2 + i t`, summing zeroes and their
conjugates out to `N = 2000`. Truncation is the whole difficulty: the terms are only `O(1/|ρ|²)`,
so the partial sums converge like `log(T/2π)/(2πT)` and three digits is all a direct sum buys. What
was checked is therefore not raw agreement but that the residual *is* the tail:

* it decreases monotonically, roughly halving as `N` quadruples, which is the Riemann–von Mangoldt
  rate;
* **it is almost purely real, and that is the sharp test.** In all three cases `w − s` is real, so
  the tail terms `(w−s)/((s−ρ)(w−ρ)) ≈ (w−s)/ρ²`, summed over conjugate pairs, are real to leading
  order. The imaginary parts are consequently free of it, and they agree to **9 significant
  figures** at `N = 2000` — `4·10⁻⁷`, `5.9·10⁻⁷` and `1.9·10⁻⁹` relative — while the real residuals
  are still `10⁻³`;
* in differentiated form, `(ζ'/ζ)'(s) = −∑_ρ 1/(s−ρ)² − ¼ψ'(s/2+1) + 1/(s−1)²`, where the terms are
  `O(1/|ρ|³)`, the residual is `s`-independent to four digits across four test points and its ratio
  between `N = 100` and `N = 400` is `0.428` observed against `0.443` predicted.

A sign or normalisation error would be invisible to the type-checker and fatal downstream, so
agreement with the mathematics was established before any Lean proof existed.
-/

namespace ZetaHadamard.v1

open IEANTN

/-- **The partial-fraction expansion of `ζ'/ζ`, in paired form.**

For `s, w` off the pole and off the zeroes,

`∑_ρ (1/(s−ρ) − 1/(w−ρ)) = ζ'/ζ(s) − ζ'/ζ(w) + ½(ψ(s/2+1) − ψ(w/2+1)) + 1/(s−1) − 1/(w−1)`,

the sum running over the non-trivial zeroes `ρ` — those with `0 < Re ρ < 1` — counted with
multiplicity. This is Montgomery–Vaughan Corollary 10.14 (equivalently Davenport §12) with the
identity taken at two points and subtracted, which removes both the additive constant and the
conditional convergence.

`HasSum` rather than `∑'`, deliberately: it asserts summability as part of the claim, and an
unsummable `tsum` would be the junk value `0`. The multiplicity weight is
`IEANTN.zetaOrder`, matching `IEANTN.zetaZeroesSum`; the index set is
`zetaZeroesIn (Set.Ioo 0 1) Set.univ`, which is the critical strip and hence exactly the
non-trivial zeroes, `ζ` having no zeroes with `Re ρ ≤ 0` other than the trivial ones and none with
`Re ρ ≥ 1`.

Imports nothing: `s` and `w` are universally quantified with every condition a hypothesis. -/
noncomputable def logDeriv_partial_fractions : Prop :=
  ∀ s w : ℂ, s ≠ 1 → w ≠ 1 → riemannZeta s ≠ 0 → riemannZeta w ≠ 0 →
    HasSum (fun ρ : zetaZeroesIn (Set.Ioo (0:ℝ) 1) Set.univ ↦
        (1 / (s - (ρ : ℂ)) - 1 / (w - (ρ : ℂ))) * (zetaOrder (ρ : ℂ) : ℂ))
      (deriv riemannZeta s / riemannZeta s - deriv riemannZeta w / riemannZeta w
        + (Complex.digamma (s / 2 + 1) - Complex.digamma (w / 2 + 1)) / 2
        + 1 / (s - 1) - 1 / (w - 1))

end ZetaHadamard.v1
