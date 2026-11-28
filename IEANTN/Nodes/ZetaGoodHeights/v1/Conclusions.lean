/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import IEANTN.Vocabulary.Zeta

/-!
# Node `ZetaGoodHeights.v1`

DRAFT (Claude, 26 November 2026), not compiled. The family name is a suggestion.

Two textbook facts about the zeroes of `ζ` near a given height, from Montgomery–Vaughan,
*Multiplicative Number Theory I*:

* **Theorem 10.13**: `N(T + 1) - N(T) ≪ log(T + 2)`;
* **Lemma 12.2**: for each `T ≥ 2` there is `T₁ ∈ [T, T + 1]` such that `ζ'/ζ(σ + iT₁) ≪ (log T)²`
  uniformly for `-1 ≤ σ ≤ 2`.

These are what a contour argument needs to place its horizontal sides: a height whose segment
`[-1, 2] + iT₁` stays away from the zeroes, with `ζ'/ζ` under control along it. Several explicit
formulas need exactly this (Weil's, in `WeilExplicitFormula.v1`; Perron-type formulas generally).

## Counting convention

Montgomery–Vaughan count zeroes with `0 < γ ≤ T` and weight `1/2` at `γ = T`. Since the claim is
`≪`, counting the closed interval `[T, T + 1]` instead changes only the constant (the closed count is
at most `N(T + 2) - N(T - 1)` in their convention), so the conclusion below uses the closed interval,
through `IEANTN.zetaZeroesSum`, whose sum is finite (Mathlib's `IsCompact.inter_riemannZetaZeros_finite`;
also `ZetaZeroes.v1.finite_zeroes_on_compact`).

## Junk values

`ζ'/ζ` is written `deriv riemannZeta s / riemannZeta s`, which is `0` where `ζ(s) = 0`. A bound on
it would therefore be vacuous at a zero, so `lemma_12_2` asserts `ζ(σ + iT₁) ≠ 0` along the whole
segment as well. That is implicit in Montgomery–Vaughan's statement (`ζ'/ζ` is finite there) and is
the half of the lemma that a contour argument actually uses.

## How it is to be proved

Not as in Montgomery–Vaughan, who obtain Lemma 12.2 from Lemma 12.1 and so from the Hadamard
product (their Theorem 10.12 and Corollary 10.14; IEANTN's `ZetaHadamard.v1`, which rests on the
literature), but by the route they mention as an alternative, the method of their Lemma 6.4.
Theorem 10.13 from Jensen's inequality (Mathlib's `AnalyticOnNhd.sum_divisor_le`) applied to
`riemannZeta₁ = (s - 1) ζ(s)` on the disc of Montgomery–Vaughan's proof; then, for `1/2 ≤ σ ≤ 2`, the
local expansion of `ζ'/ζ` over nearby zeroes from the Borel–Carathéodory lemma
(`Complex.borelCaratheodory`) and `MeromorphicOn.extract_zeros_poles`, as in their Lemma 6.3, with a
pigeonhole choice of `T₁`; for `-1 ≤ σ < 1/2`, the functional equation of `ζ'/ζ`
(`ZetaLogDeriv.v1`) and a bound for the digamma function on a vertical strip.
-/

namespace ZetaGoodHeights.v1

open IEANTN

/-- **Montgomery–Vaughan, Theorem 10.13.** The number of non-trivial zeroes with ordinate in
`[T, T + 1]`, counted with multiplicity, is `≪ log(T + 2)` for `T ≥ 0`. -/
def theorem_10_13 : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
    zetaZeroesSum (Set.Ioo 0 1) (Set.Icc T (T + 1)) (fun _ ↦ (1 : ℝ)) ≤ C * Real.log (T + 2)

/-- **Montgomery–Vaughan, Lemma 12.2.** For each `T ≥ 2` there is `T₁ ∈ [T, T + 1]` such that
`ζ` does not vanish on the segment `σ + iT₁`, `-1 ≤ σ ≤ 2`, and `ζ'/ζ(σ + iT₁) ≪ (log T)²` there,
uniformly in `σ`. -/
def lemma_12_2 : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∃ T₁ ∈ Set.Icc T (T + 1), ∀ σ ∈ Set.Icc (-1 : ℝ) 2,
    riemannZeta (σ + T₁ * Complex.I) ≠ 0 ∧
      ‖deriv riemannZeta (σ + T₁ * Complex.I) / riemannZeta (σ + T₁ * Complex.I)‖ ≤
        C * Real.log T ^ 2

end ZetaGoodHeights.v1
