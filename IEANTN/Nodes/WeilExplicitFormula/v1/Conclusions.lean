/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.LeftRightLim
import IEANTN.Vocabulary.Zeta

/-!
# Node `WeilExplicitFormula.v1`

DRAFT (Claude, 26 November 2026), not compiled: to be moved into `IEANTN/Nodes/` and checked with
`lake build`, `ieantn.py gen-challenges`, `ieantn.py fingerprint` and `ieantn.py check`.

Weil's explicit formula for `ζ`: Theorem 12.13 of Montgomery–Vaughan, *Multiplicative Number
Theory I*, in the case `q = 1` (`χ = χ₀`, `E₀ = 1`, `κ = 0`, `log(q/π) = -log π`). For a test
function `F` with `Φ(s) = ∫ F(x) e^{-(s-1/2)2πx} dx`,
```
lim_{T→∞} ∑_{|γ| ≤ T} Φ(ρ) = Φ(0) + Φ(1) + (Γ'/Γ(1/4) - log π) F(0) / (2π)
    - (1/2π) ∑_n Λ(n) n^{-1/2} (F(-log n / 2π) + F(log n / 2π))
    + ∫_0^∞ e^{-πx} (1 - e^{-4πx})⁻¹ (2F(0) - F(x) - F(-x)) dx,
```
the sum running over the non-trivial zeroes `ρ = β + iγ` with multiplicity: (12.22) with `q = 1`.

## The hypotheses, and the one deviation from the printed statement

Montgomery–Vaughan assume, for some `δ₀ > 0`,
(12.20) `∫ e^{(1/2+δ₀)2π|x|} |F(x)| dx < ∞` and (12.21) `∫ e^{(1/2+δ₀)2π|x|} |dF(x)| < ∞`,
together with `F(x) = (F(x-) + F(x+))/2` for all `x` and `F(x) + F(-x) = 2F(0) + O(|x|)`.

(12.21) is an integral against the variation of `F`, which Mathlib cannot express directly. With
`a = (1/2 + δ₀)2π = (1 + 2δ₀)π`, (12.20) and (12.21) together are **equivalent** to: `x ↦ e^{a|x|}F(x)`
is integrable and of bounded variation on `ℝ`. (`⇒` is the remark following Theorem 12.13 in
Montgomery–Vaughan; `⇐` because `dF = e^{-a|x|} dG + G d(e^{-a|x|})` with `G = e^{a|x|}F`, so
`∫ e^{a|x|}|dF| ≤ ∫ |dG| + a ∫ |G|`.) That is the form stated below. The equivalence with the
printed form, as a Riemann–Stieltjes statement, is proved in the solution.

`F(x) + F(-x) = 2F(0) + O(|x|)` is read as `x → 0`; for `|x| ≥ 1` it holds anyway, `F` being bounded.

## Junk values

* The sum over zeroes is `IEANTN.zetaZeroesSum` over the critical strip and `|Im ρ| ≤ T`, a `tsum`
  of a family with finite support (finitely many zeroes in a compact set: Mathlib's
  `IsCompact.inter_riemannZetaZeros_finite`). It is an
  honest finite sum, and the theorem is about the limit of these finite sums; no summability over
  all zeroes is claimed (none holds in general: `Φ(ρ)` is only `O(1/|γ|)`).
* `Phi F ρ` is a Bochner integral. Under the hypotheses the integrand is integrable for
  `-δ₀ < Re s < 1 + δ₀`, which contains every point where `Phi` is evaluated here.
* The series over `n` converges absolutely under the hypotheses (`F(±x) ≪ e^{-a|x|}`), and the
  integral over `x > 0` converges (the integrand is bounded near `0` by the `O(|x|)` hypothesis).
  So junk values could only make the statement false, never vacuous.
-/

namespace WeilExplicitFormula.v1

open Filter Topology Asymptotics IEANTN

/-- `Φ(s) = ∫ F(x) e^{-(s - 1/2) 2πx} dx`, Montgomery–Vaughan's notation in Theorem 12.13. -/
noncomputable def Phi (F : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, F x * Complex.exp (-(s - 1 / 2) * (2 * Real.pi * x))

/-- The hypotheses of Montgomery–Vaughan Theorem 12.13, with (12.20)–(12.21) in the equivalent form
described in the module docstring. -/
def IsTestFunction (F : ℝ → ℂ) (δ₀ : ℝ) : Prop :=
  0 < δ₀ ∧
  MeasureTheory.Integrable (fun x : ℝ ↦ (Real.exp ((1 + 2 * δ₀) * Real.pi * |x|) : ℂ) * F x) ∧
  BoundedVariationOn (fun x : ℝ ↦ (Real.exp ((1 + 2 * δ₀) * Real.pi * |x|) : ℂ) * F x) Set.univ ∧
  (∀ x : ℝ, F x = (Function.leftLim F x + Function.rightLim F x) / 2) ∧
  (fun x : ℝ ↦ F x + F (-x) - 2 * F 0) =O[𝓝 0] (fun x : ℝ ↦ x)

/-- The right-hand side of (12.22) for `q = 1`. -/
noncomputable def rhs (F : ℝ → ℂ) : ℂ :=
  Phi F 0 + Phi F 1
    + (Complex.digamma (1 / 4) - (Real.log Real.pi : ℂ)) * F 0 / (2 * Real.pi)
    - (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (F (-(Real.log n / (2 * Real.pi))) + F (Real.log n / (2 * Real.pi)))) / (2 * Real.pi)
    + ∫ x in Set.Ioi (0 : ℝ),
        ((Real.exp (-(Real.pi * x)) / (1 - Real.exp (-(4 * Real.pi * x))) : ℝ) : ℂ) *
          (2 * F 0 - F x - F (-x))

/-- **Weil's explicit formula**, Montgomery–Vaughan Theorem 12.13 with `q = 1`. -/
def theorem_12_13 : Prop :=
  ∀ (F : ℝ → ℂ) (δ₀ : ℝ), IsTestFunction F δ₀ →
    Tendsto (fun T : ℝ ↦ zetaZeroesSum (Set.Ioo 0 1) (Set.Icc (-T) T) (Phi F)) atTop
      (𝓝 (rhs F))

end WeilExplicitFormula.v1
