/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.NumberTheory.Chebyshev

/-!
# Node `Schoenfeld1976.v1`: Theorem 7* and Theorem 11

L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp.
**30** (1976), 337–360: Theorem 11 (printed p. 342) and Theorem 7* (printed p. 357).

Like the rest of the mid-1970s "Sharper bounds" papers, Schoenfeld assumes the Riemann hypothesis
for the first `3 502 500` zeros, which Rosser and Schoenfeld (1975) use at the height
`A = 1894438.51224…`. Every conclusion here keeps that assumption as an explicit premise,
`RiemannHypothesisUpTo 1894438.5122`: `A` rounded down, so that the historical verification covers
it. That verification, on which Schoenfeld relied, is the computation of Rosser, Yohe and
Schoenfeld (Information Processing 68, North-Holland, 1969, pp. 70–76). The premise also follows
from `Platt2017.v1.rh_up_to` (height `3.0610046e10`) by `riemannHypothesisUpTo_mono` in
`IEANTN/Bridges/Platt/P2017ToP2015.lean`.

Theorem 11 uses `X = √(log x / 9.645908801)` and `ε₀(x) = √(8/(17π)) · √X · e^{−X}`; the constant
`9.645908801` is the `R` of the Rosser–Schoenfeld zero-free region. Theorem 7* has five displays,
(5.5a*), (5.5b*), (5.6*), (5.6a*), (5.6b*); each is a separate conclusion.

Every inequality, constant and endpoint below is transcribed from the scan; the only departure is
(7.4), whose printed form has lost a relation (see `psi_upper_theorem_11`).
-/

namespace Schoenfeld1976.v1

/-- Schoenfeld's `X = √(log x / 9.645908801)` (before Theorem 11). For `x ≥ 1`, `log x ≥ 0`, so no
junk value of `Real.sqrt` arises on the ranges used below. -/
noncomputable def X (x : ℝ) : ℝ := Real.sqrt (Real.log x / 9.645908801)

/-- Schoenfeld's `ε₀(x) = √(8/(17π)) · √X · e^{−X}` (before Theorem 11). -/
noncomputable def epsilon0 (x : ℝ) : ℝ :=
  Real.sqrt (8 / (17 * Real.pi)) * Real.sqrt (X x) * Real.exp (-X x)

/-- **Theorem 11, (7.2).** `|ψ(x) − x| < x ε₀(x)` for `x ≥ 17`. -/
def psi_theorem_11 : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 → ∀ x : ℝ, 17 ≤ x →
    |Chebyshev.psi x - x| < x * epsilon0 x

/-- **Theorem 11, (7.3).** `|θ(x) − x| < x ε₀(x)` for `x ≥ 101`. -/
def theta_theorem_11 : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 → ∀ x : ℝ, 101 ≤ x →
    |Chebyshev.theta x - x| < x * epsilon0 x

/-- **Theorem 11, (7.4).** `θ(x) − x ≤ ψ(x) − x < x ε₀(x)` for `x ≥ 1`.

The printed display reads `θ(x) − x ≤ ψ(x) − x ε₀(x) if 1 ≤ x`: a relation is missing, and read
literally it is false. The proof on printed p. 349 shows `ψ(x) < x + x ε₀(x)` for `1 ≤ x ≤ 10⁸`
and then says this completes "(7.4), (7.2) and (7.3)"; this is the form stated here. -/
def psi_upper_theorem_11 : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 → ∀ x : ℝ, 1 ≤ x →
    Chebyshev.theta x - x ≤ Chebyshev.psi x - x ∧ Chebyshev.psi x - x < x * epsilon0 x

/-- **Theorem 7*, (5.5a*).** `|ψ(x) − x| < 0.0220646 x / log x` for `x ≥ 161971`. -/
def psi_log_5_5a : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 → ∀ x : ℝ, 161971 ≤ x →
    |Chebyshev.psi x - x| < 0.0220646 * x / Real.log x

/-- **Theorem 7*, (5.5b*).** `−0.0220646 x / log x < ψ(x) − x` for `x ≥ 89909`. -/
def psi_log_lower_5_5b : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 → ∀ x : ℝ, 89909 ≤ x →
    -(0.0220646 * x / Real.log x) < Chebyshev.psi x - x

/-- **Theorem 7*, (5.6*).** `|θ(x) − x| < 0.0239922 x / log x` for `x ≥ 758711`. -/
def theta_log_5_6 : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 → ∀ x : ℝ, 758711 ≤ x →
    |Chebyshev.theta x - x| < 0.0239922 * x / Real.log x

/-- **Theorem 7*, (5.6a*).** `θ(x) − x < 0.0201384 x / log x` for `x > 1`. -/
def theta_log_upper_5_6a : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 → ∀ x : ℝ, 1 < x →
    Chebyshev.theta x - x < 0.0201384 * x / Real.log x

/-- **Theorem 7*, (5.6b*).** `|ψ(x) − x|` and `|θ(x) − x|` are both `< 0.0077629 x / log x` for
`x ≥ e^22`. -/
def psi_theta_log_5_6b : Prop :=
  IEANTN.RiemannHypothesisUpTo 1894438.5122 → ∀ x : ℝ, Real.exp 22 ≤ x →
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x

end Schoenfeld1976.v1
