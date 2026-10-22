/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Node `Patel2020.v1`

Patel, *An explicit upper bound for `|ζ(1+it)|`*, arXiv:2009.00769. Read from `mainbound.tex`.

`ChengGraham2004.v1` deliberately states nothing: Lemmas 2 and 3 of that paper are wrong, and
this is the source that prints the corrections. The zeta bound is Theorem maintheorem. The two
lemmas are the corrected forms of Cheng–Graham Lemmas 2 and 3, as printed in Section 2.

One symbol in the third-derivative test is left unstated. In `α₃` the preprint writes `32λ`
once and `λ₃` elsewhere, with `λ` never defined. That formula is not transcribed.
-/

namespace Patel2020.v1

open Complex Real
open scoped BigOperators

/-- Distance from `x` to the nearest integer. The preprint's `‖x‖`, with `0 ≤ ‖x‖ ≤ 1/2`. -/
noncomputable def distToInteger (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- **Theorem maintheorem.** For `t ≥ 3`,
`|ζ(1+it)| ≤ min(log t, (1/2) log t + 1.93, (1/5) log t + 44.02)`.

The "in particular" tail `t ≥ 8.261…·10^60` is the third term alone, so it is not a second
claim. -/
def zeta_one_bound : Prop :=
  ∀ t : ℝ, 3 ≤ t →
    ‖riemannZeta (1 + t * I)‖ ≤
      min (Real.log t) (min (Real.log t / 2 + 1.93) (Real.log t / 5 + 44.02))

/-- **Corrected Cheng–Graham Lemma 2.** If `f` is continuously differentiable on `(a, b]`, `f'`
is monotonic, and `‖f'‖ ≥ 1/U` there for some `U > 0`, then the exponential sum over the integers
in `(a, b]` is at most `(2/π) U`.

The preprint's sum is indexed by `n ∈ (a, b]`. That is the integers `n` with `⌊a⌋ + 1 ≤ n ≤ ⌊b⌋`. -/
def cheng_graham_lemma_2 : Prop :=
  ∀ (f : ℝ → ℝ) (a b U : ℝ), 0 < U →
    ContDiffOn ℝ 1 f (Set.Ioc a b) →
    (MonotoneOn (deriv f) (Set.Ioc a b) ∨ AntitoneOn (deriv f) (Set.Ioc a b)) →
    (∀ x ∈ Set.Ioc a b, U⁻¹ ≤ distToInteger (deriv f x)) →
    ‖∑ n ∈ Finset.Icc (⌊a⌋ + 1) ⌊b⌋, exp (2 * π * I * f n)‖ ≤ (2 / π) * U

/-- **Corrected Cheng–Graham Lemma 3.** If `1/W ≤ |f''| ≤ 1/V` on `[N+1, N+L]` with `V < W` and
`W > 1`, then
`|∑_{n=N+1}^{N+L} exp(2πi f(n))| ≤ 2 (L/V + 2) (2 √(W/π) + 1)`.

The preprint remarks that the leading term of the incorrect lemma is off by `√2`. The slight
Platt–Trudgian sharpening printed just after this lemma is a different inequality and is not
folded in. -/
def cheng_graham_lemma_3 : Prop :=
  ∀ (f : ℝ → ℝ) (N L : ℕ) (V W : ℝ), 0 < V → V < W → 1 < W →
    ContDiffOn ℝ 2 f (Set.Icc (N + 1) (N + L)) →
    (∀ x ∈ Set.Icc ((N + 1 : ℕ) : ℝ) ((N + L : ℕ) : ℝ),
      W⁻¹ ≤ |iteratedDeriv 2 f x| ∧ |iteratedDeriv 2 f x| ≤ V⁻¹) →
    ‖∑ n ∈ Finset.Icc (N + 1) (N + L), exp (2 * π * I * f n)‖ ≤
      2 * ((L : ℝ) / V + 2) * (2 * Real.sqrt (W / π) + 1)

end Patel2020.v1
