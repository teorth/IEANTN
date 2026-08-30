/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.Zeta

/-!
# Node `CH2.v1`

Andrés Chirre and Harald Andrés Helfgott, *Optimal bounds for sums of non-negative arithmetic
functions*, arXiv:2512.15709.

The paper's headline outputs for `ψ`. Its general result — Theorem 1.1, an optimal explicit formula
for `∑_{n ≤ x} aₙ n^{-σ}` given the poles of `∑ aₙ n^{-s}` up to height `T`, with **no zero-free
region needed** — specialises to the Chebyshev function and to `∑_{n ≤ x} Λ(n)/n`. Those four
specialisations are what this node states.

## Why the shape is unusual, and worth having

Every other `Eψ` bound in this network has the classical shape
`A (log x / R)^B exp(−C √(log x / R))`, which comes from a zero-free region. These do not. They
have the form

`|ψ(x) − x| ≤ (π/T) · x + C_T √x`,

with `T` the height to which the Riemann hypothesis has been verified. The `π/T` is **provably
optimal** in the paper's sense — it is the best any argument can do knowing only the zeros below
`T` — and the `√x` term carries all the dependence on `T`'s size. So this is a different kind of
estimate from `FKS.v1.psi_classical_bound`, better in some ranges and worse in others, and the two
should be compared rather than conflated.

Corollary 1.3 holds for **every `x ≥ 1`**, with no lower threshold at all. That is unusual among
explicit estimates and makes it directly consumable.

## A transcription warning

`PrimeNumberTheoremAnd` states these four as `CH2.cor_1_2_a`, `cor_1_2_b`, `cor_1_3_a`, `cor_1_3_b`,
all four `sorry`. **Its Corollary 1.3 constants are wrong**, in its blueprint LaTeX as well as its
Lean: it writes `π · 3 · 10⁻¹²` in part (a) and `π · √3 · 10⁻¹²` in part (b), where the paper has
`π/(3·10¹²)`. Those are `9.42·10⁻¹²` and `5.44·10⁻¹²` against the paper's `1.047·10⁻¹²` — nine and
five times too large, and inconsistent with each other, though both are *weaker* than the paper so
neither is false. The conclusions below are transcribed from the paper.

Its Corollary 1.2 transcription is right, and there is a check that says so: at `T = 3 × 10¹²`,
`C_T` evaluates to `113.6689`, which is the `113.67` the paper prints in Corollary 1.3.

## The main term of Corollary 1.2 is not `x`

It is `x · (π/T) coth(π/T)`. Since `y coth y = 1 + y²/3 + O(y⁴)`, that is `x` to enormous precision
at the heights in play, which is why Corollary 1.3 can drop it — but dropping it is a step in the
argument, not a definitional convenience.
-/

namespace CH2.v1

open IEANTN
open scoped Chebyshev

/-- The correction to the main term in Corollary 1.2: `(π/T) coth(π/T)`.

Node-local, because it is this paper's own bookkeeping. Written with `Real.tanh` since Mathlib has
no real `coth`. Tends to `1` as `T → ∞`, from above. -/
noncomputable def mainFactor (T : ℝ) : ℝ :=
  (Real.pi / T) / Real.tanh (Real.pi / T)

/-- The paper's `C_T = (1/2π) log²(T/2π) − (1/6π) log(T/2π)`, the coefficient of `√x`.

At `T = 3 × 10¹²` this is `113.6689…`, which is the `113.67` of Corollary 1.3 — the check that the
transcription of Corollary 1.2 is faithful. -/
noncomputable def CT (T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.log (T / (2 * Real.pi)) ^ (2 : ℕ)
    - (1 / (6 * Real.pi)) * Real.log (T / (2 * Real.pi))

/-- The partial sum `∑_{n ≤ x} Λ(n)/n`.

Node-local. Indexed by `Finset.Iic ⌊x⌋₊`, matching the paper's `∑_{n ≤ x}`; note `Λ 0 = 0`, so
including `0` in the range is harmless. -/
noncomputable def lambdaSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)

/-- **Corollary 1.2, the `ψ` estimate.** If the Riemann hypothesis holds up to height `T ≥ 10⁷`,
then for every `x > max(T, 10⁹)`,

`|ψ(x) − x (π/T) coth(π/T)| ≤ (π/(T−1)) x + C_T √x`.

The hypothesis is carried in the statement rather than imported, so this conclusion imports nothing
and applies at whatever height a verification node supplies — the same shape `Buthe2016.v1` uses.

The `π/(T−1)` is the paper's headline: the constant in front of the main error term is *provably
optimal* if one remains agnostic about zeros above height `T`. The `C_T √x` is best in a much
weaker sense; the paper is explicit that it should be attainable for rare very large `x` if the
ordinates of the zeros are linearly independent. -/
def corollary_1_2_psi : Prop :=
  ∀ T x : ℝ, (10 : ℝ) ^ (7 : ℕ) ≤ T → RiemannHypothesisUpTo T →
    max T ((10 : ℝ) ^ (9 : ℕ)) < x →
      |Chebyshev.psi x - x * mainFactor T| ≤ Real.pi / (T - 1) * x + CT T * Real.sqrt x

/-- **Corollary 1.2, the `∑ Λ(n)/n` estimate.** Under the same hypotheses,

`|∑_{n ≤ x} Λ(n)/n − (log x − γ)| ≤ π/(T−1) + C_T/√x`,

with `γ` the Euler–Mascheroni constant. The companion to the `ψ` bound: same two constants, divided
through by `x`. -/
def corollary_1_2_lambda_sum : Prop :=
  ∀ T x : ℝ, (10 : ℝ) ^ (7 : ℕ) ≤ T → RiemannHypothesisUpTo T →
    max T ((10 : ℝ) ^ (9 : ℕ)) < x →
      |lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)|
        ≤ Real.pi / (T - 1) + CT T / Real.sqrt x

/-- **Corollary 1.3, the `ψ` estimate.** For every `x ≥ 1`,

`|ψ(x) − x| ≤ (π/(3 · 10¹²)) x + 113.67 √x`.

Corollary 1.2 at Platt–Trudgian's verified height, which the paper quotes as
`3 · 10¹² + 1 + √3/3` and remarks is in fact `3 000 175 332 800`. The rounding to `3 · 10¹²` is the
paper's own and is the safe direction, `π/T` being decreasing in `T`.

**No lower threshold**: this holds from `x = 1`, where Corollary 1.2 needs `x > max(T, 10⁹)`. The
gap is closed in the paper, not assumed away here.

The constant is `π/(3 · 10¹²) = 1.047 · 10⁻¹²`. `PrimeNumberTheoremAnd` writes `π · 3 · 10⁻¹²`,
which is nine times larger; see the module docstring. -/
def corollary_1_3_psi : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    |Chebyshev.psi x - x| ≤
      Real.pi / (3 * (10 : ℝ) ^ (12 : ℕ)) * x + 113.67 * Real.sqrt x

/-- **Corollary 1.3, the `∑ Λ(n)/n` estimate.** For every `x ≥ 1`,

`|∑_{n ≤ x} Λ(n)/n − (log x − γ)| ≤ π/(3 · 10¹²) + 113.67/√x`.

The paper writes this with `O*`, which is exactly the two-sided bound stated here rather than an
asymptotic. `PrimeNumberTheoremAnd` writes the leading constant as `π · √3 · 10⁻¹²`, which agrees
neither with the paper nor with its own part (a); see the module docstring. -/
def corollary_1_3_lambda_sum : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    |lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)|
      ≤ Real.pi / (3 * (10 : ℝ) ^ (12 : ℕ)) + 113.67 / Real.sqrt x

end CH2.v1
