/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Nodes.BKLNW.v1.Tables

/-!
# Node `BKLNW.v1`

Broadbent, Kadiri, Lumley, Ng and Wilk, *Sharper bounds for the Chebyshev function `θ(x)`*,
Math. Comp. **90** (2021), 2281–2315.

Explicit bounds on `θ(x) − x`, and — the part the rest of the network consumes — an explicit bound
on `ψ(x) − θ(x)`, which is what lets an estimate for one Chebyshev function be carried to the
other. `FKS2`'s Proposition 13 is stated in terms of the coefficients below.

## The table

`Tables.lean` carries the paper's Table 8, the tabulated bounds `|ψ(x) − x| < ε(b) x`. It is data
only; what is claimed about it is `table8_psi_bound` and `table8_psi_bound_above` below.

Corollary 5.1's coefficient `a₁(b)` is defined by cases — the constant `1 + 1.93378 · 10⁻⁸` for
`b ≤ 38 log 10`, and `1 + ε(b/2)` read from Table 8 above it. The conclusion below still states
only the `b ≤ 38 log 10` branch, where every constant is explicit; the threshold is
`38 log 10 ≈ 87.4982` and every current consumer sits well below it (`FKS2`'s Corollary 14 uses
`x₀ = e³⁰`). Now that the table is present the other branch can be added when something needs it.

-/

namespace BKLNW.v1

open IEANTN

/-- The auxiliary sum `f` of equation (2.4):
`f(x) = Σ_{k=3}^{⌊log x / log 2⌋} x^{1/k − 1/3}`.

Node-local rather than Vocabulary: it is this paper's bookkeeping, and nothing else has wanted it.
Small enough to sit here rather than in a `Tables.lean`, which is for bulk data. -/
noncomputable def f (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊, x ^ ((1 : ℝ) / (k : ℝ) - 1 / 3)

/-- The coefficient `a₂(b)` of equation (2.12), on the range where `α` is the explicit constant of
Corollary 2.1:
`a₂(b) = (1 + 1.93378·10⁻⁸) · max(f(e^b), f(2^{⌊b/log 2⌋+1}))`.

The paper's proof of Corollary 5.1 writes `1 + 1.15177·10⁻⁸` for this leading factor while the
displayed equation (2.12) writes `1 + 1.93378·10⁻⁸`. The displayed statement is transcribed here,
being the claim; the discrepancy is recorded in the node's metadata and is worth resolving against
the published version. -/
noncomputable def a₂ (b : ℝ) : ℝ :=
  (1 + 1.93378e-8) * max (f (Real.exp b)) (f ((2 : ℝ) ^ (⌊b / Real.log 2⌋₊ + 1)))

/-- **Corollary 5.1**, on the range where its coefficients are explicit.

For `7 ≤ b ≤ 38 log 10` and every `x ≥ e^b`,
`ψ(x) − θ(x) < (1 + 1.93378·10⁻⁸) √x + a₂(b) x^{1/3}`.

This is the bound `FKS2`'s Proposition 13 turns into the multiplier relating an admissible bound
for `Eψ` to one for `Eθ`. Note the exponents: `x^{1/2}` and `x^{1/3}` here become `x₀^{-1/2}` and
`x₀^{-2/3}` there, because that multiplier is normalised by `x₀`. -/
def corollary_5_1 : Prop :=
  ∀ b : ℝ, 7 ≤ b → b ≤ 38 * Real.log 10 → ∀ x ≥ Real.exp b,
    Chebyshev.psi x - Chebyshev.theta x <
      (1 + 1.93378e-8) * x ^ ((1 : ℝ) / 2) + a₂ b * x ^ ((1 : ℝ) / 3)

/-- **Table 8**: for consecutive entries `(b, ε)` and `(b', ε')` of the table,
`|ψ(x) − x| ≤ ε · x` for all `e^b ≤ x ≤ e^b'`.

This is the paper's own gloss, from Corollary 8.1: "let `b` and `b'` be any consecutive entries of
column 1 of Table 8 such that `b < b'`, i.e. we assume that there exists `ε(b) > 0` such that
`|ψ(x) − x| ≤ ε(b) x` for all `x ∈ [e^b, e^b']`". The printed caption writes `ε(b, b')` but lists
only `b` per row, so the pairing has to be read off the column; Corollary 8.1 is what fixes it.

`zip` with `tail` is exactly "consecutive entries", and says nothing about the last row, which is
correct — the table gives no upper endpoint for it. -/
def table8_psi_bound : Prop :=
  ∀ p ∈ table8.zip table8.tail, ∀ x : ℝ,
    Real.exp (p.1.1 : ℝ) ≤ x → x ≤ Real.exp (p.2.1 : ℝ) → |Chebyshev.psi x - x| ≤ p.1.2 * x

/-- **Table 8, in the unbounded form the paper actually uses**: for every entry `(b, ε)`,
`|ψ(x) − x| ≤ ε · x` for all `e^b ≤ x ≤ e^25000`.

The paper's own Theorem 2 states exactly this shape — "let `b > 0`; then there exists a positive
constant `ε(b)` such that `|ψ(x) − x| / x ≤ ε(b)` for all `x ≥ e^b`" — and Corollaries 2.1 and 15.1
apply it that way. It follows from
`table8_psi_bound` together with the fact that the tabulated `ε` decrease — so a bound holding on
each later interval holds on the union — which is why it is stated separately rather than folded
into the one above: it is a consequence, and a solution should prove it as one.

The cutoff at `e^25000` is real and not a technicality: it is the last tabulated `b`, and past it
the table is silent. A consumer wanting larger `x` needs the paper's Theorem 13. -/
def table8_psi_bound_above : Prop :=
  ∀ p ∈ table8, ∀ x : ℝ,
    Real.exp (p.1 : ℝ) ≤ x → x ≤ Real.exp 25000 → |Chebyshev.psi x - x| ≤ p.2 * x

/-- **The numerical range covered by Tables 13 and 14**, in the form `FKS2` uses it: `Eθ(x) ≤ 1`
for every `2 ≤ x ≤ e³⁰`.

`FKS2`'s proof of its Corollary 14 needs the interval below `e³⁰`, where the asymptotic bound it is
establishing is weaker than the numerics, and takes exactly this from the paper's Tables 13 and 14.

Stated as the consequence rather than as the tables, because the consequence is what is consumed
and it is a single clean inequality. Should a downstream node want the tables' finer values, they
belong in a `Tables.lean` here and this conclusion becomes one of several. -/
def theta_error_le_one : Prop :=
  ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 30 → Eθ x ≤ 1

end BKLNW.v1
