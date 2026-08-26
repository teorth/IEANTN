/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import IEANTN.Vocabulary.PrimeCounting

/-!
# Vocabulary: normalised error terms and the shapes of the bounds on them

Explicit analytic number theory states almost all of its results as a bound on one of four
normalised error terms — `Eψ`, `Eθ`, `Eπ`, `Eπ'` — of one of three shapes: *classical*,
*numerical*, or *Vinogradov*.

The bound shapes are deliberately stated as predicates on an **arbitrary** error function
`E : ℝ → ℝ` rather than being repeated once per error term.  A node that proves a
classical-to-numerical conversion proves it once, for all four error terms, and downstream nodes
importing it get all four.  Had the predicates been duplicated per error term (as they are in the
current PNT+ `Defs.lean`) the same lemma would have to appear four times and the four copies could
silently drift apart.
-/

namespace IEANTN

open Real
open scoped Chebyshev

/-! ### The four normalised error terms -/

/-- `Eψ x = |ψ x - x| / x`, the error in the prime number theorem for the second Chebyshev
function, normalised by `x`. -/
noncomputable def Eψ (x : ℝ) : ℝ := |Chebyshev.psi x - x| / x

/-- `Eθ x = |θ x - x| / x`, the error in the prime number theorem for the first Chebyshev
function, normalised by `x`. -/
noncomputable def Eθ (x : ℝ) : ℝ := |Chebyshev.theta x - x| / x

/-- `Eπ x = |π x - Li x| / (x / log x)`, the error in the prime number theorem for `π`,
normalised by `x / log x`.

Note the comparison is against the *offset* logarithmic integral `Li`, not `li`; the two differ
by the constant `li 2 = 1.0451…`, which is not negligible at the precision these estimates are
stated to.  Check which one a source paper means before transcribing its constant. -/
noncomputable def Eπ (x : ℝ) : ℝ := |primeCounting x - Li x| / (x / log x)

/-- `Eπ' x = |π*(x) - Li x| / (x / log x)`, the same error for the Riemann prime-counting
function `π*`. -/
noncomputable def Eπ' (x : ℝ) : ℝ := |riemannPrimeCounting x - Li x| / (x / log x)

/-! ### The shapes a bound can take -/

/-- The classical admissible bound
`A (log x / R)^B exp(-C (log x / R)^{1/2})`,
the shape produced by a classical zero-free region with parameter `R`.

**Junk-value warning.** The exponentiations are `Real.rpow`, so for `log x / R < 0` — that is, for
`x < 1` when `R > 0` — the value is junk.  Every statement using this should carry `x ≥ x₀` with
`x₀` at least `1`; in practice `x₀` is astronomically large. -/
noncomputable def admissibleBound (A B C R x : ℝ) : ℝ :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / 2))

/-- **A transcription trap, and it is not the one previously recorded here.**

The papers these error terms come from define them exactly as above, with absolute values: FKS
(1.1) has `Eψ(x) = |(ψ(x) - x)/x|`, and FKS2 (1) and (2) do the same for `Eπ`, `Eθ` and `Eψ`. A
note here once claimed they were *signed*, and that a bound transcribed from such a corollary was
therefore stronger than the corollary. That was wrong, and the way it went wrong is the thing worth
recording: **PDF text extraction silently drops the absolute-value bars around a displayed
fraction.** `|(ψ(x) - x)/x| ≤ ε` extracts as `ψ(x) −x x ≤ε`, which reads as a signed one-sided
bound and is indistinguishable from one.

Bars *inline* and in captions usually survive, which is what made the mistake look confirmed. So:
when a transcription turns on whether something is two-sided, render the page and look at it —
`page.get_pixmap(clip=...)` in `pymupdf` — rather than trusting `get_text`.

`HasClassicalBound E A B C R x₀`: the error term `E` obeys the classical admissible bound with
parameters `A, B, C, R` for all `x ≥ x₀`. -/
def HasClassicalBound (E : ℝ → ℝ) (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, E x ≤ admissibleBound A B C R x

/-- `HasNumericalBound E ε x₀`: the error term `E` is at most the constant `ε` for all `x ≥ x₀`.

This is the shape a classical bound is converted into once `x₀` is past the point where the
admissible bound is decreasing. -/
def HasNumericalBound (E : ℝ → ℝ) (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, E x ≤ ε

/-- `HasVinogradovBound E A B C x₀`: the error term `E` obeys
`A (log x)^B exp(-C (log x)^{3/5} / (log log x)^{1/5})` for all `x ≥ x₀`,
the shape produced by a Vinogradov–Korobov zero-free region. -/
def HasVinogradovBound (E : ℝ → ℝ) (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, E x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))

end IEANTN
