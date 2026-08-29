/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Vocabulary: the roundoff safety margin

A table of computed values is not literally what a formalization can prove. Its entries are
rounded; the quantities behind them were themselves computed from rounded inputs; and a claim
transcribed as an exact inequality is a claim about arithmetic nobody performed.
`PrimeNumberTheoremAnd`'s IEANTN met this and settled on a multiplicative margin per table. This is
the same device, made explicit and given a place in the shared vocabulary.
-/

namespace IEANTN

/-- The roundoff safety margin carried by a numerical claim at dependency depth `n`:
`margin n = 1.001 ^ n`.

**Indexed by depth, because margins compound.** A claim resting on one table needs one margin; a
claim resting on a table that itself rested on a table needs two, and that growth is the thing a
reader must be able to see. Folding the margin into the constant — writing `0.827` where the paper
says `0.826` — hides it, and hides it exactly where a later reader is most likely to check the
transcription against the source. `margin 2 * …` says both that a margin is present and how far
down the stack it accumulated.

**`margin 0 = 1`, by `pow_zero`.** A claim carrying `margin 0` says the same thing as one carrying no margin at
all; the factor is a *site*, marking a number whose provenance is a computation, so that raising it
later is a change of one numeral rather than a change of shape. Statements should be written with
the site from the start and the index raised only when something downstream turns out to need it.

**It is not free.** Every margin weakens a claim, and one that grows without bound eventually
weakens it past usefulness. Depth is what to keep small: prefer one table covering a wider range to
two chained. Where a consumer has slack, the compounding stops — a bound of `0.413` against a
target of `0.4298` absorbs several margins without the consumer's own statement changing at all. -/
noncomputable def margin (n : ℕ) : ℝ := 1.001 ^ n

end IEANTN
