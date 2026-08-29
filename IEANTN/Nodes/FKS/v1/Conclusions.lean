/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `FKS.v1`

Fiori, Kadiri and Swidinsky, *Sharper bounds for the Chebyshev function `ψ(x)`*,
J. Math. Anal. Appl. **527** (2023), Paper No. 127426.

Explicit bounds on `ψ(x) − x`, obtained from a zero-free region, a zero density estimate, and a
numerical verification of the Riemann hypothesis to a finite height. This is the node `FKS2`'s
conversion pipelines consume: its output is the `Eψ` bound that FKS2 carries to `Eθ` and then `Eπ`.

## A version discrepancy, recorded rather than smoothed over

The preprint (arXiv:2204.02588v2, December 2022) is titled *Density results for the zeros of zeta
applied to the error term in the prime number theorem* and numbers its results differently from the
published version. `FKS2` cites "[8, Corollary 1.3]" for the bound it feeds into its Corollary 14;
in the preprint, `Corollary 1.3` is a remark and the corresponding statements are Theorem 1.2 and
Corollary 1.4.

Both conclusions below are therefore labelled by what they *say* rather than by a number that is
not stable between versions, and each records where it was read from. Anyone with the published
version should confirm the numbering and tighten these notes.
-/

namespace FKS.v1

open IEANTN

/-- **The all-`x` bound** (arXiv:2204.02588v2, Corollary 1.4).

`Eψ(x) < 9.22022 (log x)^{3/2} exp(−0.8476836 √(log x))` for every `x > 2`.

Stated in the paper's own normalisation rather than converted, because **the conversion does not
close**. Rescaling to the `admissibleBound` shape with `R = 5.5666305` gives

* `A = 9.22022 · R^{3/2} = 121.09602174…`, where `psi_classical_bound` below states `121.096`;
* `C = 0.8476836 · √R = 1.99999992…`, where it states `2`.

Both roundings go the strengthening way — a smaller `A` and a larger `C` are each a *stronger*
claim — so `psi_classical_bound` is **not** derivable from this conclusion by rescaling, and a
solution that tries will fail by `2.2·10⁻⁵` in `A` and `8·10⁻⁸` in `C`. The two are transcribed
from different places in the paper and neither is claimed to follow from the other; see the note
there. This is the shape of gap `IEANTN.margin` exists for, and a margin index on whichever
conclusion is eventually proved is the likely resolution.

A note here once put the rescaled `A` at `≈ 121.0916` and called the discrepancy rounding. The
figure was wrong — it is `121.09602` — and so was the gloss: the difference is not a benign
rounding but a gap in the direction that breaks the derivation.

Keeping the printed form means the transcription can be checked against the paper by eye. -/
def psi_bound_all_x : Prop :=
  ∀ x > (2 : ℝ), Eψ x < 9.22022 * (Real.log x) ^ ((3 : ℝ) / 2) *
    Real.exp (-0.8476836 * Real.sqrt (Real.log x))

/-- **The admissible classical bound above `e³⁰`**, in the form `FKS2` consumes.

`Eψ` obeys the admissible classical bound with `A = 121.096`, `B = 3/2`, `C = 2`,
`R = 5.5666305`, for all `x ≥ e³⁰`.

Transcribed from `FKS2`'s proof of its Corollary 14, which quotes these four parameters and this
threshold and attributes them to "[8, Corollary 1.3]". The preprint's Theorem 1.2 gives exactly
this shape, `Eψ(x) ≤ A(x₀) (log x / R)^{3/2} exp(−2 √(log x / R))`, but tabulates `A(x₀)` only for
`log x₀ > 1000`, so the value at `x₀ = e³⁰` comes from the published version.

`R = 5.5666305` is not this paper's: it is the classical zero-free region constant of Mossinghoff
and Trudgian, J. Number Theory **157** (2015), Theorem 1 and §6.1. A sharper `R = 5.558691` is
available from Mossinghoff, Trudgian and Yang (`MTY.v1`), and `FKS2` states explicitly that its
numerics do not reflect it — so this constant is the one to change first when the chain is
re-run. -/
def psi_classical_bound : Prop :=
  HasClassicalBound Eψ 121.096 (3 / 2) 2 5.5666305 (Real.exp 30)

end FKS.v1
