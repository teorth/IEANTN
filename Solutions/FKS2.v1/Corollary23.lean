/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Corollary22

/-!
# Corollary 23 — still open

See the docstring below for why this does not follow from Theorem 3, and what it does follow from.
-/

namespace FKS2Sol

open Real IEANTN

/-- **Corollary 23**, at the row this node states: `Eπ` obeys the classical bound with
`A = 0.826`, `B = 1/4`, `C = 1`, `R = 5.5666305`, for all `x ≥ e`.

**This does not come from Theorem 3.** Theorem 3 preserves `B` and `C` and requires
`B ≥ max(3/2, 1 + C²/(16R))`. Corollary 14 supplies `B = 3/2, C = 2`; this row is `B = 1/4, C = 1`,
so Theorem 3 can neither change the parameters nor accept `B = 1/4`. The paper's Remark
`rem-pi2theta` notes the `B ≥ 3/2` restriction could be lifted but never states the generalisation.

**It does not need it either.** The route is to split the range. Against Corollary 22, the paper's
headline bound (`9.2211 (log x)^{3/2} e^{-0.84768√log x}`), the ratio in `s = √(log x)` is
`≈ 17.1 s^{5/2} e^{-0.42385 s}`: it peaks near `118.9` at `x ≈ e^34.8`, so Corollary 22 does *not*
dominate on all of `[e, ∞)` — but it does from about `x ≈ e^671` onward, and below that other means
cover the range.

`PrimeNumberTheoremAnd` does exactly this, in four pieces: Corollary 22 domination on
`[e²⁰⁰⁰⁰, ∞)`, a numerical "quarter transport" over extended Table 4 cells on `[e¹⁰, e²⁰⁰⁰⁰]`, a
Büthe assembler on `[e⁶, e¹⁰]`, and one trusted numerical floor on `[e, e⁶]` — which is precisely
`FKS2Numerics.v1.table6_row2_floor`. So what this hole needs is numerical inputs and range
bookkeeping, not new analysis.

(An earlier version of this docstring said the row followed from Theorem 3 — wrong — and a later
one said it followed from nothing the paper states, which over-corrected: the peak figure is right
but it only rules out domination on the *whole* range.) -/
theorem corollary_23
    (hpsi : FKS.v1.psi_classical_bound)
    (hbuthe : Buthe.v1.theorem_2_li_minus_pi)
    (hfloor : FKS2Numerics.v1.table6_row2_floor) :
    FKS2.v1.corollary_23 := by
  sorry

end FKS2Sol
