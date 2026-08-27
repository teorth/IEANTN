/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `Trudgian2011.v1`

Trudgian, *Improvements to Turing's method*, Math. Comp. **80** (2011), no. 276, 2259–2279.

Turing's method confirms that a zero count is complete — that no zero has been missed, and so that
none lies off the critical line in the range checked. Making it explicit needs a bound on the
integral of `S(t)`, and this paper's Theorem 2.2 is the bound every modern verification uses.

`Platt2017` states it as its own Theorem 4.2, attributed to Trudgian, with the proof "This is
Theorem 2.2 of [27]". So this node turns one of `Platt2017`'s named external inputs into an edge —
and through it, the whole `Platt2017 → KLN → PlattTrudgian2021 → BKLNW` chain gains a little more
of its foundation.

## On the threshold

The paper's own footnote is worth repeating: "The constant `168π` which occurs in the triples of
Turing and Lehman seems to be a misprint." Trudgian keeps it anyway, and notes that the constants
"are valid for all `t₂ > t₁ > 168π`" while being optimal near `t₁ > 2π · 10¹²`. The threshold
stated below is therefore the paper's, not a sharpening of it.
-/

namespace Trudgian2011.v1

open IEANTN

/-- **Theorem 2.2.** `|∫_{t₁}^{t₂} S(t) dt| ≤ 2.067 + 0.059 log t₂` for every `t₂ > t₁ > 168π`.

This is the explicit form of the bound Turing's method needs. `Platt2017`'s Theorem 4.2 is exactly
this statement.

`S` is `zetaS`, defined in Vocabulary as `(1/π) Im ∫_{1/2}^{∞} (ζ'/ζ)(σ + it) dσ`. The papers
extend `S` to the ordinates of zeroes by a right limit and this definition does not; that is
harmless here and only here, because the exceptional `t` form a measure-zero set and this
conclusion integrates over `t`. A conclusion evaluating `S` at a point would need the convention —
see the `zetaS` docstring. -/
def integral_S_bound : Prop :=
  ∀ t₁ t₂ : ℝ, 168 * Real.pi < t₁ → t₁ < t₂ →
    |∫ t in Set.Ioc t₁ t₂, zetaS t| ≤ 2.067 + 0.059 * Real.log t₂

end Trudgian2011.v1
