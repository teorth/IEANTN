/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `MT.v1`

Mossinghoff and Trudgian, *Nonnegative trigonometric polynomials and a zero-free region for the
Riemann zeta-function*, J. Number Theory **157** (2015), 329–349.

The classical zero-free region with `R = 5.573412`, and — from §6.1, in combination with a
verification height — the sharper `R = 5.5666305` that the whole `FKS` → `FKS2` chain is calibrated
to.

**Not to be confused with `MTY.v1`**, which is Mossinghoff, Trudgian and Yang (2024) and gives the
further improvement `R = 5.558691`. `FKS2` states explicitly that its numerics do not reflect that
improvement, so this node, not that one, is the current input to the chain. Two papers with three
overlapping authors and nearly the same title is exactly the situation where a network that records
its edges earns its keep.
-/

namespace MT.v1

open IEANTN

/-- **Theorem 1.** The classical zero-free region holds with `R = 5.573412` above height `2`.

`ζ` has no zeroes with `Re s ≥ 1 - 1/(R log |Im s|)` and `Im s ≥ 2`. This is the paper's
unconditional headline value.

Note the boundary. The paper's abstract claims the closed region, `σ ≥ 1 - 1/(R log|t|)`, while
Theorem 1 itself claims only the open one, `σ > ...`. The closed form is stated here, matching the
abstract and matching Kadiri before and `MTY` after, each of which states `≥`; but a consumer that
genuinely needs the boundary case should know it rests on the abstract rather than on the theorem.
See the node's limitations. -/
def zero_free_region : Prop :=
  ClassicalZeroFreeRegion 5.573412 2

/-- **§6.1**, the value the downstream chain actually uses: the classical zero-free region holds
with `R = 5.5666305`.

§6.1 is where the constant is sharpened using a partial verification of the Riemann hypothesis:
"if `T₀ = 3 · 10¹¹`, then by choosing `θ = 1.85567` with `F₁₆(φ)`, we obtain that `R₀ = 5.5666305`
is permissible", whose footnote records that `T₀ = 3 · 10¹¹` "has been announced by Jan Büthe and
Jens Franke in a personal communication". `FKS` cites this alongside `H₀ = 3 · 10¹²`, which is a
different and larger height; `PlattTrudgian.v1` supplies it and so discharges the requirement, but
the requirement itself is `3 · 10¹¹`. Recorded as a separate conclusion from Theorem 1 because it
is a different claim resting on a different input, and conflating the two would hide that this one
is conditional on a numerical verification.

Stated here unconditionally, as the paper states it, with the dependence on the verification height
recorded as an import rather than as a hypothesis. That is a choice worth revisiting if the height
ever changes: see the node's limitations. -/
def zero_free_region_sharpened : Prop :=
  ClassicalZeroFreeRegion 5.5666305 2

end MT.v1
