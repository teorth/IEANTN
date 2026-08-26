/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `PlattTrudgian.v1`

Platt and Trudgian, *The Riemann hypothesis is true up to `3 · 10¹²`*,
Bull. Lond. Math. Soc. **53** (2021), 792–797.

A numerical verification: every zero of `ζ` with imaginary part up to `3 · 10¹²` lies on the
critical line. This is the finite computation that every explicit estimate downstream ultimately
rests on — `FKS` takes `H₀ = 3 · 10¹²` from here, and everything `FKS` feeds inherits it.

`kind: computation`, because that is what it is. The node will never carry a Lean solution in any
foreseeable sense: the content is thousands of hours of interval arithmetic over zeros of `ζ`, and
what a formalization could offer is a *statement* of record with an honest citation, not a proof.
That is the case the network was built to accommodate.
-/

namespace PlattTrudgian.v1

open IEANTN

/-- **The verification height.** The Riemann hypothesis holds up to `3 · 10¹²`: `ζ` has no zeroes
with real part strictly between `1/2` and `1` and imaginary part in `[0, 3 · 10¹²]`.

The paper's own framing is that the first `10¹³` zeros are on the critical line, which pins the
height at `3.0000000000 · 10¹²`; the round `3 · 10¹²` is what downstream papers quote and use, and
is what is recorded here. A node wanting the sharper height should say so explicitly rather than
read it into this one. -/
def rh_up_to : Prop :=
  RiemannHypothesisUpTo (3 * 10 ^ (12 : ℕ))

end PlattTrudgian.v1
