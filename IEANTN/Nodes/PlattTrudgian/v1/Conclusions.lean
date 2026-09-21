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

**Two heights, one computation.** The abstract quotes the round `3 · 10¹²` and that is what
downstream papers use, but Theorem 1 states the height the computation actually reached,
`3 000 175 332 800`. Both are recorded — `rh_up_to` and `rh_up_to_exact` — because the difference
of `1.75 · 10⁸` is invisible to almost every consumer and decisive for one: an estimate whose error
term is `π/(T−1)` needs `T ≥ 3 · 10¹² + 1` before it can be quoted with a `π/(3 · 10¹²)`. The
rounded conclusion is the exact one weakened, so a solution proves the exact one and derives the
other in a line.

`kind: computation`, because that is what it is. The node will never carry a Lean solution in any
foreseeable sense: the content is thousands of hours of interval arithmetic over zeros of `ζ`, and
what a formalization could offer is a *statement* of record with an honest citation, not a proof.
That is the case the network was built to accommodate.
-/

namespace PlattTrudgian.v1

open IEANTN

/-- **The verification height, rounded.** The Riemann hypothesis holds up to `3 · 10¹²`: `ζ` has no
zeroes with real part strictly between `1/2` and `1` and imaginary part in `[0, 3 · 10¹²]`.

This is the height the abstract quotes and the one downstream papers use. It is `rh_up_to_exact`
weakened, and is kept as its own conclusion because that is the form consumers cite. -/
def rh_up_to : Prop :=
  RiemannHypothesisUpTo (3 * 10 ^ (12 : ℕ))

/-- **The verification height, exact.** The Riemann hypothesis holds up to `3 000 175 332 800`.

Theorem 1 of the paper: *"The Riemann hypothesis is true up to height 3 000 175 332 800. That is,
the lowest 12 363 153 437 138 non-trivial zeroes `ρ` have `ℜρ = 1/2`."* The abstract states the
rounded `3 · 10¹²` instead, which is why the rounded form is the one usually seen.

The extra `1.75 · 10⁸` is not pedantry. `CH2.v1`'s Corollary 1.2 carries the error term `π/(T−1)`,
and its Corollary 1.3 quotes that as `π/(3 · 10¹²)`; that step needs `T ≥ 3 · 10¹² + 1`, which the
rounded height does not give and this one does. -/
def rh_up_to_exact : Prop :=
  RiemannHypothesisUpTo 3000175332800

end PlattTrudgian.v1
