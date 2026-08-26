/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `Platt2017.v1`

Platt, *Isolating some non-trivial zeros of zeta*, Math. Comp. **86** (2017), no. 307, 2449–2467.

The verification of the Riemann hypothesis to height `3.0610046 · 10¹⁰` that `KLN` fixes as its
`H₀`. Unlike the network's other computational nodes this one is recorded **at first hand**: the
paper is held, and its abstract states the height and the claim directly.

## Three Platt heights, and which is which

- **`Platt2017.v1`** — this node, `3.0610046 · 10¹⁰`, from the paper named above. `KLN` cites it
  for `H₀`, and `Platt–Trudgian`'s error-term paper says its constants are "computed at the height
  `H = 3.06 · 10¹⁰`".
- **`Platt2015.v1`** — `3.06 · 10¹⁰`, recorded because `MT` §3 says "we select `T₀ = 3.06 · 10¹⁰`
  as established in [10]", where [10] is Platt's *Computing `π(x)` analytically*. That paper is not
  held, so the node is at second hand. Almost certainly the same computation reported in a second
  place, but that is a guess and the node says so.
- **`PlattTrudgian.v1`** — `3 · 10¹²`, a later and much larger verification with Trudgian.

Since `3.06 · 10¹⁰ < 3.0610046 · 10¹⁰`, this node's claim **implies** `Platt2015.v1`'s. A bridge
discharging that is a short Lean argument — `RiemannHypothesisUpTo` is antitone in its height — and
would let the second-hand node borrow this one's first-hand evidence. Worth doing when anything
depends on it.
-/

namespace Platt2017.v1

open IEANTN

/-- **The verification height.** The Riemann hypothesis holds up to `3.0610046 · 10¹⁰`.

The abstract states it directly: the algorithm isolates "the non-trivial zeros of zeta with
imaginary part `≤ 30,610,046,000` to an absolute precision of `±2⁻¹⁰²`", and "in the process, we
provide an independent verification of the Riemann Hypothesis to this height".

As with every computational node, this states the *consequence* rather than the computation. The
output is a list of isolated zeros to a stated precision; what the network can say is that none of
them lies off the critical line. A consumer needing the zeros themselves — `Büthe`'s algorithm
does — needs more than this says. -/
def rh_up_to : Prop :=
  RiemannHypothesisUpTo 3.0610046e10

end Platt2017.v1
