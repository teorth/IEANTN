/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeGaps

/-!
# Node `Dusart2018` — explicit estimates of some functions over primes

Pierre Dusart, *Explicit estimates of some functions over primes*, Ramanujan J. **45** (2018),
227–251.

This node is currently a **stub**: it exports the one conclusion the rest of the network needs and
carries no imports and no Lean justification. Its `proposition_5_4` is asserted on the authority of
the paper.

That is a deliberate and supported state, not a defect. The node's shape is identical to that of a
fully verified node, so replacing the `literature` justification with a Lean solution later
requires no change to this file and no change to anything downstream of it. The rest of Dusart's
results — Theorem 4.2, the Corollary 5.2 and 5.3 families, Proposition 5.11, and so on — should be
added here as further conclusions when a node needs them.
-/

namespace Dusart2018.v1

/-- **Proposition 5.4.** For every real `x ≥ 89693` there is a prime `p` with
`x < p ≤ x + x / (log x)³`.

Dusart assembles this from three pieces: an analytic argument above `4 × 10¹⁸` resting on his
Theorem 4.2, a prime-gap table between `360653` and `4 × 10¹⁸`, and a direct verification on
`[89693, 360653]`. The threshold `89693` is sharp for the stated form.

The interval is open on the left and closed on the right — `x < p ≤ x + h`. Sources stating
`x ≤ p < x + h` are making a different claim at the endpoints. -/
def proposition_5_4 : Prop := IEANTN.HasPrimeInInterval.logPower 89693 3

end Dusart2018.v1
