/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import LcmDev

/-!
# Solution: `Lcm.v2`

Proves the declaration `Challenge.lean` states. The mathematics is in `LcmDev.lean`, generalised
from `Solutions/Lcm.v1/LcmDev.lean`; this file is only the bridge.

The challenge module is deliberately **not** imported: Comparator compares two modules declaring
the same names, so importing it would collide.

As in `v1`, the bridge is short because the development already states the result in the shape the
node claims -- `LcmDev.L n` and `Nat.lcmUpto n` are both `(Icc 1 n).lcm id`, and the two
`HighlyAbundant` definitions are both `∀ m, m < N → σ m < σ N`. The argument order differs only
because the node states its hypotheses in reading order (`c`, then `X₀`, then the bounds) while the
development takes the prime-gap hypothesis first.

This node has **no imports**: the prime-gap hypothesis is internal to the statement, so unlike
`v1`'s challenge there is no upstream conclusion to thread through.
-/

theorem Lcm.v2.challenge_lcmUpto_not_highlyAbundant_of_primeGap :
    Lcm.v2.lcmUpto_not_highlyAbundant_of_primeGap :=
  fun _c _X₀ hc hcX hd n hn => LcmDev.L_not_HA_of_ge hd hc hcX n hn
