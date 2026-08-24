/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import LcmDev

/-!
# Solution: `Lcm.v1`

Proves the declaration `Challenge.lean` states. The mathematics is in `LcmDev.lean`, ported from
`PrimeNumberTheoremAnd/IEANTN/Lcm.lean`; this file is only the bridge.

Note that the challenge module is deliberately **not** imported: Comparator compares two modules
declaring the same names, so importing it would collide.

The bridge is short because the ported development already states the result in the same shape the
node claims. Two identifications make it `rfl`-level:

* `LcmDev.L n` and `Nat.lcmUpto n` are both `(Icc 1 n).lcm id`;
* `LcmDev.HighlyAbundant` and `Lcm.v1.HighlyAbundant` are both
  `∀ m, m < N → σ m < σ N` with `σ = ArithmeticFunction.sigma 1`.

What is *not* cosmetic is the hypothesis. PNT+'s proof consumes its own `Dusart.proposition_5_4`,
which is unproved there; the port takes Dusart as a hypothesis instead, so this theorem depends on
`propext`, `Classical.choice` and `Quot.sound` alone.
-/

theorem Lcm.v1.challenge_lcmUpto_not_highlyAbundant
    (dusart2018_v1_proposition_5_4 : Dusart2018.v1.proposition_5_4) :
    Lcm.v1.lcmUpto_not_highlyAbundant :=
  fun n hn => LcmDev.L_not_HA_of_ge dusart2018_v1_proposition_5_4 n hn
