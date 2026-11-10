/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `ZetaZeroLocations.v11`: the zeros of `ζ` up to height 10 000

Every zero of `ζ` with `0 < Im ρ ≤ 10 000` is simple and on the critical line, and there are
exactly `10 142` of them. These are the two statements of `challenge/Count10000.lean` in
`Garald1/zeta-zero-locations`, in the network's vocabulary.

They follow from the ten ranges `ZetaZeroLocations.v1` to `v10`, which this version imports: the
ranges `(1000 (j − 1), 1000 j]` partition `(0, 10 000]`, each range's zeros are simple and on the
line, and the ten counts `649, 868, 952, 1005, 1046, 1078, 1105, 1127, 1148, 1164` add up to
`10 142`. So, unlike the ranges, this version needs no computation of its own: its solution is a
short argument from the imported statements.
-/

namespace ZetaZeroLocations.v11

open IEANTN

/-- **The Riemann hypothesis up to height 10 000, with simple zeros:** every zero of `ζ` with
`0 < Im s ≤ 10 000` has real part `1/2` and order `1`.

Imports the ten `located` conclusions of `ZetaZeroLocations.v1` to `v10`. -/
def on_line_and_simple_0_10000 : Prop :=
  ∀ s ∈ zetaZeroesIn Set.univ (Set.Ioc 0 10000), s.re = 1 / 2 ∧ zetaOrder s = 1

/-- **There are exactly `10 142` zeros of `ζ` with `0 < Im s ≤ 10 000`.**

Imports the ten `count` conclusions of `ZetaZeroLocations.v1` to `v10`. -/
def count_0_10000 : Prop :=
  (zetaZeroesIn Set.univ (Set.Ioc 0 10000)).ncard = 10142

end ZetaZeroLocations.v11
