/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Vocabulary.Zeta
import IEANTN.Nodes.ZetaZeroLocations.v4.Tables

/-!
# Node `ZetaZeroLocations.v4`: the zeros of `ζ` with `3000 < Im ρ ≤ 4000`

A `computation` node, one of the ten versions of this family that cover `0 < Im ρ ≤ 10 000`
in ranges of height 1000 (`v1` to `v10`). The family is split into versions because a node is
verified all at once, and each range is a separate, heavy computation. `v11` derives the
Riemann hypothesis, simplicity and the count up to height 10 000 from the ten ranges.

The three conclusions are the statements `located`, `unique` and `count` of
`challenge/Zeros3000to4000.lean` in `Garald1/zeta-zero-locations`, in the network's vocabulary, as
in `ZetaZeroLocations.v1` (see its module docstring for why the two forms agree).
-/

namespace ZetaZeroLocations.v4

open IEANTN

/-- **Every zero with `3000 < Im s ≤ 4000` is simple, on the critical line, and listed:** its
ordinate is within `10⁻²⁰` of `m / 10²⁴` for some `m` in `ordinates_3000_4000`.

Imports nothing. -/
def located_3000_4000 : Prop :=
  ∀ s ∈ zetaZeroesIn Set.univ (Set.Ioc 3000 4000), s.re = 1 / 2 ∧ zetaOrder s = 1 ∧
    ∃ m ∈ ordinates_3000_4000, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

/-- **Each listed `m` has exactly one zero near it:** exactly one zero of `ζ` has its ordinate
within `10⁻²⁰` of `m / 10²⁴`.

Imports nothing. -/
def unique_3000_4000 : Prop :=
  ∀ m ∈ ordinates_3000_4000,
    ∃! s : ℂ, s ∈ zetaZeroes ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

/-- **There are exactly 1005 zeros with `3000 < Im s ≤ 4000`.**

`Set.ncard` of an infinite set is `0`, so this also says the set is finite.

Imports nothing. -/
def count_3000_4000 : Prop :=
  (zetaZeroesIn Set.univ (Set.Ioc 3000 4000)).ncard = 1005

end ZetaZeroLocations.v4
