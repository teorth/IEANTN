/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Vocabulary.Zeta
import IEANTN.Nodes.ZetaZeroLocations.v1.Tables

/-!
# Node `ZetaZeroLocations.v1`: where the zeros of `ζ` below height 1000 are

A `computation` node: the location, to within `10⁻²⁰`, of every zero of `ζ` with
`0 < Im ρ ≤ 1000`, and their number. The three conclusions are the statements `located`,
`unique` and `count` of `challenge/Zeros0to1000.lean` in `Garald1/zeta-zero-locations`, restated
in the network's vocabulary:

* `zetaZeroesIn Set.univ (Set.Ioc 0 1000)` for that file's `zerosBetween 0 1000`. The two sets are
  equal by unfolding: neither restricts the real part.
* `zetaOrder s = 1` for `analyticOrderAt riemannZeta s = 1`. At a zero `s ≠ 1` these agree,
  because `ζ` is analytic there.
* The listed integers are in `Tables.lean`, unchanged.

The proof in that repository checks each zero with a certificate evaluated by the Lean kernel
(Euler–Maclaurin, a contraction argument and the functional equation) and counts the zeros with the
argument principle. Arb output is candidate data only; every inequality is re-proved in the kernel.

## Intended to grow

The ranges `(1000 j, 1000 (j + 1)]` for `j = 1, …, 9`, and the count up to `10 000`, are proved in
the same repository and belong here as further conclusions with their own tables. They are left
out for now because their verification is far heavier: the range `(9000, 10000]` alone took over
three hours in Comparator.
-/

namespace ZetaZeroLocations.v1

open IEANTN

/-- **Every zero with `0 < Im s ≤ 1000` is simple, on the critical line, and listed:** its ordinate
is within `10⁻²⁰` of `m / 10²⁴` for some `m` in `ordinates_0_1000`.

Imports nothing. -/
def located_0_1000 : Prop :=
  ∀ s ∈ zetaZeroesIn Set.univ (Set.Ioc 0 1000), s.re = 1 / 2 ∧ zetaOrder s = 1 ∧
    ∃ m ∈ ordinates_0_1000, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

/-- **Each listed `m` has exactly one zero near it:** exactly one zero of `ζ` has its ordinate
within `10⁻²⁰` of `m / 10²⁴`.

Imports nothing. -/
def unique_0_1000 : Prop :=
  ∀ m ∈ ordinates_0_1000,
    ∃! s : ℂ, s ∈ zetaZeroes ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20

/-- **There are exactly 649 zeros with `0 < Im s ≤ 1000`.**

`Set.ncard` of an infinite set is `0`, so this also says the set is finite.

Imports nothing. -/
def count_0_1000 : Prop :=
  (zetaZeroesIn Set.univ (Set.Ioc 0 1000)).ncard = 649

end ZetaZeroLocations.v1
