/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Vocabulary.Numerics

/-!
# Node `DudekPlattNumerics.v2`

The two-sided bound on `π(x)` behind the `exp(3915)` threshold, at
`PrimeNumberTheoremAnd`'s constants rather than Dudek and Platt's.

A **variant** of `DudekPlattNumerics.v1`, not a successor. Both are the same shape of claim — `π(x)`
lies within `m x/(log x)⁶` and `M x/(log x)⁶` of the fifth partial sum of `li`'s asymptotic
expansion — and they differ only in where the constants come from and how good they are:

| | `xₐ` | `m` | `M` | threshold it supports |
|---|---|---|---|---|
| `v1`, Dudek–Platt §2 | `exp(9656.8)` | `−3103.33` | `3343.48` | `exp(9659)` |
| `v2`, this node | `exp(3914)` | `−1194` | `1426` | `exp(3915)` |

`v1` is what the paper obtained from Trudgian's 2014 explicit error term; this is what
`PrimeNumberTheoremAnd` obtains from modern estimates. The improvement is the whole reason
`DudekPlatt.v2` states a better threshold than `DudekPlatt.v1`.

## The constants are literals, and weaker than PNT+'s own

`PrimeNumberTheoremAnd` carries `Mₐ` and `mₐ` as *functions*, and bounds them:

* `Mₐ_exₐ_le_1426 : Mₐ exₐ ≤ 1426`
* `mₐ_xₐ_ge_neg1194 : (-1194 : ℝ) ≤ mₐ xₐ`

The literals below are those bounds, not the exact values. That direction is the safe one: a larger
`M` weakens the upper estimate and a more negative `m` weakens the lower one, so this conclusion is
*implied by* PNT+'s and is the weaker claim. Stating literals is what lets the threshold condition
be discharged by computation downstream.

**They are load-bearing to two significant figures.** At `log x = 3915` the criterion's threshold
condition clears by `0.4989`; there is about half a unit of slack, and loosening either constant
eats into it directly. That thinness is not accidental — `exp(3914)` was chosen to sit just inside
— but it means this is not a place to round generously.

## Not a bounded-range check

Like `v1`, and unlike `ButheNumerics.v1`, this quantifies over an unbounded range and rests on
analysis rather than on arithmetic over a finite window. It is `numerical` because its constants are
the output of a computation, not because the claim is a finite check.
-/

namespace DudekPlattNumerics.v2

open IEANTN

/-- The main term both halves share, `x Σ_{k=0}^{4} k!/(log x)^{k+1}`.

Spelled the same way in `DudekPlattNumerics.v1` and in `DudekPlatt.v3`. Repeated rather than
imported so each node stands alone. -/
noncomputable def mainTerm (x : ℝ) : ℝ :=
  x * ∑ k ∈ Finset.range 5, (Nat.factorial k : ℝ) / Real.log x ^ (k + 1)

/-- **The two-sided bound on `π(x)` at `PrimeNumberTheoremAnd`'s constants**: for every
`x > exp(3914)`,

`mainTerm x − 1194 · x/(log x)⁶ < π(x) < mainTerm x + 1426 · x/(log x)⁶`.

These are `mₐ_xₐ_ge_neg1194` and `Mₐ_exₐ_le_1426`, the literal bounds PNT+ proves on its own
constants, so this conclusion is implied by its `pi_lower_specific` and `pi_upper_specific` and is
the weaker claim.

Stated on the single range `x > exp(3914)` although `DudekPlatt.v3.criterion` needs the upper half
only above `exp(3915)`. Claiming both from the lower point is the stronger statement and is what
PNT+ supports; a consumer needing only the weaker one can restrict.

Carries `margin 0` factors — see `IEANTN.margin`. At index `0` the factor is `1`, so this says
exactly what it says without them. The sites mark the two constants, whose provenance is a
computation. **Raising either index would be a real weakening here**, since the downstream threshold
condition clears by only about `0.5`; that is the sort of thing a margin index is meant to make
visible rather than hide. -/
noncomputable def pi_two_sided_pnt : Prop :=
  ∀ x : ℝ, Real.exp 3914 < x →
    mainTerm x - margin 0 * (1194 * (x / Real.log x ^ (6 : ℕ))) < primeCounting x ∧
      primeCounting x < mainTerm x + margin 0 * (1426 * (x / Real.log x ^ (6 : ℕ)))

end DudekPlattNumerics.v2
