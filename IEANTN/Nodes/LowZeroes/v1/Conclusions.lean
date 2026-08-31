/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta
import IEANTN.Vocabulary.Numerics

/-!
# Node `LowZeroes.v1`

Facts about the low-lying zeroes of `ζ` that come from a computation over a list of them rather
than from an argument.

At present there is one: the sum of the reciprocal ordinates below height `2 × 10⁴`, which
Chirre–Helfgott compute from David Platt's zero data and use in the proof of their Proposition
`vihuela` — the bound on the contribution of the zeros that produces `C_T`, the `√x` constant in
`CH2.v1`'s corollaries. Without it that constant cannot be obtained; no amount of analysis
substitutes for knowing where the low zeroes actually are.

## Why this is a `computation` node and not a `paper` one

The claim is not a theorem anybody proved on paper. Chirre and Helfgott write "by a brief
computation using the location of all `ρ` with `γ = Im ρ ≤ t₀` (furnished by D. Platt)", and the
authority is the computation together with Platt's data. That is what `computation` records: a
numerical verification split out so several papers can import it, with the understanding that
re-establishing it means re-running something rather than re-reading something.

## Intended to grow

Deliberately named for the class rather than the single fact. Other things about the low zeroes are
wanted elsewhere in the network and belong here when someone needs them — the ordinate of the first
zero, `14.134725…`, would sharpen `ZeroFreeHeight`, and further reciprocal-power sums appear
throughout the explicit-formula literature. Adding a conclusion here is cheaper than a new node each
time, and keeps the provenance — Platt's data — in one place.

## The `margin` sites

Both bounds carry a `margin 0` site. `margin 0 = 1`, so they say exactly what the paper says; the
factor marks the numbers as computationally provenanced, so that widening either later is a change
of one numeral rather than a change of shape. See `IEANTN.margin`.

## Junk values

`zetaZeroesSum` warns that `tsum` of a non-summable family is `0`. It does not bite here: there are
finitely many zeroes below a finite height, so the family has finite support and the sum is the
honest one. The `Set.Ioc 0 t` range also excludes the trivial zeroes, which sit at `Im ρ = 0`, so no
separate restriction to the critical strip is needed.
-/

namespace LowZeroes.v1

open IEANTN

/-- **The sum of reciprocal ordinates below height `2 × 10⁴`.**

`2 ∑_{0 < γ ≤ 2·10⁴} 1/γ = 10.319317…`, the zeroes counted with multiplicity, as computed by
Chirre–Helfgott from David Platt's data.

Stated as the two-sided bracket the ellipsis asserts — the displayed digits are correct, so the
value lies in `[10.319317, 10.319318)` — rather than as an equality, because an equality to a
truncated decimal would be false. A consumer needing only one side takes the half it needs.

Imports nothing: this is a fact about `ζ` with no network input. -/
noncomputable def sum_inv_ordinates_below_2e4 : Prop :=
  10.319317 / margin 0
      ≤ 2 * zetaZeroesSum Set.univ (Set.Ioc (0 : ℝ) (2 * 10 ^ (4 : ℕ)))
          (fun ρ ↦ 1 / (ρ : ℂ).im) ∧
    2 * zetaZeroesSum Set.univ (Set.Ioc (0 : ℝ) (2 * 10 ^ (4 : ℕ)))
        (fun ρ ↦ 1 / (ρ : ℂ).im)
      ≤ margin 0 * 10.319318

end LowZeroes.v1
