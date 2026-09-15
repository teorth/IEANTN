/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `PlattZeroSum.v1`

A single numerical fact about the low zeroes of `ζ`: the sum of the reciprocal ordinates of the
non-trivial zeroes up to height `2·10⁴`, counted with multiplicity,

`2 ∑_{0 < γ ≤ 2·10⁴} 1/γ = 10.319317…`.

## Where it comes from and why it is a node

Chirre–Helfgott (arXiv:2512.15709) use it in the proof of their Proposition `prop:vihuela`, the
bound on the weighted sum over non-trivial zeroes that produces the `√x` coefficient
`C_T = (1/2π) log²(T/2π) − (1/6π) log(T/2π)` of their Corollary 1.2. They obtain the value "by a
brief computation using the location of all `ρ` with `γ ≤ t₀` (furnished by D. Platt)", with
`t₀ = 2·10⁴`, about twenty-one thousand zeroes.

It cannot be replaced by zero-counting estimates. The paper writes the value as
`(1/2π) log²(t₀/2π) − 0.03435…`, and the negative constant is what pays for the improvement from
`1.01/(6π)` down to the headline `1/(6π)`; the Riemann–von Mangoldt error terms at this height are
of order `10⁻¹`, where the whole margin is below `10⁻²`. And it cannot be proved in Lean: it needs
the ordinates themselves. So it is stated once, here, and consumed as an import.

## The statement

Only the upper bound is needed, and only the upper bound is stated, rounded up in the fifth
decimal: `10.3194` against the paper's `10.319317…`.

**Junk values.** `zetaZeroesSum` is a `tsum`; were the family not summable it would be `0` and the
bound would hold vacuously. It is summable — the zeroes with `0 < Im ≤ 2·10⁴` are finitely many —
but that is a theorem, not part of this statement. A consumer relying on this node for a *lower*
bound would be misled by the junk value; none does.
-/

namespace PlattZeroSum.v1

open IEANTN

/-- **The reciprocal-ordinate sum up to `2·10⁴`.** Counting non-trivial zeroes `ρ` of `ζ` with
multiplicity `m(ρ)`,

`2 ∑_{0 < Im ρ ≤ 20000} m(ρ)/Im ρ ≤ 10.3194`.

The index set is `zetaZeroesIn Set.univ (Set.Ioc 0 20000)`: every zero with positive imaginary part
is non-trivial, so no restriction on the real part is needed. The height `20000` is included,
matching the paper's `γ ≤ t₀`. -/
def inv_ordinate_sum_le : Prop :=
  2 * zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ ↦ 1 / ρ.im) ≤ (10.3194 : ℝ)

end PlattZeroSum.v1
