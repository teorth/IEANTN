/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcos Adriano, Terence Tao
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Node `FKS.v3`

Fiori, Kadiri and Swidinsky, *Sharper bounds for the Chebyshev function `ψ(x)`*,
J. Math. Anal. Appl. **527** (2023), Paper No. 127426.

The same two conclusions as `FKS.v2`, word for word. What changes is what they rest on. `FKS.v2`
cites the paper, through `FKS.v1`. This version assembles the classical bound from three imported
claims and Mathlib, following the ranges of the paper's own proof of Corollary 1.4, and derives the
all-`x` bound from it. `Solutions/FKS.v3` is that assembly.

## The ranges

* `log x ∈ [log 2, 40]`: Mathlib gives `Eψ x ≤ 2`, and the right-hand side stays above `2`. No
  import.
* `log x ∈ [40, 2100]`: the rows `b = 40` and `b = 1000` of `BKLNW`'s Table 8. Import
  `BKLNW.v1.table8_psi_bound_above`.
* `log x ∈ [2100, 200000]`: the interpolation in the proof of Lemma 5.3. Import
  `FKSNumerics.v1.psi_classical_mid_range`.
* `log x ≥ 200000`: Theorem 1.2, with `A(e²⁰⁰⁰⁰⁰) = 121.0360`. Import
  `FKSNumerics.v1.psi_classical_above_e200000`.

The paper's proof covers `log x ≤ 2100` with its Lemma 5.2, which is false as printed for
`1 < x < 2.2901308748…` (issue #52). The assembly does not use it: below `e²¹⁰⁰` it uses Mathlib and
the two rows of Table 8 that Lemma 5.2's own proof uses.

## What is taken on trust

The three imports and nothing else. The first is `BKLNW`'s. The other two are `FKS`'s own
numerics, and the third is provisional: it is Theorem 1.2 at one row of its table, stated on
`FKSNumerics.v1` until a node states Theorem 1.2 itself.

## Numbering

The published version numbers the all-`x` bound Corollary 1.4 and has no Corollary 1.3; `FKS2`'s
"Corollary 1.3" is the arXiv v1 number. The classical form with `A = 121.096` is not a numbered
statement in any version: in arXiv v2 and v3 it appears only in the proof of Lemma 5.3, whose table
has `121.096` as its largest "Bound on `A`". Lemma numbers here are arXiv v3's.
-/

namespace FKS.v3

open IEANTN

/-- **The all-`x` bound** (published Corollary 1.4).

`Eψ(x) < 9.22022 (log x)^{3/2} exp(−0.8476836 √(log x))` for every `x > 2`.

Identical to `FKS.v2.psi_bound_all_x`. The solution derives it from `psi_classical_bound` by the
arithmetic of `IEANTN.Bridges.FKS.ClassicalToAllX`, the direction the paper's proof of Lemma 5.3
runs: "We now simply verify that `121.096/5.5666305^{3/2} < 9.22022`". -/
def psi_bound_all_x : Prop :=
  ∀ x > (2 : ℝ), Eψ x < 9.22022 * (Real.log x) ^ ((3 : ℝ) / 2) *
    Real.exp (-0.8476836 * Real.sqrt (Real.log x))

/-- **The classical bound, from the paper's own threshold** `x₀ = 2`.

`Eψ x ≤ 121.096 (log x / R)^{3/2} exp(−2 √(log x / R))` for every `x ≥ 2`, with `R = 5.5666305`.

Identical to `FKS.v2.psi_classical_bound`. `R` is Mossinghoff and Trudgian's zero-free region
constant, not this paper's; `MTY.v1` has a sharper one, and it is the first thing to change when
the chain is re-run. -/
def psi_classical_bound : Prop :=
  HasClassicalBound Eψ 121.096 (3 / 2) 2 5.5666305 2

end FKS.v3
