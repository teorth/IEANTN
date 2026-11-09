/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcos Adriano
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.Numerics

/-!
# Node `FKSNumerics.v1`

The numerical work behind `FKS`'s classical bound, separated from the analysis that produces its
inputs, as `FKS2Numerics.v1` does for `FKS2` and `BKLNWNumerics.v1` for `BKLNW`.

Fiori, Kadiri and Swidinsky's `Eψ(x) ≤ 121.096 (log x / R)^{3/2} exp(−2 √(log x / R))` for
`x ≥ 2` (`FKS.v2.psi_classical_bound`) rests on ranges of `log x` with different evidence. Below
`e²¹⁰⁰` it reduces to Mathlib and `BKLNW`'s Table 8. Between `e²¹⁰⁰` and `e²⁰⁰⁰⁰⁰` it is a
computation: the proof of Lemma 5.3 evaluates Theorem 1.1's `ε(x₀)` on a grid and interpolates the
values as a step function. Above `e²⁰⁰⁰⁰⁰` it is Theorem 1.2 at one row of its table. This node
states the second and, provisionally, the third.

## What is here, and what is not

* `psi_classical_mid_range`: the classical bound with `A = 121.096` on `[e²¹⁰⁰, e²⁰⁰⁰⁰⁰]`, folded
  into one claim as `FKS2Numerics.v1.corollary_22_mid_range` folds `FKS2`'s interpolation over these
  same subdivisions.
* `psi_classical_above_e200000`: the classical bound with `A = 121.0360` for `x ≥ e²⁰⁰⁰⁰⁰`. This is
  analysis plus one evaluation, not a finite check, and it is here only until a pipeline node states
  Theorem 1.2 with `A(x₀)` as a function; then `A(e²⁰⁰⁰⁰⁰) ≤ 121.0360` is what stays here. That
  placement is the one proposed on issue #52.

Not here: the data `A(x₀)` would read once it is a function (Table 1's `S₀(T₀)` and the
zero-density table), which belongs with that pipeline.

## The computation behind the middle range

For points `b_i` dividing `[2100, 200000]` the proof checks `121.096 · f(b_{i+1}) > ε(e^{b_i})`,
where `f(y) = (y/R)^{3/2} exp(−2 √(y/R))` and `ε(x₀)` is Theorem 1.1's bound, `Eψ(x) ≤ ε(x₀)` for
all `x ≥ x₀`. Since `f` decreases for `y > 9R/4 ≈ 12.52`, each check covers every `x` with
`b_i ≤ log x ≤ b_{i+1}`, the right endpoint included. The step sizes of the paper's table give
49 400 points, and the paper reports "over 4000 cpu/hours".

The table (arXiv v2 and v3 alike), per range of `b_i`: the step, the largest `ε(e^b) / f(b)`, the
largest `f(b) / f(b + step)`, and the "Bound on `A`", their product rounded up.

| range of `b_i` | step | max `ε/f` | at `b` | max ratio | bound on `A` |
|---|---|---|---|---|---|
| `[2100, 6000)` | `1/2` | `120.400` | `5999.5` | `1.0050` | `121.002` |
| `[6000, 7250)` | `1/5` | `120.894` | `7249.8` | `1.0011` | `121.027` |
| `[7250, 8250)` | `1/10` | `121.035` | `7914.3` | `1.0005` | `121.096` |
| `[8250, 9000)` | `1/5` | `120.805` | `8250` | `1.0009` | `120.913` |
| `[9000, 12000)` | `1` | `119.416` | `9000` | `1.0050` | `120.014` |
| `[12000, 100000)` | `5` | `113.332` | `12000` | `1.0190` | `115.486` |
| `[100000, 200000)` | `100` | `84.520` | `100000` | `1.1420` | `96.522` |

`121.096` is the largest entry, which is why it is the constant stated. The per-range constants
are not stated: nothing in the network consumes them, and they sit closer to the unprinted
`ε(e^{b_i})` than the fold does. The review notes in `formalization.yaml` record what was checked.

## Margin

As in `FKS2Numerics.v1`, both bounds carry a `margin 0` factor from Vocabulary. `margin 0 = 1`, so
each says exactly what the paper says; the factor marks a number whose provenance is a computation.

These two have no room for a deeper margin, and that is worth knowing before anyone raises one. The
consumer is the classical bound with `121.096`, which is itself the largest entry of the table
above, so the middle range has no slack at all; and `121.096 / 121.0360 = 1.0005`, less than
`margin 1 = 1.001`. Raising either index breaks the assembly of `FKS`'s classical bound unless its
constants are recomputed with more digits.

## Lemma 5.2 is not involved

The range below `e²¹⁰⁰` is not stated here, so nothing here rests on Lemma 5.2, which is false as
printed on `(1, 2.2901308748…)` (issue #52).
-/

namespace FKSNumerics.v1

open IEANTN

/-- **The middle range of the classical bound**: for every `x` in `[e²¹⁰⁰, e²⁰⁰⁰⁰⁰]`,
`Eψ(x) ≤ 121.096 (log x / R)^{3/2} exp(−2 √(log x / R))`, with `R = 5.5666305`.

This is the form the proof of Lemma 5.3 checks. The lemma's printed statement is the rescaled one,
`Eψ(x) ≤ 9.22022 (log x)^{3/2} exp(−0.8476836 √(log x))` on `2100 < log x ≤ 200000`, and follows
from this because `121.096 / R^{3/2} < 9.22022`; `IEANTN.Bridges.FKS.ClassicalToAllX` does that
arithmetic for the all-`x` bound.

Stated on the closed window `Set.Icc`: the proof's grid starts at `b = 2100` and its last step ends
at `b = 200000`, so both ends are checked, even though the printed lemma opens at `2100`.

Up to the `margin 0` factor this is `FKS.v2.psi_classical_bound` restricted to the window, so an
assembled proof of that conclusion can use it on this range as it stands. -/
def psi_classical_mid_range : Prop :=
  ∀ x ∈ Set.Icc (Real.exp 2100) (Real.exp 200000),
    Eψ x ≤ margin 0 * admissibleBound 121.096 (3 / 2) 2 5.5666305 x

/-- **The range above `e²⁰⁰⁰⁰⁰`**: for every `x ≥ e²⁰⁰⁰⁰⁰`,
`Eψ(x) ≤ 121.0360 (log x / R)^{3/2} exp(−2 √(log x / R))`, with `R = 5.5666305`.

Theorem 1.2 says that for `log x₀ > 1000`, and `R ≤ 5.573412` a zero-free-region constant,
`Eψ(x) ≤ A(x₀) (log x / R)^{3/2} exp(−2 √(log x / R))` for all `x ≥ x₀`, and that each pair
`(x₀, A(x₀))` of its table gives such a bound with `R = 5.5666305`. This is the row
`log x₀ = 200000`, where the table prints `121.0360` (arXiv v2 and v3 alike). The proof of
Corollary 1.4 uses exactly this for `log x > 200000`.

**Provisional.** Theorem 1.2 is analysis, not a computation. This conclusion is here so that an
assembled `FKS` has an edge to import while no node states Theorem 1.2; once one does, with `A(x₀)`
as a function, this should shrink to the evaluation `A(e²⁰⁰⁰⁰⁰) ≤ 121.0360`. -/
def psi_classical_above_e200000 : Prop :=
  ∀ x ≥ Real.exp 200000, Eψ x ≤ margin 0 * admissibleBound 121.0360 (3 / 2) 2 5.5666305 x

end FKSNumerics.v1
