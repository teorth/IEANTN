/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Vocabulary.Numerics

/-!
# Node `DudekPlattNumerics.v1`

The explicit two-sided bound on `π(x)` that Dudek and Platt feed into their Lemma 2.1, separated
from the analysis that consumes it.

Adrian W. Dudek and David J. Platt, *On solving a curious inequality of Ramanujan*,
Exp. Math. **24** (2015), no. 3, 289–294.

Same paper as `DudekPlatt.v1`, different kind of claim. The paper's route to Ramanujan's inequality
is a pipeline — its Lemma 2.1 — fed by a numerical input, and this node is the input.

## What the paper actually does

Lemma 2.1 says: if for `x > xₐ`

`x Σ_{k=0}^{4} k!/(log x)^{k+1} + mₐ x/(log x)⁶ < π(x)`  and
`π(x) < x Σ_{k=0}^{4} k!/(log x)^{k+1} + Mₐ x/(log x)⁶`,

then Ramanujan's inequality holds above a threshold determined by `mₐ`, `Mₐ` and `xₐ`.

The paper then chooses parameters. From §2: "It can be verified that choosing `a = 3223` gives
`xₐ = exp(9656.8)` with the values `mₐ = −3103.33`, `Mₐ = 3343.48`. One then computes, using
Lemma 2.1, that `xₐ = exp(9657.8)` will work." That is `e · exp(9656.8) = exp(9657.8)`, which
confirms the lemma's threshold is `e·xₐ` rather than `e^{xₐ}` — and `exp(9657.8)` rounded up is the
`exp(9658)` of Theorem 1.2.

The bound below is that input, at those parameters. It rests in turn on Trudgian's explicit error
term for `θ(x)` — the paper's Lemma 2.2, with `R = 6.455` — which the network does not yet hold.

## The improvement the paper flags in a footnote

Footnote 1 records that Mossinghoff–Trudgian improved `R` in Lemma 2.2 to `6.315`, "which can be
used with `a = 3130` to prove Theorem 1.2 for all `x ≥ exp(9394)`". So the paper itself names a
better threshold than its own theorem. The network holds `MTY.v1` and `MT.v1`; whether either
supplies that `R` has not been checked here, and doing so would let `exp(9394)` be stated with an
edge rather than on a footnote's authority.

`PrimeNumberTheoremAnd` reaches `exp(3915)`, far better again, by using modern estimates in place
of Trudgian's. Its constants are `Mₐ(exₐ)` and `mₐ(xₐ)` evaluated at `xₐ = exp 3914`; they are
functions there rather than literals, and are not transcribed here.
-/

namespace DudekPlattNumerics.v1

open IEANTN

/-- The main term of Dudek–Platt's two-sided estimate:
`x Σ_{k=0}^{4} k!/(log x)^{k+1}`.

Node-local, because both halves of the estimate share it and nothing else has wanted it. This is
the fifth partial sum of the asymptotic expansion of `li(x)`, which is why the error is measured
against `x/(log x)⁶`. -/
noncomputable def mainTerm (x : ℝ) : ℝ :=
  x * ∑ k ∈ Finset.range 5, (Nat.factorial k : ℝ) / Real.log x ^ (k + 1)

/-- **The two-sided bound on `π(x)` at the parameters Dudek and Platt choose**, from §2 of the
paper: for every `x > exp(9656.8)`,

`mainTerm x − 3103.33 · x/(log x)⁶ < π(x) < mainTerm x + 3343.48 · x/(log x)⁶`.

These are the `mₐ = −3103.33`, `Mₐ = 3343.48` and `xₐ = exp(9656.8)` the paper obtains at
`a = 3223`, and they are what its Lemma 2.1 is applied to in order to get Theorem 1.2. Stated as
one conclusion rather than two because the lemma consumes them together, and neither half alone is
of any use to it.

A finite computation in the sense that matters here — its constants come from evaluating an
explicit formula at a chosen `a`, not from an argument — so `numerical`. It is not, however, a
bounded-range check like `ButheNumerics.v1`'s: it quantifies over all `x > exp(9656.8)` and rests
on Trudgian's explicit `θ` error term, which is analysis. If that input ever becomes a node, this
conclusion should gain an import and may become derivable rather than asserted.

Carries a `margin 0` factor on each side — see `IEANTN.margin`. At index `0` the factor is `1`, so
this says exactly what it says without them. The sites are here because both constants are the
output of a numerical optimisation over `a`, which is precisely the provenance a margin marks. -/
noncomputable def pi_two_sided_paper : Prop :=
  ∀ x : ℝ, Real.exp 9656.8 < x →
    mainTerm x - margin 0 * (3103.33 * (x / Real.log x ^ (6 : ℕ))) < primeCounting x ∧
      primeCounting x < mainTerm x + margin 0 * (3343.48 * (x / Real.log x ^ (6 : ℕ)))

end DudekPlattNumerics.v1
