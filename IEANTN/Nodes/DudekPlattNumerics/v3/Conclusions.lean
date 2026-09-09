/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Vocabulary.Numerics

/-!
# Node `DudekPlattNumerics.v3`

The two-sided bound on `π(x)` at Dudek and Platt's own **footnote 1** parameters — the improved
zero-free region `R = 6.315` paired with `a = 3130` — rather than the paper's main-text `a = 3223`,
`R = 6.455` (`DudekPlattNumerics.v1`) or `PrimeNumberTheoremAnd`'s constants (`.v2`).

A **variant**, not a successor: all three keep the same shape of claim — `π(x)` lies within
`m x/(log x)⁶` and `M x/(log x)⁶` of the fifth partial sum of `li`'s asymptotic expansion — and
differ in where the constants come from:

| | `xₐ` | `m` | `M` |
|---|---|---|---|
| `v1`, Dudek–Platt §2 main text, `a = 3223`, `R = 6.455` | `exp(9656.8)` | `−3103.33` | `3343.48` |
| `v2`, PrimeNumberTheoremAnd | `exp(3914)` | `−1194` | `1426` |
| `v3`, this node, footnote 1, `a = 3130`, `R = 6.315` | `exp(9400)` | `−3010.333` | `3250.488` |

## Where the numbers come from

Footnote 1 of the published Exp. Math. version (already transcribed onto `DudekPlattNumerics.v1`'s
own limitations) states: *"Mossinghoff–Trudgian's improved `R = 6.315` can be used with `a = 3130`
to prove Theorem 1.2 for all `x ≥ exp(9394)`."* The footnote prints only that final,
**unrepaired** threshold — not the intermediate `xₐ`, `mₐ`, `Mₐ` a reader would need to re-run the
*repaired* `DudekPlatt.v3.criterion` at this `(a, R)` pair, which is what this node supplies.

`mₐ`, `Mₐ` come from the paper's own eq. (8)–(9) (the same formula `DudekPlattNumerics.v1`
evaluates at `a = 3223`), evaluated here at `a = 3130`, `xₐ = exp(9400)`:

```
Mₐ = 120 + a + (a+720)/yₐ + (1792a+1290240)/yₐ² + ((5040+7a)/log⁸2)·yₐ⁶/√xₐ
mₐ = 120 − a − a/yₐ − 1792/yₐ² − 2A·yₐ⁶/xₐ − (7a·yₐ⁶)/(log⁸2·√xₐ),  A = Σₖ₌₁⁵ k!/log^{k+1}2
```

with `yₐ = log xₐ = 9400`. The last two terms of each (carrying `xₐ` or `√xₐ` in the denominator)
are of order `exp(−9400)`/`exp(−4700)`, utterly negligible next to a three-decimal rounding, and
the same formula evaluated instead at the paper's own printed `a = 3223`, `yₐ = 9656.8` reproduces
the paper's own printed `Mₐ = 3343.48`, `mₐ = −3103.33` to stated precision — a check that the
formula's *arithmetic* is transcribed faithfully. It is **not**, by itself, a certified derivation:
eq. (8)–(9) apply a θ-error bound valid only above `xₐ` inside a partial-summation integral that
starts at `t = 2`, and merely evaluating the printed formula does not bound that missing `[2, xₐ]`
range at a new `(a, R)` pair. [`README.md`](README.md) supplies that bound, working from
Mossinghoff-Trudgian's Corollary 1 directly rather than trusting eq. (8)-(9)'s implicit validity at
these parameters, and [`certificate.py`](certificate.py) checks the numerical inequalities in exact
rational arithmetic — the connecting calculus (partial summation, the integration-by-parts identity,
the `θ(t) ≤ t log t` elementary bound) remains written mathematics, not Lean-formalized.

**Why `xₐ = exp(9400)`.** The θ-bound this rests on, `|θ(x) − x| < a·x/log⁵x`, is valid for *every*
`x` above its own crossing point, not merely at one. `README.md` §2 makes this precise and exact:
`f_R(u) := √(8/17π)·(u/R)^(1/4)·e^{−√(u/R)}·u⁵` is strictly decreasing for `u > 441R/4 ≈ 696.23`,
and `certificate.py` certifies `f_R(9400) < 3110 < 3130` (the footnote's own `a`) directly from
Corollary 1's formula — no numerical root-finding. `README.md` §3–4 then bounds the **entire**
partial-summation integral, not just its tail above `xₐ`, giving an exact-rational-certified
two-sided `π` estimate for all real `x ≥ exp(9400)` that implies the `3250.488`/`−3010.333` above
with about `20` coefficient units of slack in each direction.

## `R = 6.315`'s provenance

Independently traceable to Mossinghoff–Trudgian, *Nonnegative trigonometric polynomials and a
zero-free region for the Riemann zeta-function*, J. Number Theory **157** (2015), 329–349 —
**the same paper `MT.v1` already holds** — §7, Corollary 1:
`|θ(x) − x| ≤ x·√(8/17π)·X^{1/2}e^{−X}`, `X = √(log x / 6.315)`, for `x ≥ 149`, proved from that
paper's own Theorem 1 (`MT.v1.zero_free_region`, `R₀ = 5.573412`). That proof, and hence Theorem 1
itself, **consumes** an established, computationally verified height, `T₀ = 3.06·10¹⁰` (the paper's
own §3; `MT.v1.zero_free_region` already imports `Platt2015.v1.rh_up_to`) — "unconditional" means
the height is *established*, not *absent*, unlike `MT.v1`'s other conclusion
`zero_free_region_sharpened` (§6.1), whose larger `3·10¹¹` height was, at publication, merely
*announced*. `README.md` §1 and `certificate.py` record this precisely. Even so, this is
*at least as well*-attested provenance as `DudekPlattNumerics.v1`'s own `R = 6.455`, which traces to
Trudgian solo (arXiv:1401.2689) using the very same established height for its own analogous
conversion, and to a paper this network does not hold as a node at all.

It is not, however, a drawable edge today, for the same reason `v1`'s `R = 6.455` isn't: `MT.v1`
states only its Theorem 1 and the §6.1 sharpened form, not Corollary 1, and even if it did, the
θ(x)-x → π(x) partial-summation conversion actually used here is not itself represented as a node.
See `README.md` and the `formalization.yaml` justification note for the full citation chain.
-/

namespace DudekPlattNumerics.v3

open IEANTN

/-- The main term both halves share, `x Σ_{k=0}^{4} k!/(log x)^{k+1}`.

Spelled the same way in `DudekPlattNumerics.v1` and in `DudekPlatt.v3`. Repeated rather than
imported so each node stands alone. -/
noncomputable def mainTerm (x : ℝ) : ℝ :=
  x * ∑ k ∈ Finset.range 5, (Nat.factorial k : ℝ) / Real.log x ^ (k + 1)

/-- **The two-sided bound on `π(x)` at Dudek and Platt's own footnote 1 parameters**, `a = 3130`:
for every `x > exp(9400)`,

`mainTerm x − 3010.333 · x/(log x)⁶ < π(x) < mainTerm x + 3250.488 · x/(log x)⁶`.

See the module docstring for where `Mₐ = 3250.488`, `mₐ = −3010.333` and `xₐ = exp(9400)` come
from — computed here from the paper's own eq. (8)–(9), not printed by the paper itself, which
names only the final unrepaired threshold `exp(9394)`.

Stated on the single range `x > exp(9400)`, matching `DudekPlattNumerics.v1`'s own shape (both
halves from the same lower point, stronger than `DudekPlatt.v3.criterion` strictly needs since its
upper half only wants `x > e·xₐ`).

Carries `margin 0` factors — see `IEANTN.margin`. At index `0` the factor is `1`, so this says
exactly what it says without them; the sites mark that both constants are the output of evaluating
a formula at a chosen `(a, R)`, matching `v1`'s and `v2`'s own use of the same device. -/
noncomputable def pi_two_sided_footnote : Prop :=
  ∀ x : ℝ, Real.exp 9400 < x →
    mainTerm x - margin 0 * (3010.333 * (x / Real.log x ^ (6 : ℕ))) < primeCounting x ∧
      primeCounting x < mainTerm x + margin 0 * (3250.488 * (x / Real.log x ^ (6 : ℕ)))

end DudekPlattNumerics.v3
