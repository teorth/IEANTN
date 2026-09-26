/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastián Rodrigo (AI-assisted)
-/
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Vocabulary.Numerics

/-!
# Node `DudekPlattNumerics.v4`

The **same** two-sided bound on `π(x)` as `DudekPlattNumerics.v3`, at Dudek and Platt's own
**footnote 1** parameters — the improved zero-free region `R = 6.315` paired with `a = 3130` —
now derived by an actual Lean solution from an explicit, honestly-cited literature premise
(`MT.v2.corollary_1`) rather than resting on a Python-checked certificate. A **variant** of `.v3`,
not a replacement for it: same conclusion id, same statement, same constants; `.v3` stays exactly
as it was, still standing on its own `numerical` justification.

| `xₐ` | `m` | `M` | justification |
|---|---|---|---|
| `v1`, `a = 3223`, `R = 6.455` | `exp(9656.8)` | `−3103.33` | `3343.48` | `numerical` |
| `v2`, PrimeNumberTheoremAnd | `exp(3914)` | `−1194` | `1426` | `numerical` |
| `v3`, footnote 1, `a = 3130`, `R = 6.315` | `exp(9400)` | `−3010.333` | `3250.488` | `numerical` |
| `v4`, this node | `exp(9400)` | `−3010.333` | `3250.488` | Lean, modulo `MT.v2.corollary_1` |

## What is new here relative to `.v3`

`.v3`'s own docstring already gives the honest derivation: split the partial-summation integral
of `(θ(t)-t)/(t log²t)` from `2` to `x` at `x^{99/100}`, bound the near range by the elementary
`θ(t) ≤ t log t`, bound the far range by Mossinghoff–Trudgian's Corollary 1
(`|θ(x)-x| ≤ x·√(8/17π)·(log x/R)^{1/4}·e^{-√(log x/R)}`, monotone above `u = 441R/4`),
and assemble via five finite integrations by parts. `.v3` states that derivation in `README.md`
as written mathematics and checks its numerical inequalities with `certificate.py` in exact
rational arithmetic — real evidence, but not a Lean proof, and Corollary 1 itself was only
`traced` prose, not an importable node.

**This node makes both of those precise.** `MT.v2.corollary_1` now states Corollary 1 as its own
conclusion (`imports_status: identified`), so it is a real import here rather than a citation by
number proximity. Given that one conclusion as an explicit premise,
`Solutions/DudekPlattNumerics.v4` formalizes the *entire* remaining chain in Lean: the exact
`π(x) = S₅(x) + 120x/L⁶ + 720·I₇(x) - 2A + (θ(x)-x)/L + ∫₂ˣ(θ(t)-t)/(t log²t)dt` identity
from native partial summation and finite integration-by-parts (no primewise differentiation); the
elementary early-range bound; `f_R`'s monotonicity and the two endpoint certificates
`f_R(9400) < 3110`, `f_R(9306) < 3600`; the corrected normalized majorants (`D(L) < 1/2`, the `I₇`
majorant `< 1/10`, the finite-sum correction `< 1/1000`); and the real-`x` assembly recovering
exactly `.v3`'s `m = -3010.333`, `M = 3250.488` at `xₐ = exp(9400)`. Zero `sorry`, axioms exactly
`[propext, Classical.choice, Quot.sound]` — see
`formalization.yaml`'s justification note for what that solution rests on and what it does not
claim.

**What remains an explicit premise, and is not proved here.** `MT.v2.corollary_1` itself: the
zero-free-region-to-`θ` conversion argument (a contour integral against the zero-counting
function, following Trudgian's own recipe) is genuine analytic work no node in this network
currently formalizes. This node's Lean solution is therefore conditional on that one cited result,
exactly as its `formalization.yaml` records — completing the calculus around a literature input is
not the same as proving the input, and this docstring does not claim the latter.
-/

namespace DudekPlattNumerics.v4

open IEANTN

/-- The main term both halves share, `x Σ_{k=0}^{4} k!/(log x)^{k+1}`.

Spelled the same way in `DudekPlattNumerics.v1` and in `DudekPlatt.v3`. Repeated rather than
imported so each node stands alone. -/
noncomputable def mainTerm (x : ℝ) : ℝ :=
  x * ∑ k ∈ Finset.range 5, (Nat.factorial k : ℝ) / Real.log x ^ (k + 1)

/-- **The two-sided bound on `π(x)` at Dudek and Platt's own footnote 1 parameters**, `a = 3130`.

The identical statement to `DudekPlattNumerics.v3.pi_two_sided_footnote` — same threshold, same
two constants — restated under this node's own id so it can carry its own (conditional) Lean
solution rather than editing `.v3` in place. For every `x > exp(9400)`,

`mainTerm x − 3010.333 · x/(log x)⁶ < π(x) < mainTerm x + 3250.488 · x/(log x)⁶`.

See the module docstring for where `Mₐ = 3250.488`, `mₐ = −3010.333` and `xₐ = exp(9400)`
come from — computed from the paper's own eq. (8)–(9), not printed by the paper itself, which
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

end DudekPlattNumerics.v4
