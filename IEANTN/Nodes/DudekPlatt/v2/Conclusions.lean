/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeCounting

/-!
# Node `DudekPlatt.v2`

**Ramanujan's inequality at the threshold `PrimeNumberTheoremAnd` reaches**, `exp(3915)`, rather
than the `exp(9658)` Dudek and Platt prove.

A **variant** of `DudekPlatt.v1`, not a successor. Both stay, and the distinction is the point:

* `DudekPlatt.v1` is what the *paper* proves. Its justification is a citation, and a citation may
  only claim what its source claims.
* this node is what a *better set of inputs* gives. Dudek–Platt's Lemma 2.1 is a pipeline; feed it
  a sharper two-sided estimate for `π` and the threshold drops. `PrimeNumberTheoremAnd`'s
  `ramanujan_final` does exactly that, reaching `exp(3915)` — its `xₐ = exp 3914` and threshold
  `exₐ = e·xₐ`.

Stating `exp(3915)` on `DudekPlatt.v1` would have attributed to the authors a result they did not
prove. Splitting the versions is how the network records "the same argument, better inputs" without
misciting anyone.

## What justifies this is not yet settled

`PrimeNumberTheoremAnd` proves `ramanujan_final` with no `sorry` in its own file, but its
transitive import closure spans 72 modules of which 14 carry sorries, and 19 use `native_decide` —
including `Ramanujan.lean` itself, at its lines 500 and 505. `native_decide` introduces
`Lean.ofReduceBool`, which Comparator forbids. Module-level closure is an upper bound on what a
given theorem actually depends on, so the decisive test is `#print axioms ramanujan_final` against
a built `PrimeNumberTheoremAnd`; that has not been run.

So this node is `none-yet` rather than `literature`: there is no paper to cite for `exp(3915)`, and
the Lean development that claims it has not been shown to meet this repository's axiom bound. It is
a target, and saying so plainly is more useful than dressing it as evidence.

## The paper names an intermediate threshold too

Footnote 1 of Dudek–Platt records that Mossinghoff–Trudgian's improved `R = 6.315` "can be used
with `a = 3130` to prove Theorem 1.2 for all `x ≥ exp(9394)`". That is a third threshold, on the
paper's own authority, and it is not stated anywhere yet — see `DudekPlattNumerics.v1`.
-/

namespace DudekPlatt.v2

open IEANTN

/-- **Ramanujan's inequality above `exp(3915)`.**

`π(x)² < (e x / log x) · π(x/e)` for every `x > exp(3915)`.

The same statement as `DudekPlatt.v1.ramanujan_inequality` at a smaller threshold, so this
conclusion is **strictly stronger** and implies it — `exp(3915) < exp(9658)`, and the inequality's
truth is monotone in the threshold. That implication is the natural bridge to write once either
node is justified, and it is why both can coexist without duplication of evidence.

Note the strict `<` on the threshold, matching `PrimeNumberTheoremAnd`'s
`∀ x > exₐ`, where `DudekPlatt.v1` has `≤` matching the paper's `x ≥ exp(9658)`. The difference is
at a single point and is transcription fidelity rather than mathematics, but a bridge has to
respect it. -/
noncomputable def ramanujan_inequality_3915 : Prop :=
  ∀ x : ℝ, Real.exp 3915 < x →
    primeCounting x ^ (2 : ℕ) < Real.exp 1 * x / Real.log x * primeCounting (x / Real.exp 1)

end DudekPlatt.v2
