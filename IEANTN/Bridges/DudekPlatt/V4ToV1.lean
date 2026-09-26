/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastián Rodrigo (AI-assisted)
-/
import IEANTN.Nodes.DudekPlatt.v1.Conclusions
import IEANTN.Nodes.DudekPlatt.v4.Conclusions

/-!
# Bridge: `DudekPlatt.v4` to `.v1`

`.v4` proves Ramanujan's inequality above `exp(9401)`; `.v1` is the paper's own printed threshold
`exp(9658)`. Since `.v4`'s conclusion is `∀ x, exp 9401 < x → …` and `exp(9401) < exp(9658)`, every
`x` satisfying `.v1`'s hypothesis `exp 9658 ≤ x` also satisfies `.v4`'s `exp 9401 < x`, so `.v4`'s
conclusion is **strictly stronger** and implies `.v1`'s pointwise. This is the same
monotone-in-the-threshold relationship `DudekPlatt.v2`'s `exp(3915)` already has to `.v1` (see
`.v2`'s own module docstring), transported through `.v4` instead.

This closes issue #63's own request directly: the paper's printed `exp(9658)` is now reachable,
inside this network, from the repaired criterion (`DudekPlatt.v3`, itself `lean-comparator`
verified) and the footnote-improved two-sided `π` estimate (`DudekPlattNumerics.v3`), with `257`
log-units to spare — see `Solutions/DudekPlatt.v4/Endpoint.lean` for the composed witness closing
that whole chain in one proof term.

**This bridge imports only `Conclusions.lean` files — no `Challenge`, no `Solution`, no `sorry`.**
It is registered as a second, **non-designated** `bridged` justification on `DudekPlatt.v1`'s
`ramanujan_inequality` conclusion (see that node's `formalization.yaml`): `.v1` keeps its own
`literature` citation as the designated ground of record, exactly as `.v2`'s own (as yet
unregistered) relationship to `.v1` does, and this bridge records that an independent,
unconditional-of-the-paper's-own-defective-lemma route to the identical statement is now also
machine-checked in the core build. -/

theorem DudekPlatt.v4.ramanujan_inequality_of_9401_to_v1
    (h : DudekPlatt.v4.ramanujan_inequality_9401) :
    DudekPlatt.v1.ramanujan_inequality := by
  intro x hx
  exact h x (lt_of_lt_of_le (Real.exp_lt_exp.mpr (by norm_num : (9401 : ℝ) < 9658)) hx)
