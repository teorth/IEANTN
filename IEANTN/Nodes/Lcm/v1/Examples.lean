/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.Lcm.v1.Conclusions

/-!
# Examples: `Lcm.v1`

Consequences drawn from this node's conclusions, to show what the node actually buys.

An examples file is optional, makes no claims of record, and is therefore not fingerprinted. Two
rules apply, and both are checked by `ieantn.py check-closure`:

* it may not import the node's `Challenge`, which is sorried -- an example resting on that `sorry`
  would prove anything while looking exactly like one that proves something;
* it may not contain `sorry` itself, for the same reason.

So every example here takes the conclusion as a *hypothesis* and derives something from it. That is
the useful shape: it exhibits the statement's force without assuming it is true, and it is a cheap
guard against a conclusion that typechecks but says less than its docstring claims.
-/

namespace Lcm.v1

/-- The conclusion applies at any concrete threshold past `89693² = 8044834249`.

Worth stating because the quantifier and the cast are exactly where a transcription error would
hide: if the bound had been written over `ℝ`, or the inequality the wrong way round, this would not
elaborate. -/
example (h : lcmUpto_not_highlyAbundant) : ¬ HighlyAbundant (Nat.lcmUpto (10 ^ 10)) :=
  h (10 ^ 10) (by norm_num)

/-- The conclusion is a statement about *every* sufficiently large `n`, not merely infinitely many.

This is the difference between what this node proves and what Alaoglu and Erdős asserted without
proof in 1944; see the node's `formalization.yaml`. An example is the cheapest way to keep that
distinction visible to a reader who only skims the Lean. -/
example (h : lcmUpto_not_highlyAbundant) :
    ∀ n : ℕ, 89693 ^ 2 ≤ n → ¬ HighlyAbundant (Nat.lcmUpto n) :=
  h

end Lcm.v1
