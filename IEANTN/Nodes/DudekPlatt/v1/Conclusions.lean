/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Vocabulary.Zeta

/-!
# Node `DudekPlatt.v1`

Adrian W. Dudek and David J. Platt, *On solving a curious inequality of Ramanujan*,
Exp. Math. **24** (2015), no. 3, 289–294.

**Ramanujan's inequality**, `π(x)² < (e x / log x) · π(x/e)`, asserted by Ramanujan in his notebooks
for sufficiently large `x`. This paper makes "sufficiently large" explicit, unconditionally and
under the Riemann hypothesis.

## The threshold is the paper's, not the best known

`Theorem 1.2` gives `x ≥ exp(9658)`. That is what this node states, because this node is the
*paper*, and a `literature` justification may only claim what its source claims.

Better thresholds exist and it is worth knowing where:

* the paper's own **footnote 1** notes that Mossinghoff–Trudgian's improved `R = 6.315` "can be used
  with `a = 3130` to prove Theorem 1.2 for all `x ≥ exp(9394)`";
* `PrimeNumberTheoremAnd` proves `exp(3915)`, using modern estimates in place of Trudgian's. That is
  `DudekPlatt.v2` — a variant, not a successor, and not something Dudek and Platt claim.

Anyone tempted to state `exp(3915)` here should not: it would attribute to the authors a result
they did not prove. That distinction is the reason these are separate nodes.

## The two theorems are of different kinds

Theorem 1.2 is unconditional. Theorem 1.3 assumes the Riemann hypothesis and is **sharp** — it
identifies the largest integer counterexample rather than bounding it — so it is stated as the
equality it is, not weakened to an inequality.
-/

namespace DudekPlatt.v1

open IEANTN

/-- **Theorem 1.2.** Ramanujan's inequality `π(x)² < (e x / log x) · π(x/e)` holds unconditionally
for every `x ≥ exp(9658)`.

The paper reaches this by applying its Lemma 2.1 to the two-sided estimate for `π` recorded as
`DudekPlattNumerics.v1.pi_two_sided_paper`: at `a = 3223` that estimate holds above
`xₐ = exp(9656.8)`, and Lemma 2.1's threshold `e·xₐ = exp(9657.8)` rounds up to the `exp(9658)`
printed here.

So this conclusion is the composite of a pipeline and a numerical input, and both are recorded as
imports. Once the pipeline is a node with a proof, this becomes derivable rather than asserted;
until then it rests on the paper. -/
noncomputable def ramanujan_inequality : Prop :=
  ∀ x : ℝ, Real.exp 9658 ≤ x →
    primeCounting x ^ (2 : ℕ) < Real.exp 1 * x / Real.log x * primeCounting (x / Real.exp 1)

/-- **Theorem 1.3.** On the Riemann hypothesis, the largest integer counterexample to Ramanujan's
inequality is `38 358 837 682`.

Sharp, and stated sharply: the inequality fails at that integer and holds at every larger one. A
version weakened to "holds for `x > 38358837682`" would lose the paper's actual result, which is
that this is the *last* failure.

The hypothesis is `RiemannHypothesis` itself, not a partial verification to a finite height — the
paper leans on Schoenfeld's conditional bound `|π(x) − li(x)| < (1/8π) √x log x` for `x ≥ 2657`,
which needs the full hypothesis. A node supplying only `RiemannHypothesisUpTo T` does **not**
discharge this. -/
noncomputable def largest_counterexample_on_rh : Prop :=
  RiemannHypothesis →
    ¬ (primeCounting 38358837682 ^ (2 : ℕ) <
        Real.exp 1 * 38358837682 / Real.log 38358837682 *
          primeCounting (38358837682 / Real.exp 1)) ∧
      ∀ n : ℕ, 38358837682 < n →
        primeCounting n ^ (2 : ℕ) <
          Real.exp 1 * n / Real.log n * primeCounting ((n : ℝ) / Real.exp 1)

end DudekPlatt.v1
