/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Vocabulary: prime counting and the logarithmic integral

The prime-counting function and the two logarithmic integrals, in the real-variable form the
explicit analytic number theory literature states its estimates in.

Everything here is a **definition**.  Vocabulary carries no theorems: it exists so that two
different nodes stating an estimate about `π(x)` state it about *the same* `π(x)`, which is what
makes the dependency graph's edges real rather than decorative.
-/

namespace IEANTN

open scoped Nat
open Real MeasureTheory

/-- The prime-counting function `π(x)`, extended to a real variable: the number of primes `≤ x`.

For `x < 0` this is `0`, since `⌊x⌋₊ = 0`; that is the usual convention and matches the literature,
which only ever states estimates for `x` at least `2`. -/
noncomputable def primeCounting (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

/-- The Riemann prime-counting function `π*(x) = ∑_{k ≥ 1} π(x^{1/k}) / k`.

The sum is finite for every real `x`: `π(x^{1/k}) = 0` once `x^{1/k} < 2`. -/
noncomputable def riemannPrimeCounting (x : ℝ) : ℝ :=
  ∑' k : ℕ, primeCounting (x ^ (1 / (k + 1 : ℝ))) / (k + 1 : ℝ)

/-- The logarithmic integral `li(x) = ∫₀ˣ dt / log t`, taken in the principal-value sense at the
singularity `t = 1`.

**Junk-value warning.** This is defined as a `lim` of the symmetric truncations, so for `x` where
that limit does not exist the value is whatever `Classical.choice` supplies.  The limit *does*
exist for `x > 0`, which is the only range in which any node should state an estimate about `li`.
A statement about `li x` for unrestricted real `x` is very likely to be vacuous rather than false;
always carry a hypothesis pinning `x` into a range where the paper's claim is meant to apply. -/
noncomputable def li (x : ℝ) : ℝ :=
  Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0)) fun ε ↦
    ∫ t in Set.Ioc 0 x \ Set.Ioo (1 - ε) (1 + ε), 1 / Real.log t

/-- The offset logarithmic integral `Li(x) = ∫₂ˣ dt / log t`.

Unlike `li` this has no singularity in its range of integration, so it is an honest interval
integral and carries no junk-value hazard for `x ≥ 2`.  The two differ by the constant `li 2`
(the Ramanujan–Soldner constant, `1.0451…`). -/
noncomputable def Li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

end IEANTN
