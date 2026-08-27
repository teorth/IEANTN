/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.RosserSchoenfeld.v1.Conclusions

/-!
# Bridge: Rosser–Schoenfeld's Theorem 1 to the network's usual shape

Theorem 1 states its region with a `log|t/17|` denominator. `Kadiri2005` consumes it in the plain
`1/(R log t)` form, at heights past `3.3 · 10⁹`. The first implies the second because
`log(t/17) ≤ log t`, so `1/(R log(t/17)) ≥ 1/(R log t)` and the paper's boundary lies to the *left*
of the plain one — the region it clears is strictly larger.

The point of doing this as a bridge rather than by simply stating the weaker form on the node is
that the weakening is then a proof rather than a transcription. The paper's own claim is written
down once, in its own shape, and what a consumer wants is derived from it and recompiled on every
push.

Both logarithms have to be positive for the reciprocals to compare the expected way, which is why
the `21` threshold is doing real work: at `t = 21`, `t/17` is `1.235…` and `log(t/17)` is `0.211…`.
Below `17` it would be negative and the inequality would reverse.
-/

namespace IEANTN.Bridges.RosserSchoenfeld

open IEANTN

/-- The `log(t/17)` region contains the plain classical one above the same height. -/
theorem bridge_to_classical (h : RosserSchoenfeld.v1.zero_free_region) :
    RosserSchoenfeld.v1.zero_free_region_classical := by
  intro σ t ht hσ
  refine h σ t ht (le_trans ?_ hσ)
  have h17 : (0 : ℝ) < t / 17 := by linarith
  have hlt : (1 : ℝ) < t / 17 := by linarith
  have hpos : 0 < Real.log (t / 17) := Real.log_pos hlt
  have hle : Real.log (t / 17) ≤ Real.log t := by
    apply Real.log_le_log h17
    linarith
  have hR : (0 : ℝ) < 9.645908801 := by norm_num
  have h1 : 0 < 9.645908801 * Real.log (t / 17) := by positivity
  have h2 : 9.645908801 * Real.log (t / 17) ≤ 9.645908801 * Real.log t := by nlinarith
  have : 1 / (9.645908801 * Real.log t) ≤ 1 / (9.645908801 * Real.log (t / 17)) :=
    one_div_le_one_div_of_le h1 h2
  linarith

end IEANTN.Bridges.RosserSchoenfeld
