/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcos Adriano
-/
import IEANTN.Bridges.FKS.ThresholdTwo

/-!
# Bridge: `FKS.v1.psi_bound_all_x` follows from `FKS.v1.psi_classical_bound`

The node records its two conclusions as independent, and the note on `psi_bound_all_x` explains
why rescaling it into `psi_classical_bound` cannot close: both roundings go the strengthening way.
For the same reason they go the *weakening* way in the other direction, which is the one the paper
takes in the proof of its Lemma 5.3 ("`121.096 / 5.5666305^{3/2} < 9.22022`"). With `q = √R` and
`w = √(log x / R)`, so that `√(log x) = q w`:

* `121.096 < 9.22022 q³`, which is `FKS.v1.rescaled_A_exceeds_printed`;
* `0.8476836 q < 2`, which is `FKS.v1.rescaled_C_is_short_of_two`;

hence `121.096 w³ e^{−2w} < 9.22022 (q w)³ e^{−0.8476836 q w}` for every `w > 0`, which is the
all-`x` bound. It is needed from `x = 2` on, and `ThresholdTwo` supplies the classical bound there
from the `e³⁰` form. No margin index is involved.
-/

namespace IEANTN.Bridges.FKS

open IEANTN Real

/-- `√R` for `R = 5.5666305`, to seven decimals. -/
lemma sqrt_R_bounds : 2.3593705 < √(5.5666305 : ℝ) ∧ √(5.5666305 : ℝ) < 2.3593708 := by
  constructor
  · rw [lt_sqrt (by norm_num)]
    norm_num
  · rw [sqrt_lt' (by norm_num)]
    norm_num

/-- `R^{3/2} = R √R`, so the node comparison is an endpoint bound on `√R`. -/
lemma rpow_three_halves : (5.5666305 : ℝ) ^ ((3 : ℝ) / 2) = 5.5666305 * √(5.5666305 : ℝ) := by
  have hpos : (0 : ℝ) < 5.5666305 := by norm_num
  have hsplit : ((3 : ℝ) / 2) = (1 : ℝ) + (1 / 2) := by norm_num
  rw [hsplit, rpow_add hpos, rpow_one, sqrt_eq_rpow]

/-- **`FKS.v1.rescaled_A_exceeds_printed`.** Lemma 5.3's check
`121.096 / R^{3/2} < 9.22022`, written as `9.22022 R^{3/2} > 121.096`.

`√R > 2.3593705` and `9.22022 · R · 2.3593705 > 121.096` are both `norm_num`. The product of
those two facts is the node statement, which the rescaling below used to re-derive inline. -/
theorem rescaled_A_exceeds_printed : FKS.v1.rescaled_A_exceeds_printed := by
  unfold FKS.v1.rescaled_A_exceeds_printed
  rw [rpow_three_halves]
  have hsqrt := sqrt_R_bounds.1
  have hnum : (121.096 : ℝ) < 9.22022 * 5.5666305 * 2.3593705 := by norm_num
  have hpos : (0 : ℝ) < 9.22022 * 5.5666305 := by norm_num
  have hmul : 9.22022 * 5.5666305 * 2.3593705 < 9.22022 * 5.5666305 * √(5.5666305 : ℝ) :=
    mul_lt_mul_of_pos_left hsqrt hpos
  linarith

/-- **`FKS.v1.rescaled_C_is_short_of_two`.** `0.8476836 √R < 2`, so the printed `C = 2` is
stronger than the rescaling of Corollary 1.4. `√R < 2.3593708` and
`0.8476836 · 2.3593708 < 2` are both `norm_num`. -/
theorem rescaled_C_is_short_of_two : FKS.v1.rescaled_C_is_short_of_two := by
  unfold FKS.v1.rescaled_C_is_short_of_two
  have hsqrt := sqrt_R_bounds.2
  have hnum : (0.8476836 : ℝ) * 2.3593708 < 2 := by norm_num
  have hmul : 0.8476836 * √(5.5666305 : ℝ) < 0.8476836 * 2.3593708 :=
    mul_lt_mul_of_pos_left hsqrt (by norm_num)
  linarith

/-- A positive square root is the number whose square is `R`. -/
lemma q_eq_sqrt {q : ℝ} (hq0 : 0 ≤ q) (hq2 : q ^ 2 = (5.5666305 : ℝ)) :
    q = √(5.5666305 : ℝ) := by
  rw [← sqrt_sq hq0, hq2]

/-- The rescaling, in `q = √R` and `w = √(log x / R)`.

Both numerical comparisons are the node conclusions, not a second copy of the arithmetic. -/
lemma rescaled_lt {q w : ℝ} (hw : 0 < w) (hq_lo : 2.3593705 < q) (_hq_hi : q < 2.3593708)
    (hq2 : q ^ 2 = 5.5666305) :
    121.096 * w ^ 3 * exp (-2 * w) < 9.22022 * (q * w) ^ 3 * exp (-0.8476836 * (q * w)) := by
  have hq : q = √(5.5666305 : ℝ) := q_eq_sqrt (by linarith) hq2
  have hC : (0.8476836 : ℝ) * q < 2 := by
    rw [hq]
    exact rescaled_C_is_short_of_two
  have hexp : exp (-2 * w) ≤ exp (-0.8476836 * (q * w)) := exp_le_exp.mpr (by nlinarith)
  have hq3 : (121.096 : ℝ) < 9.22022 * q ^ 3 := by
    have hA := rescaled_A_exceeds_printed
    unfold FKS.v1.rescaled_A_exceeds_printed at hA
    rw [rpow_three_halves, ← hq] at hA
    have h3 : q ^ 3 = 5.5666305 * q := by rw [show q ^ 3 = q ^ 2 * q by ring, hq2]
    rw [h3]
    exact hA
  have hw3 : 0 < w ^ 3 := pow_pos hw 3
  calc 121.096 * w ^ 3 * exp (-2 * w)
      ≤ 121.096 * w ^ 3 * exp (-0.8476836 * (q * w)) :=
        mul_le_mul_of_nonneg_left hexp (mul_pos (by norm_num) hw3).le
    _ < 9.22022 * q ^ 3 * w ^ 3 * exp (-0.8476836 * (q * w)) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hq3 hw3) (exp_pos _)
    _ = 9.22022 * (q * w) ^ 3 * exp (-0.8476836 * (q * w)) := by ring

/-- Past `x = 1`, the classical right-hand side is below the all-`x` one. -/
lemma admissibleBound_lt_all_x {x : ℝ} (hx : 1 < x) :
    admissibleBound 121.096 (3 / 2) 2 5.5666305 x <
      9.22022 * log x ^ ((3 : ℝ) / 2) * exp (-0.8476836 * √(log x)) := by
  have hL : 0 < log x := log_pos hx
  have ht : 0 < log x / 5.5666305 := div_pos hL (by norm_num)
  obtain ⟨hq_lo, hq_hi⟩ := sqrt_R_bounds
  have h32 : (log x / 5.5666305) ^ ((3 : ℝ) / 2) = √(log x / 5.5666305) ^ 3 := by
    rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul ht.le]
    norm_num
  have hL32 : log x ^ ((3 : ℝ) / 2) = √(log x) ^ 3 := by
    rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hL.le]
    norm_num
  have hsplit : √(log x) = √(5.5666305 : ℝ) * √(log x / 5.5666305) := by
    rw [← sqrt_mul (by norm_num : (0 : ℝ) ≤ 5.5666305)]
    congr 1
    ring
  unfold admissibleBound
  rw [h32, ← sqrt_eq_rpow, hL32, hsplit]
  exact rescaled_lt (sqrt_pos.mpr ht) hq_lo hq_hi (sq_sqrt (by norm_num))

/-- **The bridge.** `FKS.v1.psi_classical_bound`, stated from `x₀ = e³⁰`, implies
`FKS.v2.psi_bound_all_x`: the all-`x` bound is the classical one rescaled, which is the direction
the paper's own proof of Lemma 5.3 takes. The statement is `FKS.v1.psi_bound_all_x`'s as well,
so this also re-grounds that conclusion, and nothing here needs a `margin` index. -/
theorem psi_bound_all_x_from_classical (h : FKS.v1.psi_classical_bound) :
    FKS.v2.psi_bound_all_x := by
  intro x hx
  exact (psi_classical_bound_from_two h x (le_of_lt hx)).trans_lt
    (admissibleBound_lt_all_x (by linarith))

end IEANTN.Bridges.FKS
