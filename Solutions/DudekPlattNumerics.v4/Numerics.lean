/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors (AI-assisted)
-/
import Mathlib
import Mathlib.NumberTheory.Chebyshev

/-!
# Scalar endpoint / monotonic / majorant bounds for `DudekPlattNumerics.v4`

Owned by the "numerics" parallel worker of IEANTN issue #63. NOT a graph node and NOT
registered in any `formalization.yaml`. No `sorry`; only the three permitted axioms.
-/

namespace DudekPlattNumerics.v4.Numerics

open Real Finset

/-! ## Part 0: general helpers -/

theorem poly_exp_decreasing (n : ℕ) {c L0 L : ℝ} (hL0 : 0 < L0) (hc : (n : ℝ) / L0 ≤ c)
    (hL : L0 ≤ L) : L ^ n * Real.exp (-c * L) ≤ L0 ^ n * Real.exp (-c * L0) := by
  have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
  have hratio_pos : (0 : ℝ) < L / L0 := div_pos hLpos hL0
  have hlog_ratio : Real.log (L / L0) ≤ L / L0 - 1 := Real.log_le_sub_one_of_pos hratio_pos
  have hlog_sub : Real.log L - Real.log L0 ≤ (L - L0) / L0 := by
    have heq : Real.log (L / L0) = Real.log L - Real.log L0 :=
      Real.log_div (ne_of_gt hLpos) (ne_of_gt hL0)
    have heq2 : L / L0 - 1 = (L - L0) / L0 := by field_simp
    linarith [hlog_ratio, heq, heq2]
  have hkey : (n : ℝ) * (Real.log L - Real.log L0) ≤ c * (L - L0) := by
    have hLsub_nonneg : (0 : ℝ) ≤ L - L0 := by linarith
    have hstep1 : (n : ℝ) * (Real.log L - Real.log L0) ≤ (n : ℝ) * ((L - L0) / L0) :=
      mul_le_mul_of_nonneg_left hlog_sub (Nat.cast_nonneg n)
    have hstep2 : (n : ℝ) * ((L - L0) / L0) ≤ c * (L - L0) := by
      have hmm := mul_le_mul_of_nonneg_right hc hLsub_nonneg
      calc (n : ℝ) * ((L - L0) / L0) = ((n : ℝ) / L0) * (L - L0) := by ring
        _ ≤ c * (L - L0) := hmm
    linarith
  have hrw : ∀ v : ℝ, 0 < v →
      Real.exp ((n : ℝ) * Real.log v - c * v) = v ^ n * Real.exp (-c * v) := by
    intro v hvpos
    have hsplit : (n : ℝ) * Real.log v - c * v = ((n : ℝ) * Real.log v) + (-c * v) := by ring
    rw [hsplit, Real.exp_add]
    congr 1
    rw [show (n : ℝ) * Real.log v = Real.log (v ^ n) from (Real.log_pow v n).symm]
    exact Real.exp_log (by positivity)
  have hexp_le : Real.exp ((n : ℝ) * Real.log L - c * L)
      ≤ Real.exp ((n : ℝ) * Real.log L0 - c * L0) := by
    apply Real.exp_le_exp.mpr; linarith [hkey]
  rw [hrw L hLpos, hrw L0 hL0] at hexp_le
  exact hexp_le

theorem hlog2_proof : (2 / 3 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- `exp 1 ^ n = exp n` as reals, the cast/mul_one bridge used repeatedly below. -/
theorem exp_one_pow (n : ℕ) : Real.exp 1 ^ n = Real.exp (n : ℝ) := by
  have h : Real.exp ((n:ℝ) * 1) = Real.exp 1 ^ n := Real.exp_nat_mul 1 n
  simp only [mul_one] at h
  exact h.symm

theorem exp_neg_nat_le (t : ℕ) : Real.exp (-(t : ℝ)) ≤ 1 / 2 ^ t := by
  have h2exp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3exp : (2 : ℝ) ^ t ≤ Real.exp (t : ℝ) := by
    rw [← exp_one_pow t]; exact pow_le_pow_left₀ (by norm_num) h2exp t
  rw [Real.exp_neg, ← one_div]
  gcongr

theorem inv_log2_lt : (1 : ℝ) / Real.log 2 < 3 / 2 := by
  have hl := hlog2_proof
  have hl0 : (0:ℝ) < Real.log 2 := by linarith
  rw [div_lt_iff₀ hl0]; linarith

/-- A reusable "lower bound `exp(n+r)` by splitting off the integer part" helper. -/
theorem exp_ge_of_split (n : ℕ) (r en fr : ℝ) (hen0 : 0 ≤ en)
    (hen : en ≤ Real.exp 1) (hfr0 : 0 ≤ fr) (hfr : fr ≤ Real.exp r) :
    en ^ n * fr ≤ Real.exp ((n : ℝ) + r) := by
  rw [Real.exp_add, ← exp_one_pow n]
  exact mul_le_mul (pow_le_pow_left₀ hen0 hen n) hfr hfr0 (by positivity)

/-! ## Part 1: three pure-scalar certificates for the calculus assembly (`K := 3600`) -/

theorem hD_proof {L : ℝ} (hL : 9400 ≤ L) :
    4 * L ^ 6 * Real.exp (-L / 100) + 3600 / ((99 / 100 : ℝ) ^ 7 * L) < 1 / 2 := by
  have hL0 : (0 : ℝ) < 9400 := by norm_num
  have hLpos : (0 : ℝ) < L := by linarith
  have h1 : L ^ 6 * Real.exp (-(1 / 100 : ℝ) * L) ≤
      (9400 : ℝ) ^ 6 * Real.exp (-(1 / 100 : ℝ) * 9400) :=
    poly_exp_decreasing 6 hL0 (by norm_num) hL
  have h4exp : Real.exp (-(94:ℕ) : ℝ) ≤ 1 / 2 ^ (94:ℕ) := exp_neg_nat_le 94
  have hearly : 4 * L ^ 6 * Real.exp (-L / 100) ≤ 4 * (9400 : ℝ) ^ 6 / 2 ^ 94 := by
    have e1 : Real.exp (-L / 100) = Real.exp (-(1 / 100 : ℝ) * L) := by congr 1; ring
    have e2 : Real.exp (-(1 / 100 : ℝ) * (9400:ℝ)) = Real.exp (-(94:ℕ) : ℝ) := by
      congr 1; push_cast; ring
    calc 4 * L ^ 6 * Real.exp (-L / 100)
        = 4 * (L ^ 6 * Real.exp (-(1 / 100 : ℝ) * L)) := by rw [e1]; ring
      _ ≤ 4 * ((9400:ℝ) ^ 6 * Real.exp (-(1 / 100 : ℝ) * 9400)) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 4 * (9400:ℝ) ^ 6 * Real.exp (-(94:ℕ) : ℝ) := by rw [e2]; ring
      _ ≤ 4 * (9400:ℝ) ^ 6 * (1 / 2 ^ (94:ℕ)) :=
          mul_le_mul_of_nonneg_left h4exp (by positivity)
      _ = 4 * (9400 : ℝ) ^ 6 / 2 ^ 94 := by ring
  have hlate : 3600 / ((99 / 100 : ℝ) ^ 7 * L) ≤ 3600 / ((99 / 100 : ℝ) ^ 7 * 9400) := by
    gcongr
  have hfin : (4 * (9400:ℝ) ^ 6 / 2 ^ 94 + 3600 / ((99 / 100 : ℝ) ^ 7 * 9400) : ℝ) < 1 / 2 := by
    norm_num
  linarith [hearly, hlate, hfin]

noncomputable def A : ℝ :=
  1 / Real.log 2 ^ 2 + 2 / Real.log 2 ^ 3 + 6 / Real.log 2 ^ 4 +
    24 / Real.log 2 ^ 5 + 120 / Real.log 2 ^ 6

theorem A_lt : A < 1600 := by
  have hl0 : (0:ℝ) < Real.log 2 := by linarith [hlog2_proof]
  have hpos : (0:ℝ) ≤ 1 / Real.log 2 := by positivity
  have hub := inv_log2_lt
  unfold A
  have h1 : (1:ℝ) / Real.log 2 ^ 2 ≤ (3/2:ℝ) ^ 2 := by
    rw [show (1:ℝ) / Real.log 2 ^ 2 = (1/Real.log 2)^2 by rw [div_pow]; ring]
    exact pow_le_pow_left₀ hpos hub.le 2
  have h2 : (2:ℝ) / Real.log 2 ^ 3 ≤ 2 * (3/2:ℝ) ^ 3 := by
    rw [show (2:ℝ) / Real.log 2 ^ 3 = 2 * (1/Real.log 2)^3 by rw [div_pow]; ring]
    gcongr
  have h3 : (6:ℝ) / Real.log 2 ^ 4 ≤ 6 * (3/2:ℝ) ^ 4 := by
    rw [show (6:ℝ) / Real.log 2 ^ 4 = 6 * (1/Real.log 2)^4 by rw [div_pow]; ring]
    gcongr
  have h4 : (24:ℝ) / Real.log 2 ^ 5 ≤ 24 * (3/2:ℝ) ^ 5 := by
    rw [show (24:ℝ) / Real.log 2 ^ 5 = 24 * (1/Real.log 2)^5 by rw [div_pow]; ring]
    gcongr
  have h5 : (120:ℝ) / Real.log 2 ^ 6 ≤ 120 * (3/2:ℝ) ^ 6 := by
    rw [show (120:ℝ) / Real.log 2 ^ 6 = 120 * (1/Real.log 2)^6 by rw [div_pow]; ring]
    gcongr
  have hfin : ((3/2:ℝ)^2 + 2*(3/2:ℝ)^3 + 6*(3/2:ℝ)^4 + 24*(3/2:ℝ)^5 + 120*(3/2:ℝ)^6 : ℝ) < 1600 := by
    norm_num
  linarith [h1, h2, h3, h4, h5, hfin]

theorem hA_proof {L : ℝ} (hL : 9400 ≤ L) : 2 * A * L ^ 6 * Real.exp (-L) < 1 / 1000 := by
  have hL0 : (0 : ℝ) < 9400 := by norm_num
  have h1 : L ^ 6 * Real.exp (-(1:ℝ) * L) ≤ (9400:ℝ) ^ 6 * Real.exp (-(1:ℝ) * 9400) :=
    poly_exp_decreasing 6 hL0 (by norm_num) hL
  have he : Real.exp (-(1:ℝ) * L) = Real.exp (-L) := by congr 1; ring
  have he2 : Real.exp (-(1:ℝ) * (9400:ℝ)) = Real.exp (-(9400:ℕ) : ℝ) := by
    congr 1; push_cast; ring
  rw [he, he2] at h1
  have hAnn : (0:ℝ) ≤ A := by
    have hl0 : (0:ℝ) < Real.log 2 := by linarith [hlog2_proof]
    unfold A; positivity
  have hAb := A_lt
  -- avoid the huge-exponent evaluator threshold: reduce -9400 to a safely negligible -200 first
  have hexp9400 : Real.exp (-(9400:ℕ) : ℝ) ≤ 1 / 2 ^ (200:ℕ) := by
    calc Real.exp (-(9400:ℕ) : ℝ) ≤ Real.exp (-(200:ℕ) : ℝ) := by
          apply Real.exp_le_exp.mpr; norm_num
      _ ≤ 1 / 2 ^ (200:ℕ) := exp_neg_nat_le 200
  have hstep : 2 * A * (L ^ 6 * Real.exp (-L)) ≤
      2 * 1600 * ((9400:ℝ) ^ 6 * (1 / 2 ^ (200:ℕ))) := by
    calc 2 * A * (L ^ 6 * Real.exp (-L))
        ≤ 2 * A * ((9400:ℝ) ^ 6 * Real.exp (-(9400:ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * 1600 * ((9400:ℝ) ^ 6 * Real.exp (-(9400:ℕ) : ℝ)) := by gcongr
      _ ≤ 2 * 1600 * ((9400:ℝ) ^ 6 * (1 / 2 ^ (200:ℕ))) := by gcongr
  have hfin : (2 * 1600 * ((9400:ℝ) ^ 6 * (1 / 2 ^ (200:ℕ))) : ℝ) < 1 / 1000 := by
    norm_num
  nlinarith [hstep, hfin]

theorem hI7_proof {L : ℝ} (hL : 9400 ≤ L) :
    720 * (1 / L + 7 * (L ^ 6 * Real.exp (-L / 2) / Real.log 2 ^ 8 + 256 / L ^ 2)) < 1 / 10 := by
  have hL0 : (0 : ℝ) < 9400 := by norm_num
  have hLpos : (0:ℝ) < L := by linarith
  have hl0 : (0:ℝ) < Real.log 2 := by linarith [hlog2_proof]
  have h1 : (1:ℝ) / L ≤ 1 / 9400 := one_div_le_one_div_of_le hL0 hL
  have h4 : (256:ℝ) / L ^ 2 ≤ 256 / 9400 ^ 2 := by gcongr
  have hpos : (0:ℝ) ≤ 1 / Real.log 2 := by positivity
  have hub := inv_log2_lt
  have h3 : (1:ℝ) / Real.log 2 ^ 8 ≤ (3/2:ℝ) ^ 8 := by
    rw [show (1:ℝ) / Real.log 2 ^ 8 = (1/Real.log 2)^8 by rw [div_pow]; ring]
    exact pow_le_pow_left₀ hpos hub.le 8
  have hb1 : L ^ 6 * Real.exp (-(1/2:ℝ) * L) ≤ (9400:ℝ) ^ 6 * Real.exp (-(1/2:ℝ) * 9400) :=
    poly_exp_decreasing 6 hL0 (by norm_num) hL
  have hb2 : Real.exp (-(1/2:ℝ) * (9400:ℝ)) ≤ 1 / 2 ^ (120:ℕ) := by
    have e : (-(1/2:ℝ) * (9400:ℝ)) = -(4700:ℕ) := by push_cast; ring
    rw [e]
    calc Real.exp (-(4700:ℕ) : ℝ) ≤ Real.exp (-(120:ℕ) : ℝ) := by
          apply Real.exp_le_exp.mpr; norm_num
      _ ≤ 1 / 2 ^ (120:ℕ) := exp_neg_nat_le 120
  have hb3 : (9400:ℝ) ^ 6 * Real.exp (-(1/2:ℝ) * 9400) ≤ (9400:ℝ) ^ 6 / 2 ^ (120:ℕ) := by
    calc (9400:ℝ) ^ 6 * Real.exp (-(1/2:ℝ) * 9400) ≤ (9400:ℝ) ^ 6 * (1 / 2 ^ (120:ℕ)) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = (9400:ℝ) ^ 6 / 2 ^ (120:ℕ) := by ring
  have hb4 : L ^ 6 * Real.exp (-(1/2:ℝ) * L) ≤ (9400:ℝ) ^ 6 / 2 ^ (120:ℕ) := le_trans hb1 hb3
  have hb6 : L ^ 6 * Real.exp (-(1/2:ℝ) * L) * ((1:ℝ) / Real.log 2 ^ 8) ≤
      ((9400:ℝ) ^ 6 / 2 ^ (120:ℕ)) * (3/2:ℝ) ^ 8 :=
    mul_le_mul hb4 h3 (by positivity) (by positivity)
  have hfinnum : (((9400:ℝ) ^ 6 / 2 ^ (120:ℕ)) * (3/2:ℝ) ^ 8 : ℝ) < 1 / 10 ^ 9 := by norm_num
  have hnegl : L ^ 6 * Real.exp (-L / 2) / Real.log 2 ^ 8 ≤ 1 / 10 ^ 9 := by
    have e1 : Real.exp (-L / 2) = Real.exp (-(1/2:ℝ) * L) := by congr 1; ring
    rw [e1, div_eq_mul_one_div]
    linarith [hb6, hfinnum]
  have heq : 720 * (1 / L + 7 * (L ^ 6 * Real.exp (-L / 2) / Real.log 2 ^ 8 + 256 / L ^ 2)) =
      720 * (1/L) + 720*7 * (L ^ 6 * Real.exp (-L / 2) / Real.log 2 ^ 8) + 720*7*(256 / L ^ 2) := by
    ring
  rw [heq]
  have hcalc : (720:ℝ) * (1/9400) + 720*7*(1/10^9) + 720*7*(256/9400^2) < 1/10 := by norm_num
  nlinarith [h1, h4, hnegl, hcalc]

/-! ## Part 2: `f_R`, its monotonicity, and the two endpoint certificates -/

noncomputable def R : ℝ := 1263 / 200
noncomputable def C : ℝ := Real.sqrt (8 / (17 * Real.pi))
noncomputable def f_R (u : ℝ) : ℝ :=
  C * Real.sqrt (Real.sqrt (u / R)) * Real.exp (-Real.sqrt (u / R)) * u ^ 5

theorem R_pos : (0:ℝ) < R := by unfold R; norm_num

theorem C_nonneg : (0:ℝ) ≤ C := by unfold C; positivity

theorem C_lt : C < 388 / 1000 := by
  have hpi := Real.pi_gt_d2
  unfold C
  rw [show (388/1000:ℝ) = Real.sqrt (((388:ℝ)/1000)^2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [div_lt_iff₀ (by positivity : (0:ℝ) < 17*Real.pi)]
  nlinarith [hpi]

/-- Core monotonicity, in `v = √(u/R)`: `h(v) := √v · v^10 · e^(-v)` is antitone for `v ≥ 21/2`. -/
theorem h_antitone {v1 v2 : ℝ} (hv1 : (21:ℝ) / 2 ≤ v1) (hv2 : v1 ≤ v2) :
    Real.sqrt v2 * v2 ^ 10 * Real.exp (-v2) ≤ Real.sqrt v1 * v1 ^ 10 * Real.exp (-v1) := by
  have hv1pos : (0:ℝ) < v1 := by linarith
  have hv2pos : (0:ℝ) < v2 := lt_of_lt_of_le hv1pos hv2
  have hratio_pos : (0:ℝ) < v2 / v1 := div_pos hv2pos hv1pos
  have hlog_ratio : Real.log (v2 / v1) ≤ v2 / v1 - 1 := Real.log_le_sub_one_of_pos hratio_pos
  have hlog_sub : Real.log v2 - Real.log v1 ≤ (v2 - v1) / v1 := by
    have heq : Real.log (v2 / v1) = Real.log v2 - Real.log v1 :=
      Real.log_div (ne_of_gt hv2pos) (ne_of_gt hv1pos)
    have heq2 : v2 / v1 - 1 = (v2 - v1) / v1 := by field_simp
    linarith [hlog_ratio, heq, heq2]
  have hkey : (21:ℝ) / 2 * (Real.log v2 - Real.log v1) ≤ v2 - v1 := by
    have hstep1 : (21:ℝ) / 2 * (Real.log v2 - Real.log v1) ≤ (21 / 2) * ((v2 - v1) / v1) :=
      mul_le_mul_of_nonneg_left hlog_sub (by norm_num)
    have hvsub_nonneg : (0:ℝ) ≤ v2 - v1 := by linarith
    have hratio_le_one : (21:ℝ) / 2 / v1 ≤ 1 := by rw [div_le_one hv1pos]; exact hv1
    have hstep2 : (21:ℝ) / 2 * ((v2 - v1) / v1) ≤ v2 - v1 := by
      have hmm := mul_le_mul_of_nonneg_right hratio_le_one hvsub_nonneg
      calc (21:ℝ) / 2 * ((v2 - v1) / v1) = (21 / 2 / v1) * (v2 - v1) := by ring
        _ ≤ 1 * (v2 - v1) := hmm
        _ = v2 - v1 := one_mul _
    linarith
  have hrw : ∀ v : ℝ, 0 < v →
      Real.exp ((21:ℝ) / 2 * Real.log v - v) = Real.sqrt v * v ^ 10 * Real.exp (-v) := by
    intro v hvpos
    have hsplit : (21:ℝ) / 2 * Real.log v - v
        = (Real.log v / 2 + 10 * Real.log v) + (-v) := by ring
    rw [hsplit, Real.exp_add, Real.exp_add]
    have e1 : Real.exp (Real.log v / 2) = Real.sqrt v := by
      rw [← Real.log_sqrt hvpos.le]
      exact Real.exp_log (Real.sqrt_pos.mpr hvpos)
    have e2 : Real.exp (10 * Real.log v) = v ^ 10 := by
      rw [show (10:ℝ) * Real.log v = Real.log (v ^ 10) from (Real.log_pow v 10).symm]
      exact Real.exp_log (by positivity)
    rw [e1, e2]
  have hexp_le : Real.exp ((21:ℝ) / 2 * Real.log v2 - v2)
      ≤ Real.exp ((21:ℝ) / 2 * Real.log v1 - v1) := by
    apply Real.exp_le_exp.mpr; linarith [hkey]
  rw [hrw v1 hv1pos, hrw v2 hv2pos] at hexp_le
  exact hexp_le

theorem f_R_eq {u : ℝ} (hu : 0 < u) :
    f_R u = C * R ^ 5 *
      (Real.sqrt (Real.sqrt (u / R)) * (Real.sqrt (u / R)) ^ 10 * Real.exp (-Real.sqrt (u / R))) := by
  have hRpos := R_pos
  unfold f_R
  set v := Real.sqrt (u / R) with hvdef
  have hv2 : v ^ 2 = u / R := Real.sq_sqrt (by positivity)
  have hueq : u = R * v ^ 2 := by rw [hv2]; field_simp
  nth_rewrite 1 [hueq]
  ring

theorem f_R_antitone {u1 u2 : ℝ} (hu1 : 441 * R / 4 ≤ u1) (hu2 : u1 ≤ u2) :
    f_R u2 ≤ f_R u1 := by
  have hRpos := R_pos
  have hu1pos : 0 < u1 := by nlinarith [hu1, hRpos]
  have hu2pos : 0 < u2 := lt_of_lt_of_le hu1pos hu2
  rw [f_R_eq hu1pos, f_R_eq hu2pos]
  have hCR5 : (0:ℝ) ≤ C * R ^ 5 := mul_nonneg C_nonneg (pow_nonneg hRpos.le 5)
  apply mul_le_mul_of_nonneg_left _ hCR5
  have hv1ge : (21:ℝ) / 2 ≤ Real.sqrt (u1 / R) := by
    rw [Real.le_sqrt' (by norm_num : (0:ℝ) < 21 / 2)]
    rw [le_div_iff₀ hRpos]
    nlinarith [hu1]
  have hv1v2 : Real.sqrt (u1 / R) ≤ Real.sqrt (u2 / R) := by
    apply Real.sqrt_le_sqrt; gcongr
  exact h_antitone hv1ge hv1v2

/-- `f_R(9400) < 3110`, via a rational bracket on `√(u/R)` and a split-exponent Taylor
lower bound on `e^(38.581)` (`38.581 = 38 + 0.581`, both via `Real.sum_le_exp_of_nonneg`). -/
theorem f_R_9400_lt : f_R 9400 < 3110 := by
  have hRpos := R_pos
  have hbracket : (9400:ℝ) / R = 1880000 / 1263 := by unfold R; norm_num
  have hXlo : (38.581:ℝ) < Real.sqrt ((9400:ℝ) / R) := by
    rw [hbracket, Real.lt_sqrt (by norm_num)]; norm_num
  have hXhi : Real.sqrt ((9400:ℝ) / R) < 38.582 := by
    rw [hbracket, Real.sqrt_lt' (by norm_num)]; norm_num
  have hsqrtXub : Real.sqrt (Real.sqrt ((9400:ℝ) / R)) < 6.212 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith [hXhi]
  have hsqrtXnn : (0:ℝ) ≤ Real.sqrt (Real.sqrt ((9400:ℝ) / R)) := Real.sqrt_nonneg _
  have hCub := C_lt
  have hCnn := C_nonneg
  have he : (2.71828182:ℝ) ≤ (∑ i ∈ range 12, (1:ℝ) ^ i / (i.factorial : ℝ)) :=
    by norm_num [Finset.sum_range_succ]
  have he1 : (2.71828182:ℝ) ≤ Real.exp 1 :=
    le_trans he (Real.sum_le_exp_of_nonneg (by norm_num) 12)
  have hf : (1.78782536:ℝ) ≤ (∑ i ∈ range 12, (0.581:ℝ) ^ i / (i.factorial : ℝ)) :=
    by norm_num [Finset.sum_range_succ]
  have hf1 : (1.78782536:ℝ) ≤ Real.exp (0.581:ℝ) :=
    le_trans hf (Real.sum_le_exp_of_nonneg (by norm_num) 12)
  have hsplit0 := exp_ge_of_split 38 (0.581:ℝ) 2.71828182 1.78782536
    (by norm_num) he1 (by norm_num) hf1
  have hsplit : (2.71828182:ℝ) ^ 38 * 1.78782536 ≤ Real.exp (38.581:ℝ) := by
    have hnum : ((38:ℕ):ℝ) + (0.581:ℝ) = (38.581:ℝ) := by norm_num
    rwa [hnum] at hsplit0
  have hexp_ub : Real.exp (-Real.sqrt ((9400:ℝ) / R)) ≤
      1 / ((2.71828182:ℝ) ^ 38 * 1.78782536) := by
    rw [Real.exp_neg, one_div]
    have hchain : (2.71828182:ℝ) ^ 38 * 1.78782536 ≤ Real.exp (Real.sqrt ((9400:ℝ) / R)) :=
      hsplit.trans (Real.exp_le_exp.mpr (by linarith [hXlo]))
    exact (inv_le_inv₀ (Real.exp_pos _)
      (by positivity : (0:ℝ) < (2.71828182:ℝ) ^ 38 * 1.78782536)).mpr hchain
  have hexp_nonneg : (0:ℝ) ≤ Real.exp (-Real.sqrt ((9400:ℝ) / R)) := (Real.exp_pos _).le
  unfold f_R
  have step1 : C * Real.sqrt (Real.sqrt ((9400:ℝ) / R)) ≤ (388/1000:ℝ) * 6.212 :=
    mul_le_mul hCub.le hsqrtXub.le hsqrtXnn (by norm_num)
  have step1nn : (0:ℝ) ≤ C * Real.sqrt (Real.sqrt ((9400:ℝ) / R)) := mul_nonneg hCnn hsqrtXnn
  have step2 : C * Real.sqrt (Real.sqrt ((9400:ℝ) / R)) * Real.exp (-Real.sqrt ((9400:ℝ) / R)) ≤
      (388/1000:ℝ) * 6.212 * (1 / ((2.71828182:ℝ) ^ 38 * 1.78782536)) :=
    mul_le_mul step1 hexp_ub hexp_nonneg (by norm_num)
  have step2nn : (0:ℝ) ≤
      C * Real.sqrt (Real.sqrt ((9400:ℝ) / R)) * Real.exp (-Real.sqrt ((9400:ℝ) / R)) :=
    mul_nonneg step1nn hexp_nonneg
  have step3 : C * Real.sqrt (Real.sqrt ((9400:ℝ) / R)) * Real.exp (-Real.sqrt ((9400:ℝ) / R)) *
      (9400:ℝ) ^ 5 ≤
      (388/1000:ℝ) * 6.212 * (1 / ((2.71828182:ℝ) ^ 38 * 1.78782536)) * (9400:ℝ) ^ 5 :=
    mul_le_mul_of_nonneg_right step2 (by positivity)
  have hfin : ((388/1000:ℝ) * 6.212 * (1 / ((2.71828182:ℝ) ^ 38 * 1.78782536)) * (9400:ℝ) ^ 5 : ℝ)
      < 3110 := by norm_num
  linarith [step3, hfin]

/-- `f_R(9306) < 3600`, same technique at the split point `9306 = 0.99 · 9400`. -/
theorem f_R_9306_lt : f_R 9306 < 3600 := by
  have hRpos := R_pos
  have hbracket : (9306:ℝ) / R = 1861200 / 1263 := by unfold R; norm_num
  have hXlo : (38.387:ℝ) < Real.sqrt ((9306:ℝ) / R) := by
    rw [hbracket, Real.lt_sqrt (by norm_num)]; norm_num
  have hXhi : Real.sqrt ((9306:ℝ) / R) < 38.388 := by
    rw [hbracket, Real.sqrt_lt' (by norm_num)]; norm_num
  have hsqrtXub : Real.sqrt (Real.sqrt ((9306:ℝ) / R)) < 6.196 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith [hXhi]
  have hsqrtXnn : (0:ℝ) ≤ Real.sqrt (Real.sqrt ((9306:ℝ) / R)) := Real.sqrt_nonneg _
  have hCub := C_lt
  have hCnn := C_nonneg
  have he : (2.71828182:ℝ) ≤ (∑ i ∈ range 12, (1:ℝ) ^ i / (i.factorial : ℝ)) :=
    by norm_num [Finset.sum_range_succ]
  have he1 : (2.71828182:ℝ) ≤ Real.exp 1 :=
    le_trans he (Real.sum_le_exp_of_nonneg (by norm_num) 12)
  have hf : (1.47255649:ℝ) ≤ (∑ i ∈ range 12, (0.387:ℝ) ^ i / (i.factorial : ℝ)) :=
    by norm_num [Finset.sum_range_succ]
  have hf1 : (1.47255649:ℝ) ≤ Real.exp (0.387:ℝ) :=
    le_trans hf (Real.sum_le_exp_of_nonneg (by norm_num) 12)
  have hsplit0 := exp_ge_of_split 38 (0.387:ℝ) 2.71828182 1.47255649
    (by norm_num) he1 (by norm_num) hf1
  have hsplit : (2.71828182:ℝ) ^ 38 * 1.47255649 ≤ Real.exp (38.387:ℝ) := by
    have hnum : ((38:ℕ):ℝ) + (0.387:ℝ) = (38.387:ℝ) := by norm_num
    rwa [hnum] at hsplit0
  have hexp_ub : Real.exp (-Real.sqrt ((9306:ℝ) / R)) ≤
      1 / ((2.71828182:ℝ) ^ 38 * 1.47255649) := by
    rw [Real.exp_neg, one_div]
    have hchain : (2.71828182:ℝ) ^ 38 * 1.47255649 ≤ Real.exp (Real.sqrt ((9306:ℝ) / R)) :=
      hsplit.trans (Real.exp_le_exp.mpr (by linarith [hXlo]))
    exact (inv_le_inv₀ (Real.exp_pos _)
      (by positivity : (0:ℝ) < (2.71828182:ℝ) ^ 38 * 1.47255649)).mpr hchain
  have hexp_nonneg : (0:ℝ) ≤ Real.exp (-Real.sqrt ((9306:ℝ) / R)) := (Real.exp_pos _).le
  unfold f_R
  have step1 : C * Real.sqrt (Real.sqrt ((9306:ℝ) / R)) ≤ (388/1000:ℝ) * 6.196 :=
    mul_le_mul hCub.le hsqrtXub.le hsqrtXnn (by norm_num)
  have step1nn : (0:ℝ) ≤ C * Real.sqrt (Real.sqrt ((9306:ℝ) / R)) := mul_nonneg hCnn hsqrtXnn
  have step2 : C * Real.sqrt (Real.sqrt ((9306:ℝ) / R)) * Real.exp (-Real.sqrt ((9306:ℝ) / R)) ≤
      (388/1000:ℝ) * 6.196 * (1 / ((2.71828182:ℝ) ^ 38 * 1.47255649)) :=
    mul_le_mul step1 hexp_ub hexp_nonneg (by norm_num)
  have step2nn : (0:ℝ) ≤
      C * Real.sqrt (Real.sqrt ((9306:ℝ) / R)) * Real.exp (-Real.sqrt ((9306:ℝ) / R)) :=
    mul_nonneg step1nn hexp_nonneg
  have step3 : C * Real.sqrt (Real.sqrt ((9306:ℝ) / R)) * Real.exp (-Real.sqrt ((9306:ℝ) / R)) *
      (9306:ℝ) ^ 5 ≤
      (388/1000:ℝ) * 6.196 * (1 / ((2.71828182:ℝ) ^ 38 * 1.47255649)) * (9306:ℝ) ^ 5 :=
    mul_le_mul_of_nonneg_right step2 (by positivity)
  have hfin : ((388/1000:ℝ) * 6.196 * (1 / ((2.71828182:ℝ) ^ 38 * 1.47255649)) * (9306:ℝ) ^ 5 : ℝ)
      < 3600 := by norm_num
  linarith [step3, hfin]

/-! ## Part 3: connect an explicit MT-Corollary-1-shaped theta hypothesis to `hpoint`/`htail`

`hMT` below has exactly the shape of the boundary worker's proposed `MT.v2.corollary_1`
(`INTERFACES.md` §2) -- an explicit LOCAL hypothesis, not a graph import, per the campaign
charge ("numeric worker may use an explicit structurally matching theta hypothesis without
creating graph nodes"). `x * C * √√(log x / R) * exp(-√(log x/R))` is definitionally Corollary
1's RHS, and equals `f_R(log x) * x / (log x)^5` exactly, which is what lets `f_R`'s
monotonicity turn the hypothesis into the `3110`/`3600` constants the calculus assembly needs. -/

theorem theta_bound_of_f_R_le
    (hMT : ∀ x : ℝ, 149 ≤ x → |Chebyshev.theta x - x| ≤
      x * C * Real.sqrt (Real.sqrt (Real.log x / R)) * Real.exp (-Real.sqrt (Real.log x / R)))
    {x u0 K : ℝ} (hu0 : 441 * R / 4 ≤ u0) (hx149 : 149 ≤ x) (hxu0 : u0 ≤ Real.log x)
    (hK : f_R u0 ≤ K) :
    |Chebyshev.theta x - x| ≤ K * x / Real.log x ^ 5 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx149
  have hu0pos : 0 < u0 := by nlinarith [hu0, R_pos]
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le hu0pos hxu0
  have hfRle : f_R (Real.log x) ≤ K := le_trans (f_R_antitone hu0 hxu0) hK
  have hrw : x * C * Real.sqrt (Real.sqrt (Real.log x / R)) * Real.exp (-Real.sqrt (Real.log x / R))
      = f_R (Real.log x) * x / Real.log x ^ 5 := by
    unfold f_R; field_simp
  have hle : f_R (Real.log x) * x / Real.log x ^ 5 ≤ K * x / Real.log x ^ 5 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfRle hx0.le) (by positivity)
  linarith [hMT x hx149, hrw ▸ hle]

/-- Discharges `pi_two_sided_from_certificates`'s `hpoint`, `K := 3110` at the point `L = log x`
itself, via `f_R_9400_lt`. -/
theorem hpoint_proof
    (hMT : ∀ x : ℝ, 149 ≤ x → |Chebyshev.theta x - x| ≤
      x * C * Real.sqrt (Real.sqrt (Real.log x / R)) * Real.exp (-Real.sqrt (Real.log x / R)))
    {x : ℝ} (hx : Real.exp 9400 < x) :
    |Chebyshev.theta x - x| ≤ 3110 * x / Real.log x ^ 5 := by
  have hx149 : (149:ℝ) ≤ x := by
    have h1 : (149:ℝ) < Real.exp 9400 := by linarith [Real.add_one_le_exp (9400:ℝ)]
    linarith
  have hxu0 : (9400:ℝ) ≤ Real.log x := by
    have h1 := Real.log_lt_log (Real.exp_pos (9400:ℝ)) hx
    simpa using h1.le
  exact theta_bound_of_f_R_le hMT (by unfold R; norm_num) hx149 hxu0 f_R_9400_lt.le

/-- Discharges `pi_two_sided_from_certificates`'s `htail`, `K := 3600` on the whole tail range
`t ≥ x^(99/100)`, via `f_R_9306_lt`. -/
theorem htail_proof
    (hMT : ∀ x : ℝ, 149 ≤ x → |Chebyshev.theta x - x| ≤
      x * C * Real.sqrt (Real.sqrt (Real.log x / R)) * Real.exp (-Real.sqrt (Real.log x / R)))
    {x : ℝ} (hx : Real.exp 9400 < x) :
    ∀ t : ℝ, Real.exp ((99 / 100 : ℝ) * Real.log x) ≤ t →
      |Chebyshev.theta t - t| ≤ 3600 * t / Real.log t ^ 5 := by
  intro t ht
  have hlogx : (9400:ℝ) < Real.log x := by
    have h1 := Real.log_lt_log (Real.exp_pos (9400:ℝ)) hx; simpa using h1
  have ht149 : (149:ℝ) ≤ t := by
    have h2 : (9306:ℝ) < (99 / 100 : ℝ) * Real.log x := by nlinarith [hlogx]
    have h3 : (149:ℝ) < Real.exp (9306:ℝ) := by linarith [Real.add_one_le_exp (9306:ℝ)]
    have h4 : Real.exp (9306:ℝ) ≤ Real.exp ((99 / 100 : ℝ) * Real.log x) :=
      Real.exp_le_exp.mpr h2.le
    linarith [h3, h4, ht]
  have htu0 : (9306:ℝ) ≤ Real.log t := by
    have h1 := Real.log_le_log (Real.exp_pos _) ht
    rw [Real.log_exp] at h1
    nlinarith [h1, hlogx]
  exact theta_bound_of_f_R_le hMT (by unfold R; norm_num) ht149 htu0 f_R_9306_lt.le

end DudekPlattNumerics.v4.Numerics

open DudekPlattNumerics.v4.Numerics in
#print axioms poly_exp_decreasing
open DudekPlattNumerics.v4.Numerics in
#print axioms hD_proof
open DudekPlattNumerics.v4.Numerics in
#print axioms A_lt
open DudekPlattNumerics.v4.Numerics in
#print axioms hA_proof
open DudekPlattNumerics.v4.Numerics in
#print axioms hI7_proof
open DudekPlattNumerics.v4.Numerics in
#print axioms h_antitone
open DudekPlattNumerics.v4.Numerics in
#print axioms f_R_antitone
open DudekPlattNumerics.v4.Numerics in
#print axioms f_R_9400_lt
open DudekPlattNumerics.v4.Numerics in
#print axioms f_R_9306_lt
open DudekPlattNumerics.v4.Numerics in
#print axioms theta_bound_of_f_R_le
open DudekPlattNumerics.v4.Numerics in
#print axioms hpoint_proof
open DudekPlattNumerics.v4.Numerics in
#print axioms htail_proof
