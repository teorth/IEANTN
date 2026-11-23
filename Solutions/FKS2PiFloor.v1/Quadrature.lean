/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IntegralBounds
import CertificateKernel

open MeasureTheory

namespace FKS2PiFloor

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Rational candidates are proposals only: each dyadic certificate is kernel-checked.
theorem Li_two : IEANTN.Li 2 = 0 := by simp [IEANTN.Li]

theorem integral_2 : (11130 : ℝ) / 10000 ≤
    (∫ t in (2 : ℝ)..3, 1 / Real.log t) ∧
    (∫ t in (2 : ℝ)..3, 1 / Real.log t) ≤ 11238 / 10000 := by
  have h := Certificate.integral_bounds (n := 2) (by norm_num)
    (11130 / 10000) (11238 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_3 : (11130 : ℝ) / 10000 ≤ IEANTN.Li 3 ∧
    IEANTN.Li 3 ≤ 11238 / 10000 := by
  have hp : IEANTN.Li 2 = 0 := Li_two
  have hu := integral_2
  have he := Li_eq_add_integral (a := (2 : ℝ)) (x := (3 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_3 : (8020 : ℝ) / 10000 ≤
    (∫ t in (3 : ℝ)..4, 1 / Real.log t) ∧
    (∫ t in (3 : ℝ)..4, 1 / Real.log t) ≤ 8060 / 10000 := by
  have h := Certificate.integral_bounds (n := 3) (by norm_num)
    (8020 / 10000) (8060 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_4 : (19150 : ℝ) / 10000 ≤ IEANTN.Li 4 ∧
    IEANTN.Li 4 ≤ 19298 / 10000 := by
  have hp := Li_3
  have hu := integral_3
  have he := Li_eq_add_integral (a := (3 : ℝ)) (x := (4 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_4 : (6659 : ℝ) / 10000 ≤
    (∫ t in (4 : ℝ)..5, 1 / Real.log t) ∧
    (∫ t in (4 : ℝ)..5, 1 / Real.log t) ≤ 6681 / 10000 := by
  have h := Certificate.integral_bounds (n := 4) (by norm_num)
    (6659 / 10000) (6681 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_5 : (25809 : ℝ) / 10000 ≤ IEANTN.Li 5 ∧
    IEANTN.Li 5 ≤ 25979 / 10000 := by
  have hp := Li_4
  have hu := integral_4
  have he := Li_eq_add_integral (a := (4 : ℝ)) (x := (5 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_5 : (5869 : ℝ) / 10000 ≤
    (∫ t in (5 : ℝ)..6, 1 / Real.log t) ∧
    (∫ t in (5 : ℝ)..6, 1 / Real.log t) ≤ 5884 / 10000 := by
  have h := Certificate.integral_bounds (n := 5) (by norm_num)
    (5869 / 10000) (5884 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_6 : (31678 : ℝ) / 10000 ≤ IEANTN.Li 6 ∧
    IEANTN.Li 6 ≤ 31863 / 10000 := by
  have hp := Li_5
  have hu := integral_5
  have he := Li_eq_add_integral (a := (5 : ℝ)) (x := (6 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_6 : (5343 : ℝ) / 10000 ≤
    (∫ t in (6 : ℝ)..7, 1 / Real.log t) ∧
    (∫ t in (6 : ℝ)..7, 1 / Real.log t) ≤ 5354 / 10000 := by
  have h := Certificate.integral_bounds (n := 6) (by norm_num)
    (5343 / 10000) (5354 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_7 : (37021 : ℝ) / 10000 ≤ IEANTN.Li 7 ∧
    IEANTN.Li 7 ≤ 37217 / 10000 := by
  have hp := Li_6
  have hu := integral_6
  have he := Li_eq_add_integral (a := (6 : ℝ)) (x := (7 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_7 : (4962 : ℝ) / 10000 ≤
    (∫ t in (7 : ℝ)..8, 1 / Real.log t) ∧
    (∫ t in (7 : ℝ)..8, 1 / Real.log t) ≤ 4971 / 10000 := by
  have h := Certificate.integral_bounds (n := 7) (by norm_num)
    (4962 / 10000) (4971 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_8 : (41983 : ℝ) / 10000 ≤ IEANTN.Li 8 ∧
    IEANTN.Li 8 ≤ 42188 / 10000 := by
  have hp := Li_7
  have hu := integral_7
  have he := Li_eq_add_integral (a := (7 : ℝ)) (x := (8 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_8 : (4672 : ℝ) / 10000 ≤
    (∫ t in (8 : ℝ)..9, 1 / Real.log t) ∧
    (∫ t in (8 : ℝ)..9, 1 / Real.log t) ≤ 4679 / 10000 := by
  have h := Certificate.integral_bounds (n := 8) (by norm_num)
    (4672 / 10000) (4679 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_9 : (46655 : ℝ) / 10000 ≤ IEANTN.Li 9 ∧
    IEANTN.Li 9 ≤ 46867 / 10000 := by
  have hp := Li_8
  have hu := integral_8
  have he := Li_eq_add_integral (a := (8 : ℝ)) (x := (9 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_9 : (4441 : ℝ) / 10000 ≤
    (∫ t in (9 : ℝ)..10, 1 / Real.log t) ∧
    (∫ t in (9 : ℝ)..10, 1 / Real.log t) ≤ 4447 / 10000 := by
  have h := Certificate.integral_bounds (n := 9) (by norm_num)
    (4441 / 10000) (4447 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_10 : (51096 : ℝ) / 10000 ≤ IEANTN.Li 10 ∧
    IEANTN.Li 10 ≤ 51314 / 10000 := by
  have hp := Li_9
  have hu := integral_9
  have he := Li_eq_add_integral (a := (9 : ℝ)) (x := (10 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_10 : (4251 : ℝ) / 10000 ≤
    (∫ t in (10 : ℝ)..11, 1 / Real.log t) ∧
    (∫ t in (10 : ℝ)..11, 1 / Real.log t) ≤ 4257 / 10000 := by
  have h := Certificate.integral_bounds (n := 10) (by norm_num)
    (4251 / 10000) (4257 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_11 : (55347 : ℝ) / 10000 ≤ IEANTN.Li 11 ∧
    IEANTN.Li 11 ≤ 55571 / 10000 := by
  have hp := Li_10
  have hu := integral_10
  have he := Li_eq_add_integral (a := (10 : ℝ)) (x := (11 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_11 : (4093 : ℝ) / 10000 ≤
    (∫ t in (11 : ℝ)..12, 1 / Real.log t) ∧
    (∫ t in (11 : ℝ)..12, 1 / Real.log t) ≤ 4098 / 10000 := by
  have h := Certificate.integral_bounds (n := 11) (by norm_num)
    (4093 / 10000) (4098 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_12 : (59440 : ℝ) / 10000 ≤ IEANTN.Li 12 ∧
    IEANTN.Li 12 ≤ 59669 / 10000 := by
  have hp := Li_11
  have hu := integral_11
  have he := Li_eq_add_integral (a := (11 : ℝ)) (x := (12 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_12 : (3958 : ℝ) / 10000 ≤
    (∫ t in (12 : ℝ)..13, 1 / Real.log t) ∧
    (∫ t in (12 : ℝ)..13, 1 / Real.log t) ≤ 3962 / 10000 := by
  have h := Certificate.integral_bounds (n := 12) (by norm_num)
    (3958 / 10000) (3962 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_13 : (63398 : ℝ) / 10000 ≤ IEANTN.Li 13 ∧
    IEANTN.Li 13 ≤ 63631 / 10000 := by
  have hp := Li_12
  have hu := integral_12
  have he := Li_eq_add_integral (a := (12 : ℝ)) (x := (13 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_13 : (3841 : ℝ) / 10000 ≤
    (∫ t in (13 : ℝ)..14, 1 / Real.log t) ∧
    (∫ t in (13 : ℝ)..14, 1 / Real.log t) ≤ 3845 / 10000 := by
  have h := Certificate.integral_bounds (n := 13) (by norm_num)
    (3841 / 10000) (3845 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_14 : (67239 : ℝ) / 10000 ≤ IEANTN.Li 14 ∧
    IEANTN.Li 14 ≤ 67476 / 10000 := by
  have hp := Li_13
  have hu := integral_13
  have he := Li_eq_add_integral (a := (13 : ℝ)) (x := (14 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_14 : (3738 : ℝ) / 10000 ≤
    (∫ t in (14 : ℝ)..15, 1 / Real.log t) ∧
    (∫ t in (14 : ℝ)..15, 1 / Real.log t) ≤ 3742 / 10000 := by
  have h := Certificate.integral_bounds (n := 14) (by norm_num)
    (3738 / 10000) (3742 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_15 : (70977 : ℝ) / 10000 ≤ IEANTN.Li 15 ∧
    IEANTN.Li 15 ≤ 71218 / 10000 := by
  have hp := Li_14
  have hu := integral_14
  have he := Li_eq_add_integral (a := (14 : ℝ)) (x := (15 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_15 : (3647 : ℝ) / 10000 ≤
    (∫ t in (15 : ℝ)..16, 1 / Real.log t) ∧
    (∫ t in (15 : ℝ)..16, 1 / Real.log t) ≤ 3651 / 10000 := by
  have h := Certificate.integral_bounds (n := 15) (by norm_num)
    (3647 / 10000) (3651 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_16 : (74624 : ℝ) / 10000 ≤ IEANTN.Li 16 ∧
    IEANTN.Li 16 ≤ 74869 / 10000 := by
  have hp := Li_15
  have hu := integral_15
  have he := Li_eq_add_integral (a := (15 : ℝ)) (x := (16 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_16 : (3566 : ℝ) / 10000 ≤
    (∫ t in (16 : ℝ)..17, 1 / Real.log t) ∧
    (∫ t in (16 : ℝ)..17, 1 / Real.log t) ≤ 3569 / 10000 := by
  have h := Certificate.integral_bounds (n := 16) (by norm_num)
    (3566 / 10000) (3569 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_17 : (78190 : ℝ) / 10000 ≤ IEANTN.Li 17 ∧
    IEANTN.Li 17 ≤ 78438 / 10000 := by
  have hp := Li_16
  have hu := integral_16
  have he := Li_eq_add_integral (a := (16 : ℝ)) (x := (17 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_17 : (3492 : ℝ) / 10000 ≤
    (∫ t in (17 : ℝ)..18, 1 / Real.log t) ∧
    (∫ t in (17 : ℝ)..18, 1 / Real.log t) ≤ 3496 / 10000 := by
  have h := Certificate.integral_bounds (n := 17) (by norm_num)
    (3492 / 10000) (3496 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_18 : (81682 : ℝ) / 10000 ≤ IEANTN.Li 18 ∧
    IEANTN.Li 18 ≤ 81934 / 10000 := by
  have hp := Li_17
  have hu := integral_17
  have he := Li_eq_add_integral (a := (17 : ℝ)) (x := (18 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_18 : (3426 : ℝ) / 10000 ≤
    (∫ t in (18 : ℝ)..19, 1 / Real.log t) ∧
    (∫ t in (18 : ℝ)..19, 1 / Real.log t) ≤ 3429 / 10000 := by
  have h := Certificate.integral_bounds (n := 18) (by norm_num)
    (3426 / 10000) (3429 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_19 : (85108 : ℝ) / 10000 ≤ IEANTN.Li 19 ∧
    IEANTN.Li 19 ≤ 85363 / 10000 := by
  have hp := Li_18
  have hu := integral_18
  have he := Li_eq_add_integral (a := (18 : ℝ)) (x := (19 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_19 : (3365 : ℝ) / 10000 ≤
    (∫ t in (19 : ℝ)..20, 1 / Real.log t) ∧
    (∫ t in (19 : ℝ)..20, 1 / Real.log t) ≤ 3368 / 10000 := by
  have h := Certificate.integral_bounds (n := 19) (by norm_num)
    (3365 / 10000) (3368 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_20 : (88473 : ℝ) / 10000 ≤ IEANTN.Li 20 ∧
    IEANTN.Li 20 ≤ 88731 / 10000 := by
  have hp := Li_19
  have hu := integral_19
  have he := Li_eq_add_integral (a := (19 : ℝ)) (x := (20 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_20 : (3309 : ℝ) / 10000 ≤
    (∫ t in (20 : ℝ)..21, 1 / Real.log t) ∧
    (∫ t in (20 : ℝ)..21, 1 / Real.log t) ≤ 3313 / 10000 := by
  have h := Certificate.integral_bounds (n := 20) (by norm_num)
    (3309 / 10000) (3313 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_21 : (91782 : ℝ) / 10000 ≤ IEANTN.Li 21 ∧
    IEANTN.Li 21 ≤ 92044 / 10000 := by
  have hp := Li_20
  have hu := integral_20
  have he := Li_eq_add_integral (a := (20 : ℝ)) (x := (21 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_21 : (3258 : ℝ) / 10000 ≤
    (∫ t in (21 : ℝ)..22, 1 / Real.log t) ∧
    (∫ t in (21 : ℝ)..22, 1 / Real.log t) ≤ 3261 / 10000 := by
  have h := Certificate.integral_bounds (n := 21) (by norm_num)
    (3258 / 10000) (3261 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_22 : (95040 : ℝ) / 10000 ≤ IEANTN.Li 22 ∧
    IEANTN.Li 22 ≤ 95305 / 10000 := by
  have hp := Li_21
  have hu := integral_21
  have he := Li_eq_add_integral (a := (21 : ℝ)) (x := (22 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_22 : (3210 : ℝ) / 10000 ≤
    (∫ t in (22 : ℝ)..23, 1 / Real.log t) ∧
    (∫ t in (22 : ℝ)..23, 1 / Real.log t) ≤ 3213 / 10000 := by
  have h := Certificate.integral_bounds (n := 22) (by norm_num)
    (3210 / 10000) (3213 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_23 : (98250 : ℝ) / 10000 ≤ IEANTN.Li 23 ∧
    IEANTN.Li 23 ≤ 98518 / 10000 := by
  have hp := Li_22
  have hu := integral_22
  have he := Li_eq_add_integral (a := (22 : ℝ)) (x := (23 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_23 : (3166 : ℝ) / 10000 ≤
    (∫ t in (23 : ℝ)..24, 1 / Real.log t) ∧
    (∫ t in (23 : ℝ)..24, 1 / Real.log t) ≤ 3169 / 10000 := by
  have h := Certificate.integral_bounds (n := 23) (by norm_num)
    (3166 / 10000) (3169 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_24 : (101416 : ℝ) / 10000 ≤ IEANTN.Li 24 ∧
    IEANTN.Li 24 ≤ 101687 / 10000 := by
  have hp := Li_23
  have hu := integral_23
  have he := Li_eq_add_integral (a := (23 : ℝ)) (x := (24 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_24 : (3125 : ℝ) / 10000 ≤
    (∫ t in (24 : ℝ)..25, 1 / Real.log t) ∧
    (∫ t in (24 : ℝ)..25, 1 / Real.log t) ≤ 3128 / 10000 := by
  have h := Certificate.integral_bounds (n := 24) (by norm_num)
    (3125 / 10000) (3128 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_25 : (104541 : ℝ) / 10000 ≤ IEANTN.Li 25 ∧
    IEANTN.Li 25 ≤ 104815 / 10000 := by
  have hp := Li_24
  have hu := integral_24
  have he := Li_eq_add_integral (a := (24 : ℝ)) (x := (25 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_25 : (3086 : ℝ) / 10000 ≤
    (∫ t in (25 : ℝ)..26, 1 / Real.log t) ∧
    (∫ t in (25 : ℝ)..26, 1 / Real.log t) ≤ 3089 / 10000 := by
  have h := Certificate.integral_bounds (n := 25) (by norm_num)
    (3086 / 10000) (3089 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_26 : (107627 : ℝ) / 10000 ≤ IEANTN.Li 26 ∧
    IEANTN.Li 26 ≤ 107904 / 10000 := by
  have hp := Li_25
  have hu := integral_25
  have he := Li_eq_add_integral (a := (25 : ℝ)) (x := (26 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_26 : (3050 : ℝ) / 10000 ≤
    (∫ t in (26 : ℝ)..27, 1 / Real.log t) ∧
    (∫ t in (26 : ℝ)..27, 1 / Real.log t) ≤ 3053 / 10000 := by
  have h := Certificate.integral_bounds (n := 26) (by norm_num)
    (3050 / 10000) (3053 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_27 : (110677 : ℝ) / 10000 ≤ IEANTN.Li 27 ∧
    IEANTN.Li 27 ≤ 110957 / 10000 := by
  have hp := Li_26
  have hu := integral_26
  have he := Li_eq_add_integral (a := (26 : ℝ)) (x := (27 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_27 : (3016 : ℝ) / 10000 ≤
    (∫ t in (27 : ℝ)..28, 1 / Real.log t) ∧
    (∫ t in (27 : ℝ)..28, 1 / Real.log t) ≤ 3019 / 10000 := by
  have h := Certificate.integral_bounds (n := 27) (by norm_num)
    (3016 / 10000) (3019 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_28 : (113693 : ℝ) / 10000 ≤ IEANTN.Li 28 ∧
    IEANTN.Li 28 ≤ 113976 / 10000 := by
  have hp := Li_27
  have hu := integral_27
  have he := Li_eq_add_integral (a := (27 : ℝ)) (x := (28 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

theorem integral_28 : (2984 : ℝ) / 10000 ≤
    (∫ t in (28 : ℝ)..29, 1 / Real.log t) ∧
    (∫ t in (28 : ℝ)..29, 1 / Real.log t) ≤ 2987 / 10000 := by
  have h := Certificate.integral_bounds (n := 28) (by norm_num)
    (2984 / 10000) (2987 / 10000) (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem Li_29 : (116677 : ℝ) / 10000 ≤ IEANTN.Li 29 ∧
    IEANTN.Li 29 ≤ 116963 / 10000 := by
  have hp := Li_28
  have hu := integral_28
  have he := Li_eq_add_integral (a := (28 : ℝ)) (x := (29 : ℝ))
    (by norm_num) (by norm_num)
  constructor <;> linarith

end FKS2PiFloor
