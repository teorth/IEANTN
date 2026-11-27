/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import CoreExpressions

namespace FKS2PiFloor

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem small_plus_2 : ∀ x ∈ Set.Icc (2.7 : ℝ) 3,
    (0 / 10000 + (x - 2) / Real.log 2 - 1) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 2 (0 / 10000) 1 2.7 3 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_2 : ∀ x ∈ Set.Icc (2.7 : ℝ) 3,
    (1 - (0 / 10000 + (x - 2) / Real.log 3)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 2 3 (0 / 10000) 1 2.7 3 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_3 : ∀ x ∈ Set.Icc (3 : ℝ) 5,
    (11238 / 10000 + (x - 3) / Real.log 3 - 2) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 3 (11238 / 10000) 2 3 5 (by norm_num) (by norm_num) (by norm_num) 2 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_3 : ∀ x ∈ Set.Icc (3 : ℝ) 5,
    (2 - (11130 / 10000 + (x - 3) / Real.log 5)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 3 5 (11130 / 10000) 2 3 5 (by norm_num) (by norm_num) (by norm_num) 4 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_5 : ∀ x ∈ Set.Icc (5 : ℝ) 7,
    (25979 / 10000 + (x - 5) / Real.log 5 - 3) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 5 (25979 / 10000) 3 5 7 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_5 : ∀ x ∈ Set.Icc (5 : ℝ) 7,
    (3 - (25809 / 10000 + (x - 5) / Real.log 7)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 5 7 (25809 / 10000) 3 5 7 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_7 : ∀ x ∈ Set.Icc (7 : ℝ) 10,
    (37217 / 10000 + (x - 7) / Real.log 7 - 4) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 7 (37217 / 10000) 4 7 10 (by norm_num) (by norm_num) (by norm_num) 2 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_7 : ∀ x ∈ Set.Icc (7 : ℝ) 10,
    (4 - (37021 / 10000 + (x - 7) / Real.log 10)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 7 10 (37021 / 10000) 4 7 10 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_10 : ∀ x ∈ Set.Icc (10 : ℝ) 11,
    (51314 / 10000 + (x - 10) / Real.log 10 - 4) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 10 (51314 / 10000) 4 10 11 (by norm_num) (by norm_num) (by norm_num) 3 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_10 : ∀ x ∈ Set.Icc (10 : ℝ) 11,
    (4 - (51096 / 10000 + (x - 10) / Real.log 11)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 10 11 (51096 / 10000) 4 10 11 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_11 : ∀ x ∈ Set.Icc (11 : ℝ) 13,
    (55571 / 10000 + (x - 11) / Real.log 11 - 5) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 11 (55571 / 10000) 5 11 13 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_11 : ∀ x ∈ Set.Icc (11 : ℝ) 13,
    (5 - (55347 / 10000 + (x - 11) / Real.log 13)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 11 13 (55347 / 10000) 5 11 13 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_13 : ∀ x ∈ Set.Icc (13 : ℝ) 17,
    (63631 / 10000 + (x - 13) / Real.log 13 - 6) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 13 (63631 / 10000) 6 13 17 (by norm_num) (by norm_num) (by norm_num) 3 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_13 : ∀ x ∈ Set.Icc (13 : ℝ) 17,
    (6 - (63398 / 10000 + (x - 13) / Real.log 17)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 13 17 (63398 / 10000) 6 13 17 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_17 : ∀ x ∈ Set.Icc (17 : ℝ) 19,
    (78438 / 10000 + (x - 17) / Real.log 17 - 7) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 17 (78438 / 10000) 7 17 19 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_17 : ∀ x ∈ Set.Icc (17 : ℝ) 19,
    (7 - (78190 / 10000 + (x - 17) / Real.log 19)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 17 19 (78190 / 10000) 7 17 19 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_19 : ∀ x ∈ Set.Icc (19 : ℝ) 23,
    (85363 / 10000 + (x - 19) / Real.log 19 - 8) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 19 (85363 / 10000) 8 19 23 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_19 : ∀ x ∈ Set.Icc (19 : ℝ) 23,
    (8 - (85108 / 10000 + (x - 19) / Real.log 23)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 19 23 (85108 / 10000) 8 19 23 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_plus_23 : ∀ x ∈ Set.Icc (23 : ℝ) 29,
    (98518 / 10000 + (x - 23) / Real.log 23 - 9) * Real.log x / x ≤ row x := by
  have h := Certificate.small_plus_core_of_check 23 (98518 / 10000) 9 23 29 (by norm_num) (by norm_num) (by norm_num) 3 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem small_minus_23 : ∀ x ∈ Set.Icc (23 : ℝ) 29,
    (9 - (98250 / 10000 + (x - 23) / Real.log 29)) * Real.log x / x ≤ row x := by
  have h := Certificate.small_minus_core_of_check 23 29 (98250 / 10000) 9 23 29 (by norm_num) (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_29 : ∀ x ∈ Set.Icc (29 : ℝ) 31,
    1 + (5 / 2) / Real.log x - (10 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 10 29 31 (by norm_num) (by norm_num) 1 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_29 : ∀ x ∈ Set.Icc (29 : ℝ) 31,
    10 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 10 29 31 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_31 : ∀ x ∈ Set.Icc (31 : ℝ) 37,
    1 + (5 / 2) / Real.log x - (11 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 11 31 37 (by norm_num) (by norm_num) 3 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_31 : ∀ x ∈ Set.Icc (31 : ℝ) 37,
    11 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 11 31 37 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_37 : ∀ x ∈ Set.Icc (37 : ℝ) 41,
    1 + (5 / 2) / Real.log x - (12 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 12 37 41 (by norm_num) (by norm_num) 2 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_37 : ∀ x ∈ Set.Icc (37 : ℝ) 41,
    12 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 12 37 41 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_41 : ∀ x ∈ Set.Icc (41 : ℝ) 43,
    1 + (5 / 2) / Real.log x - (13 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 13 41 43 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_41 : ∀ x ∈ Set.Icc (41 : ℝ) 43,
    13 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 13 41 43 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_43 : ∀ x ∈ Set.Icc (43 : ℝ) 47,
    1 + (5 / 2) / Real.log x - (14 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 14 43 47 (by norm_num) (by norm_num) 1 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_43 : ∀ x ∈ Set.Icc (43 : ℝ) 47,
    14 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 14 43 47 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_47 : ∀ x ∈ Set.Icc (47 : ℝ) 53,
    1 + (5 / 2) / Real.log x - (15 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 15 47 53 (by norm_num) (by norm_num) 1 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_47 : ∀ x ∈ Set.Icc (47 : ℝ) 53,
    15 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 15 47 53 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_53 : ∀ x ∈ Set.Icc (53 : ℝ) 59,
    1 + (5 / 2) / Real.log x - (16 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 16 53 59 (by norm_num) (by norm_num) 2 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_53 : ∀ x ∈ Set.Icc (53 : ℝ) 59,
    16 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 16 53 59 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_59 : ∀ x ∈ Set.Icc (59 : ℝ) 61,
    1 + (5 / 2) / Real.log x - (17 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 17 59 61 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_59 : ∀ x ∈ Set.Icc (59 : ℝ) 61,
    17 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 17 59 61 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_61 : ∀ x ∈ Set.Icc (61 : ℝ) 67,
    1 + (5 / 2) / Real.log x - (18 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 18 61 67 (by norm_num) (by norm_num) 1 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_61 : ∀ x ∈ Set.Icc (61 : ℝ) 67,
    18 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 18 61 67 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_67 : ∀ x ∈ Set.Icc (67 : ℝ) 71,
    1 + (5 / 2) / Real.log x - (19 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 19 67 71 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_67 : ∀ x ∈ Set.Icc (67 : ℝ) 71,
    19 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 19 67 71 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_71 : ∀ x ∈ Set.Icc (71 : ℝ) 73,
    1 + (5 / 2) / Real.log x - (20 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 20 71 73 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_71 : ∀ x ∈ Set.Icc (71 : ℝ) 73,
    20 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 20 71 73 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_73 : ∀ x ∈ Set.Icc (73 : ℝ) 79,
    1 + (5 / 2) / Real.log x - (21 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 21 73 79 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_73 : ∀ x ∈ Set.Icc (73 : ℝ) 79,
    21 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 21 73 79 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_79 : ∀ x ∈ Set.Icc (79 : ℝ) 83,
    1 + (5 / 2) / Real.log x - (22 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 22 79 83 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_79 : ∀ x ∈ Set.Icc (79 : ℝ) 83,
    22 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 22 79 83 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_83 : ∀ x ∈ Set.Icc (83 : ℝ) 89,
    1 + (5 / 2) / Real.log x - (23 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 23 83 89 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_83 : ∀ x ∈ Set.Icc (83 : ℝ) 89,
    23 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 23 83 89 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_89 : ∀ x ∈ Set.Icc (89 : ℝ) 97,
    1 + (5 / 2) / Real.log x - (24 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 24 89 97 (by norm_num) (by norm_num) 1 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_89 : ∀ x ∈ Set.Icc (89 : ℝ) 97,
    24 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 24 89 97 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_97 : ∀ x ∈ Set.Icc (97 : ℝ) 101,
    1 + (5 / 2) / Real.log x - (25 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 25 97 101 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_97 : ∀ x ∈ Set.Icc (97 : ℝ) 101,
    25 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 25 97 101 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_101 : ∀ x ∈ Set.Icc (101 : ℝ) 103,
    1 + (5 / 2) / Real.log x - (26 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 26 101 103 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_101 : ∀ x ∈ Set.Icc (101 : ℝ) 103,
    26 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 26 101 103 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_103 : ∀ x ∈ Set.Icc (103 : ℝ) 107,
    1 + (5 / 2) / Real.log x - (27 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 27 103 107 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_103 : ∀ x ∈ Set.Icc (103 : ℝ) 107,
    27 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 27 103 107 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_107 : ∀ x ∈ Set.Icc (107 : ℝ) 109,
    1 + (5 / 2) / Real.log x - (28 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 28 107 109 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_107 : ∀ x ∈ Set.Icc (107 : ℝ) 109,
    28 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 28 107 109 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_109 : ∀ x ∈ Set.Icc (109 : ℝ) 113,
    1 + (5 / 2) / Real.log x - (29 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 29 109 113 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_109 : ∀ x ∈ Set.Icc (109 : ℝ) 113,
    29 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 29 109 113 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_113 : ∀ x ∈ Set.Icc (113 : ℝ) 127,
    1 + (5 / 2) / Real.log x - (30 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 30 113 127 (by norm_num) (by norm_num) 1 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_113 : ∀ x ∈ Set.Icc (113 : ℝ) 127,
    30 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 30 113 127 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_127 : ∀ x ∈ Set.Icc (127 : ℝ) 131,
    1 + (5 / 2) / Real.log x - (31 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 31 127 131 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_127 : ∀ x ∈ Set.Icc (127 : ℝ) 131,
    31 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 31 127 131 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_131 : ∀ x ∈ Set.Icc (131 : ℝ) 137,
    1 + (5 / 2) / Real.log x - (32 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 32 131 137 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_131 : ∀ x ∈ Set.Icc (131 : ℝ) 137,
    32 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 32 131 137 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_137 : ∀ x ∈ Set.Icc (137 : ℝ) 139,
    1 + (5 / 2) / Real.log x - (33 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 33 137 139 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_137 : ∀ x ∈ Set.Icc (137 : ℝ) 139,
    33 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 33 137 139 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_139 : ∀ x ∈ Set.Icc (139 : ℝ) 149,
    1 + (5 / 2) / Real.log x - (34 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 34 139 149 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_139 : ∀ x ∈ Set.Icc (139 : ℝ) 149,
    34 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 34 139 149 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_149 : ∀ x ∈ Set.Icc (149 : ℝ) 151,
    1 + (5 / 2) / Real.log x - (35 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 35 149 151 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_149 : ∀ x ∈ Set.Icc (149 : ℝ) 151,
    35 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 35 149 151 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_151 : ∀ x ∈ Set.Icc (151 : ℝ) 157,
    1 + (5 / 2) / Real.log x - (36 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 36 151 157 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_151 : ∀ x ∈ Set.Icc (151 : ℝ) 157,
    36 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 36 151 157 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_157 : ∀ x ∈ Set.Icc (157 : ℝ) 163,
    1 + (5 / 2) / Real.log x - (37 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 37 157 163 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_157 : ∀ x ∈ Set.Icc (157 : ℝ) 163,
    37 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 37 157 163 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_163 : ∀ x ∈ Set.Icc (163 : ℝ) 167,
    1 + (5 / 2) / Real.log x - (38 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 38 163 167 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_163 : ∀ x ∈ Set.Icc (163 : ℝ) 167,
    38 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 38 163 167 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_167 : ∀ x ∈ Set.Icc (167 : ℝ) 173,
    1 + (5 / 2) / Real.log x - (39 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 39 167 173 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_167 : ∀ x ∈ Set.Icc (167 : ℝ) 173,
    39 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 39 167 173 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_173 : ∀ x ∈ Set.Icc (173 : ℝ) 179,
    1 + (5 / 2) / Real.log x - (40 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 40 173 179 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_173 : ∀ x ∈ Set.Icc (173 : ℝ) 179,
    40 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 40 173 179 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_179 : ∀ x ∈ Set.Icc (179 : ℝ) 181,
    1 + (5 / 2) / Real.log x - (41 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 41 179 181 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_179 : ∀ x ∈ Set.Icc (179 : ℝ) 181,
    41 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 41 179 181 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_181 : ∀ x ∈ Set.Icc (181 : ℝ) 191,
    1 + (5 / 2) / Real.log x - (42 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 42 181 191 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_181 : ∀ x ∈ Set.Icc (181 : ℝ) 191,
    42 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 42 181 191 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_191 : ∀ x ∈ Set.Icc (191 : ℝ) 193,
    1 + (5 / 2) / Real.log x - (43 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 43 191 193 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_191 : ∀ x ∈ Set.Icc (191 : ℝ) 193,
    43 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 43 191 193 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_193 : ∀ x ∈ Set.Icc (193 : ℝ) 197,
    1 + (5 / 2) / Real.log x - (44 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 44 193 197 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_193 : ∀ x ∈ Set.Icc (193 : ℝ) 197,
    44 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 44 193 197 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_197 : ∀ x ∈ Set.Icc (197 : ℝ) 199,
    1 + (5 / 2) / Real.log x - (45 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 45 197 199 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_197 : ∀ x ∈ Set.Icc (197 : ℝ) 199,
    45 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 45 197 199 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_199 : ∀ x ∈ Set.Icc (199 : ℝ) 211,
    1 + (5 / 2) / Real.log x - (46 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 46 199 211 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_199 : ∀ x ∈ Set.Icc (199 : ℝ) 211,
    46 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 46 199 211 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_211 : ∀ x ∈ Set.Icc (211 : ℝ) 223,
    1 + (5 / 2) / Real.log x - (47 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 47 211 223 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_211 : ∀ x ∈ Set.Icc (211 : ℝ) 223,
    47 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 47 211 223 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_223 : ∀ x ∈ Set.Icc (223 : ℝ) 227,
    1 + (5 / 2) / Real.log x - (48 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 48 223 227 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_223 : ∀ x ∈ Set.Icc (223 : ℝ) 227,
    48 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 48 223 227 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_227 : ∀ x ∈ Set.Icc (227 : ℝ) 229,
    1 + (5 / 2) / Real.log x - (49 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 49 227 229 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_227 : ∀ x ∈ Set.Icc (227 : ℝ) 229,
    49 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 49 227 229 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_229 : ∀ x ∈ Set.Icc (229 : ℝ) 233,
    1 + (5 / 2) / Real.log x - (50 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 50 229 233 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_229 : ∀ x ∈ Set.Icc (229 : ℝ) 233,
    50 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 50 229 233 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_233 : ∀ x ∈ Set.Icc (233 : ℝ) 239,
    1 + (5 / 2) / Real.log x - (51 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 51 233 239 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_233 : ∀ x ∈ Set.Icc (233 : ℝ) 239,
    51 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 51 233 239 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_239 : ∀ x ∈ Set.Icc (239 : ℝ) 241,
    1 + (5 / 2) / Real.log x - (52 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 52 239 241 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_239 : ∀ x ∈ Set.Icc (239 : ℝ) 241,
    52 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 52 239 241 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_241 : ∀ x ∈ Set.Icc (241 : ℝ) 251,
    1 + (5 / 2) / Real.log x - (53 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 53 241 251 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_241 : ∀ x ∈ Set.Icc (241 : ℝ) 251,
    53 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 53 241 251 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_251 : ∀ x ∈ Set.Icc (251 : ℝ) 257,
    1 + (5 / 2) / Real.log x - (54 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 54 251 257 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_251 : ∀ x ∈ Set.Icc (251 : ℝ) 257,
    54 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 54 251 257 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_257 : ∀ x ∈ Set.Icc (257 : ℝ) 263,
    1 + (5 / 2) / Real.log x - (55 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 55 257 263 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_257 : ∀ x ∈ Set.Icc (257 : ℝ) 263,
    55 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 55 257 263 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_263 : ∀ x ∈ Set.Icc (263 : ℝ) 269,
    1 + (5 / 2) / Real.log x - (56 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 56 263 269 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_263 : ∀ x ∈ Set.Icc (263 : ℝ) 269,
    56 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 56 263 269 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_269 : ∀ x ∈ Set.Icc (269 : ℝ) 271,
    1 + (5 / 2) / Real.log x - (57 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 57 269 271 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_269 : ∀ x ∈ Set.Icc (269 : ℝ) 271,
    57 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 57 269 271 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_271 : ∀ x ∈ Set.Icc (271 : ℝ) 277,
    1 + (5 / 2) / Real.log x - (58 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 58 271 277 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_271 : ∀ x ∈ Set.Icc (271 : ℝ) 277,
    58 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 58 271 277 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_277 : ∀ x ∈ Set.Icc (277 : ℝ) 281,
    1 + (5 / 2) / Real.log x - (59 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 59 277 281 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_277 : ∀ x ∈ Set.Icc (277 : ℝ) 281,
    59 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 59 277 281 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_281 : ∀ x ∈ Set.Icc (281 : ℝ) 283,
    1 + (5 / 2) / Real.log x - (60 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 60 281 283 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_281 : ∀ x ∈ Set.Icc (281 : ℝ) 283,
    60 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 60 281 283 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_283 : ∀ x ∈ Set.Icc (283 : ℝ) 293,
    1 + (5 / 2) / Real.log x - (61 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 61 283 293 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_283 : ∀ x ∈ Set.Icc (283 : ℝ) 293,
    61 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 61 283 293 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_293 : ∀ x ∈ Set.Icc (293 : ℝ) 307,
    1 + (5 / 2) / Real.log x - (62 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 62 293 307 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_293 : ∀ x ∈ Set.Icc (293 : ℝ) 307,
    62 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 62 293 307 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_307 : ∀ x ∈ Set.Icc (307 : ℝ) 311,
    1 + (5 / 2) / Real.log x - (63 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 63 307 311 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_307 : ∀ x ∈ Set.Icc (307 : ℝ) 311,
    63 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 63 307 311 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_311 : ∀ x ∈ Set.Icc (311 : ℝ) 313,
    1 + (5 / 2) / Real.log x - (64 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 64 311 313 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_311 : ∀ x ∈ Set.Icc (311 : ℝ) 313,
    64 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 64 311 313 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_313 : ∀ x ∈ Set.Icc (313 : ℝ) 317,
    1 + (5 / 2) / Real.log x - (65 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 65 313 317 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_313 : ∀ x ∈ Set.Icc (313 : ℝ) 317,
    65 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 65 313 317 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_317 : ∀ x ∈ Set.Icc (317 : ℝ) 331,
    1 + (5 / 2) / Real.log x - (66 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 66 317 331 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_317 : ∀ x ∈ Set.Icc (317 : ℝ) 331,
    66 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 66 317 331 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_331 : ∀ x ∈ Set.Icc (331 : ℝ) 337,
    1 + (5 / 2) / Real.log x - (67 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 67 331 337 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_331 : ∀ x ∈ Set.Icc (331 : ℝ) 337,
    67 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 67 331 337 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_337 : ∀ x ∈ Set.Icc (337 : ℝ) 347,
    1 + (5 / 2) / Real.log x - (68 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 68 337 347 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_337 : ∀ x ∈ Set.Icc (337 : ℝ) 347,
    68 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 68 337 347 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_347 : ∀ x ∈ Set.Icc (347 : ℝ) 349,
    1 + (5 / 2) / Real.log x - (69 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 69 347 349 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_347 : ∀ x ∈ Set.Icc (347 : ℝ) 349,
    69 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 69 347 349 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_349 : ∀ x ∈ Set.Icc (349 : ℝ) 353,
    1 + (5 / 2) / Real.log x - (70 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 70 349 353 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_349 : ∀ x ∈ Set.Icc (349 : ℝ) 353,
    70 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 70 349 353 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_353 : ∀ x ∈ Set.Icc (353 : ℝ) 359,
    1 + (5 / 2) / Real.log x - (71 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 71 353 359 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_353 : ∀ x ∈ Set.Icc (353 : ℝ) 359,
    71 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 71 353 359 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_359 : ∀ x ∈ Set.Icc (359 : ℝ) 367,
    1 + (5 / 2) / Real.log x - (72 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 72 359 367 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_359 : ∀ x ∈ Set.Icc (359 : ℝ) 367,
    72 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 72 359 367 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_367 : ∀ x ∈ Set.Icc (367 : ℝ) 373,
    1 + (5 / 2) / Real.log x - (73 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 73 367 373 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_367 : ∀ x ∈ Set.Icc (367 : ℝ) 373,
    73 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 73 367 373 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_373 : ∀ x ∈ Set.Icc (373 : ℝ) 379,
    1 + (5 / 2) / Real.log x - (74 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 74 373 379 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_373 : ∀ x ∈ Set.Icc (373 : ℝ) 379,
    74 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 74 373 379 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_379 : ∀ x ∈ Set.Icc (379 : ℝ) 383,
    1 + (5 / 2) / Real.log x - (75 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 75 379 383 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_379 : ∀ x ∈ Set.Icc (379 : ℝ) 383,
    75 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 75 379 383 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_383 : ∀ x ∈ Set.Icc (383 : ℝ) 389,
    1 + (5 / 2) / Real.log x - (76 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 76 383 389 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_383 : ∀ x ∈ Set.Icc (383 : ℝ) 389,
    76 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 76 383 389 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_389 : ∀ x ∈ Set.Icc (389 : ℝ) 397,
    1 + (5 / 2) / Real.log x - (77 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 77 389 397 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_389 : ∀ x ∈ Set.Icc (389 : ℝ) 397,
    77 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 77 389 397 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_397 : ∀ x ∈ Set.Icc (397 : ℝ) 401,
    1 + (5 / 2) / Real.log x - (78 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 78 397 401 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_397 : ∀ x ∈ Set.Icc (397 : ℝ) 401,
    78 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 78 397 401 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_plus_401 : ∀ x ∈ Set.Icc (401 : ℝ) 404,
    1 + (5 / 2) / Real.log x - (79 + 3.3) * Real.log x / x ≤ row x := by
  have h := Certificate.large_plus_core_of_check 79 401 404 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h

theorem large_minus_401 : ∀ x ∈ Set.Icc (401 : ℝ) 404,
    79 * Real.log x / x - 1 - 1 / Real.log x ≤ row x := by
  have h := Certificate.large_minus_core_of_check 79 401 404 (by norm_num) (by norm_num) 0 (by decide +kernel)
  norm_num at h ⊢
  exact h


end FKS2PiFloor
