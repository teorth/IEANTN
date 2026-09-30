/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.FactorialBound
import RS12.KernelLogs

open Real Finsupp Finset Chebyshev
namespace RS12Factorial

private theorem log_six_prime_powers (a b c d e f : ℕ) :
    log ((2 : ℝ)^a * 3^b * 5^c * 7^d * 11^e * 13^f) =
      a * log 2 + b * log 3 + c * log 5 + d * log 7 + e * log 11 + f * log 13 := by
  simp [Real.log_mul, Real.log_pow]

private theorem factorial_slope_expansion : slope factorialWeights =
    (545344013 / 1407656250) * log 2 +
    (373769261 / 1601600000) * log 3 +
    (7979349347 / 72072000000) * log 5 +
    (341042921 / 5148000000) * log 7 +
    (616779211 / 10920000000) * log 11 +
    (34588759 / 1848000000) * log 13 := by
  have h6 := log_six_prime_powers 1 1 0 0 0 0
  norm_num at h6
  have h10 := log_six_prime_powers 1 0 1 0 0 0
  norm_num at h10
  have h14 := log_six_prime_powers 1 0 0 1 0 0
  norm_num at h14
  have h15 := log_six_prime_powers 0 1 1 0 0 0
  norm_num at h15
  have h18 := log_six_prime_powers 1 2 0 0 0 0
  norm_num at h18
  have h20 := log_six_prime_powers 2 0 1 0 0 0
  norm_num at h20
  have h21 := log_six_prime_powers 0 1 0 1 0 0
  norm_num at h21
  have h22 := log_six_prime_powers 1 0 0 0 1 0
  norm_num at h22
  have h24 := log_six_prime_powers 3 1 0 0 0 0
  norm_num at h24
  have h26 := log_six_prime_powers 1 0 0 0 0 1
  norm_num at h26
  have h30 := log_six_prime_powers 1 1 1 0 0 0
  norm_num at h30
  have h35 := log_six_prime_powers 0 0 1 1 0 0
  norm_num at h35
  have h36 := log_six_prime_powers 2 2 0 0 0 0
  norm_num at h36
  have h39 := log_six_prime_powers 0 1 0 0 0 1
  norm_num at h39
  have h40 := log_six_prime_powers 3 0 1 0 0 0
  norm_num at h40
  have h42 := log_six_prime_powers 1 1 0 1 0 0
  norm_num at h42
  have h44 := log_six_prime_powers 2 0 0 0 1 0
  norm_num at h44
  have h55 := log_six_prime_powers 0 0 1 0 1 0
  norm_num at h55
  have h63 := log_six_prime_powers 0 2 0 1 0 0
  norm_num at h63
  have h65 := log_six_prime_powers 0 0 1 0 0 1
  norm_num at h65
  have h70 := log_six_prime_powers 1 0 1 1 0 0
  norm_num at h70
  have h78 := log_six_prime_powers 1 1 0 0 0 1
  norm_num at h78
  have h84 := log_six_prime_powers 2 1 0 1 0 0
  norm_num at h84
  have h88 := log_six_prime_powers 3 0 0 0 1 0
  norm_num at h88
  have h90 := log_six_prime_powers 1 2 1 0 0 0
  norm_num at h90
  have h91 := log_six_prime_powers 0 0 0 1 0 1
  norm_num at h91
  have h99 := log_six_prime_powers 0 2 0 0 1 0
  norm_num at h99
  have h104 := log_six_prime_powers 3 0 0 0 0 1
  norm_num at h104
  have h105 := log_six_prime_powers 0 1 1 1 0 0
  norm_num at h105
  have h110 := log_six_prime_powers 1 0 1 0 1 0
  norm_num at h110
  have h117 := log_six_prime_powers 0 2 0 0 0 1
  norm_num at h117
  have h120 := log_six_prime_powers 3 1 1 0 0 0
  norm_num at h120
  have h126 := log_six_prime_powers 1 2 0 1 0 0
  norm_num at h126
  have h130 := log_six_prime_powers 1 0 1 0 0 1
  norm_num at h130
  have h140 := log_six_prime_powers 2 0 1 1 0 0
  norm_num at h140
  have h143 := log_six_prime_powers 0 0 0 0 1 1
  norm_num at h143
  have h154 := log_six_prime_powers 1 0 0 1 1 0
  norm_num at h154
  have h156 := log_six_prime_powers 2 1 0 0 0 1
  norm_num at h156
  have h165 := log_six_prime_powers 0 1 1 0 1 0
  norm_num at h165
  have h168 := log_six_prime_powers 3 1 0 1 0 0
  norm_num at h168
  have h180 := log_six_prime_powers 2 2 1 0 0 0
  norm_num at h180
  have h182 := log_six_prime_powers 1 0 0 1 0 1
  norm_num at h182
  have h195 := log_six_prime_powers 0 1 1 0 0 1
  norm_num at h195
  have h198 := log_six_prime_powers 1 2 0 0 1 0
  norm_num at h198
  have h210 := log_six_prime_powers 1 1 1 1 0 0
  norm_num at h210
  have h220 := log_six_prime_powers 2 0 1 0 1 0
  norm_num at h220
  have h231 := log_six_prime_powers 0 1 0 1 1 0
  norm_num at h231
  have h234 := log_six_prime_powers 1 2 0 0 0 1
  norm_num at h234
  have h252 := log_six_prime_powers 2 2 0 1 0 0
  norm_num at h252
  have h260 := log_six_prime_powers 2 0 1 0 0 1
  norm_num at h260
  have h264 := log_six_prime_powers 3 1 0 0 1 0
  norm_num at h264
  have h273 := log_six_prime_powers 0 1 0 1 0 1
  norm_num at h273
  have h280 := log_six_prime_powers 3 0 1 1 0 0
  norm_num at h280
  have h286 := log_six_prime_powers 1 0 0 0 1 1
  norm_num at h286
  have h308 := log_six_prime_powers 2 0 0 1 1 0
  norm_num at h308
  have h312 := log_six_prime_powers 3 1 0 0 0 1
  norm_num at h312
  have h315 := log_six_prime_powers 0 2 1 1 0 0
  norm_num at h315
  have h330 := log_six_prime_powers 1 1 1 0 1 0
  norm_num at h330
  have h360 := log_six_prime_powers 3 2 1 0 0 0
  norm_num at h360
  have h385 := log_six_prime_powers 0 0 1 1 1 0
  norm_num at h385
  have h390 := log_six_prime_powers 1 1 1 0 0 1
  norm_num at h390
  have h396 := log_six_prime_powers 2 2 0 0 1 0
  norm_num at h396
  have h420 := log_six_prime_powers 2 1 1 1 0 0
  norm_num at h420
  have h429 := log_six_prime_powers 0 1 0 0 1 1
  norm_num at h429
  have h440 := log_six_prime_powers 3 0 1 0 1 0
  norm_num at h440
  have h455 := log_six_prime_powers 0 0 1 1 0 1
  norm_num at h455
  have h462 := log_six_prime_powers 1 1 0 1 1 0
  norm_num at h462
  have h468 := log_six_prime_powers 2 2 0 0 0 1
  norm_num at h468
  have h495 := log_six_prime_powers 0 2 1 0 1 0
  norm_num at h495
  have h504 := log_six_prime_powers 3 2 0 1 0 0
  norm_num at h504
  have h520 := log_six_prime_powers 3 0 1 0 0 1
  norm_num at h520
  have h546 := log_six_prime_powers 1 1 0 1 0 1
  norm_num at h546
  have h572 := log_six_prime_powers 2 0 0 0 1 1
  norm_num at h572
  have h585 := log_six_prime_powers 0 2 1 0 0 1
  norm_num at h585
  have h616 := log_six_prime_powers 3 0 0 1 1 0
  norm_num at h616
  have h630 := log_six_prime_powers 1 2 1 1 0 0
  norm_num at h630
  have h660 := log_six_prime_powers 2 1 1 0 1 0
  norm_num at h660
  have h693 := log_six_prime_powers 0 2 0 1 1 0
  norm_num at h693
  have h728 := log_six_prime_powers 3 0 0 1 0 1
  norm_num at h728
  have h770 := log_six_prime_powers 1 0 1 1 1 0
  norm_num at h770
  have h780 := log_six_prime_powers 2 1 1 0 0 1
  norm_num at h780
  have h792 := log_six_prime_powers 3 2 0 0 1 0
  norm_num at h792
  have h819 := log_six_prime_powers 0 2 0 1 0 1
  norm_num at h819
  have h840 := log_six_prime_powers 3 1 1 1 0 0
  norm_num at h840
  have h910 := log_six_prime_powers 1 0 1 1 0 1
  norm_num at h910
  have h924 := log_six_prime_powers 2 1 0 1 1 0
  norm_num at h924
  have h1001 := log_six_prime_powers 0 0 0 1 1 1
  norm_num at h1001
  have h1092 := log_six_prime_powers 2 1 0 1 0 1
  norm_num at h1092
  have h1155 := log_six_prime_powers 0 1 1 1 1 0
  norm_num at h1155
  have h1260 := log_six_prime_powers 2 2 1 1 0 0
  norm_num at h1260
  have h1287 := log_six_prime_powers 0 2 0 0 1 1
  norm_num at h1287
  have h1320 := log_six_prime_powers 3 1 1 0 1 0
  norm_num at h1320
  have h1365 := log_six_prime_powers 0 1 1 1 0 1
  norm_num at h1365
  have h1386 := log_six_prime_powers 1 2 0 1 1 0
  norm_num at h1386
  have h1430 := log_six_prime_powers 1 0 1 0 1 1
  norm_num at h1430
  have h1540 := log_six_prime_powers 2 0 1 1 1 0
  norm_num at h1540
  have h1560 := log_six_prime_powers 3 1 1 0 0 1
  norm_num at h1560
  have h1638 := log_six_prime_powers 1 2 0 1 0 1
  norm_num at h1638
  have h1980 := log_six_prime_powers 2 2 1 0 1 0
  norm_num at h1980
  have h2002 := log_six_prime_powers 1 0 0 1 1 1
  norm_num at h2002
  have h2145 := log_six_prime_powers 0 1 1 0 1 1
  norm_num at h2145
  have h2310 := log_six_prime_powers 1 1 1 1 1 0
  norm_num at h2310
  have h2520 := log_six_prime_powers 3 2 1 1 0 0
  norm_num at h2520
  have h2574 := log_six_prime_powers 1 2 0 0 1 1
  norm_num at h2574
  have h2730 := log_six_prime_powers 1 1 1 1 0 1
  norm_num at h2730
  have h2772 := log_six_prime_powers 2 2 0 1 1 0
  norm_num at h2772
  have h3080 := log_six_prime_powers 3 0 1 1 1 0
  norm_num at h3080
  have h3465 := log_six_prime_powers 0 2 1 1 1 0
  norm_num at h3465
  have h3640 := log_six_prime_powers 3 0 1 1 0 1
  norm_num at h3640
  have h3960 := log_six_prime_powers 3 2 1 0 1 0
  norm_num at h3960
  have h4095 := log_six_prime_powers 0 2 1 1 0 1
  norm_num at h4095
  have h4290 := log_six_prime_powers 1 1 1 0 1 1
  norm_num at h4290
  have h6006 := log_six_prime_powers 1 1 0 1 1 1
  norm_num at h6006
  have h6435 := log_six_prime_powers 0 2 1 0 1 1
  norm_num at h6435
  have h6552 := log_six_prime_powers 3 2 0 1 0 1
  norm_num at h6552
  have h8008 := log_six_prime_powers 3 0 0 1 1 1
  norm_num at h8008
  have h10920 := log_six_prime_powers 3 1 1 1 0 1
  norm_num at h10920
  have h12870 := log_six_prime_powers 1 2 1 0 1 1
  norm_num at h12870
  have h18018 := log_six_prime_powers 1 2 0 1 1 1
  norm_num at h18018
  have h20020 := log_six_prime_powers 2 0 1 1 1 1
  norm_num at h20020
  have h27720 := log_six_prime_powers 3 2 1 1 1 0
  norm_num at h27720
  have h40040 := log_six_prime_powers 3 0 1 1 1 1
  norm_num at h40040
  have h45045 := log_six_prime_powers 0 2 1 1 1 1
  norm_num at h45045
  have h72072 := log_six_prime_powers 3 2 0 1 1 1
  norm_num at h72072
  have h120120 := log_six_prime_powers 3 1 1 1 1 1
  norm_num at h120120
  have h180180 := log_six_prime_powers 2 2 1 1 1 1
  norm_num at h180180
  have h360360 := log_six_prime_powers 3 2 1 1 1 1
  norm_num at h360360
  norm_num [slope, factorialWeights, h6, h10, h14, h15, h18, h20, h21, h22, h24, h26, h30, h35, h36, h39, h40, h42, h44, h55, h63, h65, h70, h78, h84, h88, h90, h91, h99, h104, h105, h110, h117, h120, h126, h130, h140, h143, h154, h156, h165, h168, h180, h182, h195, h198, h210, h220, h231, h234, h252, h260, h264, h273, h280, h286, h308, h312, h315, h330, h360, h385, h390, h396, h420, h429, h440, h455, h462, h468, h495, h504, h520, h546, h572, h585, h616, h630, h660, h693, h728, h770, h780, h792, h819, h840, h910, h924, h1001, h1092, h1155, h1260, h1287, h1320, h1365, h1386, h1430, h1540, h1560, h1638, h1980, h2002, h2145, h2310, h2520, h2574, h2730, h2772, h3080, h3465, h3640, h3960, h4095, h4290, h6006, h6435, h6552, h8008, h10920, h12870, h18018, h20020, h27720, h40040, h45045, h72072, h120120, h180180, h360360]
  ring

theorem factorial_weights_divisors : ∀ dw ∈ factorialWeights, dw.1 ∣ 360360 := by
  decide +kernel

theorem factorial_weights_bounds : ∀ dw ∈ factorialWeights, 0 < dw.1 ∧ dw.1 ≤ 360360 := by
  decide +kernel

theorem factorial_floor_balance : floorNumerator factorialWeights 360360 = 0 := by
  decide +kernel

theorem factorial_weight_sum_nonpos : weightSum factorialWeights ≤ 0 := by
  decide +kernel

theorem factorial_weight_abs_sum_le : weightAbsSum factorialWeights ≤ 170000000 := by
  decide +kernel

private theorem factorial_balance_rat :
    (factorialWeights.map (fun dw => (dw.2 : ℚ) / 1000000 / dw.1)).sum = 0 := by
  decide +kernel

theorem factorial_balance_real :
    (factorialWeights.map (fun dw => (dw.2 : ℝ) / 1000000 / dw.1)).sum = 0 := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) factorial_balance_rat
  simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_div,
    Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_zero] using h

theorem factorial_slope_le : slope factorialWeights ≤ 1.016 := by
  rw [factorial_slope_expansion]
  linarith [kernel_log_two, kernel_log_three, kernel_log_five,
    kernel_log_seven, kernel_log_eleven, kernel_log_thirteen]

end RS12Factorial
