/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import Max113.Recurrence.FactorialData00

import Max113.Recurrence.FactorialData01

import Max113.Recurrence.FactorialData02

import Max113.Recurrence.FactorialData03

import Max113.Recurrence.FactorialData04

import Max113.Recurrence.FactorialData05

import Max113.Recurrence.FactorialData06

import Max113.Recurrence.FactorialData07

import Max113.Recurrence.FactorialData08

import Max113.Recurrence.FactorialData09

import Max113.Recurrence.FactorialData10

import Max113.Recurrence.FactorialData11


namespace RS12Factorial

private theorem factorial_join_30030_90090 : ∀ n : ℕ, 30030 ≤ n → n < 90090 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_certificate_01 factorial_certificate_02


private theorem factorial_join_0_90090 : ∀ n : ℕ, 0 ≤ n → n < 90090 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_certificate_00 factorial_join_30030_90090


private theorem factorial_join_120120_180180 : ∀ n : ℕ, 120120 ≤ n → n < 180180 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_certificate_04 factorial_certificate_05


private theorem factorial_join_90090_180180 : ∀ n : ℕ, 90090 ≤ n → n < 180180 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_certificate_03 factorial_join_120120_180180


private theorem factorial_join_0_180180 : ∀ n : ℕ, 0 ≤ n → n < 180180 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_join_0_90090 factorial_join_90090_180180


private theorem factorial_join_210210_270270 : ∀ n : ℕ, 210210 ≤ n → n < 270270 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_certificate_07 factorial_certificate_08


private theorem factorial_join_180180_270270 : ∀ n : ℕ, 180180 ≤ n → n < 270270 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_certificate_06 factorial_join_210210_270270


private theorem factorial_join_300300_360360 : ∀ n : ℕ, 300300 ≤ n → n < 360360 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_certificate_10 factorial_certificate_11


private theorem factorial_join_270270_360360 : ∀ n : ℕ, 270270 ≤ n → n < 360360 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_certificate_09 factorial_join_300300_360360


private theorem factorial_join_180180_360360 : ∀ n : ℕ, 180180 ≤ n → n < 360360 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_join_180180_270270 factorial_join_270270_360360


private theorem factorial_join_0_360360 : ∀ n : ℕ, 0 ≤ n → n < 360360 →
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n := floorBlock_join factorial_join_0_180180 factorial_join_180180_360360


theorem factorial_period_bound {n : ℕ} (hn : n < 360360) :
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤
      floorNumerator factorialWeights n :=
  factorial_join_0_360360 n (Nat.zero_le n) hn

end RS12Factorial
