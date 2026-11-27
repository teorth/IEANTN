/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Teddy Tennant
-/
import LogIntegral
import Primes
import Mathlib.NumberTheory.Chebyshev
import IEANTN.Nodes.ButheNumerics.v2.Conclusions

/-!
# Solution: `ButheNumerics.v2`

`A = π(1500) − li(1500) + (1500 − θ(1500)) / log 1500`, with each term bounded separately:

* `π(1500) = 239` and `2 ^ 2109 ≤ primorial 1500`, both from `Primes`, so
  `θ(1500) ≥ 2109 log 2`;
* `log 1500 ≥ log 1024 = 10 log 2`, so `(1500 − θ(1500)) / log 1500 ≤ 5.51`;
* `li(1500) ≥ Li(1500) > 245`, from `LogIntegral`.

So `A < 239 − 245 + 5.51 < 0`. The true value is about `−3.64`.
-/

open Real

theorem ButheNumerics.v2.challenge_lemma_3_constant_nonpos :
    ButheNumerics.v2.lemma_3_constant_nonpos := by
  have hpi : IEANTN.primeCounting 1500 = 239 := by
    rw [IEANTN.primeCounting, Nat.floor_ofNat]
    exact_mod_cast ButheNumerics.v2.Dev.primeCounting_1500
  have htheta : 2109 * log 2 ≤ Chebyshev.theta 1500 := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_ofNat]
    calc 2109 * log 2 = log ((2 : ℝ) ^ 2109) := by rw [log_pow]; norm_num
      _ ≤ _ := log_le_log (by positivity) (by exact_mod_cast ButheNumerics.v2.Dev.primorial_1500)
  have hlog : 10 * log 2 ≤ log 1500 :=
    calc 10 * log 2 = log ((2 : ℝ) ^ 10) := by rw [log_pow]; norm_num
      _ ≤ log 1500 := log_le_log (by positivity) (by norm_num)
  have hli := ButheNumerics.v2.Dev.Li_1500_gt.trans_le (ButheNumerics.v2.Dev.Li_le_li (by norm_num))
  have hfrac : (1500 - Chebyshev.theta 1500) / log 1500 ≤ 5.51 := by
    rw [div_le_iff₀ (log_pos (by norm_num))]
    linarith [log_two_gt_d9]
  rw [ButheNumerics.v2.lemma_3_constant_nonpos, hpi]
  linarith
