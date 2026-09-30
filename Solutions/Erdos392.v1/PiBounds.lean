/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib

/-!
# The one fact the Erdős 392 argument takes from the theory of primes

PrimeNumberTheoremAnd's development gets it from the Prime Number Theorem, as
`isLittleO_iff.mp pi_alt' one_half_pos`: eventually

`‖π(⌊x⌋) − x/log x‖ ≤ (1/2) ‖x/log x‖`.

That is the *only* consequence of `pi_alt'` either of its two uses consumes, and it does not need
the Prime Number Theorem. Chebyshev's bounds bracket `π(x)` between `(log 2)x/log x` and
`(log 4)x/log x`, and both `log 2 = 0.693…` and `log 4 = 1.386…` are within `1/2` of `1`. Mathlib
has both bounds — `Chebyshev.eventually_primeCounting_le` and `Chebyshev.pi_ge'` — so this file
reproves the fact from them and the port stays unconditional.

PNT+'s own blueprint note on the first of the two uses says exactly this: *"Use the prime number
theorem (or the Chebyshev bound)."*
-/

namespace Erdos392Sol

open Filter Real Asymptotics

/-- **`π(⌊x⌋)` is within a factor of `3/2` of `x/log x`, eventually** — in the shape the Erdős 392
proofs consume, so that they need no other change.

The upper half is Chebyshev's `π(x) ≤ (log 4 + ε)x/log x` at `ε = 1/10`, which gives `1.487…`,
comfortably below the `3/2` needed. The lower half is Chebyshev's
`π(⌊x⌋) ≥ ((x − 1) log 2 − log(x + 2))/log x`, where `log 2 − 1/2 = 0.193…` beats the `log(x + 2)`
once `log` is small against `x`. -/
theorem pi_within_half : ∀ᶠ x : ℝ in atTop,
    ‖(Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x‖ ≤ 1 / 2 * ‖x / Real.log x‖ := by
  have hup := Chebyshev.eventually_primeCounting_le (ε := 1 / 10) (by norm_num)
  have hlog : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 / 200 * ‖x‖ :=
    isLittleO_log_id_atTop.def (by norm_num)
  filter_upwards [hup, hlog, eventually_ge_atTop (10 : ℝ)] with x hxup hxlog hx10
  have hx1 : (1 : ℝ) < x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hdivpos : 0 < x / Real.log x := div_pos hxpos hlogpos
  -- `log x` and `x` are positive here, so the two norms in `hxlog` are the values themselves.
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogpos, abs_of_pos hxpos] at hxlog
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith [Real.log_two_lt_d9]
  have hlog2 : (0.6931 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hdivpos, abs_le]
  constructor
  · -- the lower half: `π(⌊x⌋) ≥ (1/2) x / log x`
    have hlogx2 : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
      have hle : x + 2 ≤ 2 * x := by linarith
      calc Real.log (x + 2) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hle
        _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) (by linarith)
    have hnum : x / 2 ≤ (x - 1) * Real.log 2 - Real.log (x + 2) := by nlinarith
    have hlow : 1 / 2 * (x / Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
      calc 1 / 2 * (x / Real.log x) = x / 2 / Real.log x := by ring
        _ ≤ ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x := by gcongr
        _ ≤ _ := Chebyshev.pi_ge' hx1
    linarith
  · -- the upper half: `π(⌊x⌋) ≤ (3/2) x / log x`, since `log 4 + 1/10 = 1.486… < 3/2`
    have hmul : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (Real.log 4 + 1 / 10) * (x / Real.log x) := by
      rw [mul_div_assoc] at hxup; exact hxup
    nlinarith [hdivpos]

/-! ### One entry from PNT+'s log tables

`Erdos392Dev` uses `LogTables.log_7_lt` at a single place, in a finite check. LogTables proves its
entries with LeanCert's `interval_decide`, which is not available here, so it is reproved from
Mathlib at the same strength: twelve Taylor terms for `exp` on `[0,1]`, and `exp 1` from
`exp_one_gt_d9`. -/

/-- Twelve Taylor terms, a lower bound for `exp` since the omitted terms are positive. -/
theorem exp_ge_taylor {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040
        + x ^ 8 / 40320 + x ^ 9 / 362880 + x ^ 10 / 3628800 + x ^ 11 / 39916800 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 12
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-- `log 7 < 1.945911`, PNT+'s `LogTables.log_7_lt`, from Mathlib. -/
theorem log_seven_lt : Real.log 7 < 1.945911 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num),
    show (1.945911 : ℝ) = ((1 : ℕ) : ℝ) + 0.945911 by norm_num, Nat.cast_one, Real.exp_add]
  have he : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have hf : (2.5751571 : ℝ) ≤ Real.exp 0.945911 :=
    le_trans (by norm_num) (exp_ge_taylor (x := 0.945911) (by norm_num))
  calc (7 : ℝ) < 2.7182818283 * 2.5751571 := by norm_num
    _ ≤ Real.exp 1 * Real.exp 0.945911 :=
        mul_le_mul he hf (by norm_num) (Real.exp_pos 1).le

end Erdos392Sol
