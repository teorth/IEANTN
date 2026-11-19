/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IntegralBounds
import LeanCert.Validity.Bounds.Core
import LeanCert.Validity.IntegrationDyadic

namespace FKS2PiFloor.Certificate

open LeanCert.Core LeanCert.Engine
open LeanCert.Validity LeanCert.Validity.IntegrationDyadic
open MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def config : DyadicConfig := { precision := -30, taylorDepth := 8 }

def integrand : Expr := .inv (.log (.var 0))

def unitInterval (n : ℕ) : IntervalRat := ⟨n, n + 1, by linarith⟩

theorem integral_bounds {n : ℕ} (hn : (2 : ℝ) ≤ n) (lower upper : ℚ)
    (hcheck : checkIntegralBoundsDyadicFull integrand (unitInterval n) 64
      lower upper config = true) :
    (lower : ℝ) ≤ (∫ t in (n : ℝ)..(n + 1), 1 / Real.log t) ∧
      (∫ t in (n : ℝ)..(n + 1), 1 / Real.log t) ≤ (upper : ℝ) := by
  have hi : IntervalIntegrable (fun x ↦ Expr.eval (fun _ ↦ x) integrand)
      volume (unitInterval n).lo (unitInterval n).hi := by
    simpa [unitInterval, integrand, Expr.eval] using
      (intervalIntegrable_inv_log hn (by linarith : (2 : ℝ) ≤ (n : ℝ) + 1))
  have h := integral_bounds_of_check_dyadic integrand (unitInterval n) 64 (by norm_num)
    lower upper config (by norm_num [config]) hcheck hi
  simpa [unitInterval, integrand, Expr.eval] using h

/-- A finite binary subdivision certificate. Every leaf checks its own domain. -/
def checkSplitCoreUpper (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) : ℕ → Bool
  | 0 => checkUpperBound e ⟨lo, hi, hle⟩ 0 { taylorDepth := 8 }
  | depth + 1 =>
    checkSplitCoreUpper e lo ((lo + hi) / 2) (by linarith) depth &&
      checkSplitCoreUpper e ((lo + hi) / 2) hi (by linarith) depth

theorem upper_of_checkSplitCore (e : Expr) (hsupp : ExprSupportedCore e)
    (lo hi : ℚ) (hle : lo ≤ hi) (depth : ℕ)
    (hcheck : checkSplitCoreUpper e lo hi hle depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ ↦ x) e ≤ 0 := by
  induction depth generalizing lo hi with
  | zero =>
    intro x hx
    have h := verify_upper_bound e hsupp ⟨lo, hi, hle⟩ 0 { taylorDepth := 8 } hcheck
    simpa using h x hx
  | succ depth ih =>
    simp only [checkSplitCoreUpper, Bool.and_eq_true] at hcheck
    intro x hx
    by_cases hm : x ≤ ((lo + hi) / 2 : ℚ)
    · exact ih lo ((lo + hi) / 2) (by linarith) hcheck.1 x ⟨hx.1, hm⟩
    · exact ih ((lo + hi) / 2) hi (by linarith) hcheck.2 x ⟨(lt_of_not_ge hm).le, hx.2⟩

end FKS2PiFloor.Certificate
