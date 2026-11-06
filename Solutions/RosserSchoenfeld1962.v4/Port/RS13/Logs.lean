/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Port.RS13.LogData
import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace RS5Historical.Theorem13
open Real Finset LeanCert.Core.IntervalRat

@[irreducible] def primeBases : Finset ℕ := (Icc 2 216).filter Nat.Prime

def primeList : List ℕ := (List.range 217).filter (fun p => decide (Nat.Prime p))

def logChecks : Bool := primeList.all (fun p => decide
  ((lowerLog p : ℚ) / 1000000 ≤ (logPointComputable (p : ℚ) 20).lo ∧
    (logPointComputable (p : ℚ) 20).hi ≤ (upperLog p : ℚ) / 1000000))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem logChecks_true : logChecks = true := by
  unfold logChecks primeList
  decide +kernel

/-- All proposed rounded logarithms are enclosed by a kernel-checked Taylor interval. -/
theorem log_bounds {p : ℕ} (hp : p ∈ primeBases) :
    (lowerLog p : ℝ) / 1000000 ≤ log (p : ℝ) ∧
      log (p : ℝ) ≤ (upperLog p : ℝ) / 1000000 := by
  have hc := logChecks_true
  have hpL : p ∈ primeList := by
    rw [primeBases, Finset.mem_filter, Finset.mem_Icc] at hp
    simp only [primeList, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, hp.2⟩
  have hc := List.all_eq_true.mp hc p hpL
  simp only [decide_eq_true_eq] at hc
  obtain ⟨hlo, hhi⟩ := hc
  have hprime : Nat.Prime p := by
    rw [primeBases, Finset.mem_filter] at hp
    exact hp.2
  have hm := mem_logPointComputable (q := (p : ℚ))
    (by exact_mod_cast hprime.pos) 20
  constructor
  · have hl : (lowerLog p : ℝ) / 1000000 ≤ ((logPointComputable (p : ℚ) 20).lo : ℝ) := by
      have hr := (Rat.cast_le (K := ℝ)).2 hlo
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hr
    exact hl.trans (by simpa using hm.1)
  · have hu : ((logPointComputable (p : ℚ) 20).hi : ℝ) ≤ (upperLog p : ℝ) / 1000000 := by
      have hr := (Rat.cast_le (K := ℝ)).2 hhi
      simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hr
    have hm2 : log (p : ℝ) ≤ ((logPointComputable (p : ℚ) 20).hi : ℝ) := by simpa using hm.2
    exact hm2.trans hu

end RS5Historical.Theorem13
