/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Port.RS13.Jumps
import Port.RS13.LogData

namespace RS5Historical.Theorem13
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Proposed jump list, checked against the mathematically complete candidate set. -/
def jumpList : List ℕ := [4, 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125, 128, 169, 243, 256, 289, 343, 361, 512, 529, 625, 729, 841, 961, 1024, 1331, 1369, 1681, 1849, 2048, 2187, 2197, 2209, 2401, 2809, 3125, 3481, 3721, 4096, 4489, 4913, 5041, 5329, 6241, 6561, 6859, 6889, 7921, 8192, 9409, 10201, 10609, 11449, 11881, 12167, 12769, 14641, 15625, 16129, 16384, 16807, 17161, 18769, 19321, 19683, 22201, 22801, 24389, 24649, 26569, 27889, 28561, 29791, 29929, 32041, 32761, 32768, 36481, 37249, 38809, 39601, 44521]

theorem candidates_eq : candidates = jumpList.toFinset := by
  unfold candidates jumpList
  decide +kernel

def lowerSum (m : ℕ) : ℕ := ∑ n ∈ jumpList.toFinset,
  if n ≤ m then lowerLog n.minFac else 0

def upperSum (m : ℕ) : ℕ := ∑ n ∈ jumpList.toFinset,
  if n ≤ m then upperLog n.minFac else 0

def jumpChecks : Bool := jumpList.all (fun m => decide
  (m = 361 ∨ 25 * (upperSum m) ^ 2 ≤ 49 * 1000000000000 * m))

private theorem jumpChecks_true : jumpChecks = true := by
  decide +kernel

theorem checked_squares {m : ℕ} (hm : m ∈ candidates) (hne : m ≠ 361) :
    25 * (upperSum m) ^ 2 ≤ 49 * 1000000000000 * m := by
  rw [candidates_eq, List.mem_toFinset] at hm
  have h := List.all_eq_true.mp jumpChecks_true m hm
  simp only [decide_eq_true_eq] at h
  exact h.resolve_left hne

theorem checked_anchor : 26600000 ≤ lowerSum 361 ∧ upperSum 361 < 27097800 := by
  decide +kernel

end RS5Historical.Theorem13
