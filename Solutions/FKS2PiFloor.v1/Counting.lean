/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.Tactic

namespace FKS2PiFloor

/-- A cell is half-open: its right endpoint may itself be prime. -/
theorem primeCounting_eq_on_cell {a b c : ℕ} {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x < (b : ℝ))
    (hleft : Nat.primeCounting a = c) (hright : Nat.primeCounting (b - 1) = c) :
    IEANTN.primeCounting x = (c : ℝ) := by
  have hx : 0 ≤ x := (Nat.cast_nonneg a).trans ha
  have hna : a ≤ ⌊x⌋₊ := Nat.le_floor ha
  have hnb : ⌊x⌋₊ ≤ b - 1 := by
    have := (Nat.floor_lt hx).mpr hb
    omega
  have hL := Nat.monotone_primeCounting hna
  have hU := Nat.monotone_primeCounting hnb
  rw [hleft] at hL
  rw [hright] at hU
  have heq : Nat.primeCounting ⌊x⌋₊ = c := le_antisymm hU hL
  simp only [IEANTN.primeCounting, heq]

example {x : ℝ} (hx : x ∈ Set.Ico (7 : ℝ) 11) : IEANTN.primeCounting x = 4 := by
  exact primeCounting_eq_on_cell (a := 7) (b := 11) hx.1 hx.2
    (by decide +kernel) (by decide +kernel)

end FKS2PiFloor
