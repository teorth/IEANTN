/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Counting
import Envelopes
import RowBound

namespace FKS2PiFloor

theorem small_cell_bound {a b c : ℕ} {lo L U x : ℝ}
    (ha : (2 : ℝ) ≤ a) (halo : (a : ℝ) ≤ lo) (hlo : 1 < lo)
    (hx : x ∈ Set.Ico lo (b : ℝ))
    (hleft : Nat.primeCounting a = c) (hright : Nat.primeCounting (b - 1) = c)
    (hL : L ≤ IEANTN.Li a) (hU : IEANTN.Li a ≤ U)
    (hplus : ∀ y ∈ Set.Icc lo (b : ℝ),
      (U + (y - a) / Real.log a - c) * Real.log y / y ≤ row y)
    (hminus : ∀ y ∈ Set.Icc lo (b : ℝ),
      (c - (L + (y - a) / Real.log b)) * Real.log y / y ≤ row y) :
    IEANTN.Eπ x ≤ row x := by
  have hax : (a : ℝ) ≤ x := halo.trans hx.1
  have hcount := primeCounting_eq_on_cell hax hx.2 hleft hright
  apply Epi_le_of_enclosures (hlo.trans_le hx.1)
    ((add_le_add hL le_rfl).trans (Li_add_div_log_le ha hax hx.2.le))
    ((Li_le_add_div_log ha hax).trans (add_le_add hU le_rfl))
  · rw [hcount]
    exact hplus x ⟨hx.1, hx.2.le⟩
  · rw [hcount]
    exact hminus x ⟨hx.1, hx.2.le⟩

theorem upper_normalized_identity {x : ℝ} (hx : 1 < x) (p : ℝ) :
    (primitive (5 / 2) x - 3.3 - p) * Real.log x / x =
      1 + (5 / 2) / Real.log x - (p + 3.3) * Real.log x / x := by
  have hx0 : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold primitive
  field_simp
  ring

theorem lower_normalized_identity {x : ℝ} (hx : 1 < x) (p : ℝ) :
    (p - primitive 1 x) * Real.log x / x =
      p * Real.log x / x - 1 - 1 / Real.log x := by
  have hx0 : x ≠ 0 := (lt_trans zero_lt_one hx).ne'
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold primitive
  field_simp
  ring

theorem large_cell_bound {a b c : ℕ} {x : ℝ}
    (ha : (29 : ℝ) ≤ a) (hx : x ∈ Set.Ico (a : ℝ) b)
    (hleft : Nat.primeCounting a = c) (hright : Nat.primeCounting (b - 1) = c)
    (hL : primitive 1 x ≤ IEANTN.Li x)
    (hU : IEANTN.Li x ≤ primitive (5 / 2) x - 3.3)
    (hplus : ∀ y ∈ Set.Icc (a : ℝ) b,
      1 + (5 / 2) / Real.log y - (c + 3.3) * Real.log y / y ≤ row y)
    (hminus : ∀ y ∈ Set.Icc (a : ℝ) b,
      c * Real.log y / y - 1 - 1 / Real.log y ≤ row y) :
    IEANTN.Eπ x ≤ row x := by
  have hx1 : 1 < x := by linarith [hx.1]
  have hcount := primeCounting_eq_on_cell hx.1 hx.2 hleft hright
  apply Epi_le_of_enclosures hx1 hL hU
  · rw [hcount, upper_normalized_identity hx1]
    exact hplus x ⟨hx.1, hx.2.le⟩
  · rw [hcount, lower_normalized_identity hx1]
    exact hminus x ⟨hx.1, hx.2.le⟩

end FKS2PiFloor
