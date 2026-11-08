/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Nodes.LowZeroes.v1.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v1.Conclusions

/-!
# Bridge: `ZetaZeroLocations.v1` → `LowZeroes.v1.no_zeroes_below_first_ordinate`

`LowZeroes.v1` says there is no zero of `ζ` with `0 < Im ρ < 14.134725`. It follows from the
located zeros below height 1000: such a zero would have its ordinate within `10⁻²⁰` of `m / 10²⁴`
for a listed `m`, and every listed `m` is at least `14134725141734693790457252`, so
`m / 10²⁴ ≥ 14.1347251417…`, more than `10⁻⁷` above `14.134725`. That lower bound on the list is
checked by the kernel on the list itself.

## Why this is a spare rather than the designated ground

As with `Platt2017` → `Wedeniwski`: `LowZeroes.v1` records the numerical fact the literature uses,
and its designated justification says where the literature takes it from. This bridge gives the
same fact on the evidence of `ZetaZeroLocations.v1`, recompiled on every push.
-/

namespace IEANTN.Bridges.ZetaZeroLocations

open IEANTN

/-- `true` iff every entry of the list is at least `b`. -/
private def allAtLeast (b : ℕ) : List ℕ → Bool
  | [] => true
  | m :: l => Nat.ble b m && allAtLeast b l

private theorem allAtLeast_sound (b : ℕ) :
    ∀ l : List ℕ, allAtLeast b l = true → ∀ m ∈ l, b ≤ m
  | [], _, m, hm => by simp at hm
  | a :: l, hc, m, hm => by
    simp only [allAtLeast, Bool.and_eq_true, Nat.ble_eq] at hc
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hc.1
    · exact allAtLeast_sound b l hc.2 m hm

private theorem ordinates_ge :
    allAtLeast 14134725141734693790457252 ZetaZeroLocations.v1.ordinates_0_1000 = true := by
  decide +kernel

/-- The located zeros below height 1000 give the first-ordinate bound. -/
theorem bridge_zetaZeroLocations_to_lowZeroes (h : ZetaZeroLocations.v1.located_0_1000) :
    LowZeroes.v1.no_zeroes_below_first_ordinate := by
  unfold LowZeroes.v1.no_zeroes_below_first_ordinate
  have hmargin : margin 0 = 1 := by simp [margin]
  rw [hmargin, div_one]
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro s ⟨-, him, hz⟩
  have hs : s ∈ zetaZeroesIn Set.univ (Set.Ioc 0 1000) :=
    ⟨trivial, ⟨him.1, by linarith [him.2]⟩, hz⟩
  obtain ⟨-, -, m, hmem, hclose⟩ := h s hs
  have hge : (14134725141734693790457252 : ℝ) ≤ m := by
    exact_mod_cast allAtLeast_sound _ _ ordinates_ge m hmem
  have hlow := (abs_le.mp hclose).1
  have hdiv : (14134725141734693790457252 : ℝ) / 10 ^ 24 ≤ (m : ℝ) / 10 ^ 24 :=
    div_le_div_of_nonneg_right hge (by positivity)
  have hlt := him.2
  norm_num at hdiv hlow hlt
  linarith

end IEANTN.Bridges.ZetaZeroLocations
