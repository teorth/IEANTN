/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Nodes.ZetaZeroLocations.v1.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v2.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v3.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v4.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v5.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v6.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v7.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v8.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v9.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v10.Conclusions
import IEANTN.Nodes.ZetaZeroLocations.v11.Conclusions

/-!
# Solution: `ZetaZeroLocations.v11`

Both conclusions follow from the ten ranges. A zero with `0 < Im s ≤ 10 000` lies in exactly one
range `(1000 (j − 1), 1000 j]`, whose `located` conclusion puts it on the line with order one. The
ranges are disjoint, and each is finite because its count is positive (`Set.ncard` of an infinite
set is `0`), so the counts add: `649 + 868 + … + 1164 = 10142`.
-/

open IEANTN

namespace ZetaZeroLocationsV11Solution

/-- A `located` conclusion gives real part `1/2` and order one to each zero in its range. -/
theorem pick {a b : ℝ} {L : List ℕ} {s : ℂ}
    (h : ∀ s ∈ zetaZeroesIn Set.univ (Set.Ioc a b), s.re = 1 / 2 ∧ zetaOrder s = 1 ∧
      ∃ m ∈ L, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20)
    (hz : s ∈ zetaZeroes) (ha : a < s.im) (hb : s.im ≤ b) : s.re = 1 / 2 ∧ zetaOrder s = 1 :=
  let ⟨h1, h2, _⟩ := h s ⟨trivial, ⟨ha, hb⟩, hz⟩
  ⟨h1, h2⟩

theorem split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    zetaZeroesIn Set.univ (Set.Ioc a c) =
      zetaZeroesIn Set.univ (Set.Ioc a b) ∪ zetaZeroesIn Set.univ (Set.Ioc b c) := by
  ext s
  constructor
  · rintro ⟨hr, ⟨h1, h2⟩, hz⟩
    rcases le_or_gt s.im b with h | h
    · exact Or.inl ⟨hr, ⟨h1, h⟩, hz⟩
    · exact Or.inr ⟨hr, ⟨h, h2⟩, hz⟩
  · rintro (⟨hr, ⟨h1, h2⟩, hz⟩ | ⟨hr, ⟨h1, h2⟩, hz⟩)
    · exact ⟨hr, ⟨h1, h2.trans hbc⟩, hz⟩
    · exact ⟨hr, ⟨lt_of_le_of_lt hab h1, h2⟩, hz⟩

theorem disjoint_split {a b c : ℝ} :
    Disjoint (zetaZeroesIn Set.univ (Set.Ioc a b)) (zetaZeroesIn Set.univ (Set.Ioc b c)) := by
  rw [Set.disjoint_left]
  rintro s ⟨-, ⟨-, h1⟩, -⟩ ⟨-, ⟨h2, -⟩, -⟩
  linarith

/-- Counts of adjacent ranges add, when both are positive (hence the sets finite). -/
theorem ncard_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {m n : ℕ}
    (hm : (zetaZeroesIn Set.univ (Set.Ioc a b)).ncard = m)
    (hn : (zetaZeroesIn Set.univ (Set.Ioc b c)).ncard = n) (hm0 : 0 < m) (hn0 : 0 < n) :
    (zetaZeroesIn Set.univ (Set.Ioc a c)).ncard = m + n := by
  have hfm : (zetaZeroesIn Set.univ (Set.Ioc a b)).Finite :=
    Set.finite_of_ncard_pos (hm ▸ hm0)
  have hfn : (zetaZeroesIn Set.univ (Set.Ioc b c)).Finite :=
    Set.finite_of_ncard_pos (hn ▸ hn0)
  rw [split hab hbc, Set.ncard_union_eq disjoint_split hfm hfn, hm, hn]

end ZetaZeroLocationsV11Solution

open ZetaZeroLocationsV11Solution in
theorem ZetaZeroLocations.v11.challenge_on_line_and_simple_0_10000
    (zetazerolocations_v1_located_0_1000 : ZetaZeroLocations.v1.located_0_1000)
    (zetazerolocations_v2_located_1000_2000 : ZetaZeroLocations.v2.located_1000_2000)
    (zetazerolocations_v3_located_2000_3000 : ZetaZeroLocations.v3.located_2000_3000)
    (zetazerolocations_v4_located_3000_4000 : ZetaZeroLocations.v4.located_3000_4000)
    (zetazerolocations_v5_located_4000_5000 : ZetaZeroLocations.v5.located_4000_5000)
    (zetazerolocations_v6_located_5000_6000 : ZetaZeroLocations.v6.located_5000_6000)
    (zetazerolocations_v7_located_6000_7000 : ZetaZeroLocations.v7.located_6000_7000)
    (zetazerolocations_v8_located_7000_8000 : ZetaZeroLocations.v8.located_7000_8000)
    (zetazerolocations_v9_located_8000_9000 : ZetaZeroLocations.v9.located_8000_9000)
    (zetazerolocations_v10_located_9000_10000 : ZetaZeroLocations.v10.located_9000_10000)
    : ZetaZeroLocations.v11.on_line_and_simple_0_10000 := by
  rintro s ⟨-, ⟨h0, h10000⟩, hz⟩
  rcases le_or_gt s.im 1000 with h1 | h1
  · exact pick zetazerolocations_v1_located_0_1000 hz (by linarith) h1
  rcases le_or_gt s.im 2000 with h2 | h2
  · exact pick zetazerolocations_v2_located_1000_2000 hz (by linarith) h2
  rcases le_or_gt s.im 3000 with h3 | h3
  · exact pick zetazerolocations_v3_located_2000_3000 hz (by linarith) h3
  rcases le_or_gt s.im 4000 with h4 | h4
  · exact pick zetazerolocations_v4_located_3000_4000 hz (by linarith) h4
  rcases le_or_gt s.im 5000 with h5 | h5
  · exact pick zetazerolocations_v5_located_4000_5000 hz (by linarith) h5
  rcases le_or_gt s.im 6000 with h6 | h6
  · exact pick zetazerolocations_v6_located_5000_6000 hz (by linarith) h6
  rcases le_or_gt s.im 7000 with h7 | h7
  · exact pick zetazerolocations_v7_located_6000_7000 hz (by linarith) h7
  rcases le_or_gt s.im 8000 with h8 | h8
  · exact pick zetazerolocations_v8_located_7000_8000 hz (by linarith) h8
  rcases le_or_gt s.im 9000 with h9 | h9
  · exact pick zetazerolocations_v9_located_8000_9000 hz (by linarith) h9
  exact pick zetazerolocations_v10_located_9000_10000 hz (by linarith) h10000

open ZetaZeroLocationsV11Solution in
theorem ZetaZeroLocations.v11.challenge_count_0_10000
    (zetazerolocations_v1_count_0_1000 : ZetaZeroLocations.v1.count_0_1000)
    (zetazerolocations_v2_count_1000_2000 : ZetaZeroLocations.v2.count_1000_2000)
    (zetazerolocations_v3_count_2000_3000 : ZetaZeroLocations.v3.count_2000_3000)
    (zetazerolocations_v4_count_3000_4000 : ZetaZeroLocations.v4.count_3000_4000)
    (zetazerolocations_v5_count_4000_5000 : ZetaZeroLocations.v5.count_4000_5000)
    (zetazerolocations_v6_count_5000_6000 : ZetaZeroLocations.v6.count_5000_6000)
    (zetazerolocations_v7_count_6000_7000 : ZetaZeroLocations.v7.count_6000_7000)
    (zetazerolocations_v8_count_7000_8000 : ZetaZeroLocations.v8.count_7000_8000)
    (zetazerolocations_v9_count_8000_9000 : ZetaZeroLocations.v9.count_8000_9000)
    (zetazerolocations_v10_count_9000_10000 : ZetaZeroLocations.v10.count_9000_10000)
    : ZetaZeroLocations.v11.count_0_10000 := by
  have s1 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 1000)).ncard = 649 := zetazerolocations_v1_count_0_1000
  have s2 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 2000)).ncard = 1517 :=
    ncard_split (by norm_num) (by norm_num) s1 zetazerolocations_v2_count_1000_2000 (by norm_num) (by norm_num)
  have s3 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 3000)).ncard = 2469 :=
    ncard_split (by norm_num) (by norm_num) s2 zetazerolocations_v3_count_2000_3000 (by norm_num) (by norm_num)
  have s4 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 4000)).ncard = 3474 :=
    ncard_split (by norm_num) (by norm_num) s3 zetazerolocations_v4_count_3000_4000 (by norm_num) (by norm_num)
  have s5 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 5000)).ncard = 4520 :=
    ncard_split (by norm_num) (by norm_num) s4 zetazerolocations_v5_count_4000_5000 (by norm_num) (by norm_num)
  have s6 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 6000)).ncard = 5598 :=
    ncard_split (by norm_num) (by norm_num) s5 zetazerolocations_v6_count_5000_6000 (by norm_num) (by norm_num)
  have s7 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 7000)).ncard = 6703 :=
    ncard_split (by norm_num) (by norm_num) s6 zetazerolocations_v7_count_6000_7000 (by norm_num) (by norm_num)
  have s8 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 8000)).ncard = 7830 :=
    ncard_split (by norm_num) (by norm_num) s7 zetazerolocations_v8_count_7000_8000 (by norm_num) (by norm_num)
  have s9 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 9000)).ncard = 8978 :=
    ncard_split (by norm_num) (by norm_num) s8 zetazerolocations_v9_count_8000_9000 (by norm_num) (by norm_num)
  have s10 : (zetaZeroesIn Set.univ (Set.Ioc (0 : ℝ) 10000)).ncard = 10142 :=
    ncard_split (by norm_num) (by norm_num) s9 zetazerolocations_v10_count_9000_10000 (by norm_num) (by norm_num)
  exact s10
