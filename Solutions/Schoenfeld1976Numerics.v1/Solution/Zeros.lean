/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Nodes.ZetaZeroLocations.v1.Conclusions
import RSBounds.Zeros0to1000Statement
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order

/-!
From the network's statements of `ZetaZeroLocations.v1` to the statements of
`challenge/Zeros0to1000.lean` (vendored as `RSBounds.Zeros0to1000Statement`), which are the
hypotheses of `TernaryGoldbach.RSBounds.PsiTable1976.psi_error_of_zeros0to1000`.
-/

namespace Schoenfeld1976NumericsSolution

open IEANTN

/-- The two copies of the 649 integers are the same list. -/
theorem ordinates_eq : Zeros0to1000.ordinates = ZetaZeroLocations.v1.ordinates_0_1000 := rfl

theorem zerosBetween_eq :
    Zeros0to1000.zerosBetween 0 1000 = zetaZeroesIn Set.univ (Set.Ioc 0 1000) := by
  ext s
  simp only [Zeros0to1000.zerosBetween, zetaZeroesIn, zetaZeroes, Set.mem_ofPred_eq,
    Set.mem_univ, Set.mem_Ioc, true_and]
  tauto

theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hd : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hs)

/-- At `s ≠ 1`, order one in the network's sense is analytic order one. -/
theorem analyticOrderAt_eq_one {s : ℂ} (hs : s ≠ 1) (h : zetaOrder s = 1) :
    analyticOrderAt riemannZeta s = 1 := by
  rw [zetaOrder, (analyticAt_riemannZeta hs).meromorphicOrderAt_eq] at h
  cases hn : analyticOrderAt riemannZeta s with
  | top => simp [hn] at h
  | coe n =>
    rw [hn] at h
    simp only [ENat.map_natCast, WithTop.untopD_coe] at h
    have : n = 1 := by exact_mod_cast h
    simp [this]

theorem located_of (h : ZetaZeroLocations.v1.located_0_1000) :
    ∀ s ∈ Zeros0to1000.zerosBetween 0 1000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros0to1000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 := by
  intro s hs
  have hs' : s ∈ zetaZeroesIn Set.univ (Set.Ioc 0 1000) := zerosBetween_eq ▸ hs
  obtain ⟨hre, hord, hm⟩ := h s hs'
  have hne : s ≠ 1 := by
    rintro rfl
    have him : (0 : ℝ) < (1 : ℂ).im := hs.2.1
    simp at him
  exact ⟨hre, analyticOrderAt_eq_one hne hord, by rw [ordinates_eq]; exact hm⟩

theorem unique_of (h : ZetaZeroLocations.v1.unique_0_1000) :
    ∀ m ∈ Zeros0to1000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 := by
  intro m hm
  rw [ordinates_eq] at hm
  exact h m hm

theorem count_of (h : ZetaZeroLocations.v1.count_0_1000) :
    (Zeros0to1000.zerosBetween 0 1000).ncard = 649 := by
  rw [zerosBetween_eq]
  exact h

end Schoenfeld1976NumericsSolution
