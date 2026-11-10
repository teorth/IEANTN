/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Complex
open scoped ComplexConjugate

namespace RosserSchoenfeld.v2

/-- Recover the full open critical strip and both signs of the ordinate from
IEANTN's finite-RH predicate, preserving the inclusive height endpoint. -/
theorem finiteRH_of_network {A : ℝ} (hRH : IEANTN.RiemannHypothesisUpTo A) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      |ρ.im| ≤ A → ρ.re = 1 / 2 := by
  have right_half : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → |s.im| ≤ A →
      riemannZeta s = 0 → False := by
    intro s hs hs1 hA hz
    by_cases him : 0 ≤ s.im
    · exact hRH.false ⟨s, ⟨⟨hs, hs1⟩, ⟨him, (le_abs_self _).trans hA⟩, hz⟩⟩
    · have hzc : riemannZeta (conj s) = 0 := by rw [riemannZeta_conj, hz, map_zero]
      apply hRH.false
      refine ⟨conj s, ⟨?_, ?_, hzc⟩⟩
      · simpa using And.intro hs hs1
      · simp only [Complex.conj_im, Set.mem_Icc]
        constructor
        · linarith
        · exact (neg_le_abs _).trans hA
  intro ρ hz h0 h1 hA
  rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
  · have hnat : ∀ n : ℕ, ρ ≠ -(n : ℂ) := by
      intro n heq
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hre : ρ.re = -(n : ℝ) := by simpa using congrArg Complex.re heq
      linarith
    have hne1 : ρ ≠ 1 := by
      intro heq
      rw [heq] at h1
      norm_num at h1
    have hzr : riemannZeta (1 - ρ) = 0 := by
      rw [riemannZeta_one_sub hnat hne1, hz, mul_zero]
    exact False.elim (right_half (1 - ρ) (by simp; linarith) (by simp; linarith)
      (by simpa using hA) hzr)
  · exact heq
  · exact False.elim (right_half ρ hgt h1 hA hz)

end RosserSchoenfeld.v2
