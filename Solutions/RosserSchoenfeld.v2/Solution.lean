/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.RosserSchoenfeld.v2.Conclusions
import RSBounds.RosserSchoenfeld1975

/-!
# Solution: `RosserSchoenfeld.v2`

The network RH predicate excludes right-half zeros at nonnegative heights. The
RSBounds predicate quantifies over the whole open critical strip and absolute
heights. Conjugation and reflection convert the former to the latter. These are
identities of the actual zeta/xi functions, with no quantitative zero-free input.
-/

open Complex TernaryGoldbach.Explicit
open scoped ComplexConjugate

namespace RosserSchoenfeld.v2

/-- Bridge from IEANTN's finite-RH vocabulary to the full-strip predicate used by
RSBounds. Both height bounds include their endpoints. -/
theorem finiteRH_of_network {A : ℝ} (hRH : IEANTN.RiemannHypothesisUpTo A) :
    TernaryGoldbach.RSBounds.Goals.FiniteRH A := by
  have right_half : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → |s.im| ≤ A →
      riemannZeta s = 0 → False := by
    intro s hs hs1 hA hz
    by_cases him : 0 ≤ s.im
    · exact hRH.false ⟨s, ⟨⟨hs, hs1⟩, ⟨him, (le_abs_self _).trans hA⟩, hz⟩⟩
    · have hξ : xiF s = 0 := (xiF_eq_zero_iff (by linarith) hs1).mpr hz
      have hξc : xiF (conj s) = 0 := by rw [xiF_conj, hξ, map_zero]
      have hzc : riemannZeta (conj s) = 0 :=
        (xiF_eq_zero_iff (by simp; linarith) (by simpa using hs1)).mp hξc
      apply hRH.false
      refine ⟨conj s, ⟨?_, ?_, hzc⟩⟩
      · simpa using And.intro hs hs1
      · simp only [Complex.conj_im, Set.mem_Icc]
        constructor
        · linarith
        · exact (neg_le_abs _).trans hA
  intro ρ hz h0 h1 hA
  rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
  · have hξ : xiF ρ = 0 := (xiF_eq_zero_iff h0 h1).mpr hz
    have hξr : xiF (1 - ρ) = 0 := by rw [xiF_one_sub, hξ]
    have hzr : riemannZeta (1 - ρ) = 0 :=
      (xiF_eq_zero_iff (by simp; linarith) (by simp; linarith)).mp hξr
    exact False.elim (right_half (1 - ρ) (by simp; linarith) (by simp; linarith)
      (by simpa using hA) hzr)
  · exact heq
  · exact False.elim (right_half ρ hgt h1 hA hz)

/-- The conditional psi estimate, with the exact network vocabulary and strict
constant, delegated to the published quartic proof after the proved RH bridge. -/
theorem challenge_psi_error_b23 : psi_error_b23 := by
  intro hRH x hx
  exact TernaryGoldbach.RSBounds.RosserSchoenfeld1975.psi_error_b23
    (finiteRH_of_network hRH) x hx

end RosserSchoenfeld.v2
