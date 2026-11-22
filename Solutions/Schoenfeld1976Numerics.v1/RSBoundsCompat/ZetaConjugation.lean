/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Terence Tao
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.Linarith

/-!
Compatibility helpers for the pinned IEANTN environment. The theorem blocks below are copied from Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679: Gamma/Deligne.lean and Harmonic/ZetaAsymp.lean.
They are absent at IEANTN's Mathlib pin. Imports and namespace wrappers are adapted.
-/
open Real Complex
open scoped ComplexConjugate

namespace RSBoundsCompat

namespace Complex

/-- The Gamma factor `Γ_ℝ` commutes with complex conjugation. -/
lemma Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  have hpi : (π : ℂ).arg ≠ π := by
    rw [arg_ofReal_of_nonneg pi_pos.le]
    exact pi_pos.ne
  have h := cpow_conj (π : ℂ) (-s / 2) hpi
  rw [conj_ofReal] at h
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Gamma_conj, ← h]
  congr 2 <;> simp [map_div₀, map_neg, map_ofNat]

end Complex

/-- **Conjugation symmetry of the completed zeta function** for `0 < re s`, where the
relation `Λ s = ζ s * Γ_ℝ s` is available. -/
private theorem completedRiemannZeta_conj_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  have hcs : 0 < (conj s).re := by rwa [conj_re]
  have key {z : ℂ} (hz : 0 < z.re) : completedRiemannZeta z = riemannZeta z * Gammaℝ z := by
    have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
    rw [riemannZeta_def_of_ne_zero hz0]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hz)).symm
  rw [key hcs, key hs, map_mul, riemannZeta_conj, Complex.Gammaℝ_conj]

-- TODO: prove the analogous conjugation symmetry for `completedHurwitzZetaEven`,
-- `completedHurwitzZetaOdd` and `DirichletCharacter.completedLFunction`, and deduce this
-- lemma as a special case.
/-- **Conjugation symmetry of the completed zeta function**: `Λ (conj s) = conj (Λ s)`.

For `0 < re s` this is `riemannZeta_conj` together with `Gammaℝ_conj`; the remaining
half-plane follows from the functional equation `completedRiemannZeta_one_sub`. -/
@[simp]
theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  rcases lt_or_ge 0 s.re with hs | hs
  · exact completedRiemannZeta_conj_of_re_pos hs
  · have h1 : 0 < (1 - s).re := by simp only [sub_re, one_re]; linarith
    have hcs : conj (1 - s) = 1 - conj s := by simp
    have := completedRiemannZeta_conj_of_re_pos h1
    rwa [hcs, completedRiemannZeta_one_sub, completedRiemannZeta_one_sub] at this


end RSBoundsCompat
