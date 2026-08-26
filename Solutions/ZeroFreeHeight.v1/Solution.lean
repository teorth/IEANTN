/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.ZeroFreeHeight.v1.Conclusions
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Solution: `ZeroFreeHeight.v1`

Proves the same declarations `Challenge.lean` states. Do **not** import the challenge module —
Comparator compares two modules declaring the same names, so importing it would collide.

## The argument

Fix `σ` and a height `t ≥ t₀`, with `σ` in the region. There are two cases.

If `t ≥ t₁` the given region already covers it, and there is nothing to do.

Otherwise `t₀ ≤ t < t₁ ≤ T`, so `t` lies under the verified height, and the claim is that the
region contains no zero there at all. The region at height `t` is `σ ≥ 1 - 1/(R log t)`, and the
hypothesis `exp (2 / R) < t₀ ≤ t` gives `R log t > 2`, hence `1 - 1/(R log t) > 1/2`. So any `σ` in
the region satisfies `σ > 1/2`, and splits again: either `σ ≥ 1`, where `ζ` does not vanish by the
classical non-vanishing theorem (Mathlib's `riemannZeta_ne_zero_of_one_le_re`), or `1/2 < σ < 1`,
where a zero would sit in the rectangle the verification has already emptied.

The strict inequality `exp (2 / R) < t₀` is doing real work in the second case. With `≤` in its
place the region would reach `Re s = 1/2` exactly, which is where the nontrivial zeroes live and
where `RiemannHypothesisUpTo` says nothing.
-/

open IEANTN

theorem ZeroFreeHeight.v1.challenge_classical_region_descends :
    ZeroFreeHeight.v1.classical_region_descends := by
  intro R t₀ t₁ T hR ht₀ h01 h1T hRH hreg σ t ht hσ
  rcases le_or_gt t₁ t with h | h
  · exact hreg σ t h hσ
  -- `t₀ ≤ t < t₁ ≤ T`, so `t` is under the verified height.
  have hR2 : 0 < 2 / R := by positivity
  have hexp : (1 : ℝ) < Real.exp (2 / R) := by simpa using Real.exp_lt_exp.mpr hR2
  have h1t₀ : (1 : ℝ) < t₀ := lt_trans hexp ht₀
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (lt_trans one_pos h1t₀) ht
  -- the region stays strictly right of the critical line
  have hlog : 2 / R < Real.log t := by
    have hmono : Real.log t₀ ≤ Real.log t := Real.log_le_log (by linarith) ht
    have h2 : 2 / R < Real.log t₀ := by
      simpa [Real.log_exp] using Real.log_lt_log (Real.exp_pos (2 / R)) ht₀
    linarith
  have hRlog : 2 < R * Real.log t := by
    have := (div_lt_iff₀ hR).mp hlog
    linarith
  have hhalf : (1 : ℝ) / 2 < 1 - 1 / (R * Real.log t) := by
    have hpos : 0 < R * Real.log t := by linarith
    have : 1 / (R * Real.log t) < 1 / 2 := by
      apply one_div_lt_one_div_of_lt <;> linarith
    linarith
  have hσhalf : (1 : ℝ) / 2 < σ := lt_of_lt_of_le hhalf hσ
  rcases le_or_gt 1 σ with hone | hone
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hone)
  · intro hzero
    have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈
        zetaZeroesIn (Set.Ioo (1 / 2 : ℝ) 1) (Set.Icc 0 T) := by
      refine ⟨?_, ?_, hzero⟩
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
          neg_zero, add_zero, Set.mem_Ioo]
        constructor <;> linarith
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
          zero_add, Set.mem_Icc]
        constructor <;> linarith
    exact hRH.false ⟨_, hmem⟩
