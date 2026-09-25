/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section6Contour
import ZetaReal01
import IEANTN.Nodes.ZeroCount.v1.Conclusions

/-!
# Section 6: discharging `hRC` for `δ = 1`

`svm_abs_bound` and `norm_intC_le` assume that the zeros of `ζ` in `R_C = {Re ≤ 1, |Im| ≤ δ}` lie in
`Re < 0`. For `δ = 1` this is two facts:

* no zero has `0 < |Im| ≤ 2π`: `ZeroCount.v1.rvm_error_small` at `t = 2π`, where the main term is
  `-1/8`, forces `N(2π) < 7/8`, while a zero would contribute its multiplicity `≥ 1`;
* no real zero lies in `[0, 1]`: `riemannZeta_ne_zero_Ico` and Mathlib at `s = 1`.
-/

open Complex Filter Topology

namespace CH2Section6

/-- At a zero, `m(ρ) ≥ 1`. -/
theorem one_le_zetaOrder {ρ : ℂ} (hρ : ρ ≠ 1) (h0 : riemannZeta ρ = 0) : 1 ≤ IEANTN.zetaOrder ρ := by
  have ha := CH2ZetaInstance.analyticAt_riemannZeta hρ
  have hne := CH2ZetaInstance.meromorphicOrderAt_riemannZeta_ne_top ρ
  rw [ha.meromorphicOrderAt_eq] at hne
  rw [IEANTN.zetaOrder, ha.meromorphicOrderAt_eq]
  have hz : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, ha.analyticOrderAt_eq_zero]; exact not_not.mpr h0
  have hne' : analyticOrderAt riemannZeta ρ ≠ ⊤ := fun ht ↦ hne (by rw [ht]; rfl)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne'
  rw [← hn] at hz ⊢
  have hn0 : n ≠ 0 := by intro h; apply hz; rw [h]; rfl
  show (1 : ℤ) ≤ (n : ℤ)
  omega

/-- **No zero of `ζ` has `0 < Im ≤ 2π`.** -/
theorem no_zero_low (hsmall : ZeroCount.v1.rvm_error_small) {z : ℂ} (hz : riemannZeta z = 0)
    (him0 : 0 < z.im) (him : z.im ≤ 2 * Real.pi) : False := by
  have hπ := Real.pi_pos
  have h := hsmall (2 * Real.pi) (by positivity) (by linarith [Real.pi_lt_d2])
  have hmain : ZeroCount.v1.rvmMain (2 * Real.pi) = -1 / 8 := by
    rw [ZeroCount.v1.rvmMain, div_self (by positivity), Real.log_one]; norm_num
  rw [hmain, abs_lt] at h
  -- the zero set in question is finite
  set A := IEANTN.zetaZeroesIn Set.univ (Set.Ioc 0 (2 * Real.pi)) with hA
  have hfin : A.Finite := by
    set K : Set ℂ := {w | 0 ≤ w.re ∧ w.re ≤ 1 ∧ 0 ≤ w.im ∧ w.im ≤ 2 * Real.pi} with hK
    have hKc : IsCompact K := by
      rw [Metric.isCompact_iff_isClosed_bounded]
      refine ⟨(isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          ((isClosed_le continuous_const Complex.continuous_im).inter
            (isClosed_le Complex.continuous_im continuous_const))), ?_⟩
      refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1 + 2 * Real.pi, fun w hw ↦ ?_⟩
      obtain ⟨h0, h1, h2, h3⟩ := hw
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
        _ ≤ 1 + 2 * Real.pi := by rw [abs_of_nonneg h0, abs_of_nonneg h2]; linarith
    have hmem : {w : ℂ | riemannZeta₁ w ≠ 0} ∈ codiscreteWithin K :=
      Filter.codiscreteWithin_mono (Set.subset_univ K)
        CH2ZetaInstance.riemannZeta₁_ne_zero_codiscrete
    refine (hKc.finite_sdiff_of_mem_codiscreteWithin hmem).subset ?_
    rintro w ⟨-, ⟨hw0, hw1⟩, hw⟩
    have hw1' : w ≠ 1 := by rintro rfl; simp at hw0
    have hs := CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero hw hw0.ne'
    refine ⟨⟨hs.1, hs.2, hw0.le, hw1⟩, ?_⟩
    simp only [Set.mem_setOf_eq, not_not]
    rw [CH2ZetaInstance.riemannZeta₁_eq_mul hw1', hw, mul_zero]
  haveI : Finite A := hfin.to_subtype
  have hzA : z ∈ A := ⟨trivial, ⟨him0, him⟩, hz⟩
  have hne1 : ∀ w ∈ A, w ≠ 1 := by
    rintro w ⟨-, ⟨hw0, -⟩, -⟩ rfl; simp at hw0
  have hle : (1 : ℝ) * (IEANTN.zetaOrder z : ℝ) ≤ ZeroCount.v1.zetaNClosed (2 * Real.pi) := by
    rw [ZeroCount.v1.zetaNClosed, IEANTN.zetaZeroesSum]
    refine Summable.le_tsum (f := fun ρ : A ↦ (1 : ℝ) * (IEANTN.zetaOrder ρ : ℝ))
      Summable.of_finite ⟨z, hzA⟩ fun j _ ↦ ?_
    have := CH2Section6.zetaOrder_nonneg_of_ne_one (hne1 j j.2)
    simp only [one_mul]
    exact_mod_cast this
  have hm : (1 : ℝ) ≤ (IEANTN.zetaOrder z : ℝ) := by
    exact_mod_cast one_le_zetaOrder (hne1 z hzA) hz
  linarith [h.2]

/-- **`hRC` for `δ = 1`.** -/
theorem hRC_of_rvm (hsmall : ZeroCount.v1.rvm_error_small) (l : CH2.LadderParams) (hδ1 : l.δ = 1) :
    ∀ z ∈ l.RC, riemannZeta z = 0 → z.re < 0 := by
  rintro z ⟨hre, him⟩ hz
  rw [hδ1] at him
  have hπ := Real.pi_gt_three
  rcases lt_trichotomy z.im 0 with h | h | h
  · -- conjugate
    have hz' : riemannZeta (starRingEnd ℂ z) = 0 := by rw [riemannZeta_conj, hz, map_zero]
    exact (no_zero_low hsmall hz' (by simp; linarith) (by
      simp; rw [abs_of_neg h] at him; linarith)).elim
  · by_contra hge
    push Not at hge
    have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])
    rcases hre.lt_or_eq with hlt | heq
    · exact CH2ZetaReal.riemannZeta_ne_zero_Ico hge hlt (hzr ▸ hz)
    · exact riemannZeta_ne_zero_of_one_le_re (by rw [heq]) hz
  · exact (no_zero_low hsmall hz h (by rw [abs_of_pos h] at him; linarith)).elim

end CH2Section6
