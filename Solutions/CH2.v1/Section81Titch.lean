/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section81Janframe
import GammaAnalytic
import IEANTN.Nodes.ZetaHadamard.v1.Conclusions

/-!
# Section 8.1: `prop:titch96A`

For `s = σ + it`, `-1/2 ≤ σ ≤ 1`, `t ≥ 1000`, `ζ(s) ≠ 0`, and the zeros with ordinate in
`(t - 1/4, t + 1/4]` on the critical line,

`|ζ'/ζ(s) - ∑_{t-1/4 < γ ≤ t+1/4} 1/(s-ρ)| ≤ κ₁ log(t/2π) + κ₂ (2 log t/5 + 4) + 1.5053 + 0.011`

with `κ₁ = (4(3/2-σ) + 1/4)/π` and `κ₂ = 32(3/2-σ) - 1`: the paper's statement at `a = 1/4`,
`σ₊ = 3/2`, with `ε = 0.011` in place of `0.00202` (the digamma difference is bounded crudely from
its Gauss series, and `lem:janframe` carries `0.004`).

The input is `ZetaHadamard.v1` (the partial-fraction expansion, subtracted at `s` and `3/2 + it`).
-/

open Complex Filter Topology Set MeasureTheory

namespace CH2Section81

/-! ### `|ζ'/ζ(w)| ≤ 1.5053` on `Re w ≥ 3/2` -/

open ArithmeticFunction in
theorem term_real_eq_ofReal_norm (x : ℝ) (n : ℕ) :
    LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (x : ℂ) n
      = ((‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (x : ℂ) n‖ : ℝ) : ℂ) := by
  rw [LSeries.norm_term_eq, LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [if_neg hn]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcast : ((n : ℂ)) ^ (x : ℂ) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hn0]; norm_num
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
    simp [abs_of_nonneg (Real.rpow_nonneg hn0 x)]

open ArithmeticFunction in
theorem norm_logDeriv_zeta_le_three_halves (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    {w : ℂ} (ht : 3 / 2 ≤ w.re) : ‖deriv riemannZeta w / riemannZeta w‖ ≤ 1.5053 := by
  obtain ⟨c, hc, hceq⟩ := hv
  have hmargin : IEANTN.margin 0 = 1 := by simp [IEANTN.margin]
  rw [hmargin, one_mul] at hc
  have hcabs := abs_le.mp hc
  have hret : (1 : ℝ) < w.re := by linarith
  have hre2 : (1 : ℝ) < (((3 / 2 : ℝ) : ℂ)).re := by norm_num
  have hLt := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hret
  have hL2 := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre2
  rw [neg_div, show (((3 / 2 : ℝ) : ℂ)) = 3 / 2 by push_cast; ring, hceq] at hL2
  have hsum2 : HasSum (fun n : ℕ ↦ ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (((3 / 2 : ℝ) : ℂ)) n‖) (-c) := by
    rw [← Complex.hasSum_ofReal]
    have h : HasSum (LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (((3 / 2 : ℝ) : ℂ)))
        (LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) (((3 / 2 : ℝ) : ℂ))) :=
      (LSeriesSummable_vonMangoldt hre2).hasSum
    have hval : LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) (((3 / 2 : ℝ) : ℂ)) = ((-c : ℝ) : ℂ) := by
      rw [show (((3 / 2 : ℝ) : ℂ)) = 3 / 2 by push_cast; ring, hL2]; push_cast; ring
    rw [hval] at h
    exact h.congr_fun fun n ↦ (term_real_eq_ofReal_norm (3 / 2) n).symm
  have hmono : ∀ n : ℕ, ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) w n‖
      ≤ ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) (((3 / 2 : ℝ) : ℂ)) n‖ := by
    intro n
    refine LSeries.norm_term_le_of_re_le_re _ ?_ n
    simp only [Complex.ofReal_re]; linarith
  have hsumt : Summable fun n : ℕ ↦ ‖LSeries.term (fun n ↦ ((Λ n : ℝ) : ℂ)) w n‖ :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hmono hsum2.summable
  have hLtnorm : ‖LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) w‖ ≤ -c := by
    rw [LSeries]
    refine le_trans (norm_tsum_le_tsum_norm hsumt) ?_
    rw [← hsum2.tsum_eq]
    exact Summable.tsum_le_tsum hmono hsumt hsum2.summable
  have hEq : ‖deriv riemannZeta w / riemannZeta w‖ = ‖LSeries (fun n ↦ ((Λ n : ℝ) : ℂ)) w‖ := by
    rw [hLt, neg_div, norm_neg]
  rw [hEq]
  have hmargin' : (1e-6 : ℝ) ≥ |c - (-1.505235)| := by linarith [abs_le.mpr hcabs]
  linarith [hcabs.1]

/-! ### The digamma difference, from the Gauss series -/

/-- `∑_{k ≥ 0} 1/(k+y)² ≤ 1/y² + 1/y` for `y ≥ 1`, by telescoping. -/
theorem hasSum_telescope_inv {y : ℝ} (hy : 0 < y) :
    HasSum (fun k : ℕ ↦ 1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y)) (1 / y) := by
  have hpos : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y) := by
    intro k
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [sub_nonneg]; apply one_div_le_one_div_of_le (by positivity); linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hpos]
  have e : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + y) - 1 / ((k : ℝ) + 1 + y))
      = 1 / y - 1 / ((n : ℝ) + y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  simp_rw [e]
  have : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + y)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ y tendsto_natCast_atTop_atTop)
  simpa using tendsto_const_nhds.sub this

theorem norm_digamma_sub_le {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re) (him : z₁.im = z₂.im)
    (hy : 2 ≤ z₁.im) :
    ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ ‖z₁ - z₂‖ * (4 / z₁.im) := by
  set y := z₁.im with hy_def
  have hy0 : 0 < y := by linarith
  have hn1 : ∀ n : ℕ, z₁ ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn2 : ∀ n : ℕ, z₂ ≠ -n := fun n h ↦ by
    have := congrArg Complex.re h; simp at this; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hs1 := GammaSolution.summable_gaussTerm hn1
  have hs2 := GammaSolution.summable_gaussTerm hn2
  have hdiff : Complex.digamma z₁ - Complex.digamma z₂
      = ∑' k, (GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k) := by
    rw [GammaSolution.digamma_eq_gaussSum h1, GammaSolution.digamma_eq_gaussSum h2,
      GammaSolution.gaussSum, GammaSolution.gaussSum, hs1.tsum_sub hs2]
    ring
  -- the termwise bound
  have hk : ∀ k : ℕ, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖
      ≤ ‖z₁ - z₂‖ * 2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1))) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h ↦ hn1 k (by linear_combination h)
    have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h ↦ hn2 k (by linear_combination h)
    have e : GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k
        = (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
      simp only [GammaSolution.gaussTerm]; field_simp; ring
    have hnorm : ∀ z : ℂ, 0 < z.re → z.im = y → (k : ℝ) ^ 2 + y ^ 2 ≤ ‖(k : ℂ) + z‖ ^ 2 := by
      intro z hz hzi
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, zero_add, hzi]
      nlinarith
    have hp1 := hnorm z₁ h1 rfl
    have hp2 := hnorm z₂ h2 him.symm
    have hprod : ((k : ℝ) + y) ^ 2 / 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
      rw [norm_mul]
      have ha := norm_nonneg ((k : ℂ) + z₁)
      have hb := norm_nonneg ((k : ℂ) + z₂)
      have : ((k : ℝ) + y) ^ 2 / 2 ≤ (k : ℝ) ^ 2 + y ^ 2 := by nlinarith [sq_nonneg ((k:ℝ) - y)]
      have hc1 : Real.sqrt ((k : ℝ) ^ 2 + y ^ 2) ≤ ‖(k : ℂ) + z₁‖ := by
        have := Real.sqrt_le_sqrt hp1; rwa [Real.sqrt_sq ha] at this
      have hc2 : Real.sqrt ((k : ℝ) ^ 2 + y ^ 2) ≤ ‖(k : ℂ) + z₂‖ := by
        have := Real.sqrt_le_sqrt hp2; rwa [Real.sqrt_sq hb] at this
      have hmm := mul_le_mul hc1 hc2 (Real.sqrt_nonneg _) ha
      rw [Real.mul_self_sqrt (by positivity)] at hmm
      linarith
    have htel : 2 / ((k : ℝ) + y) ^ 2 ≤ 2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1))) := by
      have hky : 0 < (k : ℝ) + (y - 1) := by linarith
      have hky' : 0 < (k : ℝ) + y := by linarith
      have h3 : 1 / ((k : ℝ) + y) ^ 2 ≤ 1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1)) := by
        rw [show (k : ℝ) + 1 + (y - 1) = (k : ℝ) + y by ring, div_sub_div _ _ hky.ne' hky'.ne',
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e2 : 2 / ((k : ℝ) + y) ^ 2 = 2 * (1 / ((k : ℝ) + y) ^ 2) := by ring
      rw [e2]; linarith
    rw [e, norm_div]
    calc ‖z₁ - z₂‖ / ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖
        ≤ ‖z₁ - z₂‖ / (((k : ℝ) + y) ^ 2 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hprod
      _ = ‖z₁ - z₂‖ * (2 / ((k : ℝ) + y) ^ 2) := by field_simp
      _ ≤ ‖z₁ - z₂‖ * (2 * (1 / ((k : ℝ) + (y - 1)) - 1 / ((k : ℝ) + 1 + (y - 1)))) :=
          mul_le_mul_of_nonneg_left htel (norm_nonneg _)
      _ = _ := by ring
  have htele := (hasSum_telescope_inv (y := y - 1) (by linarith)).mul_left (‖z₁ - z₂‖ * 2)
  have hsumn : Summable fun k : ℕ ↦ ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hk htele.summable
  rw [hdiff]
  calc _ ≤ ∑' k, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ := norm_tsum_le_tsum_norm hsumn
    _ ≤ ‖z₁ - z₂‖ * 2 * (1 / (y - 1)) := by
        rw [← htele.tsum_eq]; exact Summable.tsum_le_tsum hk hsumn htele.summable
    _ ≤ ‖z₁ - z₂‖ * (4 / y) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have : 1 / (y - 1) ≤ 2 / y := by rw [div_le_div_iff₀ (by linarith) hy0]; nlinarith
        have e : 4 / y = 2 * (2 / y) := by ring
        rw [e]; linarith

/-! ### `cor:zeroinbox` for `a = 1/4` -/

theorem zsum_one_Ioc {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc u v) (fun _ ↦ (1 : ℝ))
      = ZeroCount.v1.zetaNClosed v - ZeroCount.v1.zetaNClosed u := by
  have h := CH2Section7A.zsum_split (a := u) (b := v) hu huv (fun _ ↦ (1 : ℝ))
  unfold ZeroCount.v1.zetaNClosed
  linarith

theorem inner_count_le (hrvm : ZeroCount.v1.rvm_error_bound) {t : ℝ} (ht : 1000 ≤ t) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)) (fun _ ↦ (1 : ℝ))
      ≤ (ZeroCount.v1.zetaNClosed (t + 1 / 4) - ZeroCount.v1.rvmMain (t + 1 / 4))
        - (ZeroCount.v1.zetaNClosed (t - 1 / 4) - ZeroCount.v1.rvmMain (t - 1 / 4))
        + 1 / (4 * Real.pi) * Real.log (t / (2 * Real.pi)) + 0.00003 := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_three
  rw [zsum_one_Ioc (by linarith) (by linarith)]
  -- the main term by the mean value theorem
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope ZeroCount.v1.rvmMain
    (fun u ↦ Real.log (u / (2 * Real.pi)) / (2 * Real.pi)) (by linarith : t - 1 / 4 < t + 1 / 4)
    (fun u hu ↦ (hasDerivAt_rvmMain (by linarith [hu.1])).continuousAt.continuousWithinAt)
    (fun u hu ↦ hasDerivAt_rvmMain (by linarith [hu.1]))
  have hc0 : 0 < c := by linarith [hc.1]
  have hlogc : Real.log (c / (2 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) + 1 / (4 * t) := by
    have h1 : Real.log (c / (2 * Real.pi)) ≤ Real.log ((t + 1 / 4) / (2 * Real.pi)) :=
      Real.log_le_log (by positivity) (by gcongr; linarith [hc.2])
    have h2 : Real.log ((t + 1 / 4) / (2 * Real.pi)) = Real.log (t / (2 * Real.pi)) + Real.log (1 + 1 / (4 * t)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h3 := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (4 * t) by positivity)
    linarith
  have hM : ZeroCount.v1.rvmMain (t + 1 / 4) - ZeroCount.v1.rvmMain (t - 1 / 4)
      ≤ 1 / (4 * Real.pi) * Real.log (t / (2 * Real.pi)) + 0.00003 := by
    have e : ZeroCount.v1.rvmMain (t + 1 / 4) - ZeroCount.v1.rvmMain (t - 1 / 4)
        = (1 / 2) * (Real.log (c / (2 * Real.pi)) / (2 * Real.pi)) := by
      rw [hceq]; field_simp; ring
    rw [e]
    have h4 : 1 / (4 * t) / (4 * Real.pi) ≤ 0.00003 := by
      rw [div_div, div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul ht hπ1.le (by norm_num) (by linarith)]
    have e2 : (1 / 2) * ((Real.log (t / (2 * Real.pi)) + 1 / (4 * t)) / (2 * Real.pi))
        = 1 / (4 * Real.pi) * Real.log (t / (2 * Real.pi)) + 1 / (4 * t) / (4 * Real.pi) := by
      field_simp; ring
    have h5 : (1 / 2) * (Real.log (c / (2 * Real.pi)) / (2 * Real.pi))
        ≤ (1 / 2) * ((Real.log (t / (2 * Real.pi)) + 1 / (4 * t)) / (2 * Real.pi)) := by
      gcongr
    linarith
  linarith

/-! ### Non-trivial zeros -/

theorem re_pos_of_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (him : ρ.im ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hs := CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero hz him
  refine ⟨?_, ?_⟩
  · rcases hs.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have hn : ∀ n : ℕ, ρ ≠ -n := by intro n hn; rw [hn] at him; simp at him
      have h1 : ρ ≠ 1 := by intro h1; rw [h1] at him; simp at him
      have hz1 : riemannZeta (1 - ρ) = 0 := by rw [riemannZeta_one_sub hn h1, hz, mul_zero]
      exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith) hz1
  · rcases hs.2.lt_or_eq with h | h
    · exact h
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re h.ge)

theorem im_ne_zero_of_nontrivial {ρ : ℂ} (hρ : ρ ∈ IEANTN.zetaZeroesIn (Set.Ioo 0 1) Set.univ) :
    ρ.im ≠ 0 := by
  intro h
  obtain ⟨⟨h0, h1⟩, -, hz⟩ := hρ
  have hρr : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])
  exact CH2ZetaReal.riemannZeta_ne_zero_Ico h0.le h1 (hρr ▸ hz)

/-! ### The outer sum, at any finite stage -/

theorem outer_finset_le (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    {t : ℝ} (ht : 1000 ≤ t) (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ ρ.im ≠ 0 ∧ (ρ.im ≤ t - 1 / 4 ∨ t + 1 / 4 < ρ.im)) :
    ∑ ρ ∈ F, (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2)
      ≤ 4 / Real.pi * Real.log (t / (2 * Real.pi))
        + 16 * (2 / 5 * Real.log t + 4
          + (ZeroCount.v1.zetaNClosed (t - 1 / 4) - ZeroCount.v1.rvmMain (t - 1 / 4))
          - (ZeroCount.v1.zetaNClosed (t + 1 / 4) - ZeroCount.v1.rvmMain (t + 1 / 4))) + 0.004 := by
  set Y : ℝ := t + 1 / 4 + ∑ ρ ∈ F, |ρ.im| with hY
  have hYge : ∀ ρ ∈ F, |ρ.im| ≤ Y - (t + 1 / 4) := by
    intro ρ hρ
    rw [hY]; simp only [add_sub_cancel_left]
    exact Finset.single_le_sum (f := fun ρ ↦ |ρ.im|) (fun _ _ ↦ abs_nonneg _) hρ
  have hsum0 : 0 ≤ ∑ ρ ∈ F, |ρ.im| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hJ := janframe hrvm hsmall ht (Y := Y) (by rw [hY]; linarith)
  have hm0 : ∀ ρ ∈ F, (0 : ℝ) ≤ IEANTN.zetaOrder ρ := by
    intro ρ hρ
    have h1 : ρ ≠ 1 := by intro h; have := (hF ρ hρ).2.1; rw [h] at this; simp at this
    exact_mod_cast CH2Section6.zetaOrder_nonneg_of_ne_one h1
  -- split `F` by position
  set F1 := F.filter (fun ρ ↦ t + 1 / 4 < ρ.im) with hF1
  set F2 := F.filter (fun ρ ↦ 0 < ρ.im ∧ ρ.im ≤ t - 1 / 4) with hF2
  set F3 := F.filter (fun ρ ↦ ρ.im < 0) with hF3
  have hsplit : ∑ ρ ∈ F, (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2)
      = ∑ ρ ∈ F1, (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2)
        + ∑ ρ ∈ F2, (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2)
        + ∑ ρ ∈ F3, (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2) := by
    rw [hF1, hF2, hF3, ← Finset.sum_union, ← Finset.sum_union]
    · congr 1
      ext ρ
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hρ
        obtain ⟨-, hne, hpos⟩ := hF ρ hρ
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inr ⟨hρ, h⟩
        · rcases hpos with h' | h'
          · exact Or.inl (Or.inr ⟨hρ, h, h'⟩)
          · exact Or.inl (Or.inl ⟨hρ, h'⟩)
      · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h
    · rw [Finset.disjoint_left]
      intro ρ hρ hρ'
      simp only [Finset.mem_union, Finset.mem_filter] at hρ hρ'
      rcases hρ with ⟨-, h⟩ | ⟨-, h, -⟩ <;> linarith [hρ'.2]
    · rw [Finset.disjoint_left]
      intro ρ hρ hρ'
      simp only [Finset.mem_filter] at hρ hρ'
      linarith [hρ.2, hρ'.2.2]
  -- each part against a finite zero sum
  have hZ : ∀ {a b : ℝ} (ha : 0 ≤ a) (G : Finset ℂ) (f : ℂ → ℝ),
      (∀ ρ ∈ G, ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc a b)) → (∀ ρ, 0 ≤ f ρ) →
      ∑ ρ ∈ G, (IEANTN.zetaOrder ρ : ℝ) * f ρ ≤ IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) f := by
    intro a b ha G f hG hf
    have hfin := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin]
    calc ∑ ρ ∈ G, (IEANTN.zetaOrder ρ : ℝ) * f ρ = ∑ ρ ∈ G, f ρ * (IEANTN.zetaOrder ρ : ℝ) :=
          Finset.sum_congr rfl fun _ _ ↦ by ring
      _ ≤ ∑ ρ ∈ hfin.toFinset, f ρ * (IEANTN.zetaOrder ρ : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ ↦ (Set.Finite.mem_toFinset hfin).mpr (hG ρ hρ))
            fun ρ hρ _ ↦ ?_
          have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
          have h1 : ρ ≠ 1 := by
            intro h; have := hρ'.2.1.1; rw [h] at this; simp at this; linarith
          exact mul_nonneg (hf ρ) (by exact_mod_cast CH2Section6.zetaOrder_nonneg_of_ne_one h1)
  have h1 : ∑ ρ ∈ F1, (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2)
      ≤ IEANTN.zetaZeroesSum Set.univ (Set.Ioc (t + 1 / 4) Y) (fun ρ ↦ 1 / (ρ.im - t) ^ 2) := by
    calc _ = ∑ ρ ∈ F1, (IEANTN.zetaOrder ρ : ℝ) * (1 / (ρ.im - t) ^ 2) :=
          Finset.sum_congr rfl fun ρ _ ↦ by rw [show (t - ρ.im) ^ 2 = (ρ.im - t) ^ 2 by ring]
      _ ≤ _ := hZ (by linarith) F1 _ (fun ρ hρ ↦ by
          rw [hF1, Finset.mem_filter] at hρ
          refine ⟨trivial, ⟨hρ.2, ?_⟩, (hF ρ hρ.1).1⟩
          have := hYge ρ hρ.1
          have := le_abs_self ρ.im
          linarith) (fun ρ ↦ by positivity)
  have h2 : ∑ ρ ∈ F2, (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2)
      ≤ IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 (t - 1 / 4)) (fun ρ ↦ 1 / (t - ρ.im) ^ 2) :=
    hZ le_rfl F2 _ (fun ρ hρ ↦ by
      rw [hF2, Finset.mem_filter] at hρ
      exact ⟨trivial, ⟨hρ.2.1, hρ.2.2⟩, (hF ρ hρ.1).1⟩) (fun ρ ↦ by positivity)
  have h3 : ∑ ρ ∈ F3, (IEANTN.zetaOrder ρ : ℝ) * (1 / (t - ρ.im) ^ 2)
      ≤ IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 Y) (fun ρ ↦ 1 / (t + ρ.im) ^ 2) := by
    have hinj : Set.InjOn (starRingEnd ℂ) (F3 : Set ℂ) := fun a _ b _ h ↦ by
      simpa using congrArg (starRingEnd ℂ) h
    calc _ = ∑ ρ ∈ F3.image (starRingEnd ℂ), (IEANTN.zetaOrder ρ : ℝ) * (1 / (t + ρ.im) ^ 2) := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun ρ _ ↦ ?_
          rw [CH2Section6.zetaOrder_conj]
          simp only [Complex.conj_im]
          ring_nf
      _ ≤ _ := hZ le_rfl _ _ (fun ρ hρ ↦ by
          rw [Finset.mem_image] at hρ
          obtain ⟨ρ', hρ', rfl⟩ := hρ
          rw [hF3, Finset.mem_filter] at hρ'
          have hz := (hF ρ' hρ'.1).1
          refine ⟨trivial, ⟨by simp; linarith [hρ'.2], ?_⟩, ?_⟩
          · have := hYge ρ' hρ'.1
            rw [abs_of_neg hρ'.2] at this
            simp; linarith
          · show riemannZeta _ = 0
            rw [riemannZeta_conj, hz, map_zero]) (fun ρ ↦ by positivity)
  rw [hsplit]
  linarith [hJ]

end CH2Section81
