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

end CH2Section81
