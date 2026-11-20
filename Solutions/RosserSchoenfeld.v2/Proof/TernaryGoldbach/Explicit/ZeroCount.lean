import TernaryGoldbach.Explicit.LGrowth
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A crude count of the zeros of `L(s, χ)` (`χ ≠ 1`)

By Jensen's formula (`AnalyticOnNhd.sum_divisor_le`) on the discs `|s − (2 + iT)| ≤ 1.6 < 1.95`,
which stay in `ℜs ≥ 0.05` where `|L(s, χ)| ≤ (q + 1)|s|/ℜs`, and `|L(2 + iT, χ)| ≥ 2 − ζ(2)`:
the zeros (with multiplicity) in `|s − (2 + iT)| ≤ 1.6` — in particular those with `ℜs ≥ 1/2`,
`|ℑs − T| ≤ 1/2` — number at most `(log(q + 1) + log(|T| + 4) + 4.04)/0.1978`.
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real

namespace TernaryGoldbach.Explicit

variable {q : ℕ} [NeZero q]

/-- `|L(s, χ) − 1| ≤ ζ(2) − 1` on `ℜs = 2`, so `|L(s, χ)| ≥ 2 − π²/6`. -/
theorem norm_LFunction_two_ge (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s.re = 2) :
    2 - π ^ 2 / 6 ≤ ‖χ.LFunction s‖ := by
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1, LSeries]
  have hsum := χ.LSeriesSummable_of_one_lt_re hs1
  rw [hsum.tsum_eq_add_tsum_ite 1]
  have h1 : LSeries.term (fun n => χ (n : ZMod q)) s 1 = 1 := by
    simp [LSeries.term]
  rw [h1]
  set c : ℕ → ℝ := fun n => if n = 1 then 0 else 1 / (n : ℝ) ^ 2
  have hc : HasSum c (π ^ 2 / 6 - 1) := by
    have h := hasSum_zeta_two
    have h' := h.summable.tsum_eq_add_tsum_ite 1
    rw [h.tsum_eq] at h'
    have : ∑' n, c n = π ^ 2 / 6 - 1 := by simp only [c]; norm_num at h' ⊢; linarith
    rw [← this]
    exact (h.summable.congr_cofinite (by
      filter_upwards [Filter.eventually_cofinite_ne 1] with n hn
      simp [c, hn])).hasSum
  have hb : ‖∑' n, (if n = 1 then 0 else LSeries.term (fun n => χ (n : ZMod q)) s n)‖ ≤
      π ^ 2 / 6 - 1 := by
    refine tsum_of_norm_bounded hc fun n => ?_
    by_cases hn : n = 1
    · simp [c, hn]
    · simp only [c, hn, ite_false]
      rw [LSeries.norm_term_eq]
      split_ifs with h0
      · simp [h0]
      · rw [hs]
        have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero h0
        have : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        rw [Real.rpow_two]
        exact div_le_div_of_nonneg_right this (by positivity)
  have := norm_sub_norm_le (1 : ℂ) (-(∑' n, (if n = 1 then 0 else
    LSeries.term (fun n => χ (n : ZMod q)) s n)))
  rw [norm_one, norm_neg, sub_neg_eq_add] at this
  linarith

/-- **Crude zero count** (Jensen): the zeros of `L(s, χ)` with `|s − (2 + iT)| ≤ 1.6`, counted with
multiplicity, number at most `(log(q + 1) + log(|T| + 4) + 4.04) / 0.1978`. -/
theorem zero_count_disc {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (T : ℝ) :
    ((∑ᶠ u, MeromorphicOn.divisor χ.LFunction (closedBall (2 + T * I) |(1.6 : ℝ)|) u : ℤ) : ℝ) ≤
      (Real.log ((q : ℝ) + 1) + Real.log (|T| + 4) + 4.04) / 0.1978 := by
  set c : ℂ := 2 + T * I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcn : ‖c‖ ≤ 2 + |T| := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real, Real.norm_eq_abs]
  set M : ℝ := ((q : ℝ) + 1) * (|T| + 4) / 0.05 with hM
  have hM1 : 1 ≤ M := by
    rw [hM, le_div_iff₀ (by norm_num)]
    have : (1:ℝ) ≤ (q : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) q]
    nlinarith [abs_nonneg T]
  have hf : AnalyticOnNhd ℂ χ.LFunction (closedBall c |(1.95 : ℝ)|) := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hLc := norm_LFunction_two_ge χ hcre
  have hpi := Real.pi_lt_d4
  have hLc0 : (0.355 : ℝ) ≤ ‖χ.LFunction c‖ := by nlinarith [Real.pi_pos]
  have hfc : χ.LFunction c ≠ 0 := by
    intro h; rw [h, norm_zero] at hLc0; norm_num at hLc0
  have hbound : ∀ z ∈ sphere c |(1.95 : ℝ)|, ‖χ.LFunction z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0:ℝ) < 1.95)] at hz
    have hre : 0.05 ≤ z.re := by
      have := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre, hz] at this
      linarith [neg_abs_le (z.re - 2)]
    have hzn : ‖z‖ ≤ |T| + 4 := by
      have := norm_le_insert' z c
      have h2 : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
        calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
          _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
      linarith
    refine (norm_LFunction_le hχ (by linarith)).trans ?_
    rw [hM]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hzn (by positivity))
      (by norm_num) hre
  have h := hf.sum_divisor_le (r := 1.6) (R := 1.95) (by norm_num) (by norm_num) hM1 hfc hbound
  refine h.trans ?_
  have hlogR : (0.1978 : ℝ) ≤ Real.log (1.95 / 1.6) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_bound' (x := 0.1978) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢
    linarith
  have hnum : Real.log (M / ‖χ.LFunction c‖) ≤
      Real.log ((q : ℝ) + 1) + Real.log (|T| + 4) + 4.04 := by
    have hq1 : (0:ℝ) < (q : ℝ) + 1 := by positivity
    have hT4 : (0:ℝ) < |T| + 4 := by positivity
    have h1 : M / ‖χ.LFunction c‖ ≤ ((q : ℝ) + 1) * (|T| + 4) * 56.4 := by
      rw [div_le_iff₀ (by linarith), hM]
      have hp : (0:ℝ) < ((q : ℝ) + 1) * (|T| + 4) := by positivity
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    have h2 : Real.log (((q : ℝ) + 1) * (|T| + 4) * 56.4) =
        Real.log ((q : ℝ) + 1) + Real.log (|T| + 4) + Real.log 56.4 := by
      rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity)]
    have h3 : Real.log 56.4 ≤ 4.04 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      calc (56.4 : ℝ) ≤ 2.7182818283 ^ 4 * 1.04 := by norm_num
        _ ≤ Real.exp 1 ^ 4 * Real.exp 0.04 := by
          gcongr
          have := Real.add_one_le_exp (0.04 : ℝ); linarith
        _ = Real.exp 4.04 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hpos : 0 < M / ‖χ.LFunction c‖ := by
      have : 0 < M := by linarith
      positivity
    calc Real.log (M / ‖χ.LFunction c‖) ≤ Real.log (((q : ℝ) + 1) * (|T| + 4) * 56.4) :=
          Real.log_le_log hpos h1
      _ ≤ _ := by rw [h2]; linarith
  have hnum0 : 0 ≤ Real.log (M / ‖χ.LFunction c‖) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith)]
    have : ‖χ.LFunction c‖ ≤ M := by
      have := hbound
      -- `|L(c)| ≤ ζ(2) < 2 ≤ M`
      have hle : ‖χ.LFunction c‖ ≤ π ^ 2 / 6 := by
        rw [DirichletCharacter.LFunction_eq_LSeries χ (by rw [hcre]; norm_num), LSeries]
        refine tsum_of_norm_bounded hasSum_zeta_two fun n => ?_
        rw [LSeries.norm_term_eq]
        split_ifs with h0
        · simp [h0]
        · rw [hcre, Real.rpow_two]
          exact div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (by positivity)
      have h20 : (20 : ℝ) ≤ M := by
        rw [hM, le_div_iff₀ (by norm_num)]
        have : (1:ℝ) ≤ (q : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) q]
        nlinarith [abs_nonneg T]
      have hp2 : π ^ 2 < 10 := by nlinarith [Real.pi_pos]
      linarith
    linarith
  calc Real.log (M / ‖χ.LFunction c‖) / Real.log (1.95 / 1.6)
      ≤ Real.log (M / ‖χ.LFunction c‖) / 0.1978 := div_le_div_of_nonneg_left hnum0 (by norm_num) hlogR
    _ ≤ _ := div_le_div_of_nonneg_right hnum (by norm_num)

end TernaryGoldbach.Explicit
