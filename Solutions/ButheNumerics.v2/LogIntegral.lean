/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Teddy Tennant
-/
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lower bounds for `li`

`IEANTN.li` is a principal value, defined as a limit, so the first job is to show the limit exists.
Subtracting the pole leaves `g t = 1 / log t - 1 / (t - 1)`, which lies in `[0, 1]` on `(0, ∞)`;
the two halves of `∫ 1 / (t - 1)` around `t = 1` cancel exactly, and
`li x = log (x - 1) + ∫ t in (0, x], g t` (`li_eq`). Since `g ≥ 0`, this gives `Li x ≤ li x`.

`Li 1500` is then bounded below by the midpoint rule, which is a lower bound because `1 / log t` is
convex: its tangent line lies below it (`tangent_le_inv_log`). Ten blocks with midpoints `3 · 2ᵏ`
and `1262` give `245.18`, against the true `246.77`, and need only upper bounds on `log 2` and
`log 3`.
-/

open Real MeasureTheory Set Filter Topology

namespace ButheNumerics.v2.Dev

/-- `1 / log t` with its pole at `t = 1` subtracted off. -/
noncomputable def g (t : ℝ) : ℝ := 1 / log t - 1 / (t - 1)

theorem g_mem_Icc {t : ℝ} (ht : 0 < t) : g t ∈ Icc 0 1 := by
  rcases eq_or_ne t 1 with rfl | h1
  · simp [g]
  have hP : 0 < log t * (t - 1) := by
    rcases lt_or_gt_of_ne h1 with h | h
    · exact mul_pos_of_neg_of_neg (log_neg ht h) (by linarith)
    · exact mul_pos (log_pos h) (by linarith)
  have hu := log_le_sub_one_of_pos ht
  have hl := one_sub_inv_le_log_of_pos ht
  have hg : g t = (t - 1 - log t) / (log t * (t - 1)) := by
    have : log t ≠ 0 := by rintro h; simp [h] at hP
    have : t - 1 ≠ 0 := sub_ne_zero.mpr h1
    simp only [g]
    field_simp
  rw [hg]
  refine ⟨div_nonneg (by linarith) hP.le, (div_le_one hP).mpr ?_⟩
  have : 1 - t⁻¹ = (t - 1) / t := by field_simp
  rw [this, div_le_iff₀ ht] at hl
  nlinarith

theorem measurable_g : Measurable g := by
  unfold g
  fun_prop

theorem integrableOn_g (x : ℝ) : IntegrableOn g (Ioc 0 x) := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) measurable_g.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_
  have := g_mem_Icc ht.1
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [this.1], this.2⟩

/-- `∫ 1 / (t - 1)` over the two sides of the pole, which is where the principal value comes from:
the two `log ε` cancel. -/
theorem integral_pole {x ε : ℝ} (hx : 2 ≤ x) (hε : ε ∈ Ioo 0 1) :
    ∫ t in Ioc 0 (1 - ε) ∪ Icc (1 + ε) x, 1 / (t - 1) = log (x - 1) := by
  obtain ⟨hε0, hε1⟩ := hε
  have hc₁ : ContinuousOn (fun t : ℝ ↦ 1 / (t - 1)) (Icc 0 (1 - ε)) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
    linarith [ht.2]
  have hc₂ : ContinuousOn (fun t : ℝ ↦ 1 / (t - 1)) (Icc (1 + ε) x) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
    linarith [ht.1]
  rw [setIntegral_union (Set.disjoint_left.mpr fun t h₁ h₂ ↦ by linarith [h₁.2, h₂.1])
    measurableSet_Icc
    ((hc₁.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self)
    (hc₂.integrableOn_compact isCompact_Icc),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun t ↦ 1 / t),
    intervalIntegral.integral_comp_sub_right (fun t ↦ 1 / t),
    integral_one_div, integral_one_div]
  · rw [show (1 - ε - 1) / (0 - 1) = ε by ring, show 1 + ε - 1 = ε by ring,
      log_div (by linarith) hε0.ne']
    ring
  · rw [mem_uIcc]; rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith
  · rw [mem_uIcc]; rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith

/-- The principal value `li x` is `log (x - 1)` plus an honest integral of the bounded `g`. -/
theorem li_eq {x : ℝ} (hx : 2 ≤ x) : IEANTN.li x = log (x - 1) + ∫ t in Ioc 0 x, g t := by
  have hg := integrableOn_g x
  have hsplit : ∀ ε ∈ Ioo (0 : ℝ) 1,
      (∫ t in Ioc 0 x \ Ioo (1 - ε) (1 + ε), 1 / log t) =
        log (x - 1) + (∫ t in Ioc 0 x, g t) - ∫ t in Ioo (1 - ε) (1 + ε), g t := by
    intro ε hε
    have hsub : Ioo (1 - ε) (1 + ε) ⊆ Ioc 0 x := fun t ht ↦
      ⟨by linarith [ht.1, hε.2], by linarith [ht.2, hε.2]⟩
    have hS : Ioc 0 x \ Ioo (1 - ε) (1 + ε) = Ioc 0 (1 - ε) ∪ Icc (1 + ε) x := by
      ext t
      simp only [Set.mem_sdiff, mem_Ioc, mem_Ioo, mem_union, mem_Icc, not_and_or, not_lt]
      constructor
      · rintro ⟨⟨h0, hx'⟩, h | h⟩
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr ⟨h, hx'⟩
      · rintro (⟨h0, h⟩ | ⟨h, hx'⟩)
        · exact ⟨⟨h0, by linarith [hε.1]⟩, Or.inl h⟩
        · exact ⟨⟨by linarith [hε.1], hx'⟩, Or.inr h⟩
    have hpole : IntegrableOn (fun t : ℝ ↦ 1 / (t - 1)) (Ioc 0 x \ Ioo (1 - ε) (1 + ε)) := by
      rw [hS]
      refine IntegrableOn.union ?_ ?_
      · refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Ioc_subset_Icc_self
        refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
        linarith [ht.2, hε.1]
      · refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
        refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
        linarith [ht.1, hε.1]
    have : (fun t ↦ 1 / log t) = fun t ↦ g t + 1 / (t - 1) := by ext t; simp [g]
    rw [this, integral_add (hg.mono_set sdiff_subset) hpole,
      setIntegral_sdiff measurableSet_Ioo hg hsub, hS, integral_pole hx hε]
    ring
  have hsmall : Tendsto (fun ε ↦ ∫ t in Ioo (1 - ε) (1 + ε), g t) (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun ε : ℝ ↦ 2 * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_const_mul (2 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine (norm_setIntegral_le_of_norm_le_const (C := 1) measure_Ioo_lt_top
      fun t ht ↦ ?_).trans_eq ?_
    · have := g_mem_Icc (show 0 < t by linarith [ht.1, hε.2])
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [this.1], this.2⟩
    · rw [Real.volume_real_Ioo_of_le (by linarith [hε.1])]
      ring
  refine Tendsto.limUnder_eq ?_
  have hev : (fun ε ↦ log (x - 1) + (∫ t in Ioc 0 x, g t) - ∫ t in Ioo (1 - ε) (1 + ε), g t)
      =ᶠ[𝓝[>] 0] fun ε ↦ ∫ t in Ioc 0 x \ Ioo (1 - ε) (1 + ε), 1 / log t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (hsplit ε hε).symm
  refine Tendsto.congr' hev ?_
  simpa using (tendsto_const_nhds (x := log (x - 1) + ∫ t in Ioc 0 x, g t)).sub hsmall

/-- `li x ≥ Li x`, that is `li 2 ≥ 0`. -/
theorem Li_le_li {x : ℝ} (hx : 2 ≤ x) : IEANTN.Li x ≤ IEANTN.li x := by
  have hlog : IntervalIntegrable (fun t ↦ 1 / log t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    have : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    exact (continuousAt_const.div (continuousAt_log (by linarith [ht.1])) this).continuousWithinAt
  have hpole : IntervalIntegrable (fun t : ℝ ↦ 1 / (t - 1)) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    exact (continuousAt_const.div (by fun_prop) (by linarith [ht.1])).continuousWithinAt
  have h2x : ∫ t in Ioc 2 x, g t = IEANTN.Li x - log (x - 1) := by
    rw [← intervalIntegral.integral_of_le hx, IEANTN.Li]
    simp only [g]
    rw [intervalIntegral.integral_sub hlog hpole,
      intervalIntegral.integral_comp_sub_right (fun t ↦ 1 / t), integral_one_div]
    · norm_num
    · rw [mem_uIcc]; rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith
  have hmono : ∫ t in Ioc 2 x, g t ≤ ∫ t in Ioc 0 x, g t :=
    setIntegral_mono_set (integrableOn_g x)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ (g_mem_Icc ht.1).1)
      (Ioc_subset_Ioc_left (by norm_num)).eventuallyLE
  rw [li_eq hx]
  linarith

/-- The tangent line to `1 / log` at `m` lies below it. This is the convexity of `1 / log t`,
proved from `log (t / m) ≤ t / m - 1` and `(log m - log t) ^ 2 ≥ 0`. -/
theorem tangent_le_inv_log {m t : ℝ} (hm : 1 < m) (ht : 1 < t) :
    1 / log m - (t - m) / (m * log m ^ 2) ≤ 1 / log t := by
  have hL := log_pos hm
  have hu := log_pos ht
  have hm0 : 0 < m := by linarith
  have h := log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < t) hm0)
  rw [log_div (by linarith) hm0.ne'] at h
  have h' : log t - log m ≤ (t - m) / m := by rw [sub_div, div_self hm0.ne']; exact h
  calc 1 / log m - (t - m) / (m * log m ^ 2)
      = 1 / log m - (t - m) / m / log m ^ 2 := by rw [div_div]
    _ ≤ 1 / log m - (log t - log m) / log m ^ 2 := by gcongr
    _ ≤ 1 / log t := by
      rw [← sub_nonneg]
      have : 1 / log t - (1 / log m - (log t - log m) / log m ^ 2) =
          (log m - log t) ^ 2 / (log t * log m ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity

/-- The midpoint rule is a lower bound for the convex `1 / log t`. -/
theorem midpoint_le_integral {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hc : log ((a + b) / 2) ≤ c) :
    (b - a) / c ≤ ∫ t in a..b, 1 / log t := by
  set m := (a + b) / 2
  have hm : 1 < m := by simp only [m]; linarith
  have hL := log_pos hm
  have hcont : ContinuousOn (fun t ↦ 1 / log t) (uIcc a b) := fun t ht ↦ by
    rw [uIcc_of_le hab] at ht
    exact (continuousAt_const.div (continuousAt_log (by linarith [ht.1]))
      (log_pos (by linarith [ht.1])).ne').continuousWithinAt
  have hlin : Continuous fun t : ℝ ↦ 1 / log m - (t - m) / (m * log m ^ 2) := by fun_prop
  calc (b - a) / c ≤ (b - a) / log m := by
        gcongr
    _ = ∫ t in a..b, (1 / log m - (t - m) / (m * log m ^ 2)) := by
        have h1 : ∫ t in a..b, (t - m) / (m * log m ^ 2) = 0 := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun t ↦ t),
            integral_id]
          simp only [m]
          ring
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          ((by fun_prop : Continuous fun t : ℝ ↦ (t - m) / (m * log m ^ 2)).intervalIntegrable _ _),
          h1, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div]
    _ ≤ ∫ t in a..b, 1 / log t := by
        refine intervalIntegral.integral_mono_on hab (hlin.intervalIntegrable _ _)
          hcont.intervalIntegrable fun t ht ↦ tangent_le_inv_log hm (by linarith [ht.1])

theorem log_three_le : log 3 ≤ (3 * 0.6931471808 + 1 / 8) / 2 := by
  have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9 / 8)
  rw [log_div (by norm_num) (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
    show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow, log_pow] at h
  have := log_two_lt_d9
  push_cast at h
  linarith

/-- `Li 1500 = ∫₂¹⁵⁰⁰ dt / log t ≥ 245`, by the midpoint rule on `[2, 4], [4, 8], …, [512, 1024]`
and `[1024, 1500]`. The true value is `246.77…`. -/
theorem Li_1500_gt : (245 : ℝ) < IEANTN.Li 1500 := by
  rw [IEANTN.Li]
  have hl2 := log_two_lt_d9
  have hl3 := log_three_le
  have hint : ∀ a b : ℝ, 1 < a → a ≤ b → IntervalIntegrable (fun t ↦ 1 / log t) volume a b :=
    fun a b ha hab ↦ ContinuousOn.intervalIntegrable fun t ht ↦ by
      rw [uIcc_of_le hab] at ht
      exact (continuousAt_const.div (continuousAt_log (by linarith [ht.1]))
        (log_pos (by linarith [ht.1])).ne').continuousWithinAt
  have hpow : ∀ k : ℕ, (1 : ℝ) < 2 ^ (k + 1) := fun k ↦ one_lt_pow₀ (by norm_num) (by omega)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t ↦ 1 / log t) (a := fun k : ℕ ↦ (2 : ℝ) ^ (k + 1)) (n := 9)
    fun k _ ↦ hint _ _ (hpow k) (pow_le_pow_right₀ (by norm_num) (by omega : k + 1 ≤ k + 1 + 1))
  have hblock : ∀ k ∈ Finset.range 9,
      (2 : ℝ) ^ (k + 1) / ((3 * 0.6931471808 + 1 / 8) / 2 + k * 0.6931471808) ≤
        ∫ t in (2 : ℝ) ^ (k + 1)..2 ^ (k + 1 + 1), 1 / log t := by
    intro k _
    have := midpoint_le_integral (c := (3 * 0.6931471808 + 1 / 8) / 2 + k * 0.6931471808)
      (hpow k) (pow_le_pow_right₀ (by norm_num) (by omega : k + 1 ≤ k + 1 + 1)) ?_
    · rw [pow_succ (2 : ℝ) (k + 1)] at this ⊢
      convert this using 1
      ring
    · rw [show ((2 : ℝ) ^ (k + 1) + 2 ^ (k + 1 + 1)) / 2 = 3 * 2 ^ k by ring,
        log_mul (by norm_num) (by positivity), log_pow]
      gcongr
  have hlast := midpoint_le_integral (a := 1024) (b := 1500) (c := 4 * (0.6931471808 +
    (3 * 0.6931471808 + 1 / 8) / 2)) (by norm_num) (by norm_num) (by
      calc log ((1024 + 1500) / 2) ≤ log (6 ^ 4) := log_le_log (by norm_num) (by norm_num)
        _ = 4 * (log 2 + log 3) := by
          rw [log_pow, show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
          push_cast; ring
        _ ≤ _ := by gcongr)
  have hlow := Finset.sum_le_sum hblock
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1024)
    (hint _ _ (by norm_num) (by norm_num)) (hint _ _ (by norm_num) (by norm_num))]
  norm_num [Finset.sum_range_succ] at hsum hlow hlast ⊢
  linarith

end ButheNumerics.v2.Dev
