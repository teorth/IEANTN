/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Doolan
-/
import IEANTN.Nodes.TruncatedPerron.v1.Conclusions
import PerronDev

/-!
# The truncated Perron formula for a Dirichlet series

`perron_general_of_single` derives `TruncatedPerron.v1.perron_general` from
`TruncatedPerron.v1.perron_single_term`, term by term.

* On the segment `s = σ₀ + it`, `t ∈ [-T, T]`, write
  `LSeries a s · x^s / s = ∑ₙ aₙ (x/n)^s / s` (the `n = 0` term is `0`).
  Each term is at most `‖aₙ‖ (x/n)^σ₀ / σ₀`, which is summable because
  `abscissaOfAbsConv a < σ₀`, so the sum and the finite integral commute
  (`intervalIntegral.hasSum_integral_of_dominated_convergence`).
* For `n ≠ x` the single-term bound applies with `y = x/n`.
* For `n = x` the integral is `∫ 1/(σ₀+it) dt = 2 arg(σ₀ + iT)`, and
  `π/2 − arg(σ₀ + iT) ≤ tan(π/2 − arg(σ₀ + iT)) = σ₀/T`.
* The error series is summable (each term is at most `max(1, σ₀/(πT)) ‖aₙ‖ (x/n)^σ₀`), and the
  difference is bounded with `HasSum.norm_le_of_bounded`.
-/

open Complex Real MeasureTheory intervalIntegral

namespace TruncPerronGeneral

open TruncatedPerron.v1

noncomputable section

/-! ### The term `n = x` -/

lemma integral_inv_seg {c T : ℝ} (hc : 0 < c) :
    ∫ t in (-T)..T, (1 : ℂ) / ((c : ℂ) + t * I) = 2 * (TruncPerron.ang c T : ℂ) := by
  have h := TruncPerron.VIntegral_inv (T := T) hc
  simp only [TruncPerron.VIntegral] at h
  apply mul_left_cancel₀ I_ne_zero
  rw [h]; ring

lemma pi_div_two_sub_ang_le {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    π / 2 - TruncPerron.ang c T ≤ c / T := by
  have htan : Real.tan (TruncPerron.ang c T) = T / c := by
    rw [TruncPerron.ang, Complex.tan_arg]; simp
  have habs : |TruncPerron.ang c T| < π / 2 := by
    rw [TruncPerron.ang, Complex.abs_arg_lt_pi_div_two_iff]; left; simpa using hc
  have h0 : 0 ≤ TruncPerron.ang c T := TruncPerron.ang_nonneg (c := c) hT.le
  have hne : TruncPerron.ang c T ≠ 0 := by
    intro h; rw [h, Real.tan_zero] at htan; exact (div_pos hT hc).ne' htan.symm
  have h1 : π / 2 - TruncPerron.ang c T < π / 2 := by
    have := lt_of_le_of_ne h0 (Ne.symm hne); linarith
  have h2 := Real.le_tan (by linarith [(abs_lt.mp habs).2]) h1
  rwa [Real.tan_pi_div_two_sub, htan, inv_div] at h2

lemma perron_one_bound {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖(1 / 2 : ℂ) - (1 / (2 * π) : ℂ) *
        ∫ t in (-T)..T, ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤
      c / (π * T) := by
  have e : (fun t : ℝ => ((1 : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) =
      fun t : ℝ => (1 : ℂ) / ((c : ℂ) + t * I) := by
    funext t; simp
  rw [e, integral_inv_seg hc]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have h : (1 / 2 : ℂ) - 1 / (2 * π) * (2 * (TruncPerron.ang c T : ℂ)) =
      (((π / 2 - TruncPerron.ang c T) / π : ℝ) : ℂ) := by
    push_cast; field_simp
  have hle := TruncPerron.ang_le (c := c) (T := T) hc
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) pi_pos.le),
    show c / (π * T) = c / T / π by field_simp]
  exact (div_le_div_iff_of_pos_right pi_pos).mpr (pi_div_two_sub_ang_le hc hT)

/-! ### Swapping the sum and the integral -/

/-- The `n`-th term of `LSeries a s · x^s / s` on the line `s = σ₀ + it`. -/
def Fn (a : ℕ → ℂ) (σ₀ x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  if n = 0 then 0 else a n * (((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))

lemma hasSum_Fn {a : ℕ → ℂ} {σ₀ x : ℝ} (ha : LSeries.abscissaOfAbsConv a < (σ₀ : EReal))
    (hx : 0 < x) (t : ℝ) :
    HasSum (fun n => Fn a σ₀ x n t)
      (LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) := by
  have hs : LSeriesSummable a ((σ₀ : ℂ) + t * I) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using ha)
  have h := hs.LSeriesHasSum.mul_right ((x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I))
  rw [mul_div_assoc]
  have e : (fun n => Fn a σ₀ x n t) = fun n => LSeries.term a ((σ₀ : ℂ) + t * I) n *
      ((x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Fn]
    · simp only [Fn, hn, ↓reduceIte, LSeries.term_of_ne_zero hn]
      rw [ofReal_div, div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n), ofReal_natCast]
      ring
  rw [e]; exact h

lemma summable_B {a : ℕ → ℂ} {σ₀ x : ℝ} (hσ : 0 < σ₀)
    (ha : LSeries.abscissaOfAbsConv a < (σ₀ : EReal)) (hx : 0 < x) :
    Summable fun n : ℕ => ‖a n‖ * (x / n) ^ σ₀ := by
  have h0 : LSeriesSummable a σ₀ := LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using ha)
  refine ((summable_norm_iff.mpr (show Summable (LSeries.term a σ₀) from h0)).mul_left
    (x ^ σ₀)).congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hσ.ne']
  · simp only [hn, ↓reduceIte, ofReal_re]
    rw [Real.div_rpow hx.le (Nat.cast_nonneg n)]; ring

lemma norm_Fn_le {a : ℕ → ℂ} {σ₀ x : ℝ} (hσ : 0 < σ₀) (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖Fn a σ₀ x n t‖ ≤ ‖a n‖ * (x / n) ^ σ₀ / σ₀ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Fn, ↓reduceIte, norm_zero]
    exact div_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (div_nonneg hx.le (Nat.cast_nonneg _)) _)) hσ.le
  · have hy : 0 < x / n := div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    simp only [Fn, hn, ↓reduceIte]
    rw [norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hy, mul_div_assoc]
    have hre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
    rw [hre]
    refine mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) hσ ?_) (norm_nonneg _)
    have := TruncPerron.norm_add_mul_I_ge_re σ₀ t
    rwa [abs_of_pos hσ] at this

lemma continuous_Fn {a : ℕ → ℂ} {σ₀ x : ℝ} (hσ : 0 < σ₀) (hx : 0 < x) (n : ℕ) :
    Continuous (Fn a σ₀ x n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Fn a σ₀ x 0 = fun _ => 0 := by funext t; simp [Fn]
    rw [this]; exact continuous_const
  · have hy : 0 < x / n := div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    have : Fn a σ₀ x n = fun t : ℝ =>
        a n * (((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) := by
      funext t; simp only [Fn, hn, ↓reduceIte]
    rw [this]
    have hs : Continuous fun t : ℝ => (σ₀ : ℂ) + t * I := by fun_prop
    exact continuous_const.mul
      (((TruncPerron.differentiable_cpow_const hy).continuous.comp hs).div hs
        fun t => TruncPerron.ne_zero_of_re hσ.ne')

lemma hasSum_integral {a : ℕ → ℂ} {σ₀ x T : ℝ} (hσ : 0 < σ₀)
    (ha : LSeries.abscissaOfAbsConv a < (σ₀ : EReal)) (hx : 0 < x) :
    HasSum (fun n => ∫ t in (-T)..T, Fn a σ₀ x n t)
      (∫ t in (-T)..T,
        LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)) :=
  intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => ‖a n‖ * (x / n) ^ σ₀ / σ₀)
    (fun n => (continuous_Fn hσ hx n).aestronglyMeasurable)
    (fun n => ae_of_all _ fun t _ => norm_Fn_le hσ hx n t)
    (ae_of_all _ fun _ _ => (summable_B hσ ha hx).div_const σ₀)
    intervalIntegrable_const
    (ae_of_all _ fun t _ => hasSum_Fn ha hx t)

lemma integral_Fn {a : ℕ → ℂ} {σ₀ x T : ℝ} {n : ℕ} (hn : n ≠ 0) :
    ∫ t in (-T)..T, Fn a σ₀ x n t =
      a n * ∫ t in (-T)..T, ((x / n : ℝ) : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I) := by
  simp only [Fn, hn, ↓reduceIte]
  exact intervalIntegral.integral_const_mul _ _

/-! ### The termwise bound -/

lemma term_bound (hS : perron_single_term) {a : ℕ → ℂ} {σ₀ x T : ℝ} (hσ : 0 < σ₀) (hx : 0 < x)
    (hT : 0 < T) (n : ℕ) :
    ‖(if n ∈ Finset.Icc 1 ⌊x⌋₊ then (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * a n else 0)
        - (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, Fn a σ₀ x n t‖ ≤
      ‖a n‖ * (x / n) ^ σ₀ *
        (if (n : ℝ) = x then σ₀ / (π * T) else min 1 (1 / (π * T * |Real.log (x / n)|))) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Fn, Real.zero_rpow hσ.ne']
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hy : 0 < x / n := div_pos hx hnpos
  have hmem : n ∈ Finset.Icc 1 ⌊x⌋₊ ↔ (n : ℝ) ≤ x := by
    rw [Finset.mem_Icc, Nat.le_floor_iff hx.le]
    exact ⟨fun h => h.2, fun h => ⟨Nat.pos_of_ne_zero hn, h⟩⟩
  rw [integral_Fn hn]
  by_cases hnx : (n : ℝ) = x
  · have hy1 : x / n = 1 := by rw [hnx, div_self hx.ne']
    have hb := perron_one_bound (T := T) hσ hT
    rw [if_pos (hmem.mpr hnx.le), if_pos hnx, if_pos hnx, hy1, Real.one_rpow, mul_one]
    rw [show ∀ J : ℂ, (1 / 2 : ℂ) * a n - 1 / (2 * π) * (a n * J) =
        a n * (1 / 2 - 1 / (2 * π) * J) from fun J => by ring, norm_mul]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  · have hy1 : x / n ≠ 1 := fun h => hnx ((div_eq_one_iff_eq hnpos.ne').mp h).symm
    have hlt : n ∈ Finset.Icc 1 ⌊x⌋₊ ↔ 1 < x / n := by
      rw [hmem, one_lt_div hnpos]
      exact ⟨fun h => lt_of_le_of_ne h hnx, le_of_lt⟩
    have hb := hS (x / n) σ₀ T hy hy1 hσ hT
    rw [if_neg hnx, if_neg hnx, mul_assoc]
    have key : ∀ J : ℂ,
        (if n ∈ Finset.Icc 1 ⌊x⌋₊ then 1 * a n else 0) - 1 / (2 * π) * (a n * J) =
          -(a n * (1 / (2 * π) * J - (if 1 < x / n then 1 else 0))) := by
      intro J
      by_cases h : 1 < x / n
      · rw [if_pos (hlt.mpr h), if_pos h]; ring
      · rw [if_neg (mt hlt.mp h), if_neg h]; ring
    rw [key, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

/-! ### The formula -/

theorem perron_general_of_single (hS : perron_single_term) : perron_general := by
  intro a σ₀ x T hσ ha hx hT
  have he : HasSum
      (fun n : ℕ => if n ∈ Finset.Icc 1 ⌊x⌋₊ then
        (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * a n else 0)
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * a n) := by
    have h := hasSum_sum_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊)
      (f := fun n : ℕ => if n ∈ Finset.Icc 1 ⌊x⌋₊ then
        (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * a n else 0)
      (fun n hn => if_neg hn) (L := SummationFilter.unconditional ℕ)
    rwa [Finset.sum_congr rfl fun n hn => if_pos hn] at h
  have hP := (hasSum_integral (T := T) hσ ha hx).mul_left (1 / (2 * π) : ℂ)
  have hM : 0 ≤ max 1 (σ₀ / (π * T)) := le_max_of_le_left zero_le_one
  have hK : ∀ n : ℕ,
      0 ≤ (if (n : ℝ) = x then σ₀ / (π * T) else min 1 (1 / (π * T * |Real.log (x / n)|))) ∧
      (if (n : ℝ) = x then σ₀ / (π * T) else min 1 (1 / (π * T * |Real.log (x / n)|))) ≤
        max 1 (σ₀ / (π * T)) := by
    intro n
    split_ifs
    · exact ⟨by positivity, le_max_right _ _⟩
    · exact ⟨le_min zero_le_one (by positivity), (min_le_left _ _).trans (le_max_left _ _)⟩
  have hB0 : ∀ n : ℕ, 0 ≤ ‖a n‖ * (x / n) ^ σ₀ := fun n =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (div_nonneg hx.le (Nat.cast_nonneg _)) _)
  have hR : Summable fun n : ℕ => ‖a n‖ * (x / n) ^ σ₀ *
      (if (n : ℝ) = x then σ₀ / (π * T) else min 1 (1 / (π * T * |Real.log (x / n)|))) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hB0 n) (hK n).1)
      (fun n => mul_le_mul_of_nonneg_left (hK n).2 (hB0 n))
      ((summable_B hσ ha hx).mul_right _)
  exact (he.sub hP).norm_le_of_bounded hR.hasSum (term_bound hS hσ hx hT)

end

end TruncPerronGeneral
