import TernaryGoldbach.Explicit.LGrowthPoly
import TernaryGoldbach.Explicit.ExplicitFormula

/-!
# Zero counts with polynomial growth, and sums over zeros

`B'_T = 1400 q⁹ (q+1)(|T|+22)(1.25(|T|+11))^{10}` bounds `|L|` on `|z − (2 + iT)| ≤ 10`
(`LGrowthPoly` for `ℜz ≤ 1/4`, `LGrowth` otherwise), so Jensen gives `O(log qT)` zeros per window.
-/

open Complex MeasureTheory Set Filter
open scoped Real

namespace TernaryGoldbach.Explicit

/-- `B'_T`. -/
noncomputable def BP (N : ℕ) (T : ℝ) : ℝ :=
  1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) * (1.25 * (|T| + 11)) ^ (10 : ℝ)

theorem one_le_BP {N : ℕ} [NeZero N] (T : ℝ) : 1400 ≤ BP N T := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h9 : (1:ℝ) ≤ (N : ℝ) ^ 9 := one_le_pow₀ hN1
  have hp : (1:ℝ) ≤ (1.25 * (|T| + 11)) ^ (10 : ℝ) :=
    Real.one_le_rpow (by nlinarith [abs_nonneg T]) (by norm_num)
  unfold BP
  have h1 : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by nlinarith
  have h2 : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) := by nlinarith [abs_nonneg T]
  have h3 : (1:ℝ) ≤ (N : ℝ) ^ 9 * ((N : ℝ) + 1) * (|T| + 22) * (1.25 * (|T| + 11)) ^ (10 : ℝ) := by
    nlinarith
  nlinarith

theorem norm_L_le_BP {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T : ℝ} {w : ℂ} (hw : w ∈ Metric.closedBall (2 + T * I) 10) :
    ‖χ.LFunction w‖ ≤ BP N T := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have hre := Complex.abs_re_le_norm (w - (2 + T * I))
  have him := Complex.abs_im_le_norm (w - (2 + T * I))
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.sub_im,
    Complex.add_im, Complex.im_ofNat, Complex.mul_im, zero_add, add_zero] at hre him
  have hwim1 : |w.im| ≤ |T| + 10 := by
    have := abs_sub_abs_le_abs_sub w.im T; linarith [abs_sub_comm w.im T]
  have hre1 : -8 ≤ w.re := by linarith [neg_abs_le (w.re - 2)]
  have hre2 : w.re ≤ 12 := by linarith [le_abs_self (w.re - 2)]
  rcases le_total w.re (1 / 4) with h | h
  · refine (norm_LFunction_left_poly hχ hχ1 hre1 h).trans ?_
    unfold BP
    have h1 : |w.im| + 9 ≤ |T| + 22 := by linarith
    have h2 : (1.25 * (|w.im| + 1)) ^ (10 : ℝ) ≤ (1.25 * (|T| + 11)) ^ (10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hA : 0 ≤ 1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) h2 (by positivity) (by positivity)
  · refine (norm_LFunction_le hχ1 (by linarith)).trans ?_
    have hwn : ‖w‖ ≤ |T| + 22 := by
      refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
      rw [abs_of_pos (by linarith : (0:ℝ) < w.re)]; linarith
    have h4 : ((N : ℝ) + 1) * ‖w‖ / w.re ≤ 4 * ((N : ℝ) + 1) * (|T| + 22) := by
      rw [div_le_iff₀ (by linarith)]
      have hp : 0 ≤ 4 * ((N : ℝ) + 1) * (|T| + 22) := by positivity
      have h1 := mul_le_mul_of_nonneg_left hwn (by positivity : (0:ℝ) ≤ (N : ℝ) + 1)
      have h2 := mul_le_mul_of_nonneg_left h hp
      nlinarith
    refine h4.trans ?_
    have h9 : (1:ℝ) ≤ (N : ℝ) ^ 9 := one_le_pow₀ hN1
    have hp : (1:ℝ) ≤ (1.25 * (|T| + 11)) ^ (10 : ℝ) :=
      Real.one_le_rpow (by nlinarith [abs_nonneg T]) (by norm_num)
    unfold BP
    have hq : 0 ≤ ((N : ℝ) + 1) * (|T| + 22) := by positivity
    calc 4 * ((N : ℝ) + 1) * (|T| + 22) = 4 * (((N : ℝ) + 1) * (|T| + 22)) := by ring
      _ ≤ 1400 * (N : ℝ) ^ 9 * (1.25 * (|T| + 11)) ^ (10 : ℝ) * (((N : ℝ) + 1) * (|T| + 22)) := by
        have : (4:ℝ) ≤ 1400 * (N : ℝ) ^ 9 * (1.25 * (|T| + 11)) ^ (10 : ℝ) := by nlinarith
        nlinarith
      _ = _ := by ring

/-- **Jensen with polynomial growth**: at most `log(B'_T/0.355)/log(10/r)` zeros in `|ρ − (2+iT)| ≤ r`. -/
theorem zero_count_poly {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (T : ℝ) {r : ℝ} (hr : 0 < r) (hr10 : r < 10) :
    ((∑ᶠ u, MeromorphicOn.divisor χ.LFunction (Metric.closedBall (2 + T * I) |r|) u : ℤ) : ℝ) ≤
      Real.log (BP N T / 0.355) / Real.log (10 / r) := by
  have hc := norm_L_center_ge χ T
  have hc0 : χ.LFunction (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := one_le_BP (N := N) T
  have hf : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall (2 + T * I) |(10 : ℝ)|) := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt z
  have h := hf.sum_divisor_le (r := r) (R := 10) (by rw [abs_of_pos hr]; exact hr)
    (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0:ℝ) < 10)]; exact hr10) (by linarith) hc0
    (fun w hw => norm_L_le_BP hχ hχ1 (Metric.sphere_subset_closedBall (by
      rwa [abs_of_pos (by norm_num : (0:ℝ) < 10)] at hw)))
  refine h.trans ?_
  have hpos : 0 < BP N T / ‖χ.LFunction (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (BP N T / ‖χ.LFunction (2 + T * I)‖) ≤ Real.log (BP N T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  exact div_le_div_of_nonneg_right hle (Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith))

/-! ## Zeros in the rectangle, and window counts -/

theorem eq_zero_of_mem_zerosIn {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c u : ℂ} {R r : ℝ}
    (hu : u ∈ zerosIn f c R r) : f u = 0 := by
  by_contra hfu
  apply (mem_zerosIn hu).2
  by_cases hcR : u ∈ Metric.closedBall c R
  · rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (Metric.closedBall c R)) hcR,
      (hf.analyticAt u).analyticOrderAt_eq_zero.2 hfu]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hcR

/-- `L(z, χ) ≠ 0` on `ℜz = 0`, `z ≠ 0` (`χ` primitive, `≠ 1`). -/
theorem LFunction_ne_zero_re_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) {z : ℂ} (h0 : z.re = 0) (hz0 : z ≠ 0) :
    χ.LFunction z ≠ 0 := by
  have hN : N ≠ 1 := by
    rintro rfl; exact hχ1 (Subsingleton.elim _ _)
  set s := 1 - z with hs
  have hz : z = 1 - s := by rw [hs]; ring
  have hsre : s.re = 1 := by simp [hs, h0]
  have hχi : χ⁻¹ ≠ 1 := fun h => hχ1 (inv_eq_one.1 h)
  have hGs0 : DirichletCharacter.gammaFactor χ⁻¹ s ≠ 0 := by
    rcases χ⁻¹.even_or_odd with he | ho
    · rw [he.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by linarith)
    · rw [ho.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΛ : DirichletCharacter.completedLFunction χ⁻¹ s =
      DirichletCharacter.gammaFactor χ⁻¹ s * χ⁻¹.LFunction s := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ s (Or.inr hN)]
    field_simp
  have hL : χ.LFunction z = (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
      (DirichletCharacter.gammaFactor χ⁻¹ s * χ⁻¹.LFunction s) /
        DirichletCharacter.gammaFactor χ (1 - s) := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (Or.inr hN), hz,
      hχ.completedLFunction_one_sub s, hΛ]
  rw [hL]
  have hNp : (N : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left; exact_mod_cast NeZero.ne N
  have hε : DirichletCharacter.rootNumber χ ≠ 0 := by
    intro h; have := norm_rootNumber hχ; rw [h, norm_zero] at this; exact zero_ne_one this
  have hLs : χ⁻¹.LFunction s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi) hsre.ge
  have hG1 : DirichletCharacter.gammaFactor χ (1 - s) ≠ 0 := by
    rw [← hz]
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact hz0 (by simpa using hn)
      · have := congrArg Complex.re hn
        simp [h0] at this
        have : (1:ℝ) ≤ n := by exact_mod_cast hpos
        linarith
    · rw [ho.gammaFactor_def, Ne, Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      simp [h0] at this
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hNp hε) (mul_ne_zero hGs0 hLs)) hG1

/-- The zeros in the rectangle: `0`, or in the open critical strip. -/
theorem zerosRect_cases {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T : ℝ} {u : ℂ} (hu : u ∈ zerosRect χ T) :
    χ.LFunction u = 0 ∧ |u.im| < T ∧ (u = 0 ∨ (0 < u.re ∧ u.re < 1)) := by
  rw [zerosRect, Finset.mem_filter] at hu
  obtain ⟨hu, h1, h2, h3, h4⟩ := hu
  simp only [zT_re, zT_im, wT_re, wT_im] at h1 h2 h3 h4
  have hL := eq_zero_of_mem_zerosIn (DirichletCharacter.differentiable_LFunction hχ1) hu
  refine ⟨hL, abs_lt.2 ⟨h3, h4⟩, ?_⟩
  by_cases hu0 : u = 0
  · exact Or.inl hu0
  right
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    rcases lt_or_eq_of_le h with h' | h'
    · exact LFunction_ne_zero_strip hχ hχ1 (by linarith) h' hL
    · exact LFunction_ne_zero_re_zero hχ hχ1 h' hu0 hL
  · by_contra h
    push Not at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h hL

/-- `Σ_{u ∈ S} m_u ≤ Σᶠ divisor(closedBall c' |r'|)` for `S ⊆ closedBall c R ∩ closedBall c' r'`. -/
theorem sum_divB_le_finsum {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c c' : ℂ} {R r' : ℝ}
    (S : Finset ℂ) (hS : ∀ u ∈ S, u ∈ Metric.closedBall c R ∧ u ∈ Metric.closedBall c' |r'|) :
    ((∑ u ∈ S, (divB f c R u).toNat : ℕ) : ℝ) ≤
      ((∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall c' |r'|) u : ℤ) : ℝ) := by
  set D := MeromorphicOn.divisor f (Metric.closedBall c' |r'|)
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall c' |r'|) := fun z _ => hf.analyticAt z
  have hDnn : ∀ u, 0 ≤ D u := fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa) u
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall c' |r'|)
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp)]
  push_cast
  have e : ∀ u ∈ S, ((divB f c R u).toNat : ℝ) = (D u : ℝ) := by
    intro u hu
    rw [divB_eq_of_mem hf (hS u hu).1 (hS u hu).2]
    exact_mod_cast Int.toNat_of_nonneg (hDnn u)
  rw [Finset.sum_congr rfl e]
  have h1 : ∑ u ∈ S, (D u : ℝ) = ∑ u ∈ S.filter (fun u => D u ≠ 0), (D u : ℝ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun u _ => by split_ifs with h <;> simp_all
  rw [h1]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun u _ _ => by exact_mod_cast hDnn u
  rw [Finset.mem_filter] at hu
  rw [Set.Finite.mem_toFinset, Function.mem_support]; exact hu.2

/-- **Window count**: zeros of the rectangle in `|u − (2 + ic)| ≤ r` have total multiplicity at most
`log(B'_c/0.355)/log(10/r)`. -/
theorem sum_multRect_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T : ℝ} (S : Finset ℂ) (hS : S ⊆ zerosRect χ T) (c : ℝ) {r : ℝ} (hr : 0 < r)
    (hr10 : r < 10) (hball : ∀ u ∈ S, ‖u - (2 + c * I)‖ ≤ r) :
    ∑ u ∈ S, (multRect χ T u : ℝ) ≤ Real.log (BP N c / 0.355) / Real.log (10 / r) := by
  have hf := DirichletCharacter.differentiable_LFunction hχ1
  have h1 := sum_divB_le_finsum hf (c := 2) (R := RT T) (c' := 2 + c * I) (r' := r) S fun u hu => by
    have hu' := hS hu
    rw [zerosRect, Finset.mem_filter] at hu'
    obtain ⟨hu1, -⟩ := mem_zerosIn hu'.1
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have : 0 ≤ RT T / 2 := le_trans (norm_nonneg _) hu1.le
      linarith
    · rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hr]; exact hball u hu
  have h2 := zero_count_poly hχ hχ1 c hr hr10
  unfold multRect
  push_cast at h1 ⊢
  linarith

end TernaryGoldbach.Explicit
