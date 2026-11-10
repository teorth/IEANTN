import TernaryGoldbach.Explicit.MellinPlancherel

/-!
# Sums of `|G_δ(ρ)|` over zeros on the critical line

`|f(γ)| ≤ (1/h)∫_I |f| + ∫_I |f'|` on a window `I ∋ γ` of length `h`; summing over windows of zeros
(each of total multiplicity `≤ Z`) and Cauchy–Schwarz with the Plancherel identities
(`MellinPlancherel`) gives `Σ m_ρ |G(ρ)| ≤ Z √(2Jh) (√(2π·0.6647)/h + √(2π·0.1707))`.
-/

open Complex MeasureTheory Set Filter
open scoped Real

namespace TernaryGoldbach.Explicit

/-- **Sobolev on an interval**. -/
theorem norm_le_sobolev {f f' : ℝ → ℂ} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f')
    {a b γ : ℝ} (hab : a < b) (hγ : γ ∈ Icc a b) :
    ‖f γ‖ ≤ (1 / (b - a)) * (∫ t in a..b, ‖f t‖) + ∫ t in a..b, ‖f' t‖ := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  set M := ∫ t in a..b, ‖f' t‖ with hM
  have hmono : ∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ b → ∫ u in c..d, ‖f' u‖ ≤ M := fun c d hc hcd hd =>
    intervalIntegral.integral_mono_interval hc hcd hd
      (Eventually.of_forall fun u => norm_nonneg _) (hf'.norm.intervalIntegrable _ _)
  have hpt : ∀ t ∈ Icc a b, ‖f γ‖ ≤ ‖f t‖ + M := by
    intro t ht
    have hftc : ∫ u in t..γ, f' u = f γ - f t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hf u) (hf'.intervalIntegrable _ _)
    have h1 : ‖∫ u in t..γ, f' u‖ ≤ M := by
      rcases le_total t γ with h | h
      · exact (intervalIntegral.norm_integral_le_integral_norm h).trans (hmono t γ ht.1 h hγ.2)
      · rw [intervalIntegral.integral_symm, norm_neg]
        exact (intervalIntegral.norm_integral_le_integral_norm h).trans (hmono γ t hγ.1 h ht.2)
    rw [hftc] at h1
    calc ‖f γ‖ = ‖f t + (f γ - f t)‖ := by ring_nf
      _ ≤ ‖f t‖ + ‖f γ - f t‖ := norm_add_le _ _
      _ ≤ ‖f t‖ + M := by linarith
  have hint : ∫ _ in a..b, ‖f γ‖ ≤ ∫ t in a..b, (‖f t‖ + M) :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      ((hfc.norm.add continuous_const).intervalIntegrable _ _) hpt
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add (hfc.norm.intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at hint
  have hba : 0 < b - a := by linarith
  rw [one_div, ← div_eq_inv_mul, div_add' _ _ _ hba.ne', le_div_iff₀ hba]
  nlinarith

/-- **Cauchy–Schwarz on an interval** (via AM–GM): `∫_a^b |g| ≤ √(A(b − a))` if `∫ |g|² ≤ A`. -/
theorem intervalIntegral_norm_le_sqrt {g : ℝ → ℂ} (hg : Continuous g)
    (hg2 : Integrable fun t => ‖g t‖ ^ 2) {A : ℝ} (hA : 0 < A) (hgA : ∫ t, ‖g t‖ ^ 2 ≤ A)
    {a b : ℝ} (hab : a < b) :
    ∫ t in a..b, ‖g t‖ ≤ √(A * (b - a)) := by
  set L := b - a with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  set s := √(A * L) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = A * L := Real.sq_sqrt (by positivity)
  set c := s / L with hc
  have hc0 : 0 < c := by positivity
  have hpt : ∀ t, ‖g t‖ ≤ ‖g t‖ ^ 2 / (2 * c) + c / 2 := by
    intro t
    rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖g t‖ - c)]
  have hgc := hg
  have i1 : IntervalIntegrable (fun t => ‖g t‖ ^ 2 / (2 * c)) volume a b :=
    (by fun_prop : Continuous fun t => ‖g t‖ ^ 2 / (2 * c)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2 / (2 * c) + c / 2) volume a b :=
    (by fun_prop : Continuous fun t => ‖g t‖ ^ 2 / (2 * c) + c / 2).intervalIntegrable _ _
  have h1 : ∫ t in a..b, ‖g t‖ ≤ ∫ t in a..b, (‖g t‖ ^ 2 / (2 * c) + c / 2) :=
    intervalIntegral.integral_mono_on hab.le (hg.norm.intervalIntegrable _ _) i2 fun t _ => hpt t
  have h2 : ∫ t in a..b, ‖g t‖ ^ 2 ≤ A := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact (setIntegral_le_integral hg2 (Eventually.of_forall fun t => by positivity)).trans hgA
  rw [intervalIntegral.integral_add i1 intervalIntegrable_const, intervalIntegral.integral_div, intervalIntegral.integral_const,
    smul_eq_mul] at h1
  have h3 : (∫ t in a..b, ‖g t‖ ^ 2) / (2 * c) ≤ A / (2 * c) :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : A / (2 * c) + (b - a) * (c / 2) = s := by
    rw [← hL, hc]; field_simp; nlinarith [hs2]
  linarith

/-- **Window sums**: if each window `[(k − J)h, (k − J + 1)h]` carries total weight `≤ Z`, then
`Σ m_u |f(ℑu)| ≤ Z ((1/h)∫_{−Jh}^{Jh}|f| + ∫_{−Jh}^{Jh}|f'|)`. -/
theorem sum_window_le {S : Finset ℂ} (m : ℂ → ℝ) (hm : ∀ u ∈ S, 0 ≤ m u) {h T0 Z : ℝ} (hh : 0 < h)
    (J : ℕ) (hJ : T0 < J * h) (hS : ∀ u ∈ S, |u.im| ≤ T0) (hZ0 : 0 ≤ Z)
    (hZ : ∀ k : ℕ, ∑ u ∈ S.filter (fun u => (⌊u.im / h⌋ + J).toNat = k), m u ≤ Z)
    {f f' : ℝ → ℂ} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    ∑ u ∈ S, m u * ‖f u.im‖ ≤
      Z * ((1 / h) * (∫ t in (-(J * h))..(J * h), ‖f t‖) + ∫ t in (-(J * h))..(J * h), ‖f' t‖) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  set idx : ℂ → ℕ := fun u => (⌊u.im / h⌋ + J).toNat with hidx
  set a : ℕ → ℝ := fun k => ((k : ℝ) - J) * h with ha
  set W : ℕ → ℝ := fun k => (1 / h) * (∫ t in a k..a (k + 1), ‖f t‖) + ∫ t in a k..a (k + 1), ‖f' t‖
    with hW
  have hW0 : ∀ k, 0 ≤ W k := by
    intro k
    have hak : a k ≤ a (k + 1) := by simp only [ha]; push_cast; nlinarith
    have i1 := intervalIntegral.integral_nonneg (μ := volume) hak fun t _ => norm_nonneg (f t)
    have i2 := intervalIntegral.integral_nonneg (μ := volume) hak fun t _ => norm_nonneg (f' t)
    simp only [hW]; positivity
  -- each zero lies in its window
  have hwin : ∀ u ∈ S, idx u < 2 * J ∧ u.im ∈ Icc (a (idx u)) (a (idx u + 1)) := by
    intro u hu
    have hb := abs_le.1 (hS u hu)
    have hT0h : T0 / h < J := by rw [div_lt_iff₀ hh]; exact hJ
    have hl : -(J : ℝ) < u.im / h := by
      rw [lt_div_iff₀ hh]; linarith
    have hr : u.im / h < J := lt_of_le_of_lt (div_le_div_of_nonneg_right hb.2 hh.le) hT0h
    have hfl1 : -(J : ℤ) ≤ ⌊u.im / h⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    have hfl2 : ⌊u.im / h⌋ < J := by
      rw [Int.floor_lt]; push_cast; exact hr
    have hnn : 0 ≤ ⌊u.im / h⌋ + J := by linarith
    have hk : ((idx u : ℕ) : ℤ) = ⌊u.im / h⌋ + J := Int.toNat_of_nonneg hnn
    have hkR : ((idx u : ℕ) : ℝ) = (⌊u.im / h⌋ : ℝ) + J := by exact_mod_cast hk
    refine ⟨by omega, ?_, ?_⟩
    · simp only [ha]; rw [hkR]
      have := Int.floor_le (u.im / h)
      have : (⌊u.im / h⌋ : ℝ) * h ≤ u.im := by rwa [le_div_iff₀ hh] at this
      nlinarith
    · simp only [ha]; push_cast; rw [hkR]
      have := Int.lt_floor_add_one (u.im / h)
      have : u.im < ((⌊u.im / h⌋ : ℝ) + 1) * h := by rwa [div_lt_iff₀ hh] at this
      nlinarith
  have hpt : ∀ u ∈ S, ‖f u.im‖ ≤ W (idx u) := by
    intro u hu
    have h1 := norm_le_sobolev hf hf' (a := a (idx u)) (b := a (idx u + 1))
      (by simp only [ha]; push_cast; nlinarith) (hwin u hu).2
    have e : a (idx u + 1) - a (idx u) = h := by simp only [ha]; push_cast; ring
    rw [e] at h1
    exact h1
  calc ∑ u ∈ S, m u * ‖f u.im‖ ≤ ∑ u ∈ S, m u * W (idx u) :=
        Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left (hpt u hu) (hm u hu)
    _ = ∑ k ∈ Finset.range (2 * J), ∑ u ∈ S.filter (fun u => idx u = k), m u * W (idx u) :=
        (Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_range.2 (hwin u hu).1) _).symm
    _ = ∑ k ∈ Finset.range (2 * J), W k * ∑ u ∈ S.filter (fun u => idx u = k), m u := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [(Finset.mem_filter.1 hu).2]; ring
    _ ≤ ∑ k ∈ Finset.range (2 * J), W k * Z :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hZ k) (hW0 k)
    _ = Z * ∑ k ∈ Finset.range (2 * J), W k := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        congr 1
        simp only [hW]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hfc.norm.intervalIntegrable _ _),
          intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hf'.norm.intervalIntegrable _ _)]
        simp only [ha]; push_cast
        congr 3 <;> ring

theorem integrable_norm_sq_fline (δ : ℝ) : Integrable fun t => ‖fline δ t‖ ^ 2 := by
  have hM := TernaryGoldbach.memLp_fourier (integrable_Fhalf δ) (memLp_Fhalf δ)
  have h := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).1 hM
  have h2 := h.comp_div (show (2 * π : ℝ) ≠ 0 by positivity)
  refine h2.congr (Eventually.of_forall fun t => ?_)
  simp only [fline_eq]

theorem integrable_norm_sq_flineD (δ : ℝ) : Integrable fun t => ‖flineD δ t‖ ^ 2 := by
  have hM := TernaryGoldbach.memLp_fourier (integrable_memLp_FhalfD δ).1 (integrable_memLp_FhalfD δ).2
  have h := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).1 hM
  have h2 := (h.comp_div (show (2 * π : ℝ) ≠ 0 by positivity)).const_mul ((1 / (2 * π)) ^ 2)
  refine h2.congr (Eventually.of_forall fun t => ?_)
  simp only [flineD, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]

theorem integral_norm_sq_fline_le (δ : ℝ) : ∫ t, ‖fline δ t‖ ^ 2 ≤ 2 * π * 0.6647 := by
  rw [integral_norm_sq_fline, integral_etaSq]
  have := sqrt_pi_bounds.2
  have hpi := Real.pi_pos
  nlinarith

theorem integral_norm_sq_flineD_le (δ : ℝ) : ∫ t, ‖flineD δ t‖ ^ 2 ≤ 2 * π * 0.1707 := by
  rw [integral_norm_sq_flineD]
  have := integral_log_sq_etaSq_le
  have := sqrt_pi_bounds.1
  have hpi := Real.pi_pos
  nlinarith

/-- **Zeros on the critical line**: under the window hypothesis, with `T₀ < Jh`,
`Σ m_u |G_δ(1/2 + iℑu)| ≤ Z ((1/h)√(2π·0.6647·2Jh) + √(2π·0.1707·2Jh))`. -/
theorem sum_window_fline_le {S : Finset ℂ} (m : ℂ → ℝ) (hm : ∀ u ∈ S, 0 ≤ m u) {h T0 Z : ℝ}
    (hh : 0 < h) (hT0 : 0 ≤ T0) (J : ℕ) (hJ : T0 < J * h) (hS : ∀ u ∈ S, |u.im| ≤ T0) (hZ0 : 0 ≤ Z)
    (hZ : ∀ k : ℕ, ∑ u ∈ S.filter (fun u => (⌊u.im / h⌋ + J).toNat = k), m u ≤ Z) (δ : ℝ) :
    ∑ u ∈ S, m u * ‖fline δ u.im‖ ≤
      Z * ((1 / h) * √(2 * π * 0.6647 * (2 * (J * h))) + √(2 * π * 0.1707 * (2 * (J * h)))) := by
  have hJh : 0 < (J : ℝ) * h := by linarith
  refine (sum_window_le m hm hh J hJ hS hZ0 hZ (hasDerivAt_fline δ) (continuous_flineD δ)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hZ0
  have e : (J : ℝ) * h - -(J * h) = 2 * (J * h) := by ring
  have h1 := intervalIntegral_norm_le_sqrt (continuous_fline δ) (integrable_norm_sq_fline δ)
    (by positivity) (integral_norm_sq_fline_le δ) (a := -(J * h)) (b := J * h) (by linarith)
  have h2 := intervalIntegral_norm_le_sqrt (continuous_flineD δ) (integrable_norm_sq_flineD δ)
    (by positivity) (integral_norm_sq_flineD_le δ) (a := -(J * h)) (b := J * h) (by linarith)
  rw [e] at h1 h2
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 1 / h)
  linarith

end TernaryGoldbach.Explicit
