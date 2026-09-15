/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section7Tritura
import Section7Zeros

/-!
# Section 7: `lem:adar`

The sum over zeros with `t₀ < γ ≤ T` of `|ω⁺_{T,σ}(ρ) + ξ θ_{T,1}(ρ) i|`, under RH up to `T`.
Each term is compared with `φ(γ) = √(F(γ/T)² + (1 - γ/T)²)` by `cor:thonny`; `∑ φ(γ)` is turned into
an integral by `lem:Lehmanmodern`, and the integral is `prop:tritura`.
-/

open Real MeasureTheory Set

namespace CH2Section7A

open CH2Section7 CH2Section7T

/-! ### `F` is decreasing, with an explicit derivative -/

theorem hasDerivAt_Fweight {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    HasDerivAt Fweight (-Real.cot (Real.pi * u) - (1 - u) * (Real.pi / Real.sin (Real.pi * u) ^ 2)) u := by
  have hs := sin_pi_ne_zero h0 h1
  have hπu : HasDerivAt (fun v : ℝ ↦ Real.pi * v) Real.pi u := by
    simpa using (hasDerivAt_id u).const_mul Real.pi
  have hcot : HasDerivAt (fun v ↦ Real.cot (Real.pi * v))
      (-(1 / Real.sin (Real.pi * u) ^ 2) * Real.pi) u := (hasDerivAt_cot hs).comp u hπu
  have h := (hasDerivAt_const u (1 / Real.pi)).add
    (((hasDerivAt_id u).const_sub 1).mul hcot)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v ↦ ?_)).congr_deriv ?_
  · simp [Fweight_eq]
  · simp only [id]; field_simp; ring

theorem deriv_Fweight_nonpos {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    -Real.cot (Real.pi * u) - (1 - u) * (Real.pi / Real.sin (Real.pi * u) ^ 2) ≤ 0 := by
  have hπ := Real.pi_pos
  set x := Real.pi * u with hx
  have hx0 : 0 < x := by positivity
  have hxπ : x < Real.pi := by nlinarith
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxπ
  have hsin2 : Real.sin (2 * x) ≥ -(2 * Real.pi - 2 * x) := by
    have h := Real.sin_le (by linarith : 0 ≤ 2 * Real.pi - 2 * x)
    rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi] at h
    linarith
  have e : -Real.cot x - (1 - u) * (Real.pi / Real.sin x ^ 2)
      = -(Real.sin x * Real.cos x + (Real.pi - x)) / Real.sin x ^ 2 := by
    rw [Real.cot_eq_cos_div_sin, hx]; field_simp; ring
  rw [e]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  rw [Real.sin_two_mul] at hsin2
  linarith

/-! ### The comparison weight `φ(t) = √(F(t/T)² + (1 - t/T)²)` -/

noncomputable def phiW (T t : ℝ) : ℝ := Real.sqrt (Fweight (t / T) ^ 2 + (1 - t / T) ^ 2)

noncomputable def dF (u : ℝ) : ℝ :=
  -Real.cot (Real.pi * u) - (1 - u) * (Real.pi / Real.sin (Real.pi * u) ^ 2)

noncomputable def phiW' (T t : ℝ) : ℝ :=
  (2 * Fweight (t / T) * dF (t / T) / T - 2 * (1 - t / T) / T) / (2 * phiW T t)

theorem phiW_pos {T t : ℝ} (hT : 0 < T) (htT : t < T) : 0 < phiW T t := by
  unfold phiW
  apply Real.sqrt_pos.mpr
  have : 0 < 1 - t / T := by rw [sub_pos, div_lt_one hT]; exact htT
  positivity

theorem hasDerivAt_phiW {T t : ℝ} (hT : 0 < T) (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (phiW T) (phiW' T t) t := by
  have hu0 : 0 < t / T := div_pos ht0 hT
  have hu1 : t / T < 1 := (div_lt_one hT).mpr htT
  have hdiv : HasDerivAt (fun s : ℝ ↦ s / T) (1 / T) t := by
    simpa using (hasDerivAt_id t).div_const T
  have hFw : HasDerivAt Fweight (dF (t / T)) (t / T) := hasDerivAt_Fweight hu0 hu1
  have hF := hFw.comp t hdiv
  have hQ : HasDerivAt (fun s ↦ Fweight (s / T) ^ 2 + (1 - s / T) ^ 2)
      (2 * Fweight (t / T) * dF (t / T) / T - 2 * (1 - t / T) / T) t := by
    refine ((hF.pow 2).add ((hdiv.const_sub 1).pow 2)).congr_deriv ?_
    simp only [Function.comp_apply]
    push_cast; ring
  have hpos : 0 < Fweight (t / T) ^ 2 + (1 - t / T) ^ 2 := by
    have : 0 < 1 - t / T := by linarith
    positivity
  exact hQ.sqrt hpos.ne'

theorem phiW'_nonpos {T t : ℝ} (hT : 0 < T) (ht0 : 0 < t) (htT : t < T) : phiW' T t ≤ 0 := by
  have hu0 : 0 < t / T := div_pos ht0 hT
  have hu1 : t / T < 1 := (div_lt_one hT).mpr htT
  have hF := Fweight_pos hu0 hu1
  have hdF := deriv_Fweight_nonpos hu0 hu1
  have hp := phiW_pos hT htT
  unfold phiW'
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have h1 : 2 * Fweight (t / T) * dF (t / T) / T ≤ 0 := by
    unfold dF
    apply div_nonpos_of_nonpos_of_nonneg _ hT.le
    nlinarith
  have h2 : 0 ≤ 2 * (1 - t / T) / T := by
    apply div_nonneg _ hT.le; linarith
  linarith

theorem continuousOn_phiW' {T a b : ℝ} (hT : 0 < T) (ha : 0 < a) (hbT : b < T) :
    ContinuousOn (phiW' T) (Set.Icc a b) := by
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have htT : t < T := by linarith [ht.2]
  have hu0 : 0 < t / T := div_pos ht0 hT
  have hu1 : t / T < 1 := (div_lt_one hT).mpr htT
  refine ContinuousAt.continuousWithinAt ?_
  have hs := sin_pi_ne_zero hu0 hu1
  have hcont_div : ContinuousAt (fun s : ℝ ↦ s / T) t := by fun_prop
  have hFc : ContinuousAt (fun s ↦ Fweight (s / T)) t :=
    ((continuousOn_Fweight (a := t / T / 2) (b := (t / T + 1) / 2) (by positivity)
      (by linarith)).continuousAt (Icc_mem_nhds (by linarith) (by linarith))).comp hcont_div
  have hcotc : ContinuousAt (fun s : ℝ ↦ Real.cot (Real.pi * (s / T))) t := by
    simp only [Real.cot_eq_cos_div_sin]
    exact (by fun_prop : ContinuousAt (fun s : ℝ ↦ Real.cos (Real.pi * (s / T))) t).div
      (by fun_prop) hs
  have hdFc : ContinuousAt (fun s ↦ dF (s / T)) t := by
    unfold dF
    exact hcotc.neg.sub (((continuousAt_const.sub hcont_div)).mul
      (continuousAt_const.div (by fun_prop) (pow_ne_zero 2 hs)))
  have hphic : ContinuousAt (phiW T) t := (hasDerivAt_phiW hT ht0 htT).continuousAt
  unfold phiW'
  exact ((((continuousAt_const.mul hFc).mul hdFc).div_const T).sub
    (((continuousAt_const.mul (continuousAt_const.sub hcont_div))).div_const T)).div
    (continuousAt_const.mul hphic) (by have := phiW_pos hT htT; positivity)

/-! ### Zeros on the critical line, and sums over them -/

/-- **RH up to `T` puts every zero with `0 < γ ≤ T` on the line**: `RiemannHypothesisUpTo` excludes only
`1/2 < Re < 1`; the functional equation and conjugation reflect `Re < 1/2` into it. -/
theorem re_eq_half_of_RH {T : ℝ} (hRH : IEANTN.RiemannHypothesisUpTo T) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.im) (hT : ρ.im ≤ T) : ρ.re = 1 / 2 := by
  have hs := CH2ZetaInstance.re_mem_Icc_of_riemannZeta_eq_zero hz h0.ne'
  have hlt1 : ρ.re < 1 := by
    rcases hs.2.lt_or_eq with h | h
    · exact h
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re h.ge)
  have hnot : ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 < w.re → w.re < 1 → 0 ≤ w.im → w.im ≤ T → False :=
    fun w hw h1 h2 h3 h4 ↦ hRH.false ⟨w, ⟨h1, h2⟩, ⟨h3, h4⟩, hw⟩
  rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
  · -- reflect: `ζ(1 - ρ) = 0`, then conjugate
    have hn : ∀ n : ℕ, ρ ≠ -n := by
      intro n hn; rw [hn] at h0; simp at h0
    have h1 : ρ ≠ 1 := by intro h1; rw [h1] at h0; simp at h0
    have hz1 : riemannZeta (1 - ρ) = 0 := by rw [riemannZeta_one_sub hn h1, hz, mul_zero]
    have hz2 : riemannZeta (starRingEnd ℂ (1 - ρ)) = 0 := by
      rw [riemannZeta_conj, hz1, map_zero]
    have hre : (starRingEnd ℂ (1 - ρ)).re = 1 - ρ.re := by simp
    have him : (starRingEnd ℂ (1 - ρ)).im = ρ.im := by simp
    rcases hs.1.lt_or_eq with h' | h'
    · exact (hnot _ hz2 (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact h0.le)
        (by rw [him]; exact hT)).elim
    · exact absurd hz2 (riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith))
  · exact h
  · exact (hnot ρ hz h hlt1 h0.le hT).elim

/-- Monotonicity of a zero sum with non-negative multiplicities. -/
theorem zsum_mono {a b : ℝ} (ha : 0 ≤ a) {f g : ℂ → ℝ}
    (hfg : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc a b), f ρ ≤ g ρ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) f ≤ IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) g := by
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin]
  refine Finset.sum_le_sum fun ρ hρ ↦ ?_
  have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
  have hm := CH2Section7Z.zetaOrder_nonneg_of_mem (J := Set.Ioc a b)
    (fun x hx ↦ lt_of_le_of_lt ha hx.1) hρ'
  exact mul_le_mul_of_nonneg_right (hfg ρ hρ') hm

theorem zsum_add {a b : ℝ} (ha : 0 ≤ a) (f g : ℂ → ℝ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ f ρ + g ρ)
      = IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) f
        + IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) g := by
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin,
    CH2Section7Z.zetaZeroesSum_eq_sum hfin, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ρ _ ↦ by ring

theorem zsum_const_mul {a b : ℝ} (ha : 0 ≤ a) (c : ℝ) (f : ℂ → ℝ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun ρ ↦ c * f ρ)
      = c * IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) f := by
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin, CH2Section7Z.zetaZeroesSum_eq_sum hfin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ ↦ by ring

/-- `∑_{a < γ ≤ b} 1 ≤ N(b)`. -/
theorem zsum_one_le {a b : ℝ} (ha : 0 ≤ a) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun _ ↦ 1) ≤ ZeroCount.v1.zetaNClosed b := by
  rcases le_or_gt b a with hba | hab
  · have hempty : IEANTN.zetaZeroesIn Set.univ (Set.Ioc a b) = ∅ := by
      ext ρ; simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, ⟨h1, h2⟩, -⟩; linarith
    have h0 : IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) (fun _ ↦ (1:ℝ)) = 0 := by
      unfold IEANTN.zetaZeroesSum; rw [hempty]; simp
    rw [h0, ZeroCount.v1.zetaNClosed]
    have hfin := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := b) le_rfl
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin]
    refine Finset.sum_nonneg fun ρ hρ ↦ ?_
    have := CH2Section7Z.zetaOrder_nonneg_of_mem (J := Set.Ioc 0 b) (fun x hx ↦ hx.1)
      ((Set.Finite.mem_toFinset hfin).mp hρ)
    linarith
  · have hs := CH2Section7Z.zetaNClosed_eq_sum (t₁ := b) (s := b) (by linarith) le_rfl
    have hfin := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha
    rw [hs, CH2Section7Z.zetaZeroesSum_eq_sum hfin]
    have hfin0 := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := b) le_rfl
    have hsub : hfin.toFinset ⊆ hfin0.toFinset := by
      intro ρ hρ; rw [Set.Finite.mem_toFinset] at hρ ⊢
      exact ⟨hρ.1, ⟨lt_of_le_of_lt ha hρ.2.1.1, hρ.2.1.2⟩, hρ.2.2⟩
    calc ∑ ρ ∈ hfin.toFinset, 1 * (IEANTN.zetaOrder ρ : ℝ)
        = ∑ ρ ∈ hfin.toFinset, (if ρ.im ≤ b then (IEANTN.zetaOrder ρ : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
          rw [Set.Finite.mem_toFinset] at hρ
          rw [if_pos hρ.2.1.2, one_mul]
      _ ≤ ∑ ρ ∈ hfin0.toFinset, (if ρ.im ≤ b then (IEANTN.zetaOrder ρ : ℝ) else 0) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun ρ hρ _ ↦ ?_
          have := CH2Section7Z.zetaOrder_nonneg_of_mem (J := Set.Ioc 0 b) (fun x hx ↦ hx.1)
            ((Set.Finite.mem_toFinset hfin0).mp hρ)
          split_ifs <;> linarith

/-! ### Bounds on the comparison weight -/

theorem norm_F_add_le_phiW {T t ξ : ℝ} (hξ : |ξ| ≤ 1) :
    ‖((Fweight (t / T) : ℝ) : ℂ) + (ξ : ℂ) * (((1 - t / T) : ℝ) : ℂ) * Complex.I‖ ≤ phiW T t := by
  rw [show ((Fweight (t / T) : ℝ) : ℂ) + (ξ : ℂ) * (((1 - t / T) : ℝ) : ℂ) * Complex.I
      = ((Fweight (t / T) : ℝ) : ℂ) + ((ξ * (1 - t / T) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_add_mul_I, phiW]
  apply Real.sqrt_le_sqrt
  have : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ξ]
  nlinarith [sq_nonneg (1 - t / T)]

theorem phiW_le {T t : ℝ} (hT : 0 < T) (ht0 : 0 < t) (htT : t < T) :
    phiW T t ≤ T / (Real.pi * t) + 1 := by
  have hu0 : 0 < t / T := div_pos ht0 hT
  have hu1 : t / T < 1 := (div_lt_one hT).mpr htT
  have hF := Fweight_pos hu0 hu1
  have hF2 := Fweight_lt_inv hu0 hu1
  have h1u : 0 ≤ 1 - t / T := by linarith
  have e : 1 / (Real.pi * (t / T)) = T / (Real.pi * t) := by field_simp
  rw [e] at hF2
  unfold phiW
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- **The weight at a zero on the line** (`witdim`, summed form). -/
theorem weight_le {T σ ξ : ℝ} (hcs : CotangentSeries.v1.cot_series_zeta_values) (hT : 0 < T)
    (hσ1 : σ ≠ 1) (hσT : |σ - 1 / 2| ≤ T / 2) (hξ : |ξ| ≤ 1) {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (h0 : 0 < ρ.im) (hT' : ρ.im < T) :
    ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ‖
      ≤ phiW T ρ.im + |σ - 1 / 2| * T / (Real.pi * ρ.im ^ 2) + (2.78 * |σ - 1 / 2| + 1) / T := by
  have hρ : ρ = 1 / 2 + (ρ.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
  have hw := CH2Section6.thonny_witdim hcs hT hσ1 hσT hξ h0 hT'
  rw [← hρ] at hw
  have := norm_F_add_le_phiW (T := T) (t := ρ.im) hξ
  calc _ ≤ ‖((Fweight (ρ.im / T) : ℝ) : ℂ) + (ξ : ℂ) * (((1 - ρ.im / T) : ℝ) : ℂ) * Complex.I‖
        + ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ
          - (((Fweight (ρ.im / T) : ℝ) : ℂ) + (ξ : ℂ) * (((1 - ρ.im / T) : ℝ) : ℂ) * Complex.I)‖ := by
          exact norm_le_insert' _ _
    _ ≤ _ := by linarith

/-! ### The `φ` sum up to `t₁ < T` -/

set_option maxHeartbeats 1000000 in
theorem sum_phiW_le (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) {T t₀ t₁ : ℝ} (ht0 : 14 ≤ t₀) (h2 : 2 * t₀ ≤ T)
    (h01 : t₀ ≤ t₁) (h1T : t₁ < T) :
    2 * Real.pi / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ phiW T ρ.im)
      ≤ (1 / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) ^ 2 - Real.log (t₀ / (2 * Real.pi)) ^ 2
          - 2 * C1lo 12 * (Real.log (T / (2 * Real.pi)) + 1) + 2 * C2hi
          + (2 * (Real.log (T / (2 * Real.pi)) + 1) * ((t₀ / T) ^ 2 / 2 + (1 - t₁ / T)) * 14
            + Real.pi ^ 2 * gT (t₁ / T) * Real.log (T / (2 * Real.pi))))
        + (2 / (5 * t₀) + 2 * Real.pi * Real.log (T / t₀) / (5 * T))
        + (2 / t₀ + 2 * Real.pi / T) * (2 * Real.log t₀ / 5 + 4) := by
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_lt_d2
  have ht0p : 0 < t₀ := by linarith
  have hT : 0 < T := by linarith
  have ht1p : 0 < t₁ := by linarith
  set y := Real.log (T / (2 * Real.pi)) with hy
  have hmemI : ∀ t ∈ Set.uIcc t₀ t₁, 0 < t ∧ t < T := by
    intro t ht; rw [Set.uIcc_of_le h01] at ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hL := CH2Section7Z.lehman_antitone hrvm (φ := phiW T) (φ' := phiW' T) (by linarith) h01
    (fun t ht ↦ hasDerivAt_phiW hT (hmemI t ht).1 (hmemI t ht).2)
    (by rw [Set.uIcc_of_le h01]; exact continuousOn_phiW' hT ht0p h1T)
    (fun t ht ↦ phiW'_nonpos hT (by linarith [ht.1]) (by linarith [ht.2]))
    (phiW_pos hT h1T).le
  -- continuity
  have hphic : ContinuousOn (phiW T) (Set.Icc t₀ t₁) := fun t ht ↦
    (hasDerivAt_phiW hT (by linarith [ht.1]) (by linarith [ht.2])).continuousAt.continuousWithinAt
  have hlogc : ContinuousOn (fun t ↦ Real.log (t / (2 * Real.pi))) (Set.Icc t₀ t₁) := by
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have hne : t / (2 * Real.pi) ≠ 0 := by positivity
    exact (((continuous_id.div_const (2 * Real.pi)).continuousAt (x := t)).log hne).continuousWithinAt
  have hinvc : ContinuousOn (fun t : ℝ ↦ 1 / (5 * t)) (Set.Icc t₀ t₁) := by
    intro t ht
    have htp : 0 < t := by linarith [ht.1]
    have hne : 5 * t ≠ 0 := by positivity
    exact (continuousAt_const.div (by fun_prop) hne).continuousWithinAt
  -- split the integral
  have hsplit : (∫ t in t₀..t₁, phiW T t * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + 1 / (5 * t)))
      = (1 / (2 * Real.pi)) * (∫ t in t₀..t₁, phiW T t * Real.log (t / (2 * Real.pi)))
        + ∫ t in t₀..t₁, phiW T t * (1 / (5 * t)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun t _ ↦ by ring
    · exact ((hphic.mul hlogc).const_mul _).intervalIntegrable_of_Icc h01
    · exact (hphic.mul hinvc).intervalIntegrable_of_Icc h01
  -- the main integral is tritura
  set ε := t₀ / T with hε
  set b := t₁ / T with hb
  have hεp : 0 < ε := div_pos ht0p hT
  have hε2 : ε ≤ 1 / 2 := by rw [hε, div_le_iff₀ hT]; linarith
  have hεb : ε ≤ b := div_le_div_of_nonneg_right h01 hT.le
  have hb1 : b < 1 := (div_lt_one hT).mpr h1T
  have hw : 0 ≤ y + Real.log ε := by
    have e : y + Real.log ε = Real.log (t₀ / (2 * Real.pi)) := by
      rw [hy, hε, ← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    rw [e]; apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
  have htr := tritura hcs hεp hε2 hεb hb1 hw 12
  have hsub : (∫ t in t₀..t₁, phiW T t * Real.log (t / (2 * Real.pi)))
      = T * ∫ u in ε..b, Real.sqrt (Fweight u ^ 2 + (1 - u) ^ 2) * (y + Real.log u) := by
    have hcomp := intervalIntegral.integral_comp_mul_left
      (fun t ↦ phiW T t * Real.log (t / (2 * Real.pi))) (a := ε) (b := b) hT.ne'
    rw [show T * ε = t₀ by rw [hε]; field_simp, show T * b = t₁ by rw [hb]; field_simp] at hcomp
    have h3 : (∫ t in t₀..t₁, phiW T t * Real.log (t / (2 * Real.pi)))
        = T * ∫ x in ε..b, phiW T (T * x) * Real.log (T * x / (2 * Real.pi)) := by
      rw [hcomp, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
    rw [h3]
    congr 1
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [Set.uIcc_of_le hεb] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    simp only [phiW]
    rw [show T * u / T = u by field_simp, show T * u / (2 * Real.pi) = (T / (2 * Real.pi)) * u by ring,
      Real.log_mul (by positivity) hu0.ne', ← hy]
  -- the `1/(5t)` integral
  have hI2 : (∫ t in t₀..t₁, phiW T t * (1 / (5 * t)))
      ≤ T / (5 * Real.pi * t₀) + Real.log (T / t₀) / 5 := by
    have hmono : (∫ t in t₀..t₁, phiW T t * (1 / (5 * t)))
        ≤ ∫ t in t₀..t₁, (T / (5 * Real.pi) * (1 / t ^ 2) + (1 / 5) * (1 / t)) := by
      refine intervalIntegral.integral_mono_on h01 ((hphic.mul hinvc).intervalIntegrable_of_Icc h01) ?_
        fun t ht ↦ ?_
      · refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le h01]
        intro t ht
        have : t ≠ 0 := by linarith [ht.1]
        have : t ^ 2 ≠ 0 := by positivity
        exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
      · have htp : 0 < t := by linarith [ht.1]
        have hle := phiW_le hT htp (by linarith [ht.2])
        have := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ 1 / (5 * t))
        calc _ ≤ (T / (Real.pi * t) + 1) * (1 / (5 * t)) := this
          _ = _ := by field_simp
    have hd : ∀ t ∈ Set.uIcc t₀ t₁, HasDerivAt (fun t ↦ -(T / (5 * Real.pi)) * (1 / t) + (1 / 5) * Real.log t)
        (T / (5 * Real.pi) * (1 / t ^ 2) + (1 / 5) * (1 / t)) t := by
      intro t ht
      have htp := (hmemI t ht).1
      have h1 := ((hasDerivAt_inv htp.ne').const_mul (-(T / (5 * Real.pi))))
      have h2 := (Real.hasDerivAt_log htp.ne').const_mul (1 / 5 : ℝ)
      refine (h1.add h2).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · exact Filter.Eventually.of_forall fun s ↦ by simp [one_div]
      · field_simp
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le h01]
      intro t ht
      have : t ≠ 0 := by linarith [ht.1]
      have : t ^ 2 ≠ 0 := by positivity
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption)))
    rw [hint] at hmono
    have hlog : Real.log t₁ - Real.log t₀ ≤ Real.log (T / t₀) := by
      rw [Real.log_div hT.ne' ht0p.ne']
      have := Real.log_le_log ht1p h1T.le
      linarith
    have ht1inv : 0 ≤ T / (5 * Real.pi) * (1 / t₁) := by positivity
    have e : T / (5 * Real.pi * t₀) = T / (5 * Real.pi) * (1 / t₀) := by field_simp
    nlinarith
  -- the endpoint term
  have hQ := (abs_le.mp (hrvm t₀ (by linarith))).1
  have hphi0 := phiW_le hT ht0p (by linarith)
  have hphi0p := (phiW_pos hT (by linarith : t₀ < T)).le
  have hend : phiW T t₀ * (Real.log t₀ / 5 + 2 - (ZeroCount.v1.zetaNClosed t₀ - ZeroCount.v1.rvmMain t₀))
      ≤ (T / (Real.pi * t₀) + 1) * (2 * Real.log t₀ / 5 + 4) := by
    have hlog0 : 0 ≤ Real.log t₀ := Real.log_nonneg (by linarith)
    have h1 : Real.log t₀ / 5 + 2 - (ZeroCount.v1.zetaNClosed t₀ - ZeroCount.v1.rvmMain t₀)
        ≤ 2 * Real.log t₀ / 5 + 4 := by linarith
    have h2 : 0 ≤ Real.log t₀ / 5 + 2 - (ZeroCount.v1.zetaNClosed t₀ - ZeroCount.v1.rvmMain t₀) := by
      have := (abs_le.mp (hrvm t₀ (by linarith))).2; linarith
    calc _ ≤ phiW T t₀ * (2 * Real.log t₀ / 5 + 4) := mul_le_mul_of_nonneg_left h1 hphi0p
      _ ≤ _ := mul_le_mul_of_nonneg_right hphi0 (by positivity)
  -- assemble
  rw [hsplit, hsub] at hL
  have hsumC : ∑ n ∈ Finset.range 12, cLow n ≤ 14 := sum_cLow_twelve
  have hE : 2 * (y + 1) * (ε ^ 2 / 2 + (1 - b)) * ∑ n ∈ Finset.range 12, cLow n
      ≤ 2 * (y + 1) * (ε ^ 2 / 2 + (1 - b)) * 14 := by
    have : 0 ≤ y := by
      rw [hy]; apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; linarith
    have : 0 ≤ 2 * (y + 1) * (ε ^ 2 / 2 + (1 - b)) := by
      have : 0 ≤ 1 - b := by linarith
      positivity
    exact mul_le_mul_of_nonneg_left hsumC this
  have hK : 0 ≤ 2 * Real.pi / T := by positivity
  have hmain := mul_le_mul_of_nonneg_left hL hK
  have e1 : 2 * Real.pi / T * ((1 / (2 * Real.pi)) * (T * ∫ u in ε..b,
      Real.sqrt (Fweight u ^ 2 + (1 - u) ^ 2) * (y + Real.log u)))
      = (1 / (2 * Real.pi)) * (2 * Real.pi * ∫ u in ε..b,
        Real.sqrt (Fweight u ^ 2 + (1 - u) ^ 2) * (y + Real.log u)) := by
    field_simp
  have e2 : Real.log (t₀ / (2 * Real.pi)) = y + Real.log ε := by
    rw [hy, hε, ← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have htr' := mul_le_mul_of_nonneg_left htr (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))
  have hI2' := mul_le_mul_of_nonneg_left hI2 hK
  have hend' := mul_le_mul_of_nonneg_left hend hK
  have e3 : 2 * Real.pi / T * (T / (5 * Real.pi * t₀) + Real.log (T / t₀) / 5)
      = 2 / (5 * t₀) + 2 * Real.pi * Real.log (T / t₀) / (5 * T) := by field_simp
  have e4 : 2 * Real.pi / T * ((T / (Real.pi * t₀) + 1) * (2 * Real.log t₀ / 5 + 4))
      = (2 / t₀ + 2 * Real.pi / T) * (2 * Real.log t₀ / 5 + 4) := by field_simp
  rw [e3] at hI2'
  rw [e4] at hend'
  rw [e2]
  have hE' := mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))
  nlinarith [hmain, e1, htr', hI2', hend', hE']

/-! ### `lem:adar` -/

theorem tendsto_gT_one (hcs : CotangentSeries.v1.cot_series_zeta_values) {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun t₁ ↦ gT (t₁ / T)) (nhdsWithin T (Set.Iio T)) (nhds 0) := by
  have hπ := Real.pi_pos
  have hbound : Filter.Tendsto (fun t₁ : ℝ ↦ (1 - t₁ / T) ^ 2 / (Real.pi ^ 2 * (t₁ / T))
      + (1 - t₁ / T) / Real.pi ^ 2) (nhdsWithin T (Set.Iio T)) (nhds 0) := by
    have hc : ContinuousAt (fun t₁ : ℝ ↦ (1 - t₁ / T) ^ 2 / (Real.pi ^ 2 * (t₁ / T))
        + (1 - t₁ / T) / Real.pi ^ 2) T := by
      have : Real.pi ^ 2 * (T / T) ≠ 0 := by rw [div_self hT.ne']; positivity
      fun_prop (disch := first | assumption | positivity)
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio T))
    simpa [div_self hT.ne'] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT hT] with t₁ ht
    exact gT_nonneg hcs (div_pos ht.1 hT) ((div_lt_one hT).mpr ht.2)
  · filter_upwards [Ioo_mem_nhdsLT hT] with t₁ ht
    exact gT_le (div_pos ht.1 hT) ((div_lt_one hT).mpr ht.2)

set_option maxHeartbeats 1000000 in
/-- **`lem:adar`**, for `14 ≤ t₀ ≤ T/2`, RH up to `T` and no zero ordinate at `T`. -/
theorem adar (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    {T σ ξ t₀ : ℝ} (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → z.im ≠ T) (ht0 : 14 ≤ t₀) (h2 : 2 * t₀ ≤ T)
    (hσ1 : σ ≠ 1) (hσT : |σ - 1 / 2| ≤ T / 2) (hξ : |ξ| ≤ 1) :
    2 * Real.pi / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T)
        (fun ρ ↦ ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ‖)
      ≤ (1 / (2 * Real.pi)) * (Real.log (T / (2 * Real.pi)) ^ 2 - Real.log (t₀ / (2 * Real.pi)) ^ 2
          - 2 * C1lo 12 * (Real.log (T / (2 * Real.pi)) + 1) + 2 * C2hi
          + 14 * (Real.log (T / (2 * Real.pi)) + 1) * (t₀ / T) ^ 2)
        + (2 / (5 * t₀) + 2 * Real.pi * Real.log (T / t₀) / (5 * T))
        + (2 / t₀ + 2 * Real.pi / T) * (2 * Real.log t₀ / 5 + 4)
        + 2 * |σ - 1 / 2| * (Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀)
          + (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2)
        + (2.78 * |σ - 1 / 2| + 1) * Real.log (T / (2 * Real.pi)) / T := by
  have hπ := Real.pi_pos
  have ht0p : 0 < t₀ := by linarith
  have hT : 0 < T := by linarith
  have hK : 0 ≤ 2 * Real.pi / T := by positivity
  set y := Real.log (T / (2 * Real.pi)) with hy
  set c := 2.78 * |σ - 1 / 2| + 1 with hc
  -- (i) termwise
  have hterm := zsum_mono ht0p.le (a := t₀) (b := T)
    (f := fun ρ ↦ ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ‖)
    (g := fun ρ ↦ phiW T ρ.im + ((|σ - 1 / 2| * T / Real.pi) * (1 / ρ.im ^ 2) + (c / T) * 1))
    (fun ρ hρ ↦ by
      obtain ⟨-, ⟨h0, h1⟩, hz⟩ := hρ
      have hre := re_eq_half_of_RH hRH hz (by linarith) h1
      have hlt : ρ.im < T := lt_of_le_of_ne h1 (hTfree ρ hz)
      have := weight_le hcs hT hσ1 hσT hξ hre (by linarith) hlt
      have e : |σ - 1 / 2| * T / (Real.pi * ρ.im ^ 2)
          = |σ - 1 / 2| * T / Real.pi * (1 / ρ.im ^ 2) := by
        have : ρ.im ≠ 0 := by linarith
        field_simp
      rw [← hc, e] at this
      linarith)
  rw [zsum_add ht0p.le, zsum_add ht0p.le, zsum_const_mul ht0p.le, zsum_const_mul ht0p.le] at hterm
  -- (ii) the three pieces
  have hinvsq := CH2Section7Z.sum_inv_sq_le hrvm ht0 (by linarith : t₀ ≤ T)
  have hcount : IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun _ ↦ (1:ℝ)) ≤ T / (2 * Real.pi) * y :=
    (zsum_one_le ht0p.le).trans (CH2Section7Z.zetaN_le_brut hrvm hsmall (by linarith))
  -- (iii) the `φ` sum, by a limit
  have hphi : 2 * Real.pi / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ phiW T ρ.im)
      ≤ (1 / (2 * Real.pi)) * (y ^ 2 - Real.log (t₀ / (2 * Real.pi)) ^ 2
          - 2 * C1lo 12 * (y + 1) + 2 * C2hi
          + (2 * (y + 1) * ((t₀ / T) ^ 2 / 2 + (1 - T / T)) * 14 + Real.pi ^ 2 * 0 * y))
        + (2 / (5 * t₀) + 2 * Real.pi * Real.log (T / t₀) / (5 * T))
        + (2 / t₀ + 2 * Real.pi / T) * (2 * Real.log t₀ / 5 + 4) := by
    have hfin := CH2Section7Z.finite_zeros_Ioc (a := t₀) (b := T) ht0p.le
    have hev : ∀ᶠ t₁ in nhdsWithin T (Set.Iio T),
        2 * Real.pi / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ phiW T ρ.im)
        ≤ (1 / (2 * Real.pi)) * (y ^ 2 - Real.log (t₀ / (2 * Real.pi)) ^ 2
            - 2 * C1lo 12 * (y + 1) + 2 * C2hi
            + (2 * (y + 1) * ((t₀ / T) ^ 2 / 2 + (1 - t₁ / T)) * 14 + Real.pi ^ 2 * gT (t₁ / T) * y))
          + (2 / (5 * t₀) + 2 * Real.pi * Real.log (T / t₀) / (5 * T))
          + (2 / t₀ + 2 * Real.pi / T) * (2 * Real.log t₀ / 5 + 4) := by
      have hall : ∀ᶠ t₁ in nhdsWithin T (Set.Iio T),
          ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc t₀ T), ρ.im < t₁ := by
        refine (Filter.eventually_all_finite hfin).mpr fun ρ hρ ↦ ?_
        obtain ⟨-, ⟨-, h1⟩, hz⟩ := hρ
        have hlt : ρ.im < T := lt_of_le_of_ne h1 (hTfree ρ hz)
        exact Ioo_mem_nhdsLT hlt |> fun h ↦ Filter.mem_of_superset h fun t ht ↦ ht.1
      filter_upwards [hall, Ioo_mem_nhdsLT (by linarith : t₀ < T)] with t₁ ht₁ ht₁'
      have hset : IEANTN.zetaZeroesIn Set.univ (Set.Ioc t₀ T)
          = IEANTN.zetaZeroesIn Set.univ (Set.Ioc t₀ t₁) := by
        ext ρ
        constructor
        · intro hρ
          exact ⟨hρ.1, ⟨hρ.2.1.1, (ht₁ ρ hρ).le⟩, hρ.2.2⟩
        · rintro ⟨h0, ⟨h1, h2⟩, h3⟩
          exact ⟨h0, ⟨h1, h2.trans ht₁'.2.le⟩, h3⟩
      have hsum_eq : IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ phiW T ρ.im)
          = IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ t₁) (fun ρ ↦ phiW T ρ.im) := by
        unfold IEANTN.zetaZeroesSum; rw [hset]
      rw [hsum_eq]
      exact sum_phiW_le hcs hrvm ht0 h2 ht₁'.1.le ht₁'.2
    refine ge_of_tendsto ?_ hev
    have hg := tendsto_gT_one hcs hT
    have hlin : Filter.Tendsto (fun t₁ : ℝ ↦ 1 - t₁ / T) (nhdsWithin T (Set.Iio T)) (nhds (1 - T / T)) :=
      ((continuous_const.sub (continuous_id.div_const T)).tendsto T).mono_left nhdsWithin_le_nhds
    refine Filter.Tendsto.add (Filter.Tendsto.add (Filter.Tendsto.const_mul _ ?_) tendsto_const_nhds)
      tendsto_const_nhds
    refine Filter.Tendsto.add tendsto_const_nhds (Filter.Tendsto.add ?_ ?_)
    · exact ((tendsto_const_nhds.add hlin).const_mul _).mul_const _
    · exact ((hg.const_mul _).mul_const _)
  -- assemble
  have e0 : (1 - T / T) = 0 := by rw [div_self hT.ne']; ring
  rw [e0] at hphi
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hs0 : 0 ≤ |σ - 1 / 2| := abs_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hterm hK
  have h3 : 2 * Real.pi / T * (|σ - 1 / 2| * T / Real.pi
      * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ 1 / ρ.im ^ 2))
      ≤ 2 * |σ - 1 / 2| * (Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀)
          + (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2) := by
    have e : 2 * Real.pi / T * (|σ - 1 / 2| * T / Real.pi
        * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ 1 / ρ.im ^ 2))
        = 2 * |σ - 1 / 2| * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ 1 / ρ.im ^ 2) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hinvsq (by positivity)
  have h4 : 2 * Real.pi / T * (c / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun _ ↦ (1:ℝ)))
      ≤ c * y / T := by
    calc _ ≤ 2 * Real.pi / T * (c / T * (T / (2 * Real.pi) * y)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = c * y / T := by field_simp
  have e1 : 2 * Real.pi / T * (IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ phiW T ρ.im)
      + (|σ - 1 / 2| * T / Real.pi * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ 1 / ρ.im ^ 2)
        + c / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun _ ↦ (1:ℝ))))
      = 2 * Real.pi / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ phiW T ρ.im)
        + 2 * Real.pi / T * (|σ - 1 / 2| * T / Real.pi
          * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun ρ ↦ 1 / ρ.im ^ 2))
        + 2 * Real.pi / T * (c / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc t₀ T) (fun _ ↦ (1:ℝ))) := by
    ring
  rw [e1] at h1
  have e2 : 2 * (y + 1) * ((t₀ / T) ^ 2 / 2 + 0) * 14 + Real.pi ^ 2 * 0 * y
      = 14 * (y + 1) * (t₀ / T) ^ 2 := by ring
  rw [e2] at hphi
  linarith [h1, hphi, h3, h4]

end CH2Section7A
