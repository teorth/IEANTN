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

end CH2Section7A
