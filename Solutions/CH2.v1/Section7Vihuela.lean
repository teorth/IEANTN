/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section7Adar
import IEANTN.Nodes.PlattZeroSum.v1.Conclusions

/-!
# Section 7: `lem:salmon` and `prop:vihuela`

`lem:salmon` handles the zeros with `0 < γ ≤ t₀` by the classical weight (`cor:thonny`, eq. `demoscen`);
`prop:vihuela` splits at `t₀ = 2·10⁴`, uses `PlattZeroSum.v1` below and `lem:adar` above, and concludes

`(2π/T) ∑_{0 < γ ≤ T} |ω⁺_{T,σ}(ρ) + ξ θ_{T,1}(ρ) i| ≤ (1/2π) log²(T/2π) - (1.001/6π) log(T/2π)`

for `T ≥ 10⁷`, `0 ≤ σ < 1`, `|ξ| ≤ 1`, RH up to `T` and no zero ordinate at `T`.

The paper states `1.01/6π` for `|σ - 1/2| ≤ 100`; Section 9 needs only `σ ∈ [0, 1]` and uses the
extra `0.01/6π` for terms of size `10⁻⁴`, so `1.001` is what is proved. Its margin at `T = 10⁷` is
about `0.017`, growing with `T`.
-/

open Real MeasureTheory Set

namespace CH2Section7A

open CH2Section7 CH2Section7T

/-! ### Numbers -/

theorem exp_small_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 * 4 / 18 := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  norm_num at h ⊢
  linarith

theorem exp_small_ge {x : ℝ} (h0 : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg h0 5
  simpa [Finset.sum_range_succ, Nat.factorial] using h

theorem exp_nat_bounds (n : ℕ) :
    (2.7182818283 : ℝ) ^ n ≤ Real.exp n ∧ Real.exp n ≤ (2.7182818286 : ℝ) ^ n := by
  rw [← Real.exp_one_pow]
  exact ⟨pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n,
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n⟩

theorem log_t0_bounds : (8.064 : ℝ) ≤ Real.log (20000 / (2 * Real.pi)) ∧
    Real.log (20000 / (2 * Real.pi)) ≤ 8.07 := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hpos : (0 : ℝ) < 20000 / (2 * Real.pi) := by positivity
  constructor
  · rw [Real.le_log_iff_exp_le hpos, show (8.064 : ℝ) = (8 : ℕ) + 0.064 by norm_num, Real.exp_add]
    have h8 := (exp_nat_bounds 8).2
    have hs := exp_small_le (x := 0.064) (by norm_num) (by norm_num)
    rw [le_div_iff₀ (by positivity)]
    have h8' : Real.exp ((8 : ℕ) : ℝ) ≤ 2980.96 := by norm_num at h8 ⊢; linarith
    have hs' : Real.exp 0.064 ≤ 1.06611 := by norm_num at hs ⊢; linarith
    have : Real.exp ((8 : ℕ) : ℝ) * Real.exp 0.064 ≤ 2980.96 * 1.06611 :=
      mul_le_mul h8' hs' (Real.exp_pos _).le (by norm_num)
    nlinarith
  · rw [Real.log_le_iff_le_exp hpos, show (8.07 : ℝ) = (8 : ℕ) + 0.07 by norm_num, Real.exp_add]
    have h8 := (exp_nat_bounds 8).1
    have hs := exp_small_ge (x := 0.07) (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    have h8' : (2980.95 : ℝ) ≤ Real.exp ((8 : ℕ) : ℝ) := by norm_num at h8 ⊢; linarith
    have hs' : (1.0725 : ℝ) ≤ Real.exp 0.07 := by norm_num at hs ⊢; linarith
    have : (2980.95 : ℝ) * 1.0725 ≤ Real.exp ((8 : ℕ) : ℝ) * Real.exp 0.07 :=
      mul_le_mul h8' hs' (by norm_num) (Real.exp_pos _).le
    nlinarith

theorem log_T0_le : Real.log ((10 : ℝ) ^ 7 / (2 * Real.pi)) ≤ 14.3 := by
  have hπ1 := Real.pi_gt_d6
  have hpos : (0 : ℝ) < (10 : ℝ) ^ 7 / (2 * Real.pi) := by positivity
  rw [Real.log_le_iff_le_exp hpos, show (14.3 : ℝ) = (14 : ℕ) + 0.3 by norm_num, Real.exp_add]
  have h14 := (exp_nat_bounds 14).1
  have hs := exp_small_ge (x := 0.3) (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  have h14' : (1202604 : ℝ) ≤ Real.exp ((14 : ℕ) : ℝ) := by norm_num at h14 ⊢; linarith
  have hs' : (1.3498 : ℝ) ≤ Real.exp 0.3 := by norm_num at hs ⊢; linarith
  have : (1202604 : ℝ) * 1.3498 ≤ Real.exp ((14 : ℕ) : ℝ) * Real.exp 0.3 :=
    mul_le_mul h14' hs' (by norm_num) (Real.exp_pos _).le
  nlinarith

theorem log_20000_le : Real.log 20000 ≤ 9.92 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (9.92 : ℝ) = (9 : ℕ) + 0.92 by norm_num, Real.exp_add]
  have h9 := (exp_nat_bounds 9).1
  have hs := exp_small_ge (x := 0.92) (by norm_num)
  have h9' : (8103 : ℝ) ≤ Real.exp ((9 : ℕ) : ℝ) := by norm_num at h9 ⊢; linarith
  have hs' : (2.5 : ℝ) ≤ Real.exp 0.92 := by norm_num at hs ⊢; linarith
  have : (8103 : ℝ) * 2.5 ≤ Real.exp ((9 : ℕ) : ℝ) * Real.exp 0.92 :=
    mul_le_mul h9' hs' (by norm_num) (Real.exp_pos _).le
  linarith

theorem log_500_le : Real.log 500 ≤ 6.22 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (6.22 : ℝ) = (6 : ℕ) + 0.22 by norm_num, Real.exp_add]
  have h6 := (exp_nat_bounds 6).1
  have hs := exp_small_ge (x := 0.22) (by norm_num)
  have h6' : (403.4 : ℝ) ≤ Real.exp ((6 : ℕ) : ℝ) := by norm_num at h6 ⊢; linarith
  have hs' : (1.246 : ℝ) ≤ Real.exp 0.22 := by norm_num at hs ⊢; linarith
  have : (403.4 : ℝ) * 1.246 ≤ Real.exp ((6 : ℕ) : ℝ) * Real.exp 0.22 :=
    mul_le_mul h6' hs' (by norm_num) (Real.exp_pos _).le
  linarith

/-! ### Splitting a zero sum -/

theorem zsum_split {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (f : ℂ → ℝ) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 b) f
      = IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 a) f + IEANTN.zetaZeroesSum Set.univ (Set.Ioc a b) f := by
  have hfb := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := b) le_rfl
  have hfa := CH2Section7Z.finite_zeros_Ioc (a := 0) (b := a) le_rfl
  have hfab := CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfb, CH2Section7Z.zetaZeroesSum_eq_sum hfa,
    CH2Section7Z.zetaZeroesSum_eq_sum hfab,
    ← Finset.sum_filter_add_sum_filter_not hfb.toFinset (fun ρ ↦ ρ.im ≤ a)]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨h1, ⟨h2, -⟩, h3⟩, h4⟩; exact ⟨h1, ⟨h2, h4⟩, h3⟩
    · rintro ⟨h1, ⟨h2, h4⟩, h3⟩; exact ⟨⟨h1, ⟨h2, h4.trans hab⟩, h3⟩, h4⟩
  · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext ρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, not_le]
    constructor
    · rintro ⟨⟨h1, ⟨-, h2⟩, h3⟩, h4⟩; exact ⟨h1, ⟨h4, h2⟩, h3⟩
    · rintro ⟨h1, ⟨h4, h2⟩, h3⟩; exact ⟨⟨h1, ⟨lt_of_le_of_lt ha h4, h2⟩, h3⟩, h4⟩

/-! ### `lem:salmon` -/

theorem salmon (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    {T σ ξ t₀ : ℝ} (hRH : IEANTN.RiemannHypothesisUpTo T) (ht0 : 12 ≤ t₀) (h2 : 2 * t₀ ≤ T)
    (hσ1 : σ ≠ 1) (hσT : |σ - 1 / 2| ≤ T / 2) (hξ : |ξ| ≤ 1) :
    2 * Real.pi / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀)
        (fun ρ ↦ ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ‖)
      ≤ 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun ρ ↦ 1 / ρ.im)
        + t₀ / T * (1 + (2.78 * |σ - 1 / 2| + 1) / T) * Real.log (t₀ / (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have hT : 0 < T := by linarith
  set c := 1 + (2.78 * |σ - 1 / 2| + 1) / T with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hterm := zsum_mono le_rfl (a := 0) (b := t₀)
    (f := fun ρ ↦ ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ‖)
    (g := fun ρ ↦ (T / Real.pi) * (1 / ρ.im) + c * 1)
    (fun ρ hρ ↦ by
      obtain ⟨-, ⟨h0, h1⟩, hz⟩ := hρ
      have hre := re_eq_half_of_RH hRH hz h0 (by linarith)
      have hρ : ρ = 1 / 2 + (ρ.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
      have hd := CH2Section6.thonny_demoscen hcs hT hσ1 hσT hξ h0 (by linarith)
      rw [← hρ] at hd
      have hsσ : ρ - σ ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp at this; linarith
      have hnorm : ‖Complex.I * T / ((ρ - σ) * Real.pi)‖ ≤ T / Real.pi * (1 / ρ.im) := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hT, abs_of_pos hπ, one_mul]
        have hge : ρ.im ≤ ‖ρ - σ‖ := by
          have := Complex.abs_im_le_norm (ρ - σ)
          simp at this
          rw [abs_of_pos h0] at this
          exact this
        rw [div_le_iff₀ (by positivity)]
        calc T = T / Real.pi * (1 / ρ.im) * (ρ.im * Real.pi) := by field_simp
          _ ≤ T / Real.pi * (1 / ρ.im) * (‖ρ - σ‖ * Real.pi) := by gcongr
      calc _ ≤ ‖Complex.I * T / ((ρ - σ) * Real.pi)‖
            + ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ
              - Complex.I * T / ((ρ - σ) * Real.pi)‖ := norm_le_insert' _ _
        _ ≤ _ := by rw [hc]; linarith)
  rw [zsum_add le_rfl, zsum_const_mul le_rfl, zsum_const_mul le_rfl] at hterm
  have hcount : IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun _ ↦ (1:ℝ))
      ≤ t₀ / (2 * Real.pi) * Real.log (t₀ / (2 * Real.pi)) :=
    (zsum_one_le le_rfl).trans (CH2Section7Z.zetaN_le_brut hrvm hsmall ht0)
  have hK : 0 ≤ 2 * Real.pi / T := by positivity
  have h1 := mul_le_mul_of_nonneg_left hterm hK
  have h3 : 2 * Real.pi / T * (c * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun _ ↦ (1:ℝ)))
      ≤ t₀ / T * c * Real.log (t₀ / (2 * Real.pi)) := by
    calc _ ≤ 2 * Real.pi / T * (c * (t₀ / (2 * Real.pi) * Real.log (t₀ / (2 * Real.pi)))) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact mul_le_mul_of_nonneg_left hcount hc0
      _ = _ := by field_simp
  have e : 2 * Real.pi / T * (T / Real.pi * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun ρ ↦ 1 / ρ.im)
      + c * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun _ ↦ (1:ℝ)))
      = 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun ρ ↦ 1 / ρ.im)
        + 2 * Real.pi / T * (c * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun _ ↦ (1:ℝ))) := by
    field_simp
  rw [e] at h1
  linarith

/-! ### `prop:vihuela` -/

set_option maxHeartbeats 2000000 in
theorem vihuela (hcs : CotangentSeries.v1.cot_series_zeta_values)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)
    {T σ ξ : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hRH : IEANTN.RiemannHypothesisUpTo T)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → z.im ≠ T) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hξ : |ξ| ≤ 1) :
    2 * Real.pi / T * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 T)
        (fun ρ ↦ ‖CH2Section6.omegaPlus T σ ρ + (ξ : ℂ) * Complex.I * CH2Section6.thetaTS T 1 ρ‖)
      ≤ 1 / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) ^ 2
        - 1.001 / (6 * Real.pi) * Real.log (T / (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hT0 : (0 : ℝ) < T := by linarith [show (0:ℝ) < 10 ^ 7 by norm_num]
  have hs : |σ - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hσT : |σ - 1 / 2| ≤ T / 2 := by linarith
  set t₀ : ℝ := 20000 with ht₀
  rw [zsum_split (a := t₀) (by norm_num) (by rw [ht₀]; linarith), mul_add]
  have hsal := salmon hcs hrvm hsmall hRH (t₀ := t₀) (by norm_num) (by rw [ht₀]; linarith)
    hσ1.ne hσT hξ
  have had := adar hcs hrvm hsmall hRH hTfree (t₀ := t₀) (by norm_num) (by rw [ht₀]; linarith)
    hσ1.ne hσT hξ
  have hP : 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 t₀) (fun ρ ↦ 1 / ρ.im) ≤ 10.3194 := by
    have := hplatt; unfold PlattZeroSum.v1.inv_ordinate_sum_le at this; exact this
  -- the numbers
  obtain ⟨hL0lo, hL0hi⟩ := log_t0_bounds
  rw [← ht₀] at hL0lo hL0hi
  have hC1 := C1lo_twelve
  have hC2 := C2hi_le
  set y := Real.log (T / (2 * Real.pi)) with hy
  set L0 := Real.log (t₀ / (2 * Real.pi)) with hL0
  -- `y ≤ log(10⁷/2π) + T/10⁷ - 1`
  have hylog : y ≤ 14.3 + T / 10 ^ 7 - 1 := by
    have h1 : y = Real.log ((10 : ℝ) ^ 7 / (2 * Real.pi)) + Real.log (T / 10 ^ 7) := by
      rw [hy, ← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h2 := Real.log_le_sub_one_of_pos (show 0 < T / 10 ^ 7 by positivity)
    linarith [log_T0_le]
  have hy0 : 0 ≤ y := by
    rw [hy]; apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; nlinarith
  have hu : 1 / T ≤ 1e-7 := by rw [div_le_iff₀ hT0]; norm_num; linarith
  have hu0 : 0 < 1 / T := by positivity
  -- each error term
  have hlogTt0 : Real.log (T / t₀) ≤ T / 10 ^ 7 + 5.22 := by
    have h1 : Real.log (T / t₀) = Real.log (T / 10 ^ 7) + Real.log 500 := by
      rw [← Real.log_mul (by positivity) (by norm_num)]; congr 1; rw [ht₀]; field_simp; norm_num
    have h2 := Real.log_le_sub_one_of_pos (show 0 < T / 10 ^ 7 by positivity)
    linarith [log_500_le]
  have hlog20000 := log_20000_le
  rw [← ht₀] at hlog20000
  have hLe : Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) ≤ 9.07 := by
    rw [mul_div_assoc, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    linarith
  have hLe0 : 0 ≤ Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; nlinarith [Real.exp_one_gt_d9]
  have hlog0 : 0 ≤ Real.log t₀ := Real.log_nonneg (by norm_num)
  have hL0nn : 0 ≤ L0 := by linarith
  have hc' : 2.78 * |σ - 1 / 2| + 1 ≤ 2.39 := by linarith
  have hc'0 : 0 ≤ 2.78 * |σ - 1 / 2| + 1 := by positivity
  -- salmon's error
  have hE1 : t₀ / T * (1 + (2.78 * |σ - 1 / 2| + 1) / T) * L0 ≤ 0.016141 := by
    have ha : t₀ / T ≤ 0.002 := by rw [ht₀, div_le_iff₀ hT0]; linarith
    have hb : (2.78 * |σ - 1 / 2| + 1) / T ≤ 2.39e-7 := by
      rw [div_le_iff₀ hT0]; nlinarith
    have hb0 : 0 ≤ (2.78 * |σ - 1 / 2| + 1) / T := by positivity
    have : t₀ / T * (1 + (2.78 * |σ - 1 / 2| + 1) / T) ≤ 0.002 * (1 + 2.39e-7) := by
      apply mul_le_mul ha (by linarith) (by positivity) (by norm_num)
    calc _ ≤ 0.002 * (1 + 2.39e-7) * 8.07 := mul_le_mul this hL0hi hL0nn (by norm_num)
      _ ≤ 0.016141 := by norm_num
  have hE2 : 14 * (y + 1) * (t₀ / T) ^ 2 ≤ 0.001 := by
    have h1 : (y + 1) * (1 / T) ≤ 15.3e-7 := by
      have : (y + 1) * (1 / T) ≤ (14.3 + T / 10 ^ 7) * (1 / T) :=
        mul_le_mul_of_nonneg_right (by linarith) hu0.le
      have e : (14.3 + T / 10 ^ 7) * (1 / T) = 14.3 * (1 / T) + 1e-7 := by field_simp; ring
      nlinarith
    have e : 14 * (y + 1) * (t₀ / T) ^ 2 = 14 * ((y + 1) * (1 / T)) * (t₀ ^ 2 * (1 / T)) := by
      field_simp
    rw [e]
    have h2 : t₀ ^ 2 * (1 / T) ≤ 40 := by rw [ht₀]; nlinarith
    have h3 : 0 ≤ (y + 1) * (1 / T) := by positivity
    calc 14 * ((y + 1) * (1 / T)) * (t₀ ^ 2 * (1 / T)) ≤ 14 * 15.3e-7 * 40 := by gcongr
      _ ≤ 0.001 := by norm_num
  have hE3 : 2 / (5 * t₀) + 2 * Real.pi * Real.log (T / t₀) / (5 * T) ≤ 0.000031 := by
    have h1 : Real.log (T / t₀) * (1 / T) ≤ 1e-7 + 5.22e-7 := by
      have hlp : 0 ≤ Real.log (T / t₀) := Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
      have : Real.log (T / t₀) * (1 / T) ≤ (T / 10 ^ 7 + 5.22) * (1 / T) :=
        mul_le_mul_of_nonneg_right hlogTt0 hu0.le
      have e : (T / 10 ^ 7 + 5.22) * (1 / T) = 1e-7 + 5.22 * (1 / T) := by field_simp; ring
      nlinarith
    have e : 2 * Real.pi * Real.log (T / t₀) / (5 * T) = 2 * Real.pi / 5 * (Real.log (T / t₀) * (1 / T)) := by
      field_simp
    rw [e, ht₀]
    have hl0 : 0 ≤ Real.log (T / 20000) * (1 / T) := by
      apply mul_nonneg _ hu0.le; apply Real.log_nonneg; rw [le_div_iff₀ (by norm_num)]; linarith
    rw [ht₀] at h1
    nlinarith
  have hE4 : (2 / t₀ + 2 * Real.pi / T) * (2 * Real.log t₀ / 5 + 4) ≤ 0.000802 := by
    have h1 : 2 * Real.pi / T ≤ 6.3e-7 := by
      rw [div_le_iff₀ hT0]; nlinarith
    have h2 : 2 * Real.log t₀ / 5 + 4 ≤ 7.968 := by linarith
    have h3 : 2 / t₀ + 2 * Real.pi / T ≤ 0.0001 + 6.3e-7 := by rw [ht₀]; norm_num; linarith
    calc _ ≤ (0.0001 + 6.3e-7) * 7.968 := mul_le_mul h3 h2 (by positivity) (by norm_num)
      _ ≤ 0.000802 := by norm_num
  have hE5 : 2 * |σ - 1 / 2| * (Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀)
      + (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2) ≤ 0.0000723 := by
    have h1 : Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀) ≤ 9.07 / (2 * 3.141592 * 20000) := by
      rw [ht₀]; rw [ht₀] at hLe hLe0
      apply div_le_div₀ (by norm_num) hLe (by positivity); nlinarith
    have h2 : (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2 ≤ 8.07 / 20000 ^ 2 := by
      rw [ht₀]; rw [ht₀] at hlog20000
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have h3 : 2 * |σ - 1 / 2| ≤ 1 := by linarith
    have h4 : 0 ≤ Real.log (Real.exp 1 * t₀ / (2 * Real.pi)) / (2 * Real.pi * t₀)
        + (2 * Real.log t₀ / 5 + 41 / 10) / t₀ ^ 2 := by positivity
    calc _ ≤ 1 * (9.07 / (2 * 3.141592 * 20000) + 8.07 / 20000 ^ 2) :=
          mul_le_mul h3 (by linarith) h4 (by norm_num)
      _ ≤ 0.0000723 := by norm_num
  have hE6 : (2.78 * |σ - 1 / 2| + 1) * y / T ≤ 0.0000037 := by
    have h1 : y * (1 / T) ≤ 14.3e-7 := by
      have : y * (1 / T) ≤ (13.3 + T / 10 ^ 7) * (1 / T) :=
        mul_le_mul_of_nonneg_right (by linarith) hu0.le
      have e : (13.3 + T / 10 ^ 7) * (1 / T) = 13.3 * (1 / T) + 1e-7 := by field_simp; ring
      nlinarith
    have e : (2.78 * |σ - 1 / 2| + 1) * y / T = (2.78 * |σ - 1 / 2| + 1) * (y * (1 / T)) := by
      field_simp
    rw [e]
    have : 0 ≤ y * (1 / T) := by positivity
    calc _ ≤ 2.39 * 14.3e-7 := mul_le_mul hc' h1 this (by norm_num)
      _ ≤ 0.0000037 := by norm_num
  -- the main terms
  have hmain : (1 / (2 * Real.pi)) * (y ^ 2 - L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi
      + 14 * (y + 1) * (t₀ / T) ^ 2) + 10.3194
      ≤ 1 / (2 * Real.pi) * y ^ 2 - 1.001 / (6 * Real.pi) * y
        - (0.016141 + 0.000031 + 0.000802 + 0.0000723 + 0.0000037) := by
    have hL0sq : 65.028 ≤ L0 ^ 2 := by nlinarith
    have hkey : (1 / (2 * Real.pi)) * (- L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi
        + 14 * (y + 1) * (t₀ / T) ^ 2) + 10.3194
        ≤ - 1.001 / (6 * Real.pi) * y - 0.01705 := by
      rw [show - 1.001 / (6 * Real.pi) * y = (1 / (2 * Real.pi)) * (-(1.001 / 3) * y) by
        field_simp; ring]
      have hA : - L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi + 14 * (y + 1) * (t₀ / T) ^ 2
          ≤ -(1.001 / 3) * y - 2 * Real.pi * (10.3194 + 0.01705) := by
        have hy' : 0 ≤ (2 * C1lo 12 - 1.001 / 3) * y := by
          apply mul_nonneg _ hy0; linarith
        nlinarith
      have := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi))
      have e : 1 / (2 * Real.pi) * (-(1.001 / 3) * y - 2 * Real.pi * (10.3194 + 0.01705))
          = 1 / (2 * Real.pi) * (-(1.001 / 3) * y) - (10.3194 + 0.01705) := by
        field_simp
      linarith
    have e : (1 / (2 * Real.pi)) * (y ^ 2 - L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi
        + 14 * (y + 1) * (t₀ / T) ^ 2)
        = 1 / (2 * Real.pi) * y ^ 2 + (1 / (2 * Real.pi)) * (- L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi
          + 14 * (y + 1) * (t₀ / T) ^ 2) := by ring
    rw [e]
    have : 0.01705 ≥ (0.016141 + 0.000031 + 0.000802 + 0.0000723 + 0.0000037 : ℝ) := by norm_num
    have hneg : -1.001 / (6 * Real.pi) * y = -(1.001 / (6 * Real.pi) * y) := by ring
    rw [hneg] at hkey
    set Z := 1.001 / (6 * Real.pi) * y
    set X := 1 / (2 * Real.pi) * (-L0 ^ 2 - 2 * C1lo 12 * (y + 1) + 2 * C2hi + 14 * (y + 1) * (t₀ / T) ^ 2)
    linarith
  linarith [hsal, had, hP, hE1, hE2, hE3, hE4, hE5, hE6, hmain]

end CH2Section7A
