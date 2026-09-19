/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section81Saghar
import Section6Hyp

/-!
# Section 8.1: `prop:adoro`, `cor:adiaro` and the integral half of `lem:hardin`

For `T ≥ 10^7`, `RH` up to `T` and `x ≥ max(T, 10^9)`, there is `t ∈ [T - 1/2, T]` with no zero
ordinate `±t` and

`∫_0^∞ u |F(1 - u + it)| x^{-u} du ≤ 12.5 R/L² + 62 R/L³ + 2 (R + 10)²/√x`, `R = log T`, `L = log x`.

The paper chooses `t` by a continuous pigeonhole over `[T_∘ - α, T_∘ + α]`, which keeps the
`1/√x` coefficient at `O(log T log log T)`. That coefficient has enormous slack in `prop:sagaro`,
so here `t` is chosen by a discrete pigeonhole instead: of `n + 1` equally spaced points in
`[T - 1/2, T - 1/4]`, with `n` the number of distinct zero ordinates in `(T - 3/4, T]`, one is at
distance at least `1/(8(n+1))` from all of them. This costs a `(log T)²` in the `1/√x` term only.
-/

open Complex Filter Topology Set MeasureTheory

namespace CH2Section81

/-- **Discrete pigeonhole.** Of the `|G| + 1` points `a + jh`, one is at distance `≥ h/2` from `G`. -/
theorem exists_far_point (G : Finset ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ j : ℕ, j ≤ G.card ∧ ∀ γ ∈ G, h / 2 ≤ |a + j * h - γ| := by
  classical
  by_contra hcon
  push_neg at hcon
  choose! f hfG hfd using hcon
  obtain ⟨i, hi, j, hj, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (G.card + 1)) (t := G) (f := f) (by simp)
    (fun j hj ↦ hfG j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
  have h1 := hfd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have h2 := hfd j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [hfij] at h1
  have h3 := abs_sub_le (a + i * h) (f j) (a + j * h)
  rw [abs_sub_comm (f j)] at h3
  have e : a + i * h - (a + j * h) = ((i : ℝ) - j) * h := by ring
  rw [e, abs_mul, abs_of_pos hh] at h3
  have hij' : (1 : ℝ) ≤ |(i : ℝ) - j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  nlinarith

/-! ### Zero counts -/

theorem log_ten_ge : (2.3 : ℝ) ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num), show (2.3 : ℝ) = (2 : ℕ) + 0.3 by norm_num,
    Real.exp_add]
  have h2 := (CH2Section7A.exp_nat_bounds 2).2
  have hs := CH2Section7A.exp_small_le (x := 0.3) (by norm_num) (by norm_num)
  have h0 : 0 ≤ Real.exp 0.3 := (Real.exp_pos _).le
  calc Real.exp ((2 : ℕ) : ℝ) * Real.exp 0.3 ≤ (2.7182818286 : ℝ) ^ 2 * Real.exp 0.3 :=
        mul_le_mul_of_nonneg_right h2 h0
    _ ≤ (2.7182818286 : ℝ) ^ 2 * (1 + 0.3 + 0.3 ^ 2 / 2 + 0.3 ^ 3 * 4 / 18) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 10 := by norm_num

theorem log_two_pi_ge : (1.8 : ℝ) ≤ Real.log (2 * Real.pi) := by
  have hπ := Real.pi_gt_d2
  rw [Real.le_log_iff_exp_le (by positivity), show (1.8 : ℝ) = (1 : ℕ) + 0.8 by norm_num,
    Real.exp_add]
  have h1 := (CH2Section7A.exp_nat_bounds 1).2
  have hs := CH2Section7A.exp_small_le (x := 0.8) (by norm_num) (by norm_num)
  have h0 : 0 ≤ Real.exp 0.8 := (Real.exp_pos _).le
  calc Real.exp ((1 : ℕ) : ℝ) * Real.exp 0.8 ≤ (2.7182818286 : ℝ) ^ 1 * Real.exp 0.8 :=
        mul_le_mul_of_nonneg_right h1 h0
    _ ≤ (2.7182818286 : ℝ) ^ 1 * (1 + 0.8 + 0.8 ^ 2 / 2 + 0.8 ^ 3 * 4 / 18) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 2 * 3.14 := by norm_num
    _ ≤ 2 * Real.pi := by linarith

theorem exp_three_halves_le : Real.exp 1.5 ≤ 4.5 := by
  rw [show (1.5 : ℝ) = (1 : ℕ) + 0.5 by norm_num, Real.exp_add]
  have h1 := (CH2Section7A.exp_nat_bounds 1).2
  have hs := CH2Section7A.exp_small_le (x := 0.5) (by norm_num) (by norm_num)
  have h0 : 0 ≤ Real.exp 0.5 := (Real.exp_pos _).le
  calc Real.exp ((1 : ℕ) : ℝ) * Real.exp 0.5 ≤ (2.7182818286 : ℝ) ^ 1 * Real.exp 0.5 :=
        mul_le_mul_of_nonneg_right h1 h0
    _ ≤ (2.7182818286 : ℝ) ^ 1 * (1 + 0.5 + 0.5 ^ 2 / 2 + 0.5 ^ 3 * 4 / 18) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 4.5 := by norm_num

theorem window_count_le (hrvm : ZeroCount.v1.rvm_error_bound) {T : ℝ} (hT : 1000 ≤ T) :
    IEANTN.zetaZeroesSum Set.univ (Set.Ioc (T - 3 / 4) T) (fun _ ↦ (1 : ℝ))
      ≤ 0.52 * Real.log T + 4 := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_d2
  rw [zsum_one_Ioc (by linarith) (by linarith)]
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope ZeroCount.v1.rvmMain
    (fun u ↦ Real.log (u / (2 * Real.pi)) / (2 * Real.pi)) (by linarith : T - 3 / 4 < T)
    (fun u hu ↦ (hasDerivAt_rvmMain (by linarith [hu.1])).continuousAt.continuousWithinAt)
    (fun u hu ↦ hasDerivAt_rvmMain (by linarith [hu.1]))
  have hc0 : 0 < c := by linarith [hc.1]
  have hlogc : Real.log (c / (2 * Real.pi)) ≤ Real.log T :=
    Real.log_le_log (by positivity) ((div_le_self hc0.le (by linarith)).trans hc.2.le)
  have hlogc0 : 0 ≤ Real.log (c / (2 * Real.pi)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four, hc.1])
  have hM : ZeroCount.v1.rvmMain T - ZeroCount.v1.rvmMain (T - 3 / 4) ≤ 0.12 * Real.log T := by
    have e : ZeroCount.v1.rvmMain T - ZeroCount.v1.rvmMain (T - 3 / 4)
        = (3 / 4) * (Real.log (c / (2 * Real.pi)) / (2 * Real.pi)) := by
      rw [hceq]; field_simp; ring
    rw [e]
    have h1 : (3 / 4) * (Real.log (c / (2 * Real.pi)) / (2 * Real.pi))
        ≤ (3 / 4) * (Real.log T / (2 * Real.pi)) := by gcongr
    have h2 : (3 / 4) * (Real.log T / (2 * Real.pi)) ≤ 0.12 * Real.log T := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ T by linarith)]
    linarith
  have hQ1 := abs_le.mp (hrvm T (by linarith))
  have hQ2 := abs_le.mp (hrvm (T - 3 / 4) (by linarith))
  have hl : Real.log (T - 3 / 4) ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
  linarith

theorem inner_sum_le (hrvm : ZeroCount.v1.rvm_error_bound) {t T : ℝ} (ht : 1000 ≤ t)
    (htT : t + 1 / 4 ≤ T) :
    ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) ≤ 0.48 * Real.log T + 4.0001 := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_d2
  have hfin := CH2Section7Z.finite_zeros_Ioc (a := t - 1 / 4) (b := t + 1 / 4) (by linarith)
  have h := inner_count_le hrvm ht
  rw [CH2Section7Z.zetaZeroesSum_eq_sum hfin] at h
  simp only [one_mul] at h
  rw [innerZ_eq hfin]
  have hQ1 := abs_le.mp (hrvm (t + 1 / 4) (by linarith))
  have hQ2 := abs_le.mp (hrvm (t - 1 / 4) (by linarith))
  have hl1 : Real.log (t + 1 / 4) ≤ Real.log T := Real.log_le_log (by linarith) htT
  have hl2 : Real.log (t - 1 / 4) ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
  have hlt : Real.log (t / (2 * Real.pi)) ≤ Real.log T :=
    Real.log_le_log (by positivity) ((div_le_self (by linarith) (by linarith)).trans (by linarith))
  have hlt0 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four])
  have hq : 1 / (4 * Real.pi) ≤ 0.08 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have := mul_le_mul hq hlt hlt0 (by norm_num)
  linarith

/-! ### Numerics -/

theorem hardin_num1 {R L A N τ : ℝ} (hR : 16.1 ≤ R) (hL : 20.7 ≤ L) (hA : A ≤ 14.08 * R + 126)
    (hN : N ≤ 0.48 * R + 4.0001) (hN0 : 0 ≤ N) (hτ : 1000 ≤ τ) :
    A * (1 / (2 * L ^ 2) + 2 / L ^ 3) + 1 / (τ * L ^ 2) + N * (2 / L ^ 2 + 8 / L ^ 3 + 336 / L ^ 4)
      ≤ 12.5 * R / L ^ 2 + 62 * R / L ^ 3 := by
  have hL0 : 0 < L := by linarith
  set a : ℝ := 1 / L ^ 2 with ha
  set b : ℝ := 1 / L ^ 3 with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have e1 : 1 / (2 * L ^ 2) + 2 / L ^ 3 = a / 2 + 2 * b := by rw [ha, hb]; field_simp
  have e2 : 12.5 * R / L ^ 2 = 12.5 * R * a := by rw [ha]; field_simp
  have e3 : 62 * R / L ^ 3 = 62 * R * b := by rw [hb]; field_simp
  have h4 : 336 / L ^ 4 ≤ 16.24 * b := by
    rw [hb, show 336 / L ^ 4 = (336 / L) * (1 / L ^ 3) by field_simp]
    exact mul_le_mul_of_nonneg_right (by rw [div_le_iff₀ hL0]; linarith) hb0.le
  have h5 : 1 / (τ * L ^ 2) ≤ 0.001 * a := by
    rw [ha, show 1 / (τ * L ^ 2) = (1 / τ) * (1 / L ^ 2) by field_simp]
    exact mul_le_mul_of_nonneg_right (by rw [div_le_iff₀ (by linarith)]; linarith) (by positivity)
  have e8 : 2 / L ^ 2 + 8 / L ^ 3 = 2 * a + 8 * b := by rw [ha, hb]; field_simp
  rw [e1, e2, e3]
  have hA' : A * (a / 2 + 2 * b) ≤ (14.08 * R + 126) * (a / 2 + 2 * b) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  have hN' : N * (2 / L ^ 2 + 8 / L ^ 3 + 336 / L ^ 4) ≤ (0.48 * R + 4.0001) * (2 * a + 24.24 * b) := by
    rw [e8]
    calc N * (2 * a + 8 * b + 336 / L ^ 4) ≤ N * (2 * a + 24.24 * b) :=
          mul_le_mul_of_nonneg_left (by linarith) hN0
      _ ≤ _ := mul_le_mul_of_nonneg_right hN (by positivity)
  have p1 := mul_nonneg (show 0 ≤ 4.5 * R - 71.0012 by linarith) ha0.le
  have p2 := mul_nonneg (show 0 ≤ 22.2048 * R - 348.97 by linarith) hb0.le
  nlinarith

theorem hardin_num2 {R L N c τ x : ℝ} (hR : 16.1 ≤ R) (hL : 20.7 ≤ L) (hx : Real.exp L = x)
    (hN : N ≤ 0.48 * R + 4.0001) (hN0 : 0 ≤ N) (hc : c ≤ 0.52 * R + 4) (hc0 : 0 ≤ c)
    (hτ : τ ≤ x) (hτ0 : 0 ≤ τ) :
    N * (Real.exp (-(L / 2)) * (1 + Real.log (1 / (1 / (8 * (c + 1)))) / 2
        + (1 + 2 / L) / (2 * (1 / (8 * (c + 1))) * L)))
      + Real.exp (-(3 / 2 * (L - 1))) * (14 + 2 * τ)
      ≤ 2 * (R + 10) ^ 2 * Real.exp (-(L / 2)) := by
  have hL0 : 0 < L := by linarith
  have hE0 := Real.exp_pos (-(L / 2))
  have hx0 : 0 < x := hx ▸ Real.exp_pos L
  have hx1 : 20000 ≤ x := by
    rw [← hx]
    have h1 := quartic_le_exp hL0.le
    have h2 := pow_le_pow_left₀ (by norm_num) hL 4
    have h3 : (20.7 : ℝ) ^ 4 ≥ 20000 * 6.5536 := by norm_num
    linarith
  have hlog : Real.log (1 / (1 / (8 * (c + 1)))) ≤ 8 * (c + 1) - 1 := by
    rw [one_div_one_div]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hq : (1 + 2 / L) / (2 * (1 / (8 * (c + 1))) * L) ≤ 0.22 * (c + 1) := by
    rw [show (1 + 2 / L) / (2 * (1 / (8 * (c + 1))) * L) = (4 * (c + 1)) * ((1 + 2 / L) / L) by
      field_simp; ring]
    have h1 : (1 + 2 / L) / L ≤ 0.055 := by
      have h2 : 2 / L ≤ 0.1 := by rw [div_le_iff₀ hL0]; linarith
      rw [div_le_iff₀ hL0]; nlinarith
    calc 4 * (c + 1) * ((1 + 2 / L) / L) ≤ 4 * (c + 1) * 0.055 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 0.22 * (c + 1) := by ring
  have hbr : 1 + Real.log (1 / (1 / (8 * (c + 1)))) / 2
      + (1 + 2 / L) / (2 * (1 / (8 * (c + 1))) * L) ≤ 2.1944 * R + 21.6 := by linarith
  have hbr0 : 0 ≤ 2.1944 * R + 21.6 := by linarith
  have h1 : N * (Real.exp (-(L / 2)) * (1 + Real.log (1 / (1 / (8 * (c + 1)))) / 2
        + (1 + 2 / L) / (2 * (1 / (8 * (c + 1))) * L)))
      ≤ (0.48 * R + 4.0001) * (2.1944 * R + 21.6) * Real.exp (-(L / 2)) := by
    calc N * (Real.exp (-(L / 2)) * (1 + Real.log (1 / (1 / (8 * (c + 1)))) / 2
          + (1 + 2 / L) / (2 * (1 / (8 * (c + 1))) * L)))
        = Real.exp (-(L / 2)) * (N * (1 + Real.log (1 / (1 / (8 * (c + 1)))) / 2
          + (1 + 2 / L) / (2 * (1 / (8 * (c + 1))) * L))) := by ring
      _ ≤ Real.exp (-(L / 2)) * ((0.48 * R + 4.0001) * (2.1944 * R + 21.6)) := by
          refine mul_le_mul_of_nonneg_left ?_ hE0.le
          exact (mul_le_mul_of_nonneg_left hbr hN0).trans (mul_le_mul_of_nonneg_right hN hbr0)
      _ = _ := by ring
  have h2 : Real.exp (-(3 / 2 * (L - 1))) * (14 + 2 * τ) ≤ 9.01 * Real.exp (-(L / 2)) := by
    have e : Real.exp (-(3 / 2 * (L - 1))) = Real.exp (-(L / 2)) * (Real.exp 1.5 / x) := by
      rw [← hx, ← Real.exp_sub, ← Real.exp_add]; congr 1; ring
    rw [e, mul_assoc, mul_comm 9.01]
    refine mul_le_mul_of_nonneg_left ?_ hE0.le
    have h3 := exp_three_halves_le
    have h4 : Real.exp 1.5 / x * (14 + 2 * τ) = Real.exp 1.5 * ((14 + 2 * τ) / x) := by ring
    rw [h4]
    have h5 : (14 + 2 * τ) / x ≤ 2.002 := by rw [div_le_iff₀ hx0]; linarith
    calc Real.exp 1.5 * ((14 + 2 * τ) / x) ≤ 4.5 * 2.002 :=
          mul_le_mul h3 h5 (by positivity) (by norm_num)
      _ ≤ 9.01 := by norm_num
  have h3 : (0.48 * R + 4.0001) * (2.1944 * R + 21.6) + 9.01 ≤ 2 * (R + 10) ^ 2 := by nlinarith
  nlinarith

/-! ### Conjugation -/

open scoped ComplexConjugate in
theorem riemannZeta₀_conj (s : ℂ) : riemannZeta₀ (conj s) = conj (riemannZeta₀ s) := by
  unfold riemannZeta₀
  by_cases h : s = 1
  · subst h; simp
  · have h' : conj s ≠ 1 := fun h2 ↦ h (by simpa using congrArg conj h2)
    rw [if_neg h, if_neg h', riemannZeta_conj, map_sub, map_inv₀, map_sub, map_one]

open scoped ComplexConjugate in
theorem riemannZeta₁_conj (s : ℂ) : riemannZeta₁ (conj s) = conj (riemannZeta₁ s) := by
  unfold riemannZeta₁
  rw [riemannZeta₀_conj]
  simp

open scoped ComplexConjugate in
theorem F_conj (s : ℂ) : CH2ZetaInstance.F (conj s) = conj (CH2ZetaInstance.F s) := by
  have hfun : (fun z ↦ conj (riemannZeta₁ (conj z))) = riemannZeta₁ :=
    funext fun z ↦ by rw [riemannZeta₁_conj, Complex.conj_conj]
  have hd : deriv riemannZeta₁ (conj s) = conj (deriv riemannZeta₁ s) := by
    have := deriv_conj_conj' riemannZeta₁ s
    rwa [hfun] at this
  simp only [CH2ZetaInstance.F, logDeriv_apply, hd, riemannZeta₁_conj, map_neg, map_div₀]

theorem titchA_le {t T : ℝ} (ht : 1000 ≤ t) (htT : t ≤ T) :
    titchA t ≤ 14.08 * Real.log T + 126 := by
  have hπ := Real.pi_pos
  have hπ1 := Real.pi_gt_d4
  have hlt : Real.log t ≤ Real.log T := Real.log_le_log (by linarith) htT
  have hl0 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four])
  have hl1 : Real.log (t / (2 * Real.pi)) ≤ Real.log T - 1.8 := by
    rw [Real.log_div (by linarith) (by positivity)]
    linarith [log_two_pi_ge]
  have hq : 4 / Real.pi ≤ 1.2733 := by rw [div_le_iff₀ hπ]; linarith
  have h := mul_le_mul hq hl1 hl0 (by norm_num)
  unfold titchA
  linarith

/-! ### `lem:hardin`, integral part -/

/-- **`lem:hardin`, the integral part.** Under `RH` up to `T ≥ 10^7` and for `x ≥ max(T, 10^9)`,
there is `t ∈ [T - 1/2, T]`, not the absolute value of any zero ordinate, at which both
horizontal integrals of `shiftError` are at most `x (12.5 R/L² + 62 R/L³ + 2 (R + 10)²/√x)`. -/
theorem hardin (hH : ZetaHadamard.v1.logDeriv_partial_fractions)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hv : ZetaLogDerivValues.v1.logDeriv_three_halves)
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    {T x : ℝ} (hT : (10 : ℝ) ^ 7 ≤ T) (hx9 : (10 : ℝ) ^ 9 ≤ x) (hxT : T ≤ x)
    (hRH : IEANTN.RiemannHypothesisUpTo T) :
    ∃ t ∈ Set.Icc (T - 1 / 2) T, (∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ t) ∧
      (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u + t * I)‖ * x ^ (1 - u))
          ≤ x * (12.5 * Real.log T / Real.log x ^ 2 + 62 * Real.log T / Real.log x ^ 3
            + 2 * (Real.log T + 10) ^ 2 / Real.sqrt x) ∧
      (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (1 - u - t * I)‖ * x ^ (1 - u))
          ≤ x * (12.5 * Real.log T / Real.log x ^ 2 + 62 * Real.log T / Real.log x ^ 3
            + 2 * (Real.log T + 10) ^ 2 / Real.sqrt x) := by
  classical
  have hT0 : 0 < T := by linarith [show (0 : ℝ) < 10 ^ 7 by norm_num]
  have hx0 : 0 < x := by linarith
  have hT1000 : 1000 ≤ T := by linarith [show (1000 : ℝ) ≤ 10 ^ 7 by norm_num]
  set R := Real.log T with hR
  set L := Real.log x with hL
  have hR16 : 16.1 ≤ R := by
    have h1 : Real.log ((10 : ℝ) ^ 7) ≤ R := Real.log_le_log (by norm_num) hT
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [log_ten_ge]
  have hL20 : 20.7 ≤ L := by
    have h1 : Real.log ((10 : ℝ) ^ 9) ≤ L := Real.log_le_log (by norm_num) hx9
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [log_ten_ge]
  have hL7 : 7 ≤ L := by linarith
  have hexpL : Real.exp L = x := Real.exp_log hx0
  -- the zeros in `(T - 3/4, T]` and their ordinates
  have hZ := CH2Section7Z.finite_zeros_Ioc (a := T - 3 / 4) (b := T) (by linarith)
  set G : Finset ℝ := hZ.toFinset.image Complex.im with hG
  set n := G.card with hn
  have hncard : (n : ℝ) ≤ 0.52 * R + 4 := by
    have h1 : n ≤ hZ.toFinset.card := Finset.card_image_le
    have h2 : (hZ.toFinset.card : ℝ) ≤ ∑ ρ ∈ hZ.toFinset, (1 : ℝ) * (IEANTN.zetaOrder ρ : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine Finset.sum_le_sum fun ρ hρ ↦ ?_
      have hρ' := (Set.Finite.mem_toFinset hZ).mp hρ
      have hne : ρ ≠ 1 := fun h ↦ by
        have := hρ'.2.1.1; rw [h] at this; simp at this; linarith
      have := CH2Section6.one_le_zetaOrder hne hρ'.2.2
      rw [one_mul]; exact_mod_cast this
    have h3 := window_count_le hrvm hT1000
    rw [CH2Section7Z.zetaZeroesSum_eq_sum hZ] at h3
    have h1' : (n : ℝ) ≤ hZ.toFinset.card := by exact_mod_cast h1
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set h : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hh
  have hh0 : 0 < h := by positivity
  obtain ⟨j, hj, hjfar⟩ := exists_far_point G (T - 1 / 2) hh0
  set t : ℝ := T - 1 / 2 + j * h with ht
  have hjh0 : 0 ≤ (j : ℝ) * h := by positivity
  have hjh : (j : ℝ) * h ≤ 1 / 4 := by
    have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
    calc (j : ℝ) * h ≤ n * h := mul_le_mul_of_nonneg_right hj' hh0.le
      _ ≤ 1 / 4 := by rw [hh, ← mul_div_assoc, div_le_iff₀ (by positivity)]; linarith
  have ht1 : T - 1 / 2 ≤ t := by linarith
  have ht2 : t + 1 / 4 ≤ T := by linarith
  have ht1000 : 1000 ≤ t := by linarith
  set Δ : ℝ := 1 / (8 * ((n : ℝ) + 1)) with hΔ
  have hΔh : h / 2 = Δ := by rw [hh, hΔ]; field_simp; ring
  have hΔ0 : 0 < Δ := by positivity
  have hwin : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
      ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (T - 3 / 4) T) := fun ρ hρ ↦
    ⟨trivial, ⟨by linarith [hρ.2.1.1], by linarith [hρ.2.1.2]⟩, hρ.2.2⟩
  have hRHw : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)), ρ.re = 1 / 2 :=
    fun ρ hρ ↦ CH2Section7A.re_eq_half_of_RH hRH hρ.2.2 (by linarith [hρ.2.1.1])
      (by linarith [hρ.2.1.2])
  have hfar : ∀ ρ ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)),
      Δ ≤ |t - ρ.im| := by
    intro ρ hρ
    have hmem : ρ.im ∈ G := Finset.mem_image.mpr ⟨ρ, (Set.Finite.mem_toFinset hZ).mpr (hwin ρ hρ), rfl⟩
    rw [← hΔh]
    exact hjfar _ hmem
  -- the integral in exponential form
  have hS := saghar_integral hH hrvm hsmall hv hfe ht1000 hL7 hΔ0 hRHw hfar
  have hN := inner_sum_le hrvm ht1000 ht2
  have hN0 : 0 ≤ ∑ ρ ∈ innerZ t, (IEANTN.zetaOrder ρ : ℝ) := by
    have hfin := CH2Section7Z.finite_zeros_Ioc (a := t - 1 / 4) (b := t + 1 / 4) (by linarith)
    rw [innerZ_eq hfin]
    exact Finset.sum_nonneg fun ρ hρ ↦ CH2Section7Z.zetaOrder_nonneg_of_mem
      (fun x hx ↦ show (0 : ℝ) < x by linarith [hx.1]) ((Set.Finite.mem_toFinset hfin).mp hρ)
  have h1 := hardin_num1 hR16 hL20 (titchA_le ht1000 (by linarith)) hN hN0 ht1000
  have h2 := hardin_num2 hR16 hL20 hexpL hN hN0 (c := (n : ℝ)) hncard hn0 (by linarith : t ≤ x)
    (by linarith)
  rw [← hΔ] at h2
  have hsqrt : Real.exp (-(L / 2)) = 1 / Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ← hL, one_div, ← Real.exp_neg]
    ring_nf
  have hJ : ∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖
      * Real.exp (-(L * u))
      ≤ 12.5 * R / L ^ 2 + 62 * R / L ^ 3 + 2 * (R + 10) ^ 2 / Real.sqrt x := by
    have e : 2 * (R + 10) ^ 2 / Real.sqrt x = 2 * (R + 10) ^ 2 * Real.exp (-(L / 2)) := by
      rw [hsqrt]; ring
    rw [e]
    linarith
  -- back to `x^{1-u}`, both signs
  have hrw : ∀ z : ℝ → ℂ, (∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (z u)‖ * x ^ (1 - u))
      = x * ∫ u in Ioi (0 : ℝ), u * ‖CH2ZetaInstance.F (z u)‖ * Real.exp (-(L * u)) := by
    intro z
    rw [← integral_const_mul]
    congr 1
    funext u
    rw [Real.rpow_def_of_pos hx0, ← hL, show L * (1 - u) = L + -(L * u) by ring, Real.exp_add,
      hexpL]
    ring
  have hplus : ∀ u : ℝ, (1 : ℂ) - u + t * I = ((1 - u : ℝ) : ℂ) + t * I := fun u ↦ by push_cast; ring
  have hminus : ∀ u : ℝ, ‖CH2ZetaInstance.F ((1 : ℂ) - u - t * I)‖
      = ‖CH2ZetaInstance.F (((1 - u : ℝ) : ℂ) + t * I)‖ := fun u ↦ by
    have e : (1 : ℂ) - u - t * I = (starRingEnd ℂ) (((1 - u : ℝ) : ℂ) + t * I) := by
      apply Complex.ext <;> simp
    rw [e, F_conj, Complex.norm_conj]
  refine ⟨t, ⟨ht1, by linarith⟩, ?_, ?_, ?_⟩
  · intro z hz habs
    have hz' : ∃ w : ℂ, riemannZeta w = 0 ∧ w.im = t := by
      rcases abs_eq (by linarith : (0 : ℝ) ≤ t) |>.mp habs with h | h
      · exact ⟨z, hz, h⟩
      · refine ⟨(starRingEnd ℂ) z, ?_, by simp [h]⟩
        rw [riemannZeta_conj, hz, map_zero]
    obtain ⟨w, hw, hwt⟩ := hz'
    have hmem : w ∈ IEANTN.zetaZeroesIn Set.univ (Set.Ioc (t - 1 / 4) (t + 1 / 4)) :=
      ⟨trivial, ⟨by linarith, by linarith⟩, hw⟩
    have := hfar w hmem
    rw [hwt, sub_self, abs_zero] at this
    linarith
  · rw [hrw (fun u ↦ (1 : ℂ) - u + t * I)]
    simp only [hplus]
    exact mul_le_mul_of_nonneg_left hJ hx0.le
  · rw [hrw (fun u ↦ (1 : ℂ) - u - t * I)]
    simp only [hminus]
    exact mul_le_mul_of_nonneg_left hJ hx0.le

end CH2Section81
