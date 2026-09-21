/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section9Cor13

/-!
# Corollary 1.3, the `∑ Λ(n)/n` display

`|∑_{n ≤ x} Λ(n)/n − (log x − γ)| ≤ π/(3·10¹²) + 113.67/√x` for every `x ≥ 1`.

Above `10⁹` this is Corollary 1.2 at `T = 3·10¹² + 5` or `T = 10⁷`, exactly as for `ψ`. Below
`10⁹` the sum is pinned against a reference point `X = 10¹⁰`, where Corollary 1.2 already applies,
by Abel summation:

`S(x) − log x + γ = [S(X) − log X + γ] − (ψ(X)/X − 1) + (ψ(x)/x − 1) − ∫ₓ^X (ψ(t)/t² − 1/t) dt`,

and every term on the right is controlled by Büthe's `|ψ(t) − t| ≤ 0.94 √t` on `11 < t ≤ 10¹⁹`.
Below `11` the bound is crude.
-/

open Complex Filter Topology Set MeasureTheory

namespace CH2Section9

open ArithmeticFunction

/-! ### Rewriting the sums -/

theorem lambdaSum_eq_Ioc (y : ℝ) :
    CH2.v1.lambdaSum y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (vonMangoldt n : ℝ) / n := by
  rw [CH2.v1.lambdaSum]
  refine (Finset.sum_subset (fun n hn ↦ Finset.mem_Iic.mpr (Finset.mem_Ioc.mp hn).2) ?_).symm
  intro n hn hn'
  have hn0 : n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact h
    · exact absurd (Finset.mem_Ioc.mpr ⟨h, Finset.mem_Iic.mp hn⟩) hn'
  simp [hn0]

theorem lambdaSum_sub {x X : ℝ} (hxX : x ≤ X) :
    CH2.v1.lambdaSum X - CH2.v1.lambdaSum x
      = ∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊X⌋₊, (k : ℝ)⁻¹ * (vonMangoldt k : ℝ) := by
  rw [lambdaSum_eq_Ioc, lambdaSum_eq_Ioc,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊x⌋₊) (Nat.floor_le_floor hxX)]
  simp only [add_sub_cancel_left]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [div_eq_inv_mul]

theorem psi_eq_Icc (t : ℝ) :
    Chebyshev.psi t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt k : ℝ) := by
  rw [Chebyshev.psi, Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp

/-! ### Abel summation for `Λ(n)/n` -/

theorem abel_lambda {x X : ℝ} (hx : 0 < x) (hxX : x ≤ X) :
    CH2.v1.lambdaSum X - CH2.v1.lambdaSum x
      = X⁻¹ * Chebyshev.psi X - x⁻¹ * Chebyshev.psi x
        + ∫ t in Set.Ioc x X, (t ^ 2)⁻¹ * Chebyshev.psi t := by
  have hdiff : ∀ t ∈ Set.Icc x X, DifferentiableAt ℝ (fun t : ℝ ↦ t⁻¹) t := fun t ht ↦
    differentiableAt_inv (by linarith [ht.1])
  have hderiv : deriv (fun t : ℝ ↦ t⁻¹) = fun t ↦ -(t ^ 2)⁻¹ := by
    funext t; exact deriv_inv
  have hint : IntegrableOn (deriv fun t : ℝ ↦ t⁻¹) (Set.Icc x X) := by
    rw [hderiv]
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
    have : t ≠ 0 := by linarith [ht.1]
    exact ((continuous_id.pow 2).continuousAt.inv₀ (pow_ne_zero 2 this)).neg.continuousWithinAt
  have h := sum_mul_eq_sub_sub_integral_mul (fun k ↦ (vonMangoldt k : ℝ)) hx.le hxX hdiff hint
  rw [lambdaSum_sub hxX, h, hderiv, psi_eq_Icc, psi_eq_Icc]
  have e : (∫ t in Set.Ioc x X, -(t ^ 2)⁻¹ * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (vonMangoldt k : ℝ))
      = -∫ t in Set.Ioc x X, (t ^ 2)⁻¹ * Chebyshev.psi t := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    rw [psi_eq_Icc]; ring
  rw [e]
  ring

/-! ### The integral, against `log(X/x)` -/

theorem integral_psi_near_log (hbuthe : Buthe.v1.theorem_2_psi) {x X : ℝ} (hx : 11 < x)
    (hxX : x ≤ X) (hX : X ≤ (10 : ℝ) ^ 19) :
    |(∫ t in Set.Ioc x X, (t ^ 2)⁻¹ * Chebyshev.psi t) - Real.log (X / x)|
      ≤ 0.94 / Real.sqrt x * Real.log (X / x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  -- integrability
  have hI1 : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹ * Chebyshev.psi t) (Set.Ioc x X) := by
    have hg : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Icc x X) := by
      refine ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
      have : t ≠ 0 := by linarith [ht.1]
      exact ((continuous_id.pow 2).continuousAt.inv₀ (pow_ne_zero 2 this)).continuousWithinAt
    have h := integrableOn_mul_sum_Icc (fun k ↦ (vonMangoldt k : ℝ)) (m := 0) hx0.le hg
    refine (h.mono_set Set.Ioc_subset_Icc_self).congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
    simp only [psi_eq_Icc]
  have hI2 : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Set.Ioc x X) := by
    refine (ContinuousOn.integrableOn_Icc fun t ht ↦ ?_).mono_set Set.Ioc_subset_Icc_self
    have : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_inv₀ this).continuousWithinAt
  have hlog : (∫ t in Set.Ioc x X, t⁻¹) = Real.log (X / x) := by
    rw [← intervalIntegral.integral_of_le hxX, integral_inv_of_pos hx0 hX0]
  rw [← hlog, ← integral_sub hI1 hI2]
  -- the pointwise bound
  have hbound : ∀ t ∈ Set.Ioc x X,
      ‖(t ^ 2)⁻¹ * Chebyshev.psi t - t⁻¹‖ ≤ 0.94 / Real.sqrt x * t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hb := hbuthe t (by linarith [ht.1]) (le_trans ht.2 hX)
    rw [abs_sub_comm] at hb
    have hst : Real.sqrt x ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1.le
    have hst0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have htt : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
    have e : (t ^ 2)⁻¹ * Chebyshev.psi t - t⁻¹ = (Chebyshev.psi t - t) / t ^ 2 := by
      field_simp
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2),
      div_le_iff₀ (by positivity)]
    -- |ψ t − t| ≤ 0.94 √t ≤ 0.94 t / √x, since √t · √x ≤ t
    have h1 : Real.sqrt t * Real.sqrt x ≤ t := by nlinarith
    calc |Chebyshev.psi t - t| ≤ 0.94 * Real.sqrt t := hb
      _ ≤ 0.94 / Real.sqrt x * t⁻¹ * t ^ 2 := by
          rw [show 0.94 / Real.sqrt x * t⁻¹ * t ^ 2 = 0.94 * (t / Real.sqrt x) by
            field_simp]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [le_div_iff₀ hsx]
          exact h1
  have hmaj : IntegrableOn (fun t : ℝ ↦ 0.94 / Real.sqrt x * t⁻¹) (Set.Ioc x X) :=
    hI2.const_mul _
  calc |∫ t in Set.Ioc x X, ((t ^ 2)⁻¹ * Chebyshev.psi t - t⁻¹)|
      = ‖∫ t in Set.Ioc x X, ((t ^ 2)⁻¹ * Chebyshev.psi t - t⁻¹)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Set.Ioc x X, 0.94 / Real.sqrt x * t⁻¹ :=
        norm_integral_le_of_norm_le hmaj
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hbound))
    _ = 0.94 / Real.sqrt x * ∫ t in Set.Ioc x X, t⁻¹ := integral_const_mul _ _

/-! ### The four ranges -/

theorem abs_four (A B C D : ℝ) : |A - B + C - D| ≤ |A| + |B| + |C| + |D| := by
  calc |A - B + C - D| = |A + -B + C + -D| := by rw [show A - B + C - D = A + -B + C + -D by ring]
    _ ≤ |A + -B + C| + |-D| := abs_add_le _ _
    _ ≤ |A + -B| + |C| + |-D| := by linarith [abs_add_le (A + -B) C]
    _ ≤ |A| + |-B| + |C| + |-D| := by linarith [abs_add_le A (-B)]
    _ = |A| + |B| + |C| + |D| := by rw [abs_neg, abs_neg]

theorem lambda_large (hcor : CH2.v1.corollary_1_2_lambda_sum)
    (hRH : PlattTrudgian.v1.rh_up_to_exact) {x : ℝ} (hx : 3 * 10 ^ 12 + 5 < x) :
    |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)|
      ≤ Real.pi / (3 * 10 ^ 12) + 113.67 / Real.sqrt x := by
  have hπ := Real.pi_pos
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 3 * 10 ^ 12 by norm_num]
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h := hcor (3 * 10 ^ 12 + 5) x (by norm_num) (RH_mono (by norm_num) hRH)
    (by rw [max_eq_left (by norm_num)]; exact hx)
  have h1 : Real.pi / (3 * 10 ^ 12 + 5 - 1) ≤ Real.pi / (3 * 10 ^ 12) :=
    div_le_div_of_nonneg_left hπ.le (by norm_num) (by norm_num)
  have h2 : CH2.v1.CT (3 * 10 ^ 12 + 5) / Real.sqrt x ≤ 113.67 / Real.sqrt x :=
    div_le_div_of_nonneg_right CT_le_big hs0.le
  linarith

theorem lambda_mid (hcor : CH2.v1.corollary_1_2_lambda_sum)
    (hRH : PlattTrudgian.v1.rh_up_to_exact) {x : ℝ} (hx1 : (10 : ℝ) ^ 9 < x)
    (hx2 : x ≤ 3 * 10 ^ 12 + 5) :
    |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)|
      ≤ Real.pi / (3 * 10 ^ 12) + 113.67 / Real.sqrt x := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hx0 : (0 : ℝ) < x := by linarith [show (0 : ℝ) < 10 ^ 9 by norm_num]
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs : Real.sqrt x ≤ 1.74e6 := by
    rw [show (1.74e6 : ℝ) = Real.sqrt (1.74e6 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h := hcor ((10 : ℝ) ^ 7) x le_rfl (RH_mono (by norm_num) hRH)
    (by rw [max_eq_right (by norm_num)]; exact hx1)
  have h2 : CH2.v1.CT ((10 : ℝ) ^ 7) / Real.sqrt x ≤ 82 / Real.sqrt x :=
    div_le_div_of_nonneg_right CT_le_small hs0.le
  -- `π/(10⁷−1)` fits inside the `√x` slack
  have h3 : Real.pi / ((10 : ℝ) ^ 7 - 1) ≤ 31.67 / Real.sqrt x := by
    rw [div_le_div_iff₀ (by norm_num) hs0]
    nlinarith
  have h4 : (82 : ℝ) / Real.sqrt x + 31.67 / Real.sqrt x = 113.67 / Real.sqrt x := by
    rw [← add_div]; norm_num
  have h5 : (0 : ℝ) ≤ Real.pi / (3 * 10 ^ 12) := by positivity
  linarith

theorem lambdaSum_le_small {x : ℝ} (hx : x ≤ 11) : CH2.v1.lambdaSum x ≤ 11 := by
  rw [lambdaSum_eq_Ioc]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / n ≤ 1 := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_le_one hnpos]
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    linarith [Real.log_le_sub_one_of_pos hnpos]
  have hcard : ((Finset.Ioc 0 ⌊x⌋₊).card : ℝ) ≤ 11 := by
    have : ⌊x⌋₊ ≤ 11 := by
      rcases le_or_gt x 0 with h | h
      · simp [Nat.floor_eq_zero.mpr (lt_of_le_of_lt h one_pos)]
      · exact Nat.floor_le_of_le hx |>.trans (by norm_num)
    have hc : (Finset.Ioc 0 ⌊x⌋₊).card ≤ 11 := by simpa using this
    exact_mod_cast hc
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (vonMangoldt n : ℝ) / n
      ≤ ∑ _n ∈ Finset.Ioc 0 ⌊x⌋₊, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (Finset.Ioc 0 ⌊x⌋₊).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 11 := hcard

theorem lambda_small {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 11) :
    |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)|
      ≤ Real.pi / (3 * 10 ^ 12) + 113.67 / Real.sqrt x := by
  have hπ := Real.pi_pos
  have hx0 : (0 : ℝ) < x := by linarith
  have hS1 : CH2.v1.lambdaSum x ≤ 11 := lambdaSum_le_small hx2
  have hS0 : (0 : ℝ) ≤ CH2.v1.lambdaSum x := by
    rw [lambdaSum_eq_Ioc]
    refine Finset.sum_nonneg fun n _ ↦ ?_
    positivity
  have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
  have hlog1 : Real.log x ≤ 2.8 := by
    refine (Real.log_le_log hx0 hx2).trans ?_
    calc Real.log 11 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
      _ = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
      _ ≤ 2.8 := by linarith [Real.log_two_lt_d9]
  have hγ0 : (0 : ℝ) ≤ Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ1 : Real.eulerMascheroniConstant ≤ 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds.le
  have habs : |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)| ≤ 12 := by
    rw [abs_le]; constructor <;> linarith
  have hs : Real.sqrt x ≤ 3.32 := by
    rw [show (3.32 : ℝ) = Real.sqrt (3.32 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hrhs : (34 : ℝ) ≤ 113.67 / Real.sqrt x := by
    rw [le_div_iff₀ hs0]; nlinarith
  have : (0 : ℝ) ≤ Real.pi / (3 * 10 ^ 12) := by positivity
  linarith

set_option maxHeartbeats 1000000 in
theorem lambda_descent (hcor : CH2.v1.corollary_1_2_lambda_sum)
    (hRH : PlattTrudgian.v1.rh_up_to_exact) (hbuthe : Buthe.v1.theorem_2_psi)
    {x : ℝ} (hx1 : 11 < x) (hx2 : x ≤ (10 : ℝ) ^ 9) :
    |CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)|
      ≤ Real.pi / (3 * 10 ^ 12) + 113.67 / Real.sqrt x := by
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsx : Real.sqrt x ≤ 31623 := by
    rw [show (31623 : ℝ) = Real.sqrt (31623 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by nlinarith)
  set X : ℝ := (10 : ℝ) ^ 10 with hX
  have hX0 : (0 : ℝ) < X := by rw [hX]; norm_num
  have hxX : x ≤ X := by rw [hX]; nlinarith
  have hsX : Real.sqrt X = 1e5 := by
    rw [hX, show ((10 : ℝ) ^ 10) = (1e5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  -- the reference point
  have hE := hcor ((10 : ℝ) ^ 7) X le_rfl (RH_mono (by norm_num) hRH)
    (by rw [max_eq_right (by norm_num), hX]; norm_num)
  rw [hsX] at hE
  have hECT : CH2.v1.CT ((10 : ℝ) ^ 7) / 1e5 ≤ 82 / 1e5 :=
    div_le_div_of_nonneg_right CT_le_small (by norm_num)
  -- `ψ` at the two endpoints
  have hbX := hbuthe X (by rw [hX]; norm_num) (by rw [hX]; norm_num)
  have hbx := hbuthe x hx1 (by nlinarith [show (10 : ℝ) ^ 9 ≤ 10 ^ 19 by norm_num])
  have hXne : X ≠ 0 := hX0.ne'
  have hxne : x ≠ 0 := hx0.ne'
  have hpsiX : |X⁻¹ * Chebyshev.psi X - 1| ≤ 0.94 / 1e5 := by
    rw [show X⁻¹ * Chebyshev.psi X - 1 = -((X - Chebyshev.psi X) / X) by field_simp; ring, abs_neg,
      abs_div, abs_of_pos hX0, div_le_div_iff₀ hX0 (by norm_num)]
    calc |X - Chebyshev.psi X| * 1e5 ≤ 0.94 * Real.sqrt X * 1e5 := by nlinarith
      _ = 0.94 * X := by rw [hsX, hX]; norm_num
  have hpsix : |x⁻¹ * Chebyshev.psi x - 1| ≤ 0.94 / Real.sqrt x := by
    rw [show x⁻¹ * Chebyshev.psi x - 1 = -((x - Chebyshev.psi x) / x) by field_simp; ring, abs_neg,
      abs_div, abs_of_pos hx0, div_le_div_iff₀ hx0 hs0]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    calc |x - Chebyshev.psi x| * Real.sqrt x ≤ 0.94 * Real.sqrt x * Real.sqrt x := by nlinarith
      _ = 0.94 * x := by rw [mul_assoc, hxx]
  -- the integral
  have hlogXx : Real.log (X / x) ≤ 23.026 := by
    have h1 : Real.log (X / x) ≤ Real.log X :=
      Real.log_le_log (by positivity) (by rw [div_le_iff₀ hx0]; nlinarith)
    have h2 : Real.log X ≤ 23.026 := by
      rw [hX, Real.log_pow]
      push_cast
      linarith [log_ten_ub]
    linarith
  have hlogXx0 : (0 : ℝ) ≤ Real.log (X / x) :=
    Real.log_nonneg (by rw [le_div_iff₀ hx0]; linarith)
  have hint := integral_psi_near_log hbuthe hx1 hxX (by rw [hX]; norm_num)
  have hintb : |(∫ t in Set.Ioc x X, (t ^ 2)⁻¹ * Chebyshev.psi t) - Real.log (X / x)|
      ≤ 21.65 / Real.sqrt x := by
    refine hint.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hs0 hs0]
    nlinarith
  -- the identity
  have habel := abel_lambda hx0 hxX
  have hlogdiv : Real.log (X / x) = Real.log X - Real.log x := Real.log_div hX0.ne' hx0.ne'
  have hid : CH2.v1.lambdaSum x - (Real.log x - Real.eulerMascheroniConstant)
      = (CH2.v1.lambdaSum X - (Real.log X - Real.eulerMascheroniConstant))
        - (X⁻¹ * Chebyshev.psi X - 1) + (x⁻¹ * Chebyshev.psi x - 1)
        - ((∫ t in Set.Ioc x X, (t ^ 2)⁻¹ * Chebyshev.psi t) - Real.log (X / x)) := by
    rw [hlogdiv]; linarith [habel]
  rw [hid]
  -- and the arithmetic
  have hsum : (113.67 : ℝ) / Real.sqrt x - 0.94 / Real.sqrt x - 21.65 / Real.sqrt x
      = 91.08 / Real.sqrt x := by field_simp; ring
  have hslack : Real.pi / ((10 : ℝ) ^ 7 - 1) + 82 / 1e5 + 0.94 / 1e5
      ≤ Real.pi / (3 * 10 ^ 12) + 91.08 / Real.sqrt x := by
    have h1 : (0 : ℝ) ≤ Real.pi / (3 * 10 ^ 12) := by positivity
    have h2 : Real.pi / ((10 : ℝ) ^ 7 - 1) + 82 / 1e5 + 0.94 / 1e5 ≤ 0.00083 := by
      rw [div_add' _ _ _ (by norm_num), div_add' _ _ _ (by norm_num),
        div_le_iff₀ (by norm_num)]
      nlinarith
    have h3 : (0.00083 : ℝ) ≤ 91.08 / Real.sqrt x := by
      rw [le_div_iff₀ hs0]; nlinarith
    linarith
  have htri := abs_four (CH2.v1.lambdaSum X - (Real.log X - Real.eulerMascheroniConstant))
    (X⁻¹ * Chebyshev.psi X - 1) (x⁻¹ * Chebyshev.psi x - 1)
    ((∫ t in Set.Ioc x X, (t ^ 2)⁻¹ * Chebyshev.psi t) - Real.log (X / x))
  linarith

/-! ### Corollary 1.3, the `∑ Λ(n)/n` display -/

theorem corollary_1_3_lambda_sum (hcor : CH2.v1.corollary_1_2_lambda_sum)
    (hRH : PlattTrudgian.v1.rh_up_to_exact) (hbuthe : Buthe.v1.theorem_2_psi) :
    CH2.v1.corollary_1_3_lambda_sum := by
  intro x hx
  rcases le_or_gt x 11 with h1 | h1
  · exact lambda_small hx h1
  rcases le_or_gt x ((10 : ℝ) ^ 9) with h2 | h2
  · exact lambda_descent hcor hRH hbuthe h1 h2
  rcases le_or_gt x (3 * 10 ^ 12 + 5) with h3 | h3
  · exact lambda_mid hcor hRH h2 h3
  · exact lambda_large hcor hRH h3

end CH2Section9
