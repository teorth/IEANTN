import RSBoundsCompat.ZetaConjugation
import TernaryGoldbach.Explicit.Xi
import TernaryGoldbach.Explicit.RectResidue2
import TernaryGoldbach.Explicit.ZetaPoly
import TernaryGoldbach.Explicit.LogNumerics

/-!
# The Hadamard-type inequality `Re ξ'/ξ(s) ≥ Σ_{ρ ∈ S} Re 1/(s − ρ)` (`ℜs > 1`)

Without the product theorem: on squares `R_k` symmetric about `ℜs = 1/2` at good heights,
`∮ ξ'/ξ(w) (w−s)^{-1} = ½ ∮ ξ'/ξ(w) [(w−s)^{-1} − (w−(1−s))^{-1}]` (symmetry `w ↦ 1 − w`), and the kernel is
`O(|w|^{-2})` while `|ξ'/ξ| ≪ log² T` on `∂R_k` (polynomial `B''_ζ`, good heights, digamma bounds). So
`ξ'/ξ(s) = lim Σ_{ρ ∈ R_k} m_ρ/(s − ρ)`, and all terms have positive real part for `ℜs > 1`.
-/

open Complex Set Metric Filter
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit


/-! ## A datum for `zetaF` with the polynomial bound `B''_ζ` -/

theorem BPz2_le (T : ℝ) : BPz2 T ≤ 9201 * (|T| + 22) * (1.25 * (|T| + 11)) ^ 9 := by
  unfold BPz2
  set a := |T| with ha
  have ha0 : 0 ≤ a := abs_nonneg T
  set b := 1.25 * (a + 11) with hb
  have hb1 : 13.75 ≤ b := by rw [hb]; linarith
  have hb0 : 0 ≤ b := by linarith
  have h1 : 20 * (a + 22) ^ 2 ≤ b ^ 7 := by
    have h2 : (a + 22) ^ 2 ≤ 4 * b ^ 2 := by rw [hb]; nlinarith
    have h3 : 80 * b ^ 2 ≤ b ^ 7 := by
      have : (13.75 : ℝ) ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ (by norm_num) hb1 5
      have : (80 : ℝ) ≤ b ^ 5 := le_trans (by norm_num) this
      nlinarith [sq_nonneg b]
    nlinarith
  have h4 : 20 * (a + 22) ^ 3 * b ^ 2 ≤ (a + 22) * b ^ 9 := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ (a + 22) * b ^ 2)
    nlinarith
  linarith

theorem log_le_log_add (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) : Real.log (a + x) ≤ Real.log a + x / a := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (a + x) / a by positivity)
  rw [Real.log_div (by positivity) ha.ne'] at h
  have : (a + x) / a - 1 = x / a := by field_simp; ring
  linarith

/-- `log(B''_ζ(T)/0.355) ≤ 10.24 + log(|T|+22) + 9 log(1.25(|T|+11))`. -/
theorem log_BPz2_le' (T : ℝ) :
    Real.log (BPz2 T / 0.355) ≤ 10.24 + Real.log (|T| + 22) + 9 * Real.log (1.25 * (|T| + 11)) := by
  have hB0 : 0 < BPz2 T := by unfold BPz2; positivity
  have hpos : (0:ℝ) < 9201 * (|T| + 22) * (1.25 * (|T| + 11)) ^ 9 := by positivity
  refine (Real.log_le_log (div_pos hB0 (by norm_num)) (div_le_div_of_nonneg_right (BPz2_le T)
    (by norm_num))).trans ?_
  rw [Real.log_div hpos.ne' (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have := log9201_le'
  have := neg_log0355_le'
  push_cast
  linarith

theorem log_BPz2_lin (T : ℝ) : Real.log (BPz2 T / 0.355) ≤ 0 + 37 + 2.6 * |T| := by
  have h := log_BPz2_le' T
  have h1 := log_le_log_add 22 |T| (by norm_num) (abs_nonneg T)
  rw [add_comm] at h1
  have h2 : Real.log (1.25 * (|T| + 11)) ≤ Real.log 13.75 + |T| / 11 := by
    have := log_le_log_add 13.75 (1.25 * |T|) (by norm_num) (by positivity)
    rw [show (1.25 : ℝ) * (|T| + 11) = 13.75 + 1.25 * |T| by ring]
    refine this.trans (le_of_eq ?_); ring
  have := log22_le'
  have := log1375_le'
  have hT := abs_nonneg T
  linarith

theorem zetaF_center_lt2 (T : ℝ) : ‖zetaF (2 + T * I)‖ < BPz2 T := by
  have hne : (2 : ℂ) + T * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [zetaF_of_ne hne, norm_mul]
  have h1 : ‖(2 : ℂ) + T * I - 1‖ ≤ 1 + |T| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp; norm_num
  have h2 := norm_zeta_two_le (s := 2 + T * I) (by simp)
  have hpi := Real.pi_lt_d4
  have h3 : π ^ 2 / 6 ≤ 1.65 := by nlinarith [Real.pi_pos]
  have hT0 := abs_nonneg T
  have h4 : (1 + |T|) * 1.65 < BPz2 T := by
    unfold BPz2
    have : (1 + |T|) * 1.65 < 9200 * (|T| + 22) * 1 := by nlinarith
    have hp : (1:ℝ) ≤ (1.25 * (|T| + 11)) ^ 9 := one_le_pow₀ (by linarith)
    have : 9200 * (|T| + 22) * 1 ≤ 9200 * (|T| + 22) * (1.25 * (|T| + 11)) ^ 9 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    have : 0 ≤ 20 * (|T| + 22) ^ 3 * (1.25 * (|T| + 11)) ^ 2 := by positivity
    linarith
  calc ‖(2 : ℂ) + T * I - 1‖ * ‖riemannZeta (2 + T * I)‖ ≤ (1 + |T|) * 1.65 :=
        mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)
    _ < _ := h4

/-- `zetaF` with the polynomial bound. -/
theorem ldatum_zeta2 : LDatum zetaF BPz2 0 (C3 + 2) where
  diff := differentiable_zetaF
  center_ge := zetaF_center_ge
  center_lt := zetaF_center_lt2
  bound := fun T w hw => norm_zetaF_le_BPz2 T hw
  B_ge := polyDatum_zeta2.B_ge
  B_mono := polyDatum_zeta2.B_mono
  logB_lin := log_BPz2_lin
  D_nonneg := le_rfl
  nz_strip := fun s h1 h2 => zetaF_ne_zero_strip h1 h2
  nz_right := fun s h => zetaF_ne_zero_right h
  right_bound := norm_logDeriv_zetaF_right

/-- `HkD B''_ζ k ≤ 11.4 P² + 7.7 P`, `P = 10.24 + 10 log(1.25(k + 23))`. -/
theorem HkD_BPz2_le (k : ℕ) :
    HkD BPz2 k ≤ 11.4 * (10.24 + 10 * Real.log (1.25 * (k + 23))) ^ 2 +
      7.7 * (10.24 + 10 * Real.log (1.25 * (k + 23))) := by
  unfold HkD
  set P := Real.log (BPz2 ((k : ℝ) + 1) / 0.355) with hP
  have hP0 : 0 ≤ P := (polyDatum_zeta2.log_pos _).le
  have hPle : P ≤ 10.24 + 10 * Real.log (1.25 * (k + 23)) := by
    have h := log_BPz2_le' ((k : ℝ) + 1)
    rw [abs_of_nonneg (by positivity)] at h
    have h1 : Real.log ((k : ℝ) + 1 + 22) ≤ Real.log (1.25 * (k + 23)) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (1.25 * ((k : ℝ) + 1 + 11)) ≤ Real.log (1.25 * (k + 23)) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have hl1 : 0.51 ≤ Real.log (10 / 6) := by
    have := log_ratio_pos (r := 6) (by norm_num) (by norm_num)
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have h := Real.exp_bound' (x := 0.51) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢; linarith
  have hl2 := Real.log_two_gt_d9
  have hX : (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8 ≤ 11.4 * P + 7.7 := by
    have e1 : 2 * P / Real.log (10 / 6) ≤ 2 * P / 0.51 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hl1
    have e2 : (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 ≤ (2 * (2 * P / 0.51) + 2) / 0.6931 := by
      have h0 : 0 ≤ 2 * (2 * P / Real.log (10 / 6)) + 2 := by
        have : 0 ≤ 2 * P / Real.log (10 / 6) := div_nonneg (by positivity) (by linarith)
        linarith
      calc (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2
          ≤ (2 * (2 * P / 0.51) + 2) / Real.log 2 := by gcongr
        _ ≤ (2 * (2 * P / 0.51) + 2) / 0.6931 := by
            apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have e3 : (2 * (2 * P / 0.51) + 2) / 0.6931 ≤ 11.4 * P + 2.9 := by
      rw [div_le_iff₀ (by norm_num)]
      have : 2 * (2 * P / 0.51) = (4 / 0.51) * P := by ring
      rw [this]; nlinarith
    linarith
  calc P * ((2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8) ≤ P * (11.4 * P + 7.7) :=
        mul_le_mul_of_nonneg_left hX hP0
    _ ≤ (10.24 + 10 * Real.log (1.25 * (k + 23))) * (11.4 * (10.24 + 10 * Real.log (1.25 * (k + 23))) + 7.7) := by
        have : 0 ≤ Real.log (1.25 * ((k : ℝ) + 23)) := Real.log_nonneg (by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
        gcongr
    _ = _ := by ring

/-! ## Rectangles symmetric about `ℜs = 1/2` -/

/-- The square `[1/2 − A, 1/2 + A] × [−T, T]`. -/
noncomputable def sqZ (A T : ℝ) : ℂ := ((1 / 2 - A : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I
noncomputable def sqW (A T : ℝ) : ℂ := ((1 / 2 + A : ℝ) : ℂ) + ((T : ℝ) : ℂ) * I

@[simp] theorem sqZ_re (A T : ℝ) : (sqZ A T).re = 1 / 2 - A := by simp [sqZ]
@[simp] theorem sqZ_im (A T : ℝ) : (sqZ A T).im = -T := by simp [sqZ]
@[simp] theorem sqW_re (A T : ℝ) : (sqW A T).re = 1 / 2 + A := by simp [sqW]
@[simp] theorem sqW_im (A T : ℝ) : (sqW A T).im = T := by simp [sqW]

/-- **Symmetry**: `∮ G(1 − w) dw = −∮ G(w) dw` on the symmetric square. -/
theorem rectInt_one_sub (G : ℂ → ℂ) (A T : ℝ) :
    rectInt (fun w => G (1 - w)) (sqZ A T) (sqW A T) = -rectInt G (sqZ A T) (sqW A T) := by
  unfold rectInt
  simp only [sqZ_re, sqZ_im, sqW_re, sqW_im]
  have e1 : (∫ x : ℝ in (1 / 2 - A)..(1 / 2 + A), G (1 - (x + ((-T : ℝ) : ℂ) * I))) =
      ∫ x : ℝ in (1 / 2 - A)..(1 / 2 + A), G (x + (T : ℂ) * I) := by
    have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => G (x + (T : ℂ) * I))
      (a := 1 / 2 - A) (b := 1 / 2 + A) 1
    rw [show (1 : ℝ) - (1 / 2 + A) = 1 / 2 - A by ring, show (1 : ℝ) - (1 / 2 - A) = 1 / 2 + A by ring]
      at this
    rw [← this]
    congr 1; ext x; congr 1; push_cast; ring
  have e2 : (∫ x : ℝ in (1 / 2 - A)..(1 / 2 + A), G (1 - (x + ((T : ℝ) : ℂ) * I))) =
      ∫ x : ℝ in (1 / 2 - A)..(1 / 2 + A), G (x + ((-T : ℝ) : ℂ) * I) := by
    have := intervalIntegral.integral_comp_sub_left (fun x : ℝ => G (x + ((-T : ℝ) : ℂ) * I))
      (a := 1 / 2 - A) (b := 1 / 2 + A) 1
    rw [show (1 : ℝ) - (1 / 2 + A) = 1 / 2 - A by ring, show (1 : ℝ) - (1 / 2 - A) = 1 / 2 + A by ring]
      at this
    rw [← this]
    congr 1; ext x; congr 1; push_cast; ring
  have e3 : (∫ y : ℝ in (-T)..T, G (1 - (((1 / 2 + A : ℝ) : ℂ) + y * I))) =
      ∫ y : ℝ in (-T)..T, G (((1 / 2 - A : ℝ) : ℂ) + y * I) := by
    have := intervalIntegral.integral_comp_neg (fun y : ℝ => G (((1 / 2 - A : ℝ) : ℂ) + y * I))
      (a := -T) (b := T)
    rw [neg_neg] at this
    rw [← this]
    congr 1; ext y; congr 1; push_cast; ring
  have e4 : (∫ y : ℝ in (-T)..T, G (1 - (((1 / 2 - A : ℝ) : ℂ) + y * I))) =
      ∫ y : ℝ in (-T)..T, G (((1 / 2 + A : ℝ) : ℂ) + y * I) := by
    have := intervalIntegral.integral_comp_neg (fun y : ℝ => G (((1 / 2 + A : ℝ) : ℂ) + y * I))
      (a := -T) (b := T)
    rw [neg_neg] at this
    rw [← this]
    congr 1; ext y; congr 1; push_cast; ring
  rw [e1, e2, e3, e4]
  ring

/-- `‖∮ G‖ ≤ 2((w.re − z.re) + (w.im − z.im)) M` if `‖G‖ ≤ M` on the boundary. -/
theorem norm_rectInt_le {G : ℂ → ℂ} {z w : ℂ} (hzw1 : z.re ≤ w.re) (hzw2 : z.im ≤ w.im) {M : ℝ}
    (h1 : ∀ x ∈ Icc z.re w.re, ‖G (x + z.im * I)‖ ≤ M) (h2 : ∀ x ∈ Icc z.re w.re, ‖G (x + w.im * I)‖ ≤ M)
    (h3 : ∀ y ∈ Icc z.im w.im, ‖G (w.re + y * I)‖ ≤ M) (h4 : ∀ y ∈ Icc z.im w.im, ‖G (z.re + y * I)‖ ≤ M) :
    ‖rectInt G z w‖ ≤ 2 * ((w.re - z.re) + (w.im - z.im)) * M := by
  have b : ∀ (f : ℝ → ℂ) (a b : ℝ), a ≤ b → (∀ x ∈ Icc a b, ‖f x‖ ≤ M) →
      ‖∫ x in a..b, f x‖ ≤ M * (b - a) := by
    intro f a b hab hf
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := M) (f := f) (a := a) (b := b)
      (fun x hx => by rw [Set.uIoc_of_le hab] at hx; exact hf x (Ioc_subset_Icc_self hx))
    rwa [abs_of_nonneg (by linarith)] at this
  have i1 := b _ _ _ hzw1 h1
  have i2 := b _ _ _ hzw1 h2
  have i3 := b _ _ _ hzw2 h3
  have i4 := b _ _ _ hzw2 h4
  unfold rectInt
  have hI : ‖(I : ℂ)‖ = 1 := Complex.norm_I
  calc ‖(∫ x : ℝ in z.re..w.re, G (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, G (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, G (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, G (z.re + y * I))‖
      ≤ ‖∫ x : ℝ in z.re..w.re, G (x + z.im * I)‖ + ‖∫ x : ℝ in z.re..w.re, G (x + w.im * I)‖ +
        ‖∫ y : ℝ in z.im..w.im, G (w.re + y * I)‖ + ‖∫ y : ℝ in z.im..w.im, G (z.re + y * I)‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)) ?_
        · rw [norm_smul, hI, one_mul]
        · rw [norm_smul, hI, one_mul]
    _ ≤ M * (w.re - z.re) + M * (w.re - z.re) + M * (w.im - z.im) + M * (w.im - z.im) := by linarith
    _ = _ := by ring

/-! ## `ξ'/ξ` on the squares -/

theorem deriv_xiF_one_sub (w : ℂ) : deriv xiF (1 - w) = -deriv xiF w := by
  have h1 : HasDerivAt (fun s => xiF (1 - s)) (deriv xiF (1 - w) * (-1)) w := by
    have h3 : HasDerivAt (fun s : ℂ => 1 - s) (-1) w := by simpa using (hasDerivAt_id w).const_sub 1
    exact ((differentiable_xiF _).hasDerivAt).comp w h3
  have e : (fun s => xiF (1 - s)) = xiF := funext xiF_one_sub
  rw [e] at h1
  have := h1.unique (differentiable_xiF w).hasDerivAt
  linear_combination -this

theorem logDeriv_xiF_one_sub (w : ℂ) : logDeriv xiF (1 - w) = -logDeriv xiF w := by
  rw [logDeriv_apply, logDeriv_apply, deriv_xiF_one_sub, xiF_one_sub]; ring

/-- `|ζ'/ζ(u)| ≤ C₃` for `ℜu ≥ 3/2`. -/
theorem norm_logDeriv_zeta_le {u : ℂ} (hu : 3 / 2 ≤ u.re) : ‖logDeriv riemannZeta u‖ ≤ C3 := by
  have hs1 : 1 < u.re := by linarith
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have e : logDeriv riemannZeta u = -LSeries (fun n : ℕ => (Λ n : ℂ)) u := by
    rw [logDeriv_apply, hL]; ring
  rw [e, norm_neg]
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine hsum.norm.tsum_le_tsum (fun n => ?_) summable_C3
  rw [LSeries.norm_term_eq]
  split_ifs with h0
  · simp [h0]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    have hn : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
    have : (n : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ u.re := Real.rpow_le_rpow_of_exponent_le hn hu
    have hp : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hp this) ArithmeticFunction.vonMangoldt_nonneg

theorem C3_nonneg : 0 ≤ C3 :=
  tsum_nonneg fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- `|ψ(u/2)| ≤ 16 log(2 + |u|) + 4` for `ℜu ≥ 1/2`, `|u| ≥ 8`. -/
theorem norm_digamma_half_le {u : ℂ} (h1 : 1 / 2 ≤ u.re) (h2 : 8 ≤ ‖u‖) :
    ‖Complex.digamma (u / 2)‖ ≤ 16 * Real.log (2 + ‖u‖) + 4 := by
  have hn2 : ‖u / 2‖ = ‖u‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
  rcases le_total 1 (u / 2).re with h | h
  · have hz : 3 ≤ ‖u / 2‖ := by rw [hn2]; linarith
    refine (norm_digamma_le h hz).trans ?_
    rw [hn2]
    have : Real.log (1 + ‖u‖ / 2) ≤ Real.log (2 + ‖u‖) :=
      Real.log_le_log (by positivity) (by linarith [norm_nonneg u])
    linarith
  · set z := u / 2 with hz
    have hzre : 1 / 4 ≤ z.re := by rw [hz]; simp; linarith
    have hm : ∀ m : ℕ, z ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hrec := Complex.digamma_apply_add_one z hm
    have hz1 : 1 ≤ (z + 1).re := by simp; linarith
    have hzn' : ‖z‖ = ‖u‖ / 2 := by rw [hz]; exact hn2
    have hzn : 3 ≤ ‖z + 1‖ := by
      have := norm_sub_norm_le z (-1)
      rw [sub_neg_eq_add, norm_neg, norm_one] at this
      linarith
    have hb := norm_digamma_le hz1 hzn
    have hzinv : ‖z⁻¹‖ ≤ 4 := by
      rw [norm_inv]
      have : 1 / 4 ≤ ‖z‖ := (by linarith : (1/4:ℝ) ≤ z.re).trans (Complex.re_le_norm z)
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have e : Complex.digamma z = Complex.digamma (z + 1) - z⁻¹ := by rw [hrec]; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have hl : Real.log (1 + ‖z + 1‖) ≤ Real.log (2 + ‖u‖) := by
      apply Real.log_le_log (by positivity)
      have := norm_add_le z 1
      rw [norm_one] at this
      linarith [norm_nonneg u]
    linarith

theorem HkD_BPz2_nonneg (k : ℕ) : 0 ≤ HkD BPz2 k := by
  unfold HkD
  have := (polyDatum_zeta2.log_pos ((k:ℝ) + 1)).le
  have h6 : 0 < Real.log (10 / 6) := log_ratio_pos (by norm_num) (by norm_num)
  have h2' := Real.log_pos (by norm_num : (1:ℝ) < 2)
  positivity

/-- The bound for `|ξ'/ξ|` on the square at a good height in `[k, k+1]`. -/
noncomputable def MX (k : ℕ) : ℝ := 3.6 + 8 * Real.log (2 * k + 5) + (C3 + 2 + HkD BPz2 k)

theorem MX_nonneg (k : ℕ) : 0 ≤ MX k := by
  unfold MX
  have := HkD_BPz2_nonneg k
  have := C3_nonneg
  have : 0 ≤ Real.log (2 * (k : ℝ) + 5) := Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  linarith

theorem log_pi_le : Real.log π ≤ 1.2 := by
  rw [Real.log_le_iff_le_exp Real.pi_pos]
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
  have h3 : 1.2 ≤ Real.exp 0.2 := by linarith [Real.add_one_le_exp (0.2 : ℝ)]
  have := Real.pi_lt_d2
  nlinarith

/-- `|ξ'/ξ(u)| ≤ 1.6 + ½|ψ(u/2)| + |zetaF'/zetaF(u)|`, for `ℜu > 0`, `|u| ≥ 1`. -/
theorem norm_logDeriv_xiF_le {u : ℂ} (h0 : 0 < u.re) (hu1 : u ≠ 1) (hξ : xiF u ≠ 0) (hn : 1 ≤ ‖u‖) :
    ‖logDeriv xiF u‖ ≤ 1.6 + 1 / 2 * ‖Complex.digamma (u / 2)‖ + ‖logDeriv zetaF u‖ := by
  rw [logDeriv_xiF h0 hu1 hξ]
  have h1 : ‖1 / u‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (by linarith)]; exact hn
  have hl : ‖-(1 / 2) * Complex.log π‖ ≤ 0.6 := by
    rw [norm_mul, show (π : ℂ) = ((π : ℝ) : ℂ) from rfl, ← Complex.ofReal_log Real.pi_pos.le,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos (by linarith [Real.pi_gt_three]))]
    have := log_pi_le
    simp only [norm_neg, norm_div, norm_one, Complex.norm_ofNat]
    linarith
  have hd : ‖1 / 2 * Complex.digamma (u / 2)‖ = 1 / 2 * ‖Complex.digamma (u / 2)‖ := by
    rw [norm_mul]; simp
  calc ‖1 / u + (-(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (u / 2)) + logDeriv zetaF u‖
      ≤ ‖1 / u + (-(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (u / 2))‖ + ‖logDeriv zetaF u‖ :=
        norm_add_le _ _
    _ ≤ ‖1 / u‖ + ‖-(1 / 2) * Complex.log π + 1 / 2 * Complex.digamma (u / 2)‖ + ‖logDeriv zetaF u‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ‖1 / u‖ + (‖-(1 / 2) * Complex.log π‖ + ‖1 / 2 * Complex.digamma (u / 2)‖) + ‖logDeriv zetaF u‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ 1 + (0.6 + 1 / 2 * ‖Complex.digamma (u / 2)‖) + ‖logDeriv zetaF u‖ := by rw [hd]; gcongr
    _ = _ := by ring

/-- **`|ξ'/ξ| ≤ MX k`** (and `ξ ≠ 0`) on the boundary of the square `[1/2 − T, 1/2 + T] × [−T, T]` at a good
height `T ∈ [k, k+1]`, `k ≥ 8`. -/
theorem xiF_sq_bound {k : ℕ} (hk : 8 ≤ k) {T : ℝ} (hT : T ∈ Icc (k : ℝ) (k + 1))
    (hgood : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]],
      (zetaF ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0 ∧ zetaF ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
      (‖logDeriv zetaF ((σ : ℂ) + ((T : ℝ) : ℂ) * I)‖ ≤ HkD BPz2 k ∧
        ‖logDeriv zetaF ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ HkD BPz2 k))
    {u : ℂ} (h1 : |u.re - 1 / 2| ≤ T) (h2 : |u.im| ≤ T) (h3 : |u.im| = T ∨ |u.re - 1 / 2| = T) :
    xiF u ≠ 0 ∧ ‖logDeriv xiF u‖ ≤ MX k := by
  have hk' : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hT8 : 8 ≤ T := le_trans hk' hT.1
  have hHk : 0 ≤ HkD BPz2 k := HkD_BPz2_nonneg k
  have hC3 := C3_nonneg
  -- the case `ℜu ≥ 1/2`
  have main : ∀ v : ℂ, 1 / 2 ≤ v.re → |v.re - 1 / 2| ≤ T → |v.im| ≤ T →
      (|v.im| = T ∨ |v.re - 1 / 2| = T) → xiF v ≠ 0 ∧ ‖logDeriv xiF v‖ ≤ MX k := by
    intro v hv1 hv2 hv3 hv4
    have hvn : 8 ≤ ‖v‖ := by
      rcases hv4 with h | h
      · exact h ▸ hT8 |>.trans (Complex.abs_im_le_norm v)
      · have : v.re = 1 / 2 + T := by
          rw [abs_of_nonneg (by linarith)] at h; linarith
        linarith [Complex.re_le_norm v]
    have hvn' : ‖v‖ ≤ 2 * k + 3 := by
      refine (Complex.norm_le_abs_re_add_abs_im v).trans ?_
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v.re)]
      have := abs_le.1 hv2
      linarith [hT.2]
    have hv1' : v ≠ 1 := by
      intro h; rw [h] at hvn; simp at hvn
    have hpsi := norm_digamma_half_le hv1 hvn
    have hlog : Real.log (2 + ‖v‖) ≤ Real.log (2 * k + 5) := Real.log_le_log (by positivity) (by linarith)
    -- the `zetaF` part and `ξ ≠ 0`
    have hZ : xiF v ≠ 0 ∧ ‖logDeriv zetaF v‖ ≤ C3 + 2 + HkD BPz2 k := by
      rcases le_or_gt (3 / 2) v.re with hr | hr
      · have hz : riemannZeta v ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
        refine ⟨xiF_ne_zero_of_one_le_re (by linarith), ?_⟩
        rw [logDeriv_zetaF_eq hv1' hz]
        have hinv : ‖1 / (v - 1)‖ ≤ 2 := by
          rw [norm_div, norm_one, div_le_iff₀ (norm_pos_iff.2 (sub_ne_zero.2 hv1'))]
          have := Complex.re_le_norm (v - 1); simp at this; linarith
        have := norm_logDeriv_zeta_le hr
        refine (norm_add_le _ _).trans ?_
        linarith
      · -- on a horizontal side
        have hvim : |v.im| = T := by
          rcases hv4 with h | h
          · exact h
          · exfalso
            rw [abs_of_nonneg (by linarith)] at h; linarith
        have hσ : v.re ∈ [[(-1 / 2 : ℝ), 3 / 2]] := by
          rw [Set.uIcc_of_le (by norm_num)]; exact ⟨by linarith, hr.le⟩
        obtain ⟨⟨hz1, hz2⟩, hb1, hb2⟩ := hgood v.re hσ
        rcases abs_choice v.im with hsg | hsg <;> rw [hsg] at hvim
        · have hv : v = (v.re : ℂ) + ((T : ℝ) : ℂ) * I := by
            apply Complex.ext <;> simp [hvim]
          rw [hv]
          refine ⟨?_, hb1.trans (by linarith)⟩
          intro hξ
          rcases le_or_gt 1 v.re with hr1 | hr1
          · exact xiF_ne_zero_of_one_le_re (by simp; linarith) hξ
          · have hζ := (xiF_eq_zero_iff (by simp; linarith) (by simp; linarith)).1 hξ
            have hne : (v.re : ℂ) + ((T : ℝ) : ℂ) * I ≠ 1 := by
              intro h; have := congrArg Complex.im h; simp at this; linarith
            exact hz1 (by rw [zetaF_of_ne hne, hζ, mul_zero])
        · have hv : v = (v.re : ℂ) + ((-T : ℝ) : ℂ) * I := by
            apply Complex.ext <;> simp; linarith
          rw [hv]
          refine ⟨?_, hb2.trans (by linarith)⟩
          intro hξ
          rcases le_or_gt 1 v.re with hr1 | hr1
          · exact xiF_ne_zero_of_one_le_re (by simp; linarith) hξ
          · have hζ := (xiF_eq_zero_iff (by simp; linarith) (by simp; linarith)).1 hξ
            have hne : (v.re : ℂ) + ((-T : ℝ) : ℂ) * I ≠ 1 := by
              intro h; have := congrArg Complex.im h; simp at this; linarith
            exact hz2 (by rw [zetaF_of_ne hne, hζ, mul_zero])
    refine ⟨hZ.1, ?_⟩
    refine (norm_logDeriv_xiF_le (by linarith) hv1' hZ.1 (by linarith)).trans ?_
    unfold MX
    nlinarith
  rcases le_total (1 / 2) u.re with hr | hr
  · exact main u hr h1 h2 h3
  · have e1 : (1 - u).re - 1 / 2 = -(u.re - 1 / 2) := by simp; ring
    have e2 : (1 - u).im = -u.im := by simp
    have hv := main (1 - u) (by simp; linarith) (by rw [e1, abs_neg]; exact h1)
      (by rw [e2, abs_neg]; exact h2) (by
        rcases h3 with h | h
        · left; rw [e2, abs_neg]; exact h
        · right; rw [e1, abs_neg]; exact h)
    rw [logDeriv_xiF_one_sub, norm_neg, xiF_one_sub] at hv
    exact hv

/-! ## The partial-fraction identity on a square -/

theorem continuousAt_logDeriv_xiF {u : ℂ} (hu : xiF u ≠ 0) : ContinuousAt (logDeriv xiF) u := by
  have h1 : ContinuousAt (deriv xiF) u := (differentiable_xiF.analyticAt u).deriv.continuousAt
  have h2 : ContinuousAt xiF u := differentiable_xiF.continuous.continuousAt
  exact h1.div h2 hu

/-- Integrability along the sides from continuity at every boundary point. -/
theorem rectIntegrable_of_continuousAt {F : ℂ → ℂ} {z w : ℂ}
    (h1 : ∀ x ∈ [[z.re, w.re]], ContinuousAt F (x + z.im * I))
    (h2 : ∀ x ∈ [[z.re, w.re]], ContinuousAt F (x + w.im * I))
    (h3 : ∀ y ∈ [[z.im, w.im]], ContinuousAt F (w.re + y * I))
    (h4 : ∀ y ∈ [[z.im, w.im]], ContinuousAt F (z.re + y * I)) : RectIntegrable F z w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable fun x hx => ?_
  · exact ((h1 x hx).comp (f := fun x : ℝ => (x : ℂ) + z.im * I) (by fun_prop)).continuousWithinAt
  · exact ((h2 x hx).comp (f := fun x : ℝ => (x : ℂ) + w.im * I) (by fun_prop)).continuousWithinAt
  · exact ((h3 x hx).comp (f := fun y : ℝ => (w.re : ℂ) + y * I) (by fun_prop)).continuousWithinAt
  · exact ((h4 x hx).comp (f := fun y : ℝ => (z.re : ℂ) + y * I) (by fun_prop)).continuousWithinAt

/-- The zeros of `ξ` strictly inside the square `|ℜu − 1/2| < T`, `|ℑu| < T` (with `R = 4T`). -/
noncomputable def sqZeros (T : ℝ) : Finset ℂ :=
  (zerosIn xiF (1 / 2) (6 * T) (6 * T / 2)).filter
    (fun u => (sqZ T T).re < u.re ∧ u.re < (sqW T T).re ∧ (sqZ T T).im < u.im ∧ u.im < (sqW T T).im)

noncomputable def mult (T : ℝ) (u : ℂ) : ℕ := (divB xiF (1 / 2) (6 * T) u).toNat

/-- **The partial-fraction identity on a square**: at a good height `T ∈ [k, k+1]` (`k ≥ 8`) and for
`‖s − 1/2‖ ≤ T/2`, `ξ(s) ≠ 0`: `‖ξ'/ξ(s) + Σ_{u} m_u (u − s)^{-1}‖ ≤ 6 MX(k) ‖s − 1/2‖/T`. -/
theorem xi_partial_frac {k : ℕ} (hk : 8 ≤ k) {T : ℝ} (hT : T ∈ Icc (k : ℝ) (k + 1))
    (hgood : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]],
      (zetaF ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0 ∧ zetaF ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
      (‖logDeriv zetaF ((σ : ℂ) + ((T : ℝ) : ℂ) * I)‖ ≤ HkD BPz2 k ∧
        ‖logDeriv zetaF ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ HkD BPz2 k))
    {s : ℂ} (hs : ‖s - 1 / 2‖ ≤ T / 2) (hξs : xiF s ≠ 0) :
    ‖logDeriv xiF s + ∑ u ∈ sqZeros T, (mult T u : ℂ) * (u - s)⁻¹‖ ≤ 6 * MX k * ‖s - 1 / 2‖ / T := by
  have hk' : (8:ℝ) ≤ k := by exact_mod_cast hk
  have hT8 : 8 ≤ T := le_trans hk' hT.1
  have hT0 : 0 < T := by linarith
  set z := sqZ T T with hz
  set w := sqW T T with hw
  have hzre : z.re = 1 / 2 - T := sqZ_re T T
  have hzim : z.im = -T := sqZ_im T T
  have hwre : w.re = 1 / 2 + T := sqW_re T T
  have hwim : w.im = T := sqW_im T T
  have hsre : |s.re - 1 / 2| ≤ T / 2 := by
    have := Complex.abs_re_le_norm (s - 1 / 2); simp at this; linarith
  have hsim : |s.im| ≤ T / 2 := by
    have := Complex.abs_im_le_norm (s - 1 / 2); simp at this; linarith
  -- boundary points
  have bd : ∀ u : ℂ, |u.re - 1 / 2| ≤ T → |u.im| ≤ T → (|u.im| = T ∨ |u.re - 1 / 2| = T) →
      xiF u ≠ 0 ∧ ‖logDeriv xiF u‖ ≤ MX k := fun u h1 h2 h3 => xiF_sq_bound hk hT hgood h1 h2 h3
  have side1 : ∀ x ∈ [[z.re, w.re]], |((x : ℂ) + z.im * I).re - 1 / 2| ≤ T ∧ |((x : ℂ) + z.im * I).im| ≤ T ∧
      (|((x : ℂ) + z.im * I).im| = T ∨ |((x : ℂ) + z.im * I).re - 1 / 2| = T) := by
    intro x hx
    rw [hzre, hwre, Set.uIcc_of_le (by linarith)] at hx
    have e1 : ((x : ℂ) + z.im * I).re = x := by simp
    have e2 : ((x : ℂ) + z.im * I).im = -T := by simp [hzim]
    rw [e1, e2, abs_neg, abs_of_pos hT0]
    exact ⟨abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩, le_rfl, Or.inl rfl⟩
  have side2 : ∀ x ∈ [[z.re, w.re]], |((x : ℂ) + w.im * I).re - 1 / 2| ≤ T ∧ |((x : ℂ) + w.im * I).im| ≤ T ∧
      (|((x : ℂ) + w.im * I).im| = T ∨ |((x : ℂ) + w.im * I).re - 1 / 2| = T) := by
    intro x hx
    rw [hzre, hwre, Set.uIcc_of_le (by linarith)] at hx
    have e1 : ((x : ℂ) + w.im * I).re = x := by simp
    have e2 : ((x : ℂ) + w.im * I).im = T := by simp [hwim]
    rw [e1, e2, abs_of_pos hT0]
    exact ⟨abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩, le_rfl, Or.inl rfl⟩
  have side3 : ∀ y ∈ [[z.im, w.im]], |((w.re : ℂ) + y * I).re - 1 / 2| ≤ T ∧ |((w.re : ℂ) + y * I).im| ≤ T ∧
      (|((w.re : ℂ) + y * I).im| = T ∨ |((w.re : ℂ) + y * I).re - 1 / 2| = T) := by
    intro y hy
    rw [hzim, hwim, Set.uIcc_of_le (by linarith)] at hy
    have e1 : ((w.re : ℂ) + y * I).re - 1 / 2 = T := by simp [hwre]
    have e2 : ((w.re : ℂ) + y * I).im = y := by simp
    rw [e1, e2, abs_of_pos hT0]
    exact ⟨le_rfl, abs_le.2 ⟨hy.1, hy.2⟩, Or.inr rfl⟩
  have side4 : ∀ y ∈ [[z.im, w.im]], |((z.re : ℂ) + y * I).re - 1 / 2| ≤ T ∧ |((z.re : ℂ) + y * I).im| ≤ T ∧
      (|((z.re : ℂ) + y * I).im| = T ∨ |((z.re : ℂ) + y * I).re - 1 / 2| = T) := by
    intro y hy
    rw [hzim, hwim, Set.uIcc_of_le (by linarith)] at hy
    have e1 : ((z.re : ℂ) + y * I).re - 1 / 2 = -T := by simp [hzre]
    have e2 : ((z.re : ℂ) + y * I).im = y := by simp
    rw [e1, e2, abs_neg, abs_of_pos hT0]
    exact ⟨le_rfl, abs_le.2 ⟨hy.1, hy.2⟩, Or.inr rfl⟩
  -- distance from the boundary to `s` and `1 − s`
  have far : ∀ u : ℂ, (|u.im| = T ∨ |u.re - 1 / 2| = T) → ∀ p : ℂ, ‖p - 1 / 2‖ ≤ T / 2 → T / 2 ≤ ‖u - p‖ := by
    intro u hu p hp
    have h1 : T ≤ ‖u - 1 / 2‖ := by
      rcases hu with h | h
      · have := Complex.abs_im_le_norm (u - 1 / 2); simp at this; linarith
      · have := Complex.abs_re_le_norm (u - 1 / 2); simp at this; linarith
    have := norm_sub_norm_le (u - 1 / 2) (p - 1 / 2)
    rw [show u - 1 / 2 - (p - 1 / 2) = u - p by ring] at this
    linarith
  have hs' : ‖(1 - s) - 1 / 2‖ ≤ T / 2 := by
    rw [show (1 - s) - 1 / 2 = -(s - 1 / 2) by ring, norm_neg]; exact hs
  have hne : ∀ u : ℂ, (|u.im| = T ∨ |u.re - 1 / 2| = T) → u ≠ s ∧ u ≠ 1 - s := by
    intro u hu
    have a := far u hu s hs
    have b := far u hu (1 - s) hs'
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, sub_self, norm_zero] at a; linarith
    · rw [h, sub_self, norm_zero] at b; linarith
  -- the integrand
  set G : ℂ → ℂ := fun v => logDeriv xiF v * (v - s)⁻¹ with hG
  have cG : ∀ u : ℂ, |u.re - 1 / 2| ≤ T → |u.im| ≤ T → (|u.im| = T ∨ |u.re - 1 / 2| = T) →
      ContinuousAt G u ∧ ContinuousAt (fun v => G (1 - v)) u := by
    intro u h1 h2 h3
    have hu := bd u h1 h2 h3
    have e1 : (1 - u).re - 1 / 2 = -(u.re - 1 / 2) := by simp; ring
    have e2 : (1 - u).im = -u.im := by simp
    have hu' := bd (1 - u) (by rw [e1, abs_neg]; exact h1) (by rw [e2, abs_neg]; exact h2)
      (by rcases h3 with h | h
          · left; rw [e2, abs_neg]; exact h
          · right; rw [e1, abs_neg]; exact h)
    have hn := hne u h3
    refine ⟨(continuousAt_logDeriv_xiF hu.1).mul ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.2 hn.1)), ?_⟩
    have hc : ContinuousAt (fun v : ℂ => 1 - v) u := continuousAt_const.sub continuousAt_id
    refine ((continuousAt_logDeriv_xiF hu'.1).comp (f := fun v : ℂ => 1 - v) hc).mul ?_
    refine ((continuousAt_const.sub continuousAt_id).sub continuousAt_const).inv₀ ?_
    intro h; apply hn.2; simp only [Pi.sub_apply, id_eq] at h; linear_combination -h
  have rG : RectIntegrable G z w :=
    rectIntegrable_of_continuousAt (fun x hx => (cG _ (side1 x hx).1 (side1 x hx).2.1 (side1 x hx).2.2).1)
      (fun x hx => (cG _ (side2 x hx).1 (side2 x hx).2.1 (side2 x hx).2.2).1)
      (fun x hx => (cG _ (side3 x hx).1 (side3 x hx).2.1 (side3 x hx).2.2).1)
      (fun x hx => (cG _ (side4 x hx).1 (side4 x hx).2.1 (side4 x hx).2.2).1)
  have rG' : RectIntegrable (fun v => G (1 - v)) z w :=
    rectIntegrable_of_continuousAt (fun x hx => (cG _ (side1 x hx).1 (side1 x hx).2.1 (side1 x hx).2.2).2)
      (fun x hx => (cG _ (side2 x hx).1 (side2 x hx).2.1 (side2 x hx).2.2).2)
      (fun x hx => (cG _ (side3 x hx).1 (side3 x hx).2.1 (side3 x hx).2.2).2)
      (fun x hx => (cG _ (side4 x hx).1 (side4 x hx).2.1 (side4 x hx).2.2).2)
  -- symmetrization
  have hsym := rectInt_one_sub G T T
  have hH : rectInt (fun v => G v + (-1) * G (1 - v)) z w = 2 * rectInt G z w := by
    rw [rectInt_add' rG (rG'.const_mul (-1)), rectInt_const_mul, hsym]; ring
  -- the bound on `G(v) − G(1 − v)`
  have hHb : ∀ u : ℂ, |u.re - 1 / 2| ≤ T → |u.im| ≤ T → (|u.im| = T ∨ |u.re - 1 / 2| = T) →
      ‖G u + (-1) * G (1 - u)‖ ≤ MX k * (8 * ‖s - 1 / 2‖ / T ^ 2) := by
    intro u h1 h2 h3
    have hu := bd u h1 h2 h3
    have hn := hne u h3
    have hus : u - s ≠ 0 := sub_ne_zero.2 hn.1
    have hus' : u - (1 - s) ≠ 0 := sub_ne_zero.2 hn.2
    have e : G u + (-1) * G (1 - u) = logDeriv xiF u * ((2 * s - 1) * ((u - s)⁻¹ * (u - (1 - s))⁻¹)) := by
      simp only [hG, logDeriv_xiF_one_sub]
      have : (1 - u - s) = -(u - (1 - s)) := by ring
      rw [this]
      field_simp
      ring
    rw [e, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv]
    have a := far u h3 s hs
    have b := far u h3 (1 - s) hs'
    have h12 : ‖2 * s - (1 : ℂ)‖ = 2 * ‖s - 1 / 2‖ := by
      rw [show 2 * s - (1 : ℂ) = 2 * (s - 1 / 2) by ring, norm_mul]; simp
    rw [h12]
    have hT2 : 0 < T / 2 := by linarith
    have i1 : ‖u - s‖⁻¹ ≤ (T / 2)⁻¹ := inv_anti₀ hT2 a
    have i2 : ‖u - (1 - s)‖⁻¹ ≤ (T / 2)⁻¹ := inv_anti₀ hT2 b
    have hM : 0 ≤ MX k := (norm_nonneg _).trans hu.2
    calc ‖logDeriv xiF u‖ * (2 * ‖s - 1 / 2‖ * (‖u - s‖⁻¹ * ‖u - (1 - s)‖⁻¹))
        ≤ MX k * (2 * ‖s - 1 / 2‖ * ((T / 2)⁻¹ * (T / 2)⁻¹)) := by
          gcongr
          exact hu.2
      _ = MX k * (8 * ‖s - 1 / 2‖ / T ^ 2) := by field_simp; ring
  have hint := norm_rectInt_le (G := fun v => G v + (-1) * G (1 - v)) (z := z) (w := w)
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith)
    (fun x hx => hHb _ (side1 x (Set.Icc_subset_uIcc hx)).1 (side1 x (Set.Icc_subset_uIcc hx)).2.1
      (side1 x (Set.Icc_subset_uIcc hx)).2.2)
    (fun x hx => hHb _ (side2 x (Set.Icc_subset_uIcc hx)).1 (side2 x (Set.Icc_subset_uIcc hx)).2.1
      (side2 x (Set.Icc_subset_uIcc hx)).2.2)
    (fun x hx => hHb _ (side3 x (Set.Icc_subset_uIcc hx)).1 (side3 x (Set.Icc_subset_uIcc hx)).2.1
      (side3 x (Set.Icc_subset_uIcc hx)).2.2)
    (fun x hx => hHb _ (side4 x (Set.Icc_subset_uIcc hx)).1 (side4 x (Set.Icc_subset_uIcc hx)).2.1
      (side4 x (Set.Icc_subset_uIcc hx)).2.2)
  rw [hH, hzre, hwre, hzim, hwim] at hint
  -- the residue theorem
  have hc : xiF (1 / 2) ≠ 0 := xiF_half_ne_zero
  have hrect : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ ball (1 / 2 : ℂ) (6 * T / 2) := by
    intro u hu
    rw [mem_reProdIm, hzre, hwre, hzim, hwim, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hu
    rw [mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [sub_re, sub_im, show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num, show ((1 / 2 : ℂ)).im = 0 by norm_num,
      sub_zero]
    have := abs_le.2 (⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩ : -T ≤ u.re - 1 / 2 ∧ u.re - 1 / 2 ≤ T)
    have := abs_le.2 (⟨hu.2.1, hu.2.2⟩ : -T ≤ u.im ∧ u.im ≤ T)
    linarith
  have hbd : NoZerosOnSides xiF z w :=
    ⟨fun x hx => (bd _ (side1 x hx).1 (side1 x hx).2.1 (side1 x hx).2.2).1,
      fun x hx => (bd _ (side2 x hx).1 (side2 x hx).2.1 (side2 x hx).2.2).1,
      fun y hy => (bd _ (side3 y hy).1 (side3 y hy).2.1 (side3 y hy).2.2).1,
      fun y hy => (bd _ (side4 y hy).1 (side4 y hy).2.1 (side4 y hy).2.2).1⟩
  have hres := rectInt_logDeriv_inv_sub differentiable_xiF (by linarith : (0:ℝ) < 6 * T) hc
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) hrect hbd
    (p := s) (by rw [hzre]; linarith [(abs_le.1 hsre).1]) (by rw [hwre]; linarith [(abs_le.1 hsre).2])
    (by rw [hzim]; linarith [(abs_le.1 hsim).1]) (by rw [hwim]; linarith [(abs_le.1 hsim).2]) hξs
  have hres' : rectInt G z w = 2 * π * I * (logDeriv xiF s + ∑ u ∈ sqZeros T, (mult T u : ℂ) * (u - s)⁻¹) :=
    hres
  rw [hres'] at hint
  have hpi : ‖(2 : ℂ) * π * I‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp
  rw [norm_mul, norm_mul, hpi] at hint
  have hpi3 := Real.pi_gt_three
  have hM : 0 ≤ MX k := MX_nonneg k
  set X := ‖logDeriv xiF s + ∑ u ∈ sqZeros T, (mult T u : ℂ) * (u - s)⁻¹‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  have key : 2 * (2 * π) * X ≤ 2 * (1 / 2 + T - (1 / 2 - T) + (T - -T)) * (MX k * (8 * ‖s - 1 / 2‖ / T ^ 2)) := by
    simpa [mul_assoc] using hint
  have e2 : 2 * (1 / 2 + T - (1 / 2 - T) + (T - -T)) * (MX k * (8 * ‖s - 1 / 2‖ / T ^ 2)) =
      64 * (MX k * ‖s - 1 / 2‖ / T) := by field_simp; ring
  rw [e2] at key
  have hq : 0 ≤ MX k * ‖s - 1 / 2‖ / T := by positivity
  rw [show 6 * MX k * ‖s - 1 / 2‖ / T = 6 * (MX k * ‖s - 1 / 2‖ / T) by ring]
  nlinarith

/-! ## Letting `T → ∞` -/

theorem xiF_conj (s : ℂ) : xiF (starRingEnd ℂ s) = starRingEnd ℂ (xiF s) := by
  rcases eq_or_ne s 0 with rfl | h0
  · simp [xiF_zero]
  rcases eq_or_ne s 1 with rfl | h1
  · simp [xiF_one]
  have h0' : starRingEnd ℂ s ≠ 0 := by simpa using h0
  have h1' : starRingEnd ℂ s ≠ 1 := by
    intro h; apply h1; simpa using congrArg (starRingEnd ℂ) h
  have e : ∀ w : ℂ, w ≠ 0 → w ≠ 1 → xiF w = w * (w - 1) * (completedRiemannZeta w + 1 / w + 1 / (1 - w)) + 1 := by
    intro w _ _
    rw [completedRiemannZeta_eq]; unfold xiF; ring
  rw [e _ h0' h1', e _ h0 h1, RSBoundsCompat.completedRiemannZeta_conj]
  simp [map_add, map_mul, map_sub, map_div₀, map_one]

theorem logDeriv_xiF_conj (s : ℂ) : logDeriv xiF (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv xiF s) := by
  have hf : (starRingEnd ℂ ∘ xiF ∘ starRingEnd ℂ) = xiF := by
    funext w; simp [Function.comp, xiF_conj]
  have hd := deriv_conj_conj (f := xiF)
  rw [hf] at hd
  have h2 : deriv xiF (starRingEnd ℂ s) = starRingEnd ℂ (deriv xiF s) := by
    rw [congrFun hd (starRingEnd ℂ s)]; simp [Function.comp]
  rw [logDeriv_apply, logDeriv_apply, h2, xiF_conj, map_div₀]

theorem mem_sqZeros_iff {T : ℝ} {u : ℂ} (hu : u ∈ sqZeros T) :
    xiF u = 0 ∧ |u.re - 1 / 2| < T ∧ |u.im| < T := by
  rw [sqZeros, Finset.mem_filter] at hu
  obtain ⟨hz, h1, h2, h3, h4⟩ := hu
  simp only [sqZ_re, sqZ_im, sqW_re, sqW_im] at h1 h2 h3 h4
  refine ⟨?_, abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  have hu' := (mem_zerosIn hz).2
  have hucR : u ∈ closedBall (1 / 2 : ℂ) (6 * T) := by
    rw [mem_closedBall, dist_eq_norm]; linarith [(mem_zerosIn hz).1]
  rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => differentiable_xiF.analyticAt z : AnalyticOnNhd ℂ xiF (closedBall (1 / 2) (6 * T))) hucR] at hu'
  by_contra hne
  exact hu' (by rw [(differentiable_xiF.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)

theorem mem_sqZeros_of_zero {T : ℝ} (hT : 0 < T) {ρ : ℂ} (hρ : xiF ρ = 0) (h1 : |ρ.re - 1 / 2| < T)
    (h2 : |ρ.im| < T) : ρ ∈ sqZeros T ∧ 1 ≤ mult T ρ := by
  have hf := differentiable_xiF
  have hnorm : ‖ρ - 1 / 2‖ < 6 * T / 2 := by
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [sub_re, sub_im, show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num,
      show ((1 / 2 : ℂ)).im = 0 by norm_num, sub_zero]
    linarith
  have huR : ρ ∈ closedBall (1 / 2 : ℂ) (6 * T) := by
    rw [mem_closedBall, dist_eq_norm]; linarith
  have han : AnalyticOnNhd ℂ xiF (closedBall (1 / 2) (6 * T)) := fun z _ => hf.analyticAt z
  have hne : divB xiF (1 / 2) (6 * T) ρ ≠ 0 := by
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply han huR]
    intro h
    have hord : analyticOrderAt xiF ρ ≠ 0 := by
      rw [Ne, (hf.analyticAt ρ).analyticOrderAt_eq_zero]; exact not_not.2 hρ
    have hfin : analyticOrderAt xiF ρ ≠ ⊤ := by
      have h2 : xiF 2 ≠ 0 := xiF_ne_zero_of_one_le_re (by norm_num)
      have hc0 : analyticOrderAt xiF 2 ≠ ⊤ := by
        rw [(hf.analyticAt 2).analyticOrderAt_eq_zero.2 h2]; simp
      exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
        (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ xiF Set.univ)
        isPreconnected_univ (Set.mem_univ 2) (Set.mem_univ ρ) hc0
    apply hord
    revert h
    cases hk : analyticOrderAt xiF ρ with
    | top => exact absurd hk hfin
    | coe n => simp
  refine ⟨?_, ?_⟩
  · rw [sqZeros, Finset.mem_filter, zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset,
      Function.mem_support]
    simp only [sqZ_re, sqZ_im, sqW_re, sqW_im]
    have := abs_lt.1 h1
    have := abs_lt.1 h2
    exact ⟨⟨hne, hnorm⟩, by linarith, by linarith, by linarith, by linarith⟩
  · have h0 : 0 ≤ divB xiF (1 / 2) (6 * T) ρ := MeromorphicOn.AnalyticOnNhd.divisor_nonneg han ρ
    unfold mult
    omega

/-- `MX k ≤ (C₃ + 14) + 2700 log²(k + 23)`. -/
theorem MX_le (k : ℕ) : MX k ≤ (C3 + 14) + 2700 * Real.log (k + 23) ^ 2 := by
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  set ℓ := Real.log ((k : ℝ) + 23) with hℓ
  have hℓ3 : 3 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have h1 := Real.exp_one_lt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h4 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 3
    rw [h3]; linarith [show (2.7182818286 : ℝ) ^ 3 ≤ 23 by norm_num]
  have hl2 : Real.log (2 * (k : ℝ) + 5) ≤ 1 + ℓ := by
    have : Real.log (2 * (k : ℝ) + 5) ≤ Real.log (2 * ((k : ℝ) + 23)) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    have := Real.log_two_lt_d9
    linarith
  have hP : 10.24 + 10 * Real.log (1.25 * ((k : ℝ) + 23)) ≤ 15 * ℓ := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 1.25 ≤ 0.25 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1.25 by norm_num); linarith
    linarith
  have hP0 : 0 ≤ 10.24 + 10 * Real.log (1.25 * ((k : ℝ) + 23)) := by
    have : 0 ≤ Real.log (1.25 * ((k : ℝ) + 23)) := Real.log_nonneg (by linarith)
    linarith
  have hH := HkD_BPz2_le k
  have hsq : (10.24 + 10 * Real.log (1.25 * ((k : ℝ) + 23))) ^ 2 ≤ (15 * ℓ) ^ 2 := pow_le_pow_left₀ hP0 hP 2
  unfold MX
  nlinarith

/-- **Uniform approximation**: for `M ≥ 0`, `ε > 0` there is a square on which
`‖ξ'/ξ(s) + Σ_u m_u (u − s)^{-1}‖ ≤ ε` for all `‖s − 1/2‖ ≤ M` (with `ξ(s) ≠ 0`), which contains all zeros with
`‖ρ − 1/2‖ ≤ M` (with multiplicity `≥ 1`), and whose sum runs over zeros only. -/
theorem xi_partial_approx {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧
      (∀ s : ℂ, ‖s - 1 / 2‖ ≤ M → xiF s ≠ 0 →
        ‖logDeriv xiF s + ∑ u ∈ sqZeros T, (mult T u : ℂ) * (u - s)⁻¹‖ ≤ ε) ∧
      (∀ ρ : ℂ, xiF ρ = 0 → ‖ρ - 1 / 2‖ ≤ M → ρ ∈ sqZeros T ∧ 1 ≤ mult T ρ) ∧
      (∀ u ∈ sqZeros T, xiF u = 0) := by
  set δ := ε / (6 * (M + 1) * 5401) with hδ
  have hδ0 : 0 < δ := by positivity
  have t1 : ∀ᶠ k : ℕ in atTop, (C3 + 14) / (k : ℝ) < δ :=
    (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (C3 + 14))).2 δ hδ0
  have hlim : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 23) ^ 2 / (1 * ((k : ℝ) + 23) + 0)) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      (tendsto_atTop_add_const_right _ 23 tendsto_natCast_atTop_atTop)
  have t2 : ∀ᶠ k : ℕ in atTop, Real.log ((k : ℝ) + 23) ^ 2 / (1 * ((k : ℝ) + 23) + 0) < δ :=
    (tendsto_order.1 hlim).2 δ hδ0
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := (t1.and (t2.and ((eventually_ge_atTop 23).and
    (eventually_ge_atTop ⌈2 * M⌉₊)))).exists
  have hk23 : (23 : ℝ) ≤ k := by exact_mod_cast hk3
  have hkM : 2 * M ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk4)
  obtain ⟨T, hT, hgood⟩ := good_heightD ldatum_zeta2 k
  have hT0 : 0 < T := by linarith [hT.1]
  have hk0 : (0:ℝ) < k := by linarith
  refine ⟨T, hT0, fun s hs hξ => ?_, fun ρ hρ hρM => ?_, fun u hu => (mem_sqZeros_iff hu).1⟩
  · have hs' : ‖s - 1 / 2‖ ≤ T / 2 := by linarith [hT.1]
    refine (xi_partial_frac (by omega) hT hgood hs' hξ).trans ?_
    have hMX := MX_le k
    have hMX0 := MX_nonneg k
    simp only [one_mul, add_zero] at hk2
    have e1 : MX k / k ≤ 5401 * δ := by
      rw [div_le_iff₀ hk0]
      have a1 : C3 + 14 ≤ δ * k := by rw [div_lt_iff₀ hk0] at hk1; linarith
      have a2 : Real.log ((k : ℝ) + 23) ^ 2 ≤ δ * ((k : ℝ) + 23) := by
        rw [div_lt_iff₀ (by linarith)] at hk2; linarith
      nlinarith
    have hsn := norm_nonneg (s - 1 / 2)
    calc 6 * MX k * ‖s - 1 / 2‖ / T ≤ 6 * MX k * M / k := by
          apply div_le_div₀ (by positivity) (by gcongr) hk0 hT.1
      _ = 6 * M * (MX k / k) := by ring
      _ ≤ 6 * M * (5401 * δ) := by gcongr
      _ = ε * (M / (M + 1)) := by rw [hδ]; field_simp
      _ ≤ ε * 1 := by gcongr; rw [div_le_one (by linarith)]; linarith
      _ = ε := mul_one ε
  · have h1 : |ρ.re - 1 / 2| < T := by
      have := Complex.abs_re_le_norm (ρ - 1 / 2); simp at this; linarith [hT.1]
    have h2 : |ρ.im| < T := by
      have := Complex.abs_im_le_norm (ρ - 1 / 2); simp at this; linarith [hT.1]
    exact mem_sqZeros_of_zero hT0 hρ h1 h2

end TernaryGoldbach.Explicit
