import TernaryGoldbach.Explicit.ZetaDatum
import TernaryGoldbach.Explicit.ZeroSums

/-!
# The explicit formula for `ζ`

`explicit_formulaD` for `zetaF = (s − 1)ζ(s)` and for `s − 1` (whose only zero, at `s = 1`, gives the
main term `M(1) x`), together with `f'/f = 1/(s − 1) + ζ'/ζ` and the Dirichlet series of `ζ'/ζ`
(`SsumG_eq_line` for the trivial character mod `1`):
`Σ_{ρ} m_ρ M(ρ) x^ρ → M(1) x − Σ Λ(n) φ(n/x) − (1/2π) ∫ (ζ'/ζ)(−1/2 + iy) M(−1/2 + iy) x^{−1/2+iy} dy`.
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

/-- `B₁(T) = |T| + 13`. -/
noncomputable def B1 (T : ℝ) : ℝ := |T| + 13

theorem logDeriv_sub_one (s : ℂ) : logDeriv (fun s : ℂ => s - 1) s = 1 / (s - 1) := by
  rw [logDeriv_apply]
  have : deriv (fun s : ℂ => s - 1) s = 1 := by
    rw [deriv_sub_const, deriv_id'']
  rw [this]

/-- `s − 1` is an `LDatum`. -/
theorem ldatum_sub_one : LDatum (fun s : ℂ => s - 1) B1 0 2 where
  diff := differentiable_id.sub_const 1
  center_ge := fun T => by
    have := Complex.abs_re_le_norm ((2 : ℂ) + T * I - 1)
    simp at this; norm_num at this ⊢; linarith
  center_lt := fun T => by
    have : ‖(2 : ℂ) + T * I - 1‖ ≤ 1 + |T| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp; norm_num
    unfold B1; linarith
  bound := fun T w hw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 : ‖(2 : ℂ) + T * I - 1‖ ≤ 1 + |T| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp; norm_num
    have : ‖w - 1‖ ≤ ‖w - (2 + T * I)‖ + ‖(2 : ℂ) + T * I - 1‖ := by
      calc ‖w - 1‖ = ‖(w - (2 + T * I)) + ((2 : ℂ) + T * I - 1)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    unfold B1; linarith
  B_ge := fun T => by unfold B1; linarith [abs_nonneg T]
  B_mono := fun T T' h => by unfold B1; linarith
  logB_lin := fun T => by
    unfold B1
    have hT0 := abs_nonneg T
    rw [Real.log_div (by positivity) (by norm_num)]
    have h1 : Real.log (|T| + 13) ≤ Real.log 13 + |T| / 13 := by
      have : Real.log (|T| + 13) - Real.log 13 ≤ |T| / 13 := by
        rw [← Real.log_div (by positivity) (by norm_num)]
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (|T| + 13) / 13 by positivity)
        linarith [show (|T| + 13) / 13 - 1 = |T| / 13 by ring]
      linarith
    have h2 : Real.log 13 ≤ 13 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 13 by norm_num); linarith
    have h3 : -Real.log 0.355 ≤ 2 := by
      rw [← Real.log_inv]
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 0.355⁻¹ by norm_num)
      norm_num at this ⊢; linarith
    linarith
  D_nonneg := le_rfl
  nz_strip := fun s h1 h2 => by
    intro h; rw [sub_eq_zero] at h; rw [h] at h2; simp at h2; linarith
  nz_right := fun s h => by
    intro h0; rw [sub_eq_zero] at h0; rw [h0] at h; simp at h
  right_bound := fun y => by
    rw [logDeriv_sub_one, norm_div, norm_one]
    have hs : ((3 / 2 : ℝ) : ℂ) + y * I - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; norm_num at this
    rw [div_le_iff₀ (norm_pos_iff.2 hs)]
    have := Complex.abs_re_le_norm (((3 / 2 : ℝ) : ℂ) + y * I - 1)
    simp at this; norm_num at this ⊢; linarith

/-- The zeros of `s − 1` in the rectangle: `s = 1`, once. -/
theorem sum_zerosRect_sub_one {T : ℝ} (hT : 0 < T) (h : ℂ → ℂ) :
    ∑ u ∈ zerosRectD (fun s : ℂ => s - 1) T, (multRectD (fun s : ℂ => s - 1) T u : ℂ) * h u = h 1 := by
  have hd : Differentiable ℂ (fun s : ℂ => s - 1) := differentiable_id.sub_const 1
  have hfa : AnalyticOnNhd ℂ (fun s : ℂ => s - 1) (Metric.closedBall 2 (RT T)) := fun z _ =>
    hd.analyticAt z
  have h1R : (1 : ℂ) ∈ Metric.closedBall 2 (RT T) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; norm_num; unfold RT; linarith
  have hdiv : divB (fun s : ℂ => s - 1) 2 (RT T) 1 = 1 := by
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply hfa h1R]
    have : analyticOrderAt (fun s : ℂ => s - 1) 1 = 1 := analyticOrderAt_id_sub_const_self
    rw [this]; rfl
  have hsub : zerosRectD (fun s : ℂ => s - 1) T = {1} := by
    ext u
    constructor
    · intro hu
      have h0 := eq_zero_of_mem_zerosIn hd (Finset.mem_filter.1 hu).1
      rw [Finset.mem_singleton]; exact sub_eq_zero.1 h0
    · intro hu
      rw [Finset.mem_singleton] at hu; subst hu
      rw [zerosRectD, Finset.mem_filter, zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset,
        Function.mem_support, hdiv]
      refine ⟨⟨one_ne_zero, ?_⟩, ?_⟩
      · norm_num; unfold RT; linarith
      · simp only [zT_re, zT_im, wT_re, wT_im, Complex.one_re, Complex.one_im]
        refine ⟨by norm_num, by norm_num, by linarith, hT⟩
  rw [hsub, Finset.sum_singleton]
  unfold multRectD
  rw [hdiv]; simp

/-- `ζ'/ζ(s) M(s) x^s`. -/
noncomputable def hZeta (φ : ℝ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  logDeriv riemannZeta s * (mellin φ s * (x : ℂ) ^ s)

theorem hIntD_zetaF_eq (φ : ℝ → ℂ) (x : ℝ) {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    hIntD zetaF φ x s = hIntD (fun s : ℂ => s - 1) φ x s + hZeta φ x s := by
  rw [hIntD, hIntD, hZeta, logDeriv_zetaF_eq hs hz, logDeriv_sub_one]; ring

theorem zeta_ne_zero_of_zetaF {s : ℂ} (hs : s ≠ 1) (h : zetaF s ≠ 0) : riemannZeta s ≠ 0 := by
  intro h0; apply h; rw [zetaF_of_ne hs, h0, mul_zero]

/-- **The explicit formula for `ζ`**: for an admissible smoothing `φ` (`M = mellin φ`), along heights
`T_k ∈ [k+1, k+2]`, `Σ_{ρ} m_ρ M(ρ) x^ρ → M(1) x − Σ Λ(n) φ(n/x) − (1/2π) ∫ hZeta(−1/2 + iy) dy`. -/
theorem explicit_formula_zeta {φ : ℝ → ℂ} {K c : ℝ} (hφ : GoodSmoothing φ K c) {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
          (mellin φ u * (x : ℂ) ^ u)) atTop
        (𝓝 (mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x -
          (1 / (2 * π) : ℂ) * ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I))) := by
  obtain ⟨T, hT, hlim⟩ := explicit_formulaD ldatum_zeta hφ hx
  obtain ⟨T', hT', hlim1⟩ := explicit_formulaD ldatum_sub_one hφ hx
  refine ⟨T, hT, ?_⟩
  -- the main term from `s − 1`
  have hconst : ∀ k, ∑ u ∈ zerosRectD (fun s : ℂ => s - 1) (T' k),
      (multRectD (fun s : ℂ => s - 1) (T' k) u : ℂ) * (mellin φ u * (x : ℂ) ^ u) = mellin φ 1 * x := by
    intro k
    have hpos : 0 < T' k := by linarith [(hT' k).1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    rw [sum_zerosRect_sub_one hpos, Complex.cpow_one]
  simp_rw [hconst] at hlim1
  have hM1 := tendsto_nhds_unique tendsto_const_nhds hlim1
  have hR1 : ∀ y : ℝ, ((3 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h; simp at this; norm_num at this
  have hL1 : ∀ y : ℝ, ((-1 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h; simp at this; norm_num at this
  have hRz : ∀ y : ℝ, riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
  have hLz : ∀ y : ℝ, riemannZeta (((-1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    zeta_ne_zero_of_zetaF (hL1 y) (zetaF_ne_zero_strip (by simp; norm_num) (by simp; norm_num))
  have iR := integrable_hIntD_right ldatum_zeta hφ hx
  have iL := integrable_hIntD_left ldatum_zeta hφ hx
  have iR1 := integrable_hIntD_right ldatum_sub_one hφ hx
  have iL1 := integrable_hIntD_left ldatum_sub_one hφ hx
  set A := ∫ y : ℝ, hIntD zetaF φ x (((3 / 2 : ℝ) : ℂ) + y * I) with hA
  set A1 := ∫ y : ℝ, hIntD (fun s : ℂ => s - 1) φ x (((3 / 2 : ℝ) : ℂ) + y * I) with hA1
  set Bv := ∫ y : ℝ, hIntD zetaF φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hBv
  set B1v := ∫ y : ℝ, hIntD (fun s : ℂ => s - 1) φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hB1v
  have IR : ∫ y : ℝ, hZeta φ x (((3 / 2 : ℝ) : ℂ) + y * I) = A - A1 := by
    rw [hA, hA1, ← integral_sub iR iR1]
    congr 1; ext y; rw [hIntD_zetaF_eq φ x (hR1 y) (hRz y)]; ring
  have IL : ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) = Bv - B1v := by
    rw [hBv, hB1v, ← integral_sub iL iL1]
    congr 1; ext y; rw [hIntD_zetaF_eq φ x (hL1 y) (hLz y)]; ring
  -- the Dirichlet series on `ℜs = 3/2`
  have hS := SsumG_eq_line (1 : DirichletCharacter ℂ 1) hφ hx
  have hF : ∀ t : ℝ, Fline (1 : DirichletCharacter ℂ 1) φ x (((3 / 2 : ℝ) : ℂ) + t * I) =
      -hZeta φ x (((3 / 2 : ℝ) : ℂ) + t * I) := by
    intro t
    rw [Fline, hZeta, LFunction_one_mod_one, logDeriv_apply]; ring
  simp_rw [hF, integral_neg, IR] at hS
  convert hlim using 2
  rw [hM1, hS, IL]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

end TernaryGoldbach.Explicit
