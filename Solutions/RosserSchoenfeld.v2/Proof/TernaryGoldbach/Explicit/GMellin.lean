import TernaryGoldbach.Explicit.MellinRotate
import Mathlib.Analysis.MellinInversion

/-!
# `G_δ(s)` as a Mellin transform: holomorphy and a uniform bound on `−1/2 ≤ ℜs ≤ 3/2`

`fδ δ t = t² e^{−t²/2} e(δt)`; `mellin (fδ δ) = G_δ = Gr · δ 0`. It is holomorphic on `ℜs > −2`
(Mathlib's `mellin_differentiableAt_of_isBigO_rpow_exp`), and on `−1/2 ≤ ℜs ≤ 3/2`
`|G_δ(s)| ≤ K_δ e^{−0.28|ℑs|}` with `K_δ = ∫₀^∞ (r^{1/2} + r^{5/2}) e^{−cos(0.56) r²/2 + 2π|δ| sin(0.28) r} dr`
(the rotation `t = re^{±0.28i}`).
-/

open Complex MeasureTheory Set Filter Asymptotics
open scoped Real Topology

namespace TernaryGoldbach.Explicit

/-- `t² e^{−t²/2} e(δt)`. -/
noncomputable def fδ (δ t : ℝ) : ℂ :=
  ((t ^ 2 * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * cexp (2 * π * I * δ * t)

theorem mellin_fδ (δ : ℝ) (s : ℂ) : mellin (fδ δ) s = Gr s δ 0 := by
  rw [Gr_zero_eq, mellin]
  rfl

theorem norm_fδ (δ t : ℝ) : ‖fδ δ t‖ = t ^ 2 * Real.exp (-t ^ 2 / 2) := by
  rw [fδ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : ‖cexp (2 * π * I * δ * t)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [this, mul_one]

theorem continuous_fδ (δ : ℝ) : Continuous (fδ δ) := by
  unfold fδ; fun_prop

theorem fδ_isBigO_top (δ : ℝ) : fδ δ =O[atTop] fun t => Real.exp (-1 * t) := by
  refine Asymptotics.IsBigO.of_bound (Real.exp 4) ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [norm_fδ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  -- `t² e^{−t²/2} ≤ e^4 e^{−t}`: `t² ≤ e^t` and `−t²/2 + 2t ≤ 2`
  have h1 : t ^ 2 ≤ 2 * Real.exp t := by
    have := Real.quadratic_le_exp_of_nonneg ht
    nlinarith [Real.exp_pos t]
  have h2 : Real.exp t * Real.exp (-t ^ 2 / 2) ≤ Real.exp 2 * Real.exp (-1 * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (t - 2)])
  have h3 : 2 * Real.exp 2 ≤ Real.exp 4 := by
    have : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    rw [this]
    have := Real.add_one_le_exp (2:ℝ)
    nlinarith [Real.exp_pos 2]
  calc t ^ 2 * Real.exp (-t ^ 2 / 2) ≤ 2 * Real.exp t * Real.exp (-t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 * (Real.exp t * Real.exp (-t ^ 2 / 2)) := by ring
    _ ≤ 2 * (Real.exp 2 * Real.exp (-1 * t)) := by gcongr
    _ = 2 * Real.exp 2 * Real.exp (-1 * t) := by ring
    _ ≤ Real.exp 4 * Real.exp (-1 * t) := by gcongr

theorem fδ_isBigO_bot (δ : ℝ) : fδ δ =O[𝓝[>] 0] fun t : ℝ => t ^ (-(-2 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [norm_fδ, neg_neg, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _), one_mul,
    Real.rpow_two]
  have : Real.exp (-t ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  nlinarith [sq_nonneg t]

/-- `G_δ` is holomorphic on `ℜs > −2`. -/
theorem differentiableAt_G (δ : ℝ) {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ (fun s => Gr s δ 0) s := by
  have h := mellin_differentiableAt_of_isBigO_rpow_exp (f := fδ δ) (a := 1) (b := -2) one_pos
    ((continuous_fδ δ).locallyIntegrable.locallyIntegrableOn _) (fδ_isBigO_top δ) (fδ_isBigO_bot δ) hs
  have e : mellin (fδ δ) = fun s => Gr s δ 0 := funext (mellin_fδ δ)
  rwa [e] at h

/-- The constant `K_δ`. -/
noncomputable def Kδ (δ : ℝ) : ℝ :=
  ∫ r in Ioi (0:ℝ), (r ^ (1 / 2 : ℝ) + r ^ (5 / 2 : ℝ)) *
    Real.exp (-(Real.cos (2 * 0.28) / 2) * r ^ 2 + (2 * π * |δ| * |Real.sin 0.28|) * r)

theorem cos_056_pos : 0 < Real.cos (2 * 0.28) / 2 := by
  have := Real.cos_pos_of_mem_Ioo (x := 2 * 0.28) ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  positivity

/-- **`|G_δ(s)| ≤ K_δ e^{−0.28|ℑs|}`** on `−1/2 ≤ ℜs ≤ 3/2`. -/
theorem norm_G_le_strip (δ : ℝ) {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    ‖Gr s δ 0‖ ≤ Kδ δ * Real.exp (-(0.28 * |s.im|)) := by
  set θ : ℝ := if 0 ≤ s.im then 0.28 else -0.28 with hθ
  have habs : |θ| = 0.28 := by rw [hθ]; split_ifs <;> norm_num
  have hθ4 : |θ| < π / 4 := by rw [habs]; linarith [Real.pi_gt_three]
  have hsg : 0 ≤ θ * s.im := by
    rw [hθ]; split_ifs with h
    · exact mul_nonneg (by norm_num) h
    · push Not at h; nlinarith
  have hcos : Real.cos (2 * θ) = Real.cos (2 * 0.28) := by
    rw [hθ]; split_ifs
    · rfl
    · rw [show (2:ℝ) * -0.28 = -(2 * 0.28) by ring, Real.cos_neg]
  have hsin : |Real.sin θ| = |Real.sin 0.28| := by
    rw [hθ]; split_ifs
    · rfl
    · rw [Real.sin_neg, abs_neg]
  have h := norm_Gr_le s δ hθ4 (by linarith) hsg
  rw [habs, hcos, hsin] at h
  refine h.trans ?_
  rw [mul_comm (Kδ δ)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hc := cos_056_pos
  have hi1 := integrableOn_rpow_mul_exp_quad (p := 1 / 2) (b := 2 * π * |δ| * |Real.sin 0.28|)
    (by norm_num) hc
  have hi2 := integrableOn_rpow_mul_exp_quad (p := 5 / 2) (b := 2 * π * |δ| * |Real.sin 0.28|)
    (by norm_num) hc
  have hi : IntegrableOn (fun r : ℝ => (r ^ (1 / 2 : ℝ) + r ^ (5 / 2 : ℝ)) *
      Real.exp (-(Real.cos (2 * 0.28) / 2) * r ^ 2 + (2 * π * |δ| * |Real.sin 0.28|) * r)) (Ioi 0) := by
    have := hi1.add hi2
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  refine setIntegral_mono_on (integrableOn_rpow_mul_exp_quad (by linarith) hc) hi measurableSet_Ioi
    fun r hr => ?_
  have hr' : (0:ℝ) < r := hr
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rcases le_total r 1 with hr1 | hr1
  · have := Real.rpow_le_rpow_of_exponent_ge hr' hr1 (show (1 / 2 : ℝ) ≤ s.re + 1 by linarith)
    have := Real.rpow_nonneg hr'.le (5 / 2 : ℝ)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le hr1 (show s.re + 1 ≤ 5 / 2 by linarith)
    have := Real.rpow_nonneg hr'.le (1 / 2 : ℝ)
    linarith

end TernaryGoldbach.Explicit
