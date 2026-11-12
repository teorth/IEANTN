import TernaryGoldbach.Explicit.ExplicitFormula

/-!
# The explicit formula for an abstract `L`-datum

`LDatum f B D C_R`: `f` entire, `0.355 ≤ |f(2 + iT)| < B(T)`, `|f| ≤ B(T)` on `|w − (2 + iT)| ≤ 10`,
`B ≥ 1` monotone in `|T|` with `log(B(T)/0.355) ≤ D + 37 + 2.6|T|`, no zeros in `−1 < ℜs < 0` or `ℜs > 1`,
and `|f'/f| ≤ C_R` on `ℜs = 3/2`. Examples: `L(s, χ)` (`χ` primitive, `≠ 1`) and `(s − 1)ζ(s)`.
The good heights, the rectangle identity and the limit (`ExplicitFormula`) carry over verbatim; the
conclusion `explicit_formulaD` keeps both vertical lines (the Dirichlet series step depends on `f`).
-/

open Complex MeasureTheory Set Filter Asymptotics Metric
open scoped Real Topology ArithmeticFunction.vonMangoldt Interval

namespace TernaryGoldbach.Explicit

/-- The analytic inputs of the explicit formula for an entire function `f`. -/
structure LDatum (f : ℂ → ℂ) (B : ℝ → ℝ) (D CR : ℝ) : Prop where
  diff : Differentiable ℂ f
  center_ge : ∀ T : ℝ, 0.355 ≤ ‖f (2 + T * I)‖
  center_lt : ∀ T : ℝ, ‖f (2 + T * I)‖ < B T
  bound : ∀ T : ℝ, ∀ w ∈ closedBall (2 + T * I) 10, ‖f w‖ ≤ B T
  B_ge : ∀ T : ℝ, 1 ≤ B T
  B_mono : ∀ T T' : ℝ, |T| ≤ |T'| → B T ≤ B T'
  logB_lin : ∀ T : ℝ, Real.log (B T / 0.355) ≤ D + 37 + 2.6 * |T|
  D_nonneg : 0 ≤ D
  nz_strip : ∀ s : ℂ, -1 < s.re → s.re < 0 → f s ≠ 0
  nz_right : ∀ s : ℂ, 1 < s.re → f s ≠ 0
  right_bound : ∀ y : ℝ, ‖logDeriv f (((3 / 2 : ℝ) : ℂ) + y * I)‖ ≤ CR

theorem LB_monoD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {T T' : ℝ}
    (h : |T| ≤ |T'|) : Real.log (B T / 0.355) ≤ Real.log (B T' / 0.355) := by
  have hB := hd.B_ge T
  exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (hd.B_mono T T' h) (by norm_num))

/-- **Landau** for `f` at `c = 2 + iT`, `R = 10`. -/
theorem logDeriv_nearD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {T : ℝ} {z : ℂ} (hz : z ∈ closedBall (2 + T * I) (10 / 4))
    (hLz : f z ≠ 0) :
    ‖logDeriv f z - ∑ u ∈ zerosIn f (2 + T * I) 10 (10 / 2),
        ((divB f (2 + T * I) 10 u).toNat : ℂ) / (z - u)‖ ≤
      4.8 * Real.log (B T / 0.355) := by
  have hc := hd.center_ge T
  have hc0 : f (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := hd.B_ge T
  have hcB : ‖f (2 + T * I)‖ < B T := hd.center_lt T
  have h := landau (hd.diff) hc0 (by norm_num : (0:ℝ) < 10)
    (fun w hw => hd.bound _ _ hw) hcB hz hLz
  refine h.trans ?_
  have hpos : 0 < B T / ‖f (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (B T / ‖f (2 + T * I)‖) ≤ Real.log (B T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  calc 48 * Real.log (B T / ‖f (2 + T * I)‖) / 10
      = 4.8 * Real.log (B T / ‖f (2 + T * I)‖) := by ring
    _ ≤ 4.8 * Real.log (B T / 0.355) := by gcongr


/-- **Zero count** in `|ρ − (2 + iT)| ≤ 5`: at most `log(B_T/0.355)/log 2`. -/
theorem zero_count_5D {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) (T : ℝ) :
    ((∑ᶠ u, MeromorphicOn.divisor f (closedBall (2 + T * I) |(5 : ℝ)|) u : ℤ) : ℝ) ≤
      Real.log (B T / 0.355) / Real.log 2 := by
  have hc := hd.center_ge T
  have hc0 : f (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := hd.B_ge T
  have hf : AnalyticOnNhd ℂ f (closedBall (2 + T * I) |(10 : ℝ)|) := fun z _ =>
    (hd.diff).analyticAt z
  have h := hf.sum_divisor_le (r := 5) (R := 10) (by norm_num) (by norm_num) (by linarith) hc0
    (fun w hw => hd.bound _ _ (sphere_subset_closedBall (by
      rwa [abs_of_pos (by norm_num : (0:ℝ) < 10)] at hw)))
  refine h.trans ?_
  have hpos : 0 < B T / ‖f (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (B T / ‖f (2 + T * I)‖) ≤ Real.log (B T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  rw [show (10:ℝ) / 5 = 2 by norm_num]
  exact div_le_div_of_nonneg_right hle (Real.log_nonneg (by norm_num))


/-- The zeros strictly inside the rectangle `[−1/2, 3/2] × [−T, T]`, with multiplicity. -/
noncomputable def zerosRectD (f : ℂ → ℂ) (T : ℝ) : Finset ℂ :=
  (zerosIn f 2 (RT T) (RT T / 2)).filter
    (fun u => (zT T).re < u.re ∧ u.re < (wT T).re ∧ (zT T).im < u.im ∧ u.im < (wT T).im)

noncomputable def multRectD (f : ℂ → ℂ) (T : ℝ) (u : ℂ) : ℕ :=
  (divB f 2 (RT T) u).toNat


/-- **Part B**: the residue theorem on `[−1/2, 3/2] × [−T, T]`, if `L` has no zeros on the horizontal
sides. -/
theorem rect_identityD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {φ : ℝ → ℂ} {K c : ℝ} (hφ : GoodSmoothing φ K c) {x : ℝ} (hx : 0 < x) {T : ℝ}
    (hT : 0 < T)
    (hbot : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (htop : ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]], f ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0) :
    rectInt (fun s => logDeriv f s * (mellin φ s * (x : ℂ) ^ s)) (zT T) (wT T) =
      2 * π * I * ∑ u ∈ zerosRectD f T, (multRectD f T u : ℂ) * (mellin φ u * (x : ℂ) ^ u) := by
  have hf : Differentiable ℂ f := hd.diff
  have hf2 : f 2 ≠ 0 :=
    hd.nz_right _ (by norm_num)
  have hR : 0 < RT T := by unfold RT; linarith
  have hrect : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆ Metric.ball 2 (RT T / 2) := by
    intro s hs
    rw [mem_reProdIm, zT_re, wT_re, zT_im, wT_im, Set.uIcc_of_le (by norm_num),
      Set.uIcc_of_le (by linarith)] at hs
    rw [Metric.mem_ball, dist_eq_norm, RT]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero]
    have h1 : |s.re - 2| ≤ 5 / 2 := by rw [abs_le]; constructor <;> linarith [hs.1.1, hs.1.2]
    have h2 : |s.im| ≤ T := by rw [abs_le]; constructor <;> linarith [hs.2.1, hs.2.2]
    linarith
  have hbd : NoZerosOnSides f (zT T) (wT T) := by
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_, fun y _ => ?_, fun y _ => ?_⟩
    · rw [zT_re, wT_re] at hσ; simpa using hbot σ hσ
    · rw [zT_re, wT_re] at hσ; simpa using htop σ hσ
    · exact hd.nz_right _ (by simp; norm_num)
    · exact hd.nz_strip _ (by simp; norm_num) (by simp; norm_num)
  set U : Set ℂ := {s | -1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsubU : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆ U := by
    intro s hs
    rw [mem_reProdIm, zT_re, wT_re, Set.uIcc_of_le (by norm_num)] at hs
    show -1 < s.re; linarith [hs.1.1]
  have hh : DifferentiableOn ℂ (fun s => mellin φ s * (x : ℂ) ^ s) U := by
    intro s hs
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact ((hφ.diff s hs).mul
      (differentiableAt_id.const_cpow (Or.inl hx0))).differentiableWithinAt
  exact rectInt_logDeriv_mul hf hR hf2 (by simp; norm_num) (by simp; linarith) hrect hbd hUo hsubU hh


/-- **`L'/L` on a horizontal segment**: if `z` (with `|z − (2 + iT)| ≤ 5/2`) is at distance `≥ δ` from
every zero `u` with `|u − (2 + iT)| < 5`, then
`|L'/L(z)| ≤ (log(B_T/0.355)/log 2)/δ + 4.8 log(B_T/0.355)`. -/
theorem norm_logDeriv_leD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {T : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall (2 + T * I) (10 / 4)) {δ : ℝ}
    (hδ : 0 < δ) (hfar : ∀ u ∈ zerosIn f (2 + T * I) 10 (10 / 2), δ ≤ ‖z - u‖)
    (hLz : f z ≠ 0) :
    ‖logDeriv f z‖ ≤
      Real.log (B T / 0.355) / Real.log 2 / δ + 4.8 * Real.log (B T / 0.355) := by
  have hf := hd.diff
  have h1 := logDeriv_nearD hd hz hLz
  set Z := zerosIn f (2 + T * I) 10 (10 / 2)
  have hsum : ‖∑ u ∈ Z, ((divB f (2 + T * I) 10 u).toNat : ℂ) / (z - u)‖ ≤
      (∑ u ∈ Z, (divB f (2 + T * I) 10 u).toNat : ℕ) / δ := by
    refine (norm_sum_le _ _).trans ?_
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun u hu => ?_
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (by positivity) hδ (hfar u hu)
  have hcnt := sum_zerosIn_le hf (c := 2 + T * I) (R := 10) (r := 10 / 2) (by norm_num) (by norm_num)
  have h5 := zero_count_5D hd T
  rw [show (10 : ℝ) / 2 = 5 by norm_num] at hcnt
  have hcnt' : ((∑ u ∈ Z, (divB f (2 + T * I) 10 u).toNat : ℕ) : ℝ) ≤
      Real.log (B T / 0.355) / Real.log 2 := by
    have : Z = zerosIn f (2 + T * I) 10 5 := by
      simp only [Z]; norm_num
    rw [this]; exact hcnt.trans h5
  calc ‖logDeriv f z‖
      ≤ ‖∑ u ∈ Z, ((divB f (2 + T * I) 10 u).toNat : ℂ) / (z - u)‖ +
          ‖logDeriv f z - ∑ u ∈ Z, ((divB f (2 + T * I) 10 u).toNat : ℂ) / (z - u)‖ := by
        have := norm_add_le (∑ u ∈ Z, ((divB f (2 + T * I) 10 u).toNat : ℂ) / (z - u))
          (logDeriv f z - ∑ u ∈ Z, ((divB f (2 + T * I) 10 u).toNat : ℂ) / (z - u))
        rwa [add_sub_cancel] at this
    _ ≤ Real.log (B T / 0.355) / Real.log 2 / δ + 4.8 * Real.log (B T / 0.355) := by
        refine add_le_add (hsum.trans ?_) h1
        exact div_le_div_of_nonneg_right hcnt' hδ.le

/-- A zero of `L` near `c` lies in `zerosIn`. -/
theorem mem_zerosIn_of_zeroD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {c u : ℂ}
    {R r : ℝ} (hrR : r ≤ R) (hu : ‖u - c‖ < r) (hLu : f u = 0) :
    u ∈ zerosIn f c R r := by
  have hf := hd.diff
  have huR : u ∈ Metric.closedBall c R := by
    rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  rw [zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support]
  refine ⟨?_, hu⟩
  rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (Metric.closedBall c R)) huR]
  intro h
  have hord : analyticOrderAt f u ≠ 0 := by
    rw [Ne, (hf.analyticAt u).analyticOrderAt_eq_zero]; exact not_not.2 hLu
  have hfin : analyticOrderAt f u ≠ ⊤ := by
    have h2 : f 2 ≠ 0 :=
      hd.nz_right _ (by norm_num)
    have hc0 : analyticOrderAt f 2 ≠ ⊤ := by
      rw [(hf.analyticAt 2).analyticOrderAt_eq_zero.2 h2]; simp
    exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f Set.univ)
      isPreconnected_univ (Set.mem_univ 2) (Set.mem_univ u) hc0
  apply hord
  revert h
  cases hk : analyticOrderAt f u with
  | top => exact absurd hk hfin
  | coe n => simp


/-- **`L'/L` on the line `ℜs = −1/2`**: `|L'/L(−1/2 + iy)| ≤ (2/log 2 + 4.8) log(B_y/0.355)`. -/
theorem norm_logDeriv_leftD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) (y : ℝ) :
    ‖logDeriv f (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤
      Real.log (B y / 0.355) / Real.log 2 / (1 / 2) + 4.8 * Real.log (B y / 0.355) := by
  set z : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hz
  have hzc : z ∈ Metric.closedBall (2 + y * I) (10 / 4) := by
    rw [Metric.mem_closedBall, dist_eq_norm, hz]
    have : ((-1 / 2 : ℝ) : ℂ) + y * I - (2 + y * I) = ((-5 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hLz : f z ≠ 0 := hd.nz_strip _ (by simp [hz]; norm_num)
    (by simp [hz]; norm_num)
  refine norm_logDeriv_leD hd hzc (by norm_num) (fun u hu => ?_) hLz
  have hLu : f u = 0 := by
    have hf := hd.diff
    obtain ⟨hur, hu0⟩ := mem_zerosIn hu
    have huR : u ∈ Metric.closedBall (2 + y * I) 10 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (Metric.closedBall _ 10)) huR] at hu0
    by_contra hne
    exact hu0 (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)
  have hre : u.re ≤ -1 ∨ 0 ≤ u.re := by
    by_contra hcon
    push Not at hcon
    exact hd.nz_strip _ hcon.1 hcon.2 hLu
  have := Complex.abs_re_le_norm (z - u)
  have hzre : z.re = -1 / 2 := by simp [hz]
  rw [Complex.sub_re, hzre] at this
  rcases hre with h | h
  · rw [abs_of_nonneg (by linarith)] at this; linarith
  · rw [abs_of_nonpos (by linarith)] at this; linarith

/-- Jensen with radii `r < 10`: at most `log(B_T/0.355)/log(10/r)` zeros in `|ρ − (2 + iT)| ≤ r`. -/
theorem zero_count_rD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) (T : ℝ) {r : ℝ} (hr : 0 < r) (hr10 : r < 10) :
    ((∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (2 + T * I) |r|) u : ℤ) : ℝ) ≤
      Real.log (B T / 0.355) / Real.log (10 / r) := by
  have hc := hd.center_ge T
  have hc0 : f (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := hd.B_ge T
  have hf : AnalyticOnNhd ℂ f (Metric.closedBall (2 + T * I) |(10 : ℝ)|) := fun z _ =>
    (hd.diff).analyticAt z
  have h := hf.sum_divisor_le (r := r) (R := 10) (by rw [abs_of_pos hr]; exact hr)
    (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0:ℝ) < 10)]; exact hr10) (by linarith) hc0
    (fun w hw => hd.bound _ _ (Metric.sphere_subset_closedBall (by
      rwa [abs_of_pos (by norm_num : (0:ℝ) < 10)] at hw)))
  refine h.trans ?_
  have hpos : 0 < B T / ‖f (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (B T / ‖f (2 + T * I)‖) ≤ Real.log (B T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  exact div_le_div_of_nonneg_right hle (Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith))


/-- The height bound: `H_k = log(B_{k+1}/0.355)·((2A_k + 2)/log 2 + 4.8)`,
`A_k = 2 log(B_{k+1}/0.355)/log(10/6)`. -/
noncomputable def HkD (B : ℝ → ℝ) (k : ℕ) : ℝ :=
  Real.log (B (k + 1) / 0.355) *
    ((2 * (2 * Real.log (B (k + 1) / 0.355) / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8)

/-- **Good heights**: in `[k, k+1]` there is `T` such that `L` has no zeros on the horizontal sides
`ℑs = ±T`, `−1/2 ≤ ℜs ≤ 3/2`, and `|L'/L| ≤ H_k` there. -/
theorem good_heightD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) (k : ℕ) :
    ∃ T ∈ Icc (k : ℝ) (k + 1), ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]],
      (f ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0 ∧
        f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
      (‖logDeriv f ((σ : ℂ) + ((T : ℝ) : ℂ) * I)‖ ≤ HkD B k ∧
        ‖logDeriv f ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ HkD B k) := by
  have hf := hd.diff
  set k' : ℝ := k + 1 / 2 with hk'
  set Wp := zerosIn f (2 + (k' : ℂ) * I) 12 6 with hWp
  set Wm := zerosIn f (2 + ((-k' : ℝ) : ℂ) * I) 12 6 with hWm
  set A : Finset ℝ := Wp.image Complex.im ∪ Wm.image (fun u => -u.im) with hA
  set LBk := Real.log (B (k + 1) / 0.355) with hLBk
  have hLB0 : 0 < LBk := by
    have := hd.B_ge ((k : ℝ) + 1)
    exact Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have hlog106 : 0 < Real.log (10 / 6) := Real.log_pos (by norm_num)
  -- `|A| ≤ A_k`
  have hcardW : ∀ (T0 : ℝ), |T0| ≤ (k : ℝ) + 1 →
      ((zerosIn f (2 + (T0 : ℂ) * I) 12 6).card : ℝ) ≤ LBk / Real.log (10 / 6) := by
    intro T0 hT0
    refine (card_zerosIn_le hf).trans ?_
    refine (sum_zerosIn_le hf (by norm_num) (by norm_num)).trans ?_
    refine (zero_count_rD hd T0 (by norm_num) (by norm_num)).trans ?_
    exact div_le_div_of_nonneg_right (LB_monoD hd (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ k + 1)]; exact hT0))
      hlog106.le
  have hk'abs : |k'| ≤ (k : ℝ) + 1 := by rw [hk', abs_of_nonneg (by positivity)]; linarith
  have hAcard : (A.card : ℝ) ≤ 2 * LBk / Real.log (10 / 6) := by
    have h1 : (A.card : ℝ) ≤ Wp.card + Wm.card := by
      have := Finset.card_union_le (Wp.image Complex.im) (Wm.image (fun u => -u.im))
      have h2 := Finset.card_image_le (s := Wp) (f := Complex.im)
      have h3 := Finset.card_image_le (s := Wm) (f := fun u : ℂ => -u.im)
      exact_mod_cast this.trans (add_le_add h2 h3)
    have hp : (Wp.card : ℝ) ≤ LBk / Real.log (10 / 6) := hcardW k' hk'abs
    have hm : (Wm.card : ℝ) ≤ LBk / Real.log (10 / 6) := hcardW (-k') (by rw [abs_neg]; exact hk'abs)
    have : (2 * LBk / Real.log (10 / 6)) = LBk / Real.log (10 / 6) + LBk / Real.log (10 / 6) := by ring
    linarith
  obtain ⟨T, hT, hfar⟩ := exists_far_point A k
  set δ := 1 / (2 * (A.card : ℝ) + 2) with hδ
  have hδ0 : 0 < δ := by positivity
  set δk := 1 / (2 * (2 * LBk / Real.log (10 / 6)) + 2) with hδk
  have hδkδ : δk ≤ δ := by
    rw [hδk, hδ]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hδk0 : 0 < δk := by positivity
  have hTabs : |T| ≤ (k : ℝ) + 1 := by rw [abs_of_nonneg (by linarith [hT.1])]; exact hT.2
  refine ⟨T, hT, fun σ hσ => ?_⟩
  rw [Set.uIcc_of_le (by norm_num)] at hσ
  -- the two points
  have key : ∀ (S : ℝ), (S = T ∨ S = -T) →
      (∀ u ∈ zerosIn f (2 + (S : ℂ) * I) 10 (10 / 2), δ ≤ ‖((σ : ℂ) + (S : ℂ) * I) - u‖) := by
    intro S hS u hu
    have hLu : f u = 0 := by
      obtain ⟨hur, hu0⟩ := mem_zerosIn hu
      have huR : u ∈ Metric.closedBall (2 + (S : ℂ) * I) 10 := by
        rw [Metric.mem_closedBall, dist_eq_norm]; linarith
      rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
        (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (Metric.closedBall _ 10)) huR] at hu0
      by_contra hne
      exact hu0 (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)
    have hur := (mem_zerosIn hu).1
    have him := Complex.abs_im_le_norm (((σ : ℂ) + (S : ℂ) * I) - u)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_add, add_zero] at him
    rcases hS with hS | hS <;> subst S
    · -- `u ∈ Wp`, so `u.im ∈ A`
      have huW : u ∈ Wp := by
        refine mem_zerosIn_of_zeroD hd (by norm_num) ?_ hLu
        have : ‖u - (2 + (k' : ℂ) * I)‖ ≤ ‖u - (2 + (T : ℂ) * I)‖ + ‖((T - k' : ℝ) : ℂ) * I‖ := by
          calc ‖u - (2 + (k' : ℂ) * I)‖ = ‖(u - (2 + (T : ℂ) * I)) + ((T - k' : ℝ) : ℂ) * I‖ := by
                congr 1; push_cast; ring
            _ ≤ _ := norm_add_le _ _
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
        have hTk : |T - k'| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
        rw [show (10:ℝ) / 2 = 5 by norm_num] at hur
        linarith
      have := hfar u.im (Finset.mem_union_left _ (Finset.mem_image_of_mem _ huW))
      linarith
    · have huW : u ∈ Wm := by
        refine mem_zerosIn_of_zeroD hd (by norm_num) ?_ hLu
        have : ‖u - (2 + ((-k' : ℝ) : ℂ) * I)‖ ≤ ‖u - (2 + ((-T : ℝ) : ℂ) * I)‖ +
            ‖((k' - T : ℝ) : ℂ) * I‖ := by
          calc ‖u - (2 + ((-k' : ℝ) : ℂ) * I)‖ =
              ‖(u - (2 + ((-T : ℝ) : ℂ) * I)) + ((k' - T : ℝ) : ℂ) * I‖ := by
                congr 1; push_cast; ring
            _ ≤ _ := norm_add_le _ _
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at this
        have hTk : |k' - T| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hT.1, hT.2]
        rw [show (10:ℝ) / 2 = 5 by norm_num] at hur
        linarith
      have := hfar (-u.im) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ huW))
      rw [show T - -u.im = -(-T - u.im) by ring, abs_neg] at this
      linarith
  have hz : ∀ (S : ℝ), (S = T ∨ S = -T) →
      ((σ : ℂ) + (S : ℂ) * I) ∈ Metric.closedBall (2 + (S : ℂ) * I) (10 / 4) := by
    intro S _
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : (σ : ℂ) + (S : ℂ) * I - (2 + (S : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ.1, hσ.2]
  have hne : ∀ (S : ℝ), (S = T ∨ S = -T) → f ((σ : ℂ) + (S : ℂ) * I) ≠ 0 := by
    intro S hS h0
    have hmem : ((σ : ℂ) + (S : ℂ) * I) ∈ zerosIn f (2 + (S : ℂ) * I) 10 (10 / 2) := by
      refine mem_zerosIn_of_zeroD hd (by norm_num) ?_ h0
      have := hz S hS
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      linarith
    have := key S hS _ hmem
    rw [sub_self, norm_zero] at this
    linarith
  have hbound : ∀ (S : ℝ), (S = T ∨ S = -T) →
      ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ ≤ HkD B k := by
    intro S hS
    have habs : |S| ≤ (k : ℝ) + 1 := by rcases hS with hS | hS <;> subst S <;> simp [hTabs]
    refine (norm_logDeriv_leD hd (hz S hS) hδ0 (key S hS) (hne S hS)).trans ?_
    have hLB := LB_monoD hd (T := S) (T' := (k : ℝ) + 1)
      (by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ k + 1)]; exact habs)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLBS0 : 0 ≤ Real.log (B S / 0.355) := by
      have := hd.B_ge S
      exact Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
    unfold HkD
    rw [← hLBk] at hLB ⊢
    have h1 : Real.log (B S / 0.355) / Real.log 2 / δ ≤ LBk / Real.log 2 / δk := by
      gcongr
    have h2 : LBk / Real.log 2 / δk = LBk * ((2 * (2 * LBk / Real.log (10 / 6)) + 2) / Real.log 2) := by
      rw [hδk]; field_simp
    nlinarith
  exact ⟨⟨hne T (Or.inl rfl), hne (-T) (Or.inr rfl)⟩, hbound T (Or.inl rfl), hbound (-T) (Or.inr rfl)⟩


/-- `h(s) = L'/L(s) M(s) x^s` (the integrand of the residue theorem). -/
noncomputable def hIntD (f : ℂ → ℂ) (φ : ℝ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  logDeriv f s * (mellin φ s * (x : ℂ) ^ s)


theorem continuous_logDeriv_lineD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR)
    (σ : ℝ) (hne : ∀ y : ℝ, f ((σ : ℂ) + y * I) ≠ 0) :
    Continuous fun y : ℝ => logDeriv f ((σ : ℂ) + y * I) := by
  have hf := hd.diff
  have hd : Continuous (deriv f) :=
    continuous_iff_continuousAt.2 fun z => (hf.analyticAt z).deriv.continuousAt
  have e : (fun y : ℝ => logDeriv f ((σ : ℂ) + y * I)) =
      fun y : ℝ => deriv f ((σ : ℂ) + y * I) / f ((σ : ℂ) + y * I) := by
    ext y; rw [logDeriv_apply]
  rw [e]
  exact (hd.comp (by fun_prop)).div (hf.continuous.comp (by fun_prop)) hne

/-- `h` is integrable on `ℜs = 3/2`. -/
theorem integrable_hIntD_right {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR)
    {φ : ℝ → ℂ} {K c : ℝ} (hφ : GoodSmoothing φ K c) {x : ℝ} (hx : 0 < x) :
    Integrable fun y : ℝ => hIntD f φ x (((3 / 2 : ℝ) : ℂ) + y * I) := by
  have hGi := hφ.integrable_line (σ := 3 / 2) (by norm_num) le_rfl
  have hc : Continuous fun y : ℝ => hIntD f φ x (((3 / 2 : ℝ) : ℂ) + y * I) := by
    unfold hIntD
    refine (continuous_logDeriv_lineD hd (3 / 2) fun y =>
      hd.nz_right _ (by simp; norm_num)).mul
      ((hφ.continuous_line (σ := 3 / 2) (by norm_num)).mul ?_)
    exact continuous_iff_continuousAt.2 fun y =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  refine (hGi.norm.const_mul (CR * x ^ (3 / 2 : ℝ))).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [hIntD, norm_mul, norm_mul, norm_cpow_x hx]
  have h1 := hd.right_bound y
  have hre : (((3 / 2 : ℝ) : ℂ) + y * I).re = 3 / 2 := by simp
  rw [hre]
  have hx0 : 0 ≤ x ^ (3 / 2 : ℝ) := by positivity
  calc ‖logDeriv f (((3 / 2 : ℝ) : ℂ) + y * I)‖ *
        (‖mellin φ (((3 / 2 : ℝ) : ℂ) + y * I)‖ * x ^ (3 / 2 : ℝ))
      ≤ CR * (‖mellin φ (((3 / 2 : ℝ) : ℂ) + y * I)‖ * x ^ (3 / 2 : ℝ)) := by gcongr
    _ = CR * x ^ (3 / 2 : ℝ) * ‖mellin φ (((3 / 2 : ℝ) : ℂ) + y * I)‖ := by ring


/-- `h` is integrable on `ℜs = −1/2`. -/
theorem integrable_hIntD_left {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {φ : ℝ → ℂ} {K c : ℝ} (hφ : GoodSmoothing φ K c) {x : ℝ} (hx : 0 < x) :
    Integrable fun y : ℝ => hIntD f φ x (((-1 / 2 : ℝ) : ℂ) + y * I) := by
  have hc : Continuous fun y : ℝ => hIntD f φ x (((-1 / 2 : ℝ) : ℂ) + y * I) := by
    unfold hIntD
    refine (continuous_logDeriv_lineD hd (-1 / 2) fun y =>
      hd.nz_strip _ (by simp; norm_num) (by simp; norm_num)).mul
      ((hφ.continuous_line (σ := -1 / 2) (by norm_num)).mul ?_)
    exact continuous_iff_continuousAt.2 fun y =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  set c1 : ℝ := 2 / Real.log 2 + 4.8 with hc1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 := hφ.c_pos
  set A : ℝ := c1 * (|D| + 37) * K * x ^ (-1 / 2 : ℝ) with hA
  set Bc : ℝ := c1 * 2.6 / (c / 2) * K * x ^ (-1 / 2 : ℝ) with hBc
  have hK : 0 ≤ K := hφ.K_nonneg
  have hint : Integrable fun y : ℝ => A * Real.exp (-(c * |y|)) + Bc * Real.exp (-(c / 2 * |y|)) :=
    ((integrable_exp_neg_abs hc0).const_mul A).add
      ((integrable_exp_neg_abs (by linarith)).const_mul Bc)
  refine hint.mono' hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [hIntD, norm_mul, norm_mul, norm_cpow_x hx]
  have hre : (((-1 / 2 : ℝ) : ℂ) + y * I).re = -1 / 2 := by simp
  have him : (((-1 / 2 : ℝ) : ℂ) + y * I).im = y := by simp
  rw [hre]
  have h1 := norm_logDeriv_leftD hd y
  have hLB := hd.logB_lin y
  have hG := hφ.strip (((-1 / 2 : ℝ) : ℂ) + y * I) (by rw [hre]) (by rw [hre]; norm_num)
  rw [him] at hG
  have hLB0 : 0 ≤ Real.log (B y / 0.355) := by
    have := hd.B_ge y
    exact Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hlogd : ‖logDeriv f (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ c1 * (|D| + 37 + 2.6 * |y|) := by
    refine h1.trans ?_
    have e : Real.log (B y / 0.355) / Real.log 2 / (1 / 2) + 4.8 * Real.log (B y / 0.355) =
        c1 * Real.log (B y / 0.355) := by rw [hc1]; field_simp
    rw [e]
    have hc10 : 0 ≤ c1 := by rw [hc1]; have := div_nonneg (by norm_num : (0:ℝ) ≤ 2) hlog2.le; linarith
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self (D)]) hc10
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := by positivity
  have hy : |y| ≤ Real.exp (c / 2 * |y|) / (c / 2) := by
    rw [le_div_iff₀ (by linarith)]
    have := Real.add_one_le_exp (c / 2 * |y|); nlinarith [abs_nonneg y]
  have hexp : Real.exp (c / 2 * |y|) * Real.exp (-(c * |y|)) = Real.exp (-(c / 2 * |y|)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc10 : 0 ≤ c1 := by rw [hc1]; have := div_nonneg (by norm_num : (0:ℝ) ≤ 2) hlog2.le; linarith
  calc ‖logDeriv f (((-1 / 2 : ℝ) : ℂ) + y * I)‖ *
        (‖mellin φ (((-1 / 2 : ℝ) : ℂ) + y * I)‖ * x ^ (-1 / 2 : ℝ))
      ≤ c1 * (|D| + 37 + 2.6 * |y|) * (K * Real.exp (-(c * |y|)) * x ^ (-1 / 2 : ℝ)) := by
        gcongr
    _ = A * Real.exp (-(c * |y|)) + c1 * 2.6 * K * x ^ (-1 / 2 : ℝ) *
          (|y| * Real.exp (-(c * |y|))) := by rw [hA]; ring
    _ ≤ A * Real.exp (-(c * |y|)) + c1 * 2.6 * K * x ^ (-1 / 2 : ℝ) *
          (Real.exp (c / 2 * |y|) / (c / 2) * Real.exp (-(c * |y|))) := by
        gcongr
    _ = A * Real.exp (-(c * |y|)) + Bc * Real.exp (-(c / 2 * |y|)) := by
        rw [hBc, ← hexp]; ring


theorem HkD_le {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) (k : ℕ) :
    HkD B k ≤ (D + 40 + 2.6 * k) * ((4 * (D + 40 + 2.6 * k) / 0.51 + 2) / 0.69 + 4.8) := by
  have hL := hd.logB_lin ((k : ℝ) + 1)
  rw [abs_of_nonneg (by positivity)] at hL
  set P := Real.log (B ((k : ℝ) + 1) / 0.355) with hP
  have hP0 : 0 ≤ P := by
    have := hd.B_ge ((k : ℝ) + 1)
    exact Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hPle : P ≤ D + 40 + 2.6 * k := by linarith
  have hl106 : 0.51 ≤ Real.log (10 / 6) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_bound' (x := 0.51) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢; linarith
  have hl2 : 0.69 ≤ Real.log 2 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_bound' (x := 0.69) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢; linarith
  unfold HkD
  rw [← hP]
  have hD := hd.D_nonneg
  have h1 : 2 * (2 * P / Real.log (10 / 6)) + 2 ≤ 4 * (D + 40 + 2.6 * k) / 0.51 + 2 := by
    have hl0 : 0 < Real.log (10 / 6) := by linarith
    have : 2 * P / Real.log (10 / 6) ≤ 2 * (D + 40 + 2.6 * k) / 0.51 :=
      calc 2 * P / Real.log (10 / 6) ≤ 2 * P / 0.51 :=
            div_le_div_of_nonneg_left (by linarith) (by norm_num) hl106
        _ ≤ 2 * (D + 40 + 2.6 * k) / 0.51 := div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have e4 : 4 * (D + 40 + 2.6 * k) / 0.51 = 2 * (2 * (D + 40 + 2.6 * k) / 0.51) := by ring
    linarith
  have h2 : (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 ≤
      (4 * (D + 40 + 2.6 * k) / 0.51 + 2) / 0.69 := by
    have h0 : 0 ≤ 2 * (2 * P / Real.log (10 / 6)) + 2 := by
      have : 0 ≤ 2 * P / Real.log (10 / 6) := div_nonneg (by linarith) (by linarith)
      linarith
    calc (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2
        ≤ (2 * (2 * P / Real.log (10 / 6)) + 2) / 0.69 := div_le_div_of_nonneg_left h0 (by norm_num) hl2
      _ ≤ _ := by gcongr
  have h3 : 0 ≤ (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8 := by
    have : 0 ≤ (2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 := by
      have : 0 ≤ 2 * P / Real.log (10 / 6) := div_nonneg (by linarith) (by linarith)
      exact div_nonneg (by linarith) (by linarith)
    linarith
  calc P * ((2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8)
      ≤ (D + 40 + 2.6 * k) * ((2 * (2 * P / Real.log (10 / 6)) + 2) / Real.log 2 + 4.8) :=
        mul_le_mul_of_nonneg_right hPle h3
    _ ≤ _ := by gcongr

theorem tendsto_HkD_exp {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => HkD B k * Real.exp (-(c * k))) atTop (𝓝 0) := by
  set a := D + 40 with ha
  have hpoly : ∀ k : ℕ, HkD B k * Real.exp (-(c * k)) ≤
      ((a + 2.6 * k) * ((4 * (a + 2.6 * k) / 0.51 + 2) / 0.69 + 4.8)) * Real.exp (-(c * k)) :=
    fun k => mul_le_mul_of_nonneg_right (HkD_le hd k) (Real.exp_pos _).le
  have hnn : ∀ k : ℕ, 0 ≤ HkD B k * Real.exp (-(c * k)) := by
    intro k
    refine mul_nonneg ?_ (Real.exp_pos _).le
    unfold HkD
    have hP0 : 0 ≤ Real.log (B ((k : ℝ) + 1) / 0.355) := by
      have := hd.B_ge ((k : ℝ) + 1)
      exact Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; linarith)
    have hl : 0 < Real.log (10 / 6) := Real.log_pos (by norm_num)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine squeeze_zero hnn hpoly ?_
  -- polynomial × exponential decay
  have hlim : ∀ n : ℕ, Tendsto (fun k : ℕ => (k : ℝ) ^ n * Real.exp (-(c * k))) atTop (𝓝 0) := by
    intro n
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
      ((tendsto_natCast_atTop_atTop).const_mul_atTop hc)
    have h' := h.const_mul ((1 / c) ^ n)
    rw [mul_zero] at h'
    refine h'.congr fun k => ?_
    simp only [Function.comp]
    rw [← mul_assoc, ← mul_pow, show (1 / c : ℝ) * (c * (k : ℝ)) = k by field_simp]
  have e : ∀ k : ℕ, ((a + 2.6 * k) * ((4 * (a + 2.6 * k) / 0.51 + 2) / 0.69 + 4.8)) * Real.exp (-(c * k)) =
      (a * ((4 * a / 0.51 + 2) / 0.69 + 4.8)) * ((k : ℝ) ^ 0 * Real.exp (-(c * k))) +
      (2.6 * ((4 * a / 0.51 + 2) / 0.69 + 4.8) + a * (4 * 2.6 / 0.51 / 0.69)) *
        ((k : ℝ) ^ 1 * Real.exp (-(c * k))) +
      (2.6 * (4 * 2.6 / 0.51 / 0.69)) * ((k : ℝ) ^ 2 * Real.exp (-(c * k))) := by
    intro k; ring
  simp_rw [e]
  have := (((hlim 0).const_mul (a * ((4 * a / 0.51 + 2) / 0.69 + 4.8))).add
    ((hlim 1).const_mul (2.6 * ((4 * a / 0.51 + 2) / 0.69 + 4.8) + a * (4 * 2.6 / 0.51 / 0.69)))).add
    ((hlim 2).const_mul (2.6 * (4 * 2.6 / 0.51 / 0.69)))
  simpa using this


set_option maxHeartbeats 1000000 in
/-- **The contour identity** for an `LDatum` `f` and an admissible smoothing `φ` (`M = mellin φ`):
along heights `T_k ∈ [k+1, k+2]`,
`Σ_{ρ ∈ (−1/2, 3/2) × (−T_k, T_k)} m_ρ M(ρ) x^ρ → (1/2π) (∫ h(3/2 + iy) dy − ∫ h(−1/2 + iy) dy)`,
`h(s) = (f'/f)(s) M(s) x^s`. -/
theorem explicit_formulaD {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ} (hd : LDatum f B D CR) {φ : ℝ → ℂ} {K c : ℝ} (hφ : GoodSmoothing φ K c) {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) * (mellin φ u * (x : ℂ) ^ u))
        atTop (𝓝 ((1 / (2 * π) : ℂ) * ((∫ y : ℝ, hIntD f φ x (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, hIntD f φ x (((-1 / 2 : ℝ) : ℂ) + y * I)))) := by
  choose T hT hgood using fun k : ℕ => good_heightD hd (k + 1)
  have hT' : ∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2) := fun k => by
    have := hT k; push_cast at this; constructor <;> linarith [this.1, this.2]
  refine ⟨T, hT', ?_⟩
  have hTpos : ∀ k, 0 < T k := fun k => by linarith [(hT' k).1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  set Rinf := ∫ y : ℝ, hIntD f φ x (((3 / 2 : ℝ) : ℂ) + y * I) with hRinf
  set Linf := ∫ y : ℝ, hIntD f φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hLinf
  set Sk := fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) * (mellin φ u * (x : ℂ) ^ u)
  set Bot := fun k => ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), hIntD f φ x ((σ : ℂ) + ((-T k : ℝ) : ℂ) * I)
  set Top := fun k => ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), hIntD f φ x ((σ : ℂ) + ((T k : ℝ) : ℂ) * I)
  set Right := fun k => ∫ y in (-T k)..(T k), hIntD f φ x (((3 / 2 : ℝ) : ℂ) + y * I)
  set Left := fun k => ∫ y in (-T k)..(T k), hIntD f φ x (((-1 / 2 : ℝ) : ℂ) + y * I)
  -- the rectangle identity, expanded
  have hrect : ∀ k, Bot k - Top k + I * Right k - I * Left k = 2 * π * I * Sk k := by
    intro k
    have h := rect_identityD hd hφ hx (hTpos k) (fun σ hσ => ((hgood k σ hσ).1).2)
      (fun σ hσ => ((hgood k σ hσ).1).1)
    rw [← h]
    unfold rectInt
    simp only [zT_re, zT_im, wT_re, wT_im, smul_eq_mul]
    rfl
  -- the horizontal sides
  have hside : ∀ k, ∀ S : ℝ, (S = T k ∨ S = -T k) →
      ‖∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), hIntD f φ x ((σ : ℂ) + (S : ℂ) * I)‖ ≤
        HkD B (k + 1) * Real.exp (-(c * ((k + 1 : ℕ) : ℝ))) * (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) *
          |(3 / 2 : ℝ) - (-1 / 2)| := by
    intro k S hS
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    have hσ' : σ ∈ [[(-1 / 2 : ℝ), 3 / 2]] := Set.uIoc_subset_uIcc hσ
    have hσ2 : -1 / 2 ≤ σ ∧ σ ≤ 3 / 2 := by
      rw [Set.uIcc_of_le (by norm_num)] at hσ'; exact hσ'
    have hb : ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ ≤ HkD B (k + 1) := by
      rcases hS with rfl | rfl
      · exact ((hgood k σ hσ').2).1
      · exact ((hgood k σ hσ').2).2
    have hS' : |S| = T k := by
      rcases hS with rfl | rfl
      · exact abs_of_pos (hTpos k)
      · rw [abs_neg]; exact abs_of_pos (hTpos k)
    have hG := hφ.strip ((σ : ℂ) + (S : ℂ) * I) (by simp; linarith) (by simp; linarith)
    have him : ((σ : ℂ) + (S : ℂ) * I).im = S := by simp
    have hre : ((σ : ℂ) + (S : ℂ) * I).re = σ := by simp
    rw [him, hS'] at hG
    have hexp : Real.exp (-(c * T k)) ≤ Real.exp (-(c * ((k + 1 : ℕ) : ℝ))) := by
      refine Real.exp_le_exp.2 ?_
      have := (hT' k).1; push_cast; nlinarith [hφ.c_pos]
    have hK : 0 ≤ K := hφ.K_nonneg
    have hxσ := rpow_le_of_mem hx hσ2.1 hσ2.2
    have hHk0 : 0 ≤ HkD B (k + 1) := le_trans (norm_nonneg _) hb
    rw [hIntD, norm_mul, norm_mul, norm_cpow_x hx, hre]
    calc ‖logDeriv f ((σ : ℂ) + (S : ℂ) * I)‖ *
          (‖mellin φ ((σ : ℂ) + (S : ℂ) * I)‖ * x ^ σ)
        ≤ HkD B (k + 1) * (K * Real.exp (-(c * ((k + 1 : ℕ) : ℝ))) *
          (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) := by
          gcongr
          exact hG.trans (mul_le_mul_of_nonneg_left hexp hK)
      _ = _ := by ring
  have hdecay : Tendsto (fun k : ℕ => HkD B (k + 1) * Real.exp (-(c * ((k + 1 : ℕ) : ℝ))) *
      (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ))) * |(3 / 2 : ℝ) - (-1 / 2)|) atTop (𝓝 0) := by
    have h := ((tendsto_HkD_exp hd hφ.c_pos).comp (tendsto_add_atTop_nat 1)).mul_const
      (K * (x ^ (3 / 2 : ℝ) + x ^ (-1 / 2 : ℝ)))
    rw [zero_mul] at h
    have h2 := h.mul_const |(3 / 2 : ℝ) - (-1 / 2)|
    rw [zero_mul] at h2
    exact h2
  have hBot : Tendsto Bot atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hside k (-T k) (Or.inr rfl)) hdecay
  have hTop : Tendsto Top atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hside k (T k) (Or.inl rfl)) hdecay
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_mono (fun k => (hT' k).1) (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hRight : Tendsto Right atTop (𝓝 Rinf) :=
    intervalIntegral_tendsto_integral (integrable_hIntD_right hd hφ hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hLeft : Tendsto Left atTop (𝓝 Linf) :=
    intervalIntegral_tendsto_integral (integrable_hIntD_left hd hφ hx)
      (tendsto_neg_atTop_atBot.comp hTtop) hTtop
  have hSk : ∀ k, Sk k = (Bot k - Top k + I * Right k - I * Left k) / (2 * π * I) := by
    intro k
    have hne : (2 * π * I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    rw [hrect k]; field_simp
  have hlim := ((((hBot.sub hTop).add (hRight.const_mul I)).sub (hLeft.const_mul I)).div_const
    (2 * π * I))
  rw [show Sk = fun k => (Bot k - Top k + I * Right k - I * Left k) / (2 * π * I) from funext hSk]
  convert hlim using 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- `L(s, χ)` (`χ` primitive, `χ ≠ 1`) is an `LDatum` with `B = B_T`, `D = D_N`, `C_R = C₃`. -/
theorem ldatum_L {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    LDatum χ.LFunction (BT N) (DN N) C3 where
  diff := DirichletCharacter.differentiable_LFunction hχ1
  center_ge := norm_L_center_ge χ
  center_lt := fun T => by
    have h1 := norm_LFunction_two_le χ (s := 2 + T * I) (by simp)
    have h2 := one_le_BT (N := N) T
    have hpi := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  bound := fun T w hw => norm_L_le_BT hχ hχ1 hw
  B_ge := fun T => le_trans (by norm_num) (one_le_BT (N := N) T)
  B_mono := fun T T' h => BT_mono h
  logB_lin := LB_le_linear
  D_nonneg := DN_nonneg N
  nz_strip := fun s h1 h2 => LFunction_ne_zero_strip hχ hχ1 h1 h2
  nz_right := fun s h => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) h.le
  right_bound := norm_logDeriv_L_right χ

end TernaryGoldbach.Explicit
