import TernaryGoldbach.Explicit.ZeroSumBound
import TernaryGoldbach.Explicit.Datum

/-!
# The sum over zeros, for an abstract datum and an abstract Mellin transform

`PolyDatum f B κ`: `f` entire, `|f(2 + iT)| ≥ 0.355`, `|f| ≤ B(T)` on `|w − (2 + iT)| ≤ 10`, `B ≥ 1`
monotone in `|T|` with `log B(T₀ + m) ≤ log B(T₀) + κm/T₀`. With a classification of the zeros in the
rectangle (`0` or `0 < ℜ < 1`), GRH up to `T₀`, and for `M` (the Mellin transform of the smoothing):
`|M(0)| ≤ G₀`, `M(1/2 + it) = F(t)` with `∫|F|² ≤ Q₁`, `∫|F'|² ≤ Q₂`, and a geometric tail bound above
`T₀`, the sum `Σ m_ρ M(ρ) x^ρ` is bounded as in `ZeroSumBound` (which is the case `L(s, χ)`, `G_δ`).
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real

namespace TernaryGoldbach.Explicit

/-- A polynomial growth datum. -/
structure PolyDatum (f : ℂ → ℂ) (B : ℝ → ℝ) (κ : ℝ) : Prop where
  diff : Differentiable ℂ f
  center_ge : ∀ T : ℝ, 0.355 ≤ ‖f (2 + T * I)‖
  bound : ∀ T : ℝ, ∀ w ∈ closedBall (2 + T * I) 10, ‖f w‖ ≤ B T
  B_ge : ∀ T : ℝ, 1 ≤ B T
  B_mono : ∀ T T' : ℝ, |T| ≤ |T'| → B T ≤ B T'
  growth : ∀ T0 m : ℝ, 0 < T0 → 0 ≤ m → Real.log (B (T0 + m) / 0.355) ≤ Real.log (B T0 / 0.355) + κ * m / T0
  κ_nonneg : 0 ≤ κ

variable {f : ℂ → ℂ} {B : ℝ → ℝ} {κ : ℝ}

theorem PolyDatum.log_pos (hp : PolyDatum f B κ) (T : ℝ) : 0 < Real.log (B T / 0.355) := by
  apply Real.log_pos; rw [lt_div_iff₀ (by norm_num)]; linarith [hp.B_ge T]

theorem PolyDatum.log_mono (hp : PolyDatum f B κ) {T T' : ℝ} (h : |T| ≤ |T'|) :
    Real.log (B T / 0.355) ≤ Real.log (B T' / 0.355) :=
  Real.log_le_log (div_pos (by linarith [hp.B_ge T]) (by norm_num))
    (div_le_div_of_nonneg_right (hp.B_mono T T' h) (by norm_num))

/-- **Jensen** for a `PolyDatum`. -/
theorem zero_count_polyG (hp : PolyDatum f B κ) (T : ℝ) {r : ℝ} (hr : 0 < r) (hr10 : r < 10) :
    ((∑ᶠ u, MeromorphicOn.divisor f (closedBall (2 + T * I) |r|) u : ℤ) : ℝ) ≤
      Real.log (B T / 0.355) / Real.log (10 / r) := by
  have hc := hp.center_ge T
  have hc0 : f (2 + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hB := hp.B_ge T
  have hf : AnalyticOnNhd ℂ f (closedBall (2 + T * I) |(10 : ℝ)|) := fun z _ => hp.diff.analyticAt z
  have h := hf.sum_divisor_le (r := r) (R := 10) (by rw [abs_of_pos hr]; exact hr)
    (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0:ℝ) < 10)]; exact hr10) (by linarith) hc0
    (fun w hw => hp.bound T w (sphere_subset_closedBall (by
      rwa [abs_of_pos (by norm_num : (0:ℝ) < 10)] at hw)))
  refine h.trans ?_
  have hBc : ‖f (2 + T * I)‖ ≤ B T := hp.bound T _ (mem_closedBall_self (by norm_num))
  have hpos : 0 < B T / ‖f (2 + T * I)‖ := div_pos (by linarith) (by linarith)
  have hle : Real.log (B T / ‖f (2 + T * I)‖) ≤ Real.log (B T / 0.355) :=
    Real.log_le_log hpos (div_le_div_of_nonneg_left (by linarith) (by norm_num) hc)
  exact div_le_div_of_nonneg_right hle (Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith))

/-- **Window count** for the zeros of the rectangle. -/
theorem sum_multRectD_le (hp : PolyDatum f B κ) {T : ℝ} (S : Finset ℂ) (hS : S ⊆ zerosRectD f T)
    (c : ℝ) {r : ℝ} (hr : 0 < r) (hr10 : r < 10) (hball : ∀ u ∈ S, ‖u - (2 + c * I)‖ ≤ r) :
    ∑ u ∈ S, (multRectD f T u : ℝ) ≤ Real.log (B c / 0.355) / Real.log (10 / r) := by
  have h1 := sum_divB_le_finsum hp.diff (c := 2) (R := RT T) (c' := 2 + c * I) (r' := r) S fun u hu => by
    have hu' := hS hu
    rw [zerosRectD, Finset.mem_filter] at hu'
    obtain ⟨hu1, -⟩ := mem_zerosIn hu'.1
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have : 0 ≤ RT T / 2 := le_trans (norm_nonneg _) hu1.le
      linarith
    · rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hr]; exact hball u hu
  have h2 := zero_count_polyG hp c hr hr10
  unfold multRectD
  push_cast at h1 ⊢
  linarith

/-- Line windows (radius `2.3`), at `T₀`. -/
noncomputable def ZLg (B : ℝ → ℝ) (T0 : ℝ) : ℝ := Real.log (B (T0 + 3.48) / 0.355) / Real.log (10 / 2.3)
/-- Tail windows (radius `3`). -/
noncomputable def Z3g (B : ℝ → ℝ) (T0 : ℝ) : ℝ := Real.log (B T0 / 0.355) / Real.log (10 / 3)
noncomputable def c3g (κ T0 : ℝ) : ℝ := κ * 4.4 / T0 / Real.log (10 / 3)

theorem count_line_windowG (hp : PolyDatum f B κ) {T T0 : ℝ} (hT0 : 0 ≤ T0) (S : Finset ℂ)
    (hS : S ⊆ zerosRectD f T) (hre : ∀ u ∈ S, u.re = 1 / 2) (him : ∀ u ∈ S, |u.im| ≤ T0) (k : ℕ) :
    ∑ u ∈ S.filter (fun u => (⌊u.im / 3.48⌋ + Jl T0).toNat = k), (multRectD f T u : ℝ) ≤ ZLg B T0 := by
  set F := S.filter (fun u => (⌊u.im / 3.48⌋ + Jl T0).toNat = k) with hF
  rcases F.eq_empty_or_nonempty with hE | ⟨u0, hu0⟩
  · rw [hE, Finset.sum_empty]
    exact div_nonneg (hp.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le
  set c := ((k : ℝ) - Jl T0 + 1 / 2) * 3.48 with hc
  have hJ := lt_Jl hT0
  have hwin : ∀ u ∈ F, |u.im - c| ≤ 1.74 := by
    intro u hu
    obtain ⟨huS, hk⟩ := Finset.mem_filter.1 hu
    have hw := mem_line_window (h := 3.48) (by norm_num) hJ (him u huS)
    rw [hk] at hw
    rw [abs_le]; constructor <;> linarith [hw.1, hw.2]
  have hball : ∀ u ∈ F, ‖u - (2 + c * I)‖ ≤ 2.3 := by
    intro u hu
    have hr := hre u (Finset.mem_filter.1 hu).1
    refine norm_le_of_re_im (a := 1.5) (b := 1.74) (by norm_num) ?_ ?_ (by norm_num)
    · simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
      rw [hr]; norm_num
    · simp only [Complex.sub_im, Complex.add_im, Complex.im_ofNat, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, zero_add]
      simpa using hwin u hu
  have h1 := sum_multRectD_le hp F ((Finset.filter_subset _ _).trans hS) c (r := 2.3)
    (by norm_num) (by norm_num) hball
  have hcT : |c| ≤ |T0 + 3.48| := by
    have h0 := hwin u0 hu0
    have h0' := him u0 (Finset.mem_filter.1 hu0).1
    rw [abs_of_pos (by linarith : (0:ℝ) < T0 + 3.48)]
    have := abs_sub_abs_le_abs_sub c u0.im
    rw [abs_sub_comm] at this
    linarith
  refine h1.trans ?_
  unfold ZLg
  exact div_le_div_of_nonneg_right (hp.log_mono hcT) (log_ratio_pos (by norm_num) (by norm_num)).le

theorem count_tail_windowG (hp : PolyDatum f B κ) {T T0 : ℝ} (hT0 : 0 < T0) (S : Finset ℂ)
    (hS : S ⊆ zerosRectD f T) (hre : ∀ u ∈ S, 0 < u.re ∧ u.re < 1) (him : ∀ u ∈ S, T0 < |u.im|)
    (k : ℕ) :
    ∑ u ∈ S.filter (fun u => ⌊(|u.im| - T0) / 4.4⌋₊ = k), (multRectD f T u : ℝ) ≤
      2 * Z3g B T0 + 2 * c3g κ T0 * (k + 1) := by
  set F := S.filter (fun u => ⌊(|u.im| - T0) / 4.4⌋₊ = k) with hF
  set c := T0 + ((k : ℝ) + 1 / 2) * 4.4 with hc
  have hL3 := log_ratio_pos (r := 3) (by norm_num) (by norm_num)
  have hpos : ∀ u ∈ F, (k : ℝ) * 4.4 ≤ |u.im| - T0 ∧ |u.im| - T0 < ((k : ℝ) + 1) * 4.4 := by
    intro u hu
    obtain ⟨huS, hk⟩ := Finset.mem_filter.1 hu
    have h0 : 0 ≤ (|u.im| - T0) / 4.4 := div_nonneg (by linarith [him u huS]) (by norm_num)
    have h1 := Nat.floor_le h0
    have h2 := Nat.lt_floor_add_one ((|u.im| - T0) / 4.4)
    rw [hk] at h1 h2
    constructor
    · rwa [le_div_iff₀ (by norm_num)] at h1
    · rwa [div_lt_iff₀ (by norm_num)] at h2
  have hcount : ∀ (F' : Finset ℂ), F' ⊆ F → ∀ c' : ℝ, |c'| = c →
      (∀ u ∈ F', ‖u - (2 + c' * I)‖ ≤ 3) →
        ∑ u ∈ F', (multRectD f T u : ℝ) ≤ Z3g B T0 + c3g κ T0 * (k + 1) := by
    intro F' hF' c' hc' hball
    have h1 := sum_multRectD_le hp F' ((hF'.trans (Finset.filter_subset _ _)).trans hS) c'
      (r := 3) (by norm_num) (by norm_num) hball
    have h2 : Real.log (B c' / 0.355) ≤ Real.log (B T0 / 0.355) + κ * (((k : ℝ) + 1 / 2) * 4.4) / T0 := by
      have e : Real.log (B c' / 0.355) ≤ Real.log (B (T0 + ((k : ℝ) + 1 / 2) * 4.4) / 0.355) := by
        apply hp.log_mono
        rw [hc', hc, abs_of_pos (by positivity : (0:ℝ) < T0 + ((k : ℝ) + 1 / 2) * 4.4)]
      exact e.trans (hp.growth T0 _ hT0 (by positivity))
    have h3 : κ * (((k : ℝ) + 1 / 2) * 4.4) / T0 ≤ κ * 4.4 / T0 * (k + 1) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hT0]
      have := hp.κ_nonneg
      nlinarith
    refine h1.trans ?_
    unfold Z3g c3g
    rw [div_add' _ _ _ hL3.ne', div_le_div_iff_of_pos_right hL3]
    rw [show κ * 4.4 / T0 / Real.log (10 / 3) * ((k : ℝ) + 1) * Real.log (10 / 3) =
      κ * 4.4 / T0 * (k + 1) by field_simp]
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not F (fun u => 0 < u.im)]
  have hp' := hcount (F.filter fun u => 0 < u.im) (Finset.filter_subset _ _) c
    (abs_of_pos (by positivity)) (fun u hu => by
      obtain ⟨huF, him0⟩ := Finset.mem_filter.1 hu
      obtain ⟨hp1, hp2⟩ := hpos u huF
      obtain ⟨hr1, hr2⟩ := hre u (Finset.mem_filter.1 huF).1
      rw [abs_of_pos him0] at hp1 hp2
      refine norm_le_of_re_im (a := 2) (b := 2.2) (by norm_num) ?_ ?_ (by norm_num)
      · simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
        rw [abs_le]; constructor <;> linarith
      · simp only [Complex.sub_im, Complex.add_im, Complex.im_ofNat, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, zero_add]
        rw [abs_le]; constructor <;> linarith)
  have hn := hcount (F.filter fun u => ¬ 0 < u.im) (Finset.filter_subset _ _) (-c)
    (by rw [abs_neg, abs_of_pos (by positivity)]) (fun u hu => by
      obtain ⟨huF, him0⟩ := Finset.mem_filter.1 hu
      obtain ⟨hp1, hp2⟩ := hpos u huF
      obtain ⟨hr1, hr2⟩ := hre u (Finset.mem_filter.1 huF).1
      push Not at him0
      rw [abs_of_nonpos him0] at hp1 hp2
      refine norm_le_of_re_im (a := 2) (b := 2.2) (by norm_num) ?_ ?_ (by norm_num)
      · simp only [Complex.sub_re, Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
        rw [abs_le]; constructor <;> linarith
      · simp only [Complex.sub_im, Complex.add_im, Complex.im_ofNat, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, zero_add]
        rw [abs_le]; constructor <;> linarith)
  linarith

/-- `E₁` for general Plancherel bounds `Q₁ ≥ ∫|F|²`, `Q₂ ≥ ∫|F'|²`. -/
noncomputable def E1g (B : ℝ → ℝ) (T0 Q1 Q2 : ℝ) : ℝ :=
  ZLg B T0 * ((1 / 3.48) * √(Q1 * (2 * (Jl T0 * 3.48))) + √(Q2 * (2 * (Jl T0 * 3.48))))

/-- `E₂` for a geometric tail `E_B ρ_B^k + E_A ρ_A^k`. -/
noncomputable def E2g (B : ℝ → ℝ) (κ T0 EB' EA' ρB ρA : ℝ) : ℝ :=
  EB' * (2 * Z3g B T0 / (1 - ρB) + 2 * c3g κ T0 / (1 - ρB) ^ 2) +
    EA' * (2 * Z3g B T0 / (1 - ρA) + 2 * c3g κ T0 / (1 - ρA) ^ 2)

/-- **The sum over zeros** (generic). -/
theorem zero_sum_boundG (hp : PolyDatum f B κ)
    (hcls : ∀ T : ℝ, ∀ u ∈ zerosRectD f T, f u = 0 ∧ (u = 0 ∨ (0 < u.re ∧ u.re < 1)))
    {T0 : ℝ} (hT0 : 50 ≤ T0)
    (hG : ∀ ρ : ℂ, f ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2)
    (M : ℂ → ℂ) {G0 : ℝ} (hM0 : ‖M 0‖ ≤ G0)
    {F F' : ℝ → ℂ} (hMF : ∀ t : ℝ, M (((1 / 2 : ℝ) : ℂ) + t * I) = F t)
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    {Q1 Q2 : ℝ} (hQ1 : 0 < Q1) (hQ2 : 0 < Q2)
    (hF2 : Integrable fun t => ‖F t‖ ^ 2) (hF2' : Integrable fun t => ‖F' t‖ ^ 2)
    (hFQ : ∫ t, ‖F t‖ ^ 2 ≤ Q1) (hFQ' : ∫ t, ‖F' t‖ ^ 2 ≤ Q2)
    {EB' EA' ρB ρA : ℝ} (hEB : 0 ≤ EB') (hEA : 0 ≤ EA') (hρB0 : 0 ≤ ρB) (hρB1 : ρB < 1)
    (hρA0 : 0 ≤ ρA) (hρA1 : ρA < 1)
    (htail : ∀ s : ℂ, 0 < s.re → s.re < 1 → T0 < |s.im| →
      ‖M s‖ ≤ EB' * ρB ^ ⌊(|s.im| - T0) / 4.4⌋₊ + EA' * ρA ^ ⌊(|s.im| - T0) / 4.4⌋₊)
    {x : ℝ} (hx : 1 ≤ x) (T : ℝ) :
    ‖∑ u ∈ zerosRectD f T, (multRectD f T u : ℂ) * (M u * (x : ℂ) ^ u)‖ ≤
      G0 * Z3g B 0 + √x * E1g B T0 Q1 Q2 + x * E2g B κ T0 EB' EA' ρB ρA := by
  set Z := zerosRectD f T with hZ
  set m : ℂ → ℝ := fun u => (multRectD f T u : ℝ) with hmdef
  have hm : ∀ u, 0 ≤ m u := fun u => Nat.cast_nonneg _
  have hx0 : 0 < x := by linarith
  have hT00 : 0 < T0 := by linarith
  have h1 : ‖∑ u ∈ Z, (multRectD f T u : ℂ) * (M u * (x : ℂ) ^ u)‖ ≤
      ∑ u ∈ Z, m u * (‖M u‖ * x ^ u.re) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0]
  refine h1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => u = 0),
    ← Finset.sum_filter_add_sum_filter_not (Z.filter fun u => ¬ u = 0) (fun u => |u.im| ≤ T0)]
  have hcases : ∀ u ∈ Z.filter (fun u => ¬ u = 0), f u = 0 ∧ 0 < u.re ∧ u.re < 1 := by
    intro u hu
    obtain ⟨huZ, hu0⟩ := Finset.mem_filter.1 hu
    obtain ⟨hL, hc⟩ := hcls T u huZ
    rcases hc with h | h
    · exact absurd h hu0
    · exact ⟨hL, h⟩
  have hG00 : 0 ≤ G0 := (norm_nonneg _).trans hM0
  -- the zero at `0`
  have hA : ∑ u ∈ Z.filter (fun u => u = 0), m u * (‖M u‖ * x ^ u.re) ≤ G0 * Z3g B 0 := by
    have hcount := sum_multRectD_le hp (Z.filter fun u => u = 0) (Finset.filter_subset _ _) 0
      (r := 3) (by norm_num) (by norm_num) (fun u hu => by
        rw [(Finset.mem_filter.1 hu).2]; norm_num)
    have hpt : ∀ u ∈ Z.filter (fun u => u = 0), m u * (‖M u‖ * x ^ u.re) ≤ m u * G0 := by
      intro u hu
      rw [(Finset.mem_filter.1 hu).2, Complex.zero_re, Real.rpow_zero, mul_one]
      exact mul_le_mul_of_nonneg_left hM0 (hm 0)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_mul, mul_comm]
    have : ∑ u ∈ Z.filter (fun u => u = 0), m u ≤ Z3g B 0 := by
      unfold Z3g; simpa using hcount
    exact mul_le_mul_of_nonneg_left this hG00
  -- zeros on the critical line, `|γ| ≤ T₀`
  have hB : ∑ u ∈ (Z.filter fun u => ¬ u = 0).filter (fun u => |u.im| ≤ T0),
      m u * (‖M u‖ * x ^ u.re) ≤ √x * E1g B T0 Q1 Q2 := by
    set S := (Z.filter fun u => ¬ u = 0).filter (fun u => |u.im| ≤ T0) with hS
    have hSZ : S ⊆ Z := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hre : ∀ u ∈ S, u.re = 1 / 2 := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
      obtain ⟨hL, hr1, hr2⟩ := hcases u hu1
      exact hG u hL hr1 hr2 hu2
    have him : ∀ u ∈ S, |u.im| ≤ T0 := fun u hu => (Finset.mem_filter.1 hu).2
    have heq : ∀ u ∈ S, m u * (‖M u‖ * x ^ u.re) = √x * (m u * ‖F u.im‖) := by
      intro u hu
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hre u hu, ← Real.sqrt_eq_rpow, ← hMF u.im, ← hu']; ring
    rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have hJ := lt_Jl hT00.le
    have hJh : 0 < (Jl T0 : ℝ) * 3.48 := by linarith
    have hZL0 : 0 ≤ ZLg B T0 :=
      div_nonneg (hp.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le
    refine (sum_window_le m (fun u _ => hm u) (h := 3.48) (by norm_num) (Jl T0) hJ him hZL0
      (fun k => count_line_windowG hp hT00.le S hSZ hre him k) hF hF').trans ?_
    unfold E1g
    refine mul_le_mul_of_nonneg_left ?_ hZL0
    have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
    have e : (Jl T0 : ℝ) * 3.48 - -(Jl T0 * 3.48) = 2 * (Jl T0 * 3.48) := by ring
    have i1 := intervalIntegral_norm_le_sqrt hFc hF2 hQ1 hFQ (a := -(Jl T0 * 3.48))
      (b := Jl T0 * 3.48) (by linarith)
    have i2 := intervalIntegral_norm_le_sqrt hF' hF2' hQ2 hFQ' (a := -(Jl T0 * 3.48))
      (b := Jl T0 * 3.48) (by linarith)
    rw [e] at i1 i2
    have := mul_le_mul_of_nonneg_left i1 (by positivity : (0:ℝ) ≤ 1 / 3.48)
    linarith
  -- zeros above `T₀`
  have hC : ∑ u ∈ (Z.filter fun u => ¬ u = 0).filter (fun u => ¬ |u.im| ≤ T0),
      m u * (‖M u‖ * x ^ u.re) ≤ x * E2g B κ T0 EB' EA' ρB ρA := by
    set S := (Z.filter fun u => ¬ u = 0).filter (fun u => ¬ |u.im| ≤ T0) with hS
    have hSZ : S ⊆ Z := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hre : ∀ u ∈ S, 0 < u.re ∧ u.re < 1 := fun u hu => (hcases u (Finset.mem_filter.1 hu).1).2
    have him : ∀ u ∈ S, T0 < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
    set idx : ℂ → ℕ := fun u => ⌊(|u.im| - T0) / 4.4⌋₊ with hidx
    have hpt : ∀ u ∈ S, m u * (‖M u‖ * x ^ u.re) ≤
        x * (m u * (EB' * ρB ^ idx u) + m u * (EA' * ρA ^ idx u)) := by
      intro u hu
      obtain ⟨hr1, hr2⟩ := hre u hu
      have hGb := htail u hr1 hr2 (him u hu)
      have hxr : x ^ u.re ≤ x := by
        calc x ^ u.re ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hr2.le
          _ = x := Real.rpow_one x
      have hGn := norm_nonneg (M u)
      calc m u * (‖M u‖ * x ^ u.re) ≤ m u * ((EB' * ρB ^ idx u + EA' * ρA ^ idx u) * x) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hGb hxr (Real.rpow_nonneg hx0.le _) (hGn.trans hGb)) (hm u)
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    rw [Finset.sum_add_distrib]
    have hZw : ∀ k : ℕ, ∑ u ∈ S.filter (fun u => idx u = k), m u ≤ 2 * Z3g B T0 + 2 * c3g κ T0 * (k + 1) :=
      fun k => count_tail_windowG hp hT00 S hSZ hre him k
    have hZ3 : 0 ≤ Z3g B T0 :=
      div_nonneg (hp.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le
    have hc3 : 0 ≤ c3g κ T0 :=
      div_nonneg (div_nonneg (mul_nonneg hp.κ_nonneg (by norm_num)) hT00.le)
        (log_ratio_pos (by norm_num) (by norm_num)).le
    have g1 := sum_geom_windows m (fun u _ => hm u) idx (Z0 := 2 * Z3g B T0) (c := 2 * c3g κ T0)
      (E := EB') (ρ := ρB) (by linarith) (by linarith) hEB hρB0 hρB1 (fun k => by
        have := hZw k; linarith)
    have g2 := sum_geom_windows m (fun u _ => hm u) idx (Z0 := 2 * Z3g B T0) (c := 2 * c3g κ T0)
      (E := EA') (ρ := ρA) (by linarith) (by linarith) hEA hρA0 hρA1 (fun k => by
        have := hZw k; linarith)
    unfold E2g
    linarith
  linarith

end TernaryGoldbach.Explicit
