import TernaryGoldbach.Explicit.LineZeros
import TernaryGoldbach.Explicit.ZeroSums

/-!
# The sum over zeros in the explicit formula

For `χ` primitive, `χ ≠ 1`, GRH up to `T₀ ≥ max(10π|δ|, 50)`, and every `T > 0`:
`|Σ_{ρ ∈ zerosRect χ T} m_ρ G_δ(ρ) x^ρ| ≤ E₀ + E₁ √x + E₂ x`, where `E₀` bounds the zero at `0`, `E₁` the
zeros on the critical line with `|γ| ≤ T₀` (`LineZeros`), and `E₂` the zeros with `|γ| > T₀` (the two
regimes of `MellinRotate`). Also the uniform bound `|G_δ(s)| ≤ 112 e^{−θ_δ|ℑs|}`, `θ_δ = 0.28/(1 + |δ|)`.
-/

open Complex MeasureTheory Set Filter
open scoped Real

namespace TernaryGoldbach.Explicit

/-- `θ_δ = 0.28/(1 + |δ|)`. -/
noncomputable def thetaD (δ : ℝ) : ℝ := 0.28 / (1 + |δ|)

theorem thetaD_pos (δ : ℝ) : 0 < thetaD δ := by unfold thetaD; positivity

theorem thetaD_le (δ : ℝ) : thetaD δ ≤ 0.28 := by
  unfold thetaD
  rw [div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg δ]

theorem abs_mul_thetaD_le (δ : ℝ) : |δ| * thetaD δ ≤ 0.28 := by
  unfold thetaD
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg δ]

theorem exp_18267_le : Real.exp 1.8267 ≤ 6.2136 := by
  have h := Real.exp_bound' (x := 0.91335) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have e : Real.exp 1.8267 = Real.exp 0.91335 * Real.exp 0.91335 := by rw [← Real.exp_add]; norm_num
  rw [e]
  have h0 := Real.exp_pos 0.91335
  nlinarith

/-- **Uniform bound**: `|G_δ(s)| ≤ 112 e^{−θ_δ|ℑs|}` on `−1 ≤ ℜs ≤ 1`. -/
theorem norm_G_uniform (s : ℂ) (δ : ℝ) (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖Gr s δ 0‖ ≤ 112 * Real.exp (-(thetaD δ * |s.im|)) := by
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  set θ := thetaD δ with hθdef
  have hθ0 := thetaD_pos δ
  have hθ1 := thetaD_le δ
  have hδθ := abs_mul_thetaD_le δ
  have h := norm_Gr_le_closed s δ (θ := θ) hθ0.le (by linarith) hs0 hs1
  have hS0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith)
  have hSθ : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hSS : Real.sin θ ≤ Real.sin 0.28 :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hθ1
  have hS28 := sin_028_le
  have hc := cos_two_mul_eq θ
  set S := Real.sin θ
  set c := Real.cos (2 * θ)
  have hS2 : S ^ 2 ≤ 0.0763741 := by nlinarith
  have hc1 : 0.847251 ≤ c := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  -- `a = 2π|δ| sin θ ≤ 2π·0.28`
  have ha : 2 * π * |δ| * S ≤ 1.75931 := by
    have : |δ| * S ≤ 0.28 := le_trans (mul_le_mul_of_nonneg_left hSθ (abs_nonneg δ)) hδθ
    have h6 := Real.pi_lt_d6
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * π)]
  have ha0 : 0 ≤ 2 * π * |δ| * S := by positivity
  have hb : (2 * π * |δ| * S) ^ 2 / (2 * c) ≤ 1.8267 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul ha ha ha0 (by norm_num)]
  have hbc : (2 * π * |δ| * S / c) ^ 2 ≤ 4.3119 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have hc2 : 0.717834 ≤ c ^ 2 := by nlinarith
    nlinarith [mul_le_mul ha ha ha0 (by norm_num)]
  obtain ⟨hsq1, hsq2⟩ := sqrt_consts (c := c) (by linarith)
  have hpre : (1 + (2 * π * |δ| * S / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)) ≤ 17.69 := by
    have := mul_le_mul (add_le_add_left hbc 1) hsq1 (Real.sqrt_nonneg _) (by norm_num)
    nlinarith
  have hpre0 : 0 ≤ (1 + (2 * π * |δ| * S / c) ^ 2) * √(π / (c / 2)) + √π / (c * √(c / 2)) := by
    positivity
  refine h.trans ?_
  rw [mul_comm (112 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have he : Real.exp ((2 * π * |δ| * S) ^ 2 / (2 * c)) ≤ 6.2136 :=
    (Real.exp_le_exp.2 hb).trans exp_18267_le
  nlinarith [Real.exp_pos ((2 * π * |δ| * S) ^ 2 / (2 * c))]

/-! ## Zeros above `T₀`: decay from `T₀` -/

/-- `0.892 T₀ e^{−0.1598 T₀}` (regime B at `T₀`). -/
noncomputable def EB (T0 : ℝ) : ℝ := 0.892 * T0 * Real.exp (-0.1598 * T0)

/-- `0.588 u₀² e^{−0.1065 u₀²}`, `u₀ = T₀/(π|δ|)` (regime A at `T₀`), `0` at `δ = 0`. -/
noncomputable def EA (T0 δ : ℝ) : ℝ :=
  if δ = 0 then 0 else 0.588 * (T0 / (π * |δ|)) ^ 2 * Real.exp (-0.1065 * (T0 / (π * |δ|)) ^ 2)

theorem EB_nonneg {T0 : ℝ} (h : 0 ≤ T0) : 0 ≤ EB T0 := by unfold EB; positivity
theorem EA_nonneg (T0 δ : ℝ) : 0 ≤ EA T0 δ := by unfold EA; split_ifs <;> positivity

theorem le_mul_exp_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b ≤ a * Real.exp ((b - a) / a) := by
  have := Real.add_one_le_exp ((b - a) / a)
  have e : a * ((b - a) / a + 1) = b := by field_simp; ring
  nlinarith

/-- **`|G_δ(s)|` above `T₀`**: for `−1 ≤ ℜs ≤ 1`, `|ℑs| ≥ T₀ ≥ max(10π|δ|, 50)`,
`|G_δ(s)| ≤ E_B e^{−0.1398(|ℑs| − T₀)} + E_A e^{−1.93(|ℑs| − T₀)/(π|δ|)}`. -/
theorem norm_G_tail (s : ℂ) (δ : ℝ) (hs0 : -1 ≤ s.re) (hs1 : s.re ≤ 1) {T0 : ℝ}
    (hT0 : max (10 * π * |δ|) 50 ≤ T0) (hτ : T0 ≤ |s.im|) :
    ‖Gr s δ 0‖ ≤ EB T0 * Real.exp (-0.1398 * (|s.im| - T0)) +
      EA T0 δ * Real.exp (-1.93 * ((|s.im| - T0) / (π * |δ|))) := by
  have h50 : 50 ≤ T0 := (le_max_right _ _).trans hT0
  have h10 : 10 * π * |δ| ≤ T0 := (le_max_left _ _).trans hT0
  set τ := |s.im| with hτdef
  have hEA := EA_nonneg T0 δ
  have hEB := EB_nonneg (by linarith : (0:ℝ) ≤ T0)
  by_cases hreg : 3 / 2 * (π * δ) ^ 2 ≤ τ
  · have hB := norm_G_le_regimeB s δ hs0 hs1 (by linarith) hreg
    have h1 : τ ≤ T0 * Real.exp (0.02 * (τ - T0)) := by
      refine (le_mul_exp_sub (by linarith) hτ).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith)
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h2 : 0.892 * τ * Real.exp (-0.1598 * τ) ≤ EB T0 * Real.exp (-0.1398 * (τ - T0)) := by
      unfold EB
      calc 0.892 * τ * Real.exp (-0.1598 * τ) ≤ 0.892 * (T0 * Real.exp (0.02 * (τ - T0))) *
            Real.exp (-0.1598 * τ) := by gcongr
        _ = 0.892 * T0 * (Real.exp (0.02 * (τ - T0)) * Real.exp (-0.1598 * τ)) := by ring
        _ = 0.892 * T0 * (Real.exp (-0.1598 * T0) * Real.exp (-0.1398 * (τ - T0))) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
        _ = _ := by ring
    have h3 : 0 ≤ EA T0 δ * Real.exp (-1.93 * ((τ - T0) / (π * |δ|))) := by positivity
    linarith
  · push Not at hreg
    have hδ : δ ≠ 0 := by
      rintro rfl; simp at hreg; linarith [abs_nonneg s.im]
    have hδ0 : 0 < |δ| := abs_pos.2 hδ
    have hA := norm_G_le_regimeA s δ hs0 hs1 (by linarith) hreg
    set P := π * |δ| with hP
    have hP0 : 0 < P := by positivity
    set u := τ / P with hu
    set u0 := T0 / P with hu0
    have hu010 : 10 ≤ u0 := by rw [hu0, le_div_iff₀ hP0]; linarith
    have huu0 : u0 ≤ u := div_le_div_of_nonneg_right hτ hP0.le
    have hdiff : u - u0 = (τ - T0) / P := by rw [hu, hu0]; ring
    have h1 : u ≤ u0 * Real.exp (0.1 * (u - u0)) := by
      refine (le_mul_exp_sub (by linarith) huu0).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by linarith)
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have h1' : u ^ 2 ≤ u0 ^ 2 * Real.exp (0.2 * (u - u0)) := by
      have hu0' : 0 ≤ u := by linarith
      have := pow_le_pow_left₀ hu0' h1 2
      rw [mul_pow, ← Real.exp_nat_mul] at this
      convert this using 3; push_cast; ring
    have h2 : -0.1065 * u ^ 2 ≤ -0.1065 * u0 ^ 2 + -2.13 * (u - u0) := by nlinarith
    have hEAeq : EA T0 δ = 0.588 * u0 ^ 2 * Real.exp (-0.1065 * u0 ^ 2) := by
      unfold EA; rw [if_neg hδ]
    have h3 : 0.588 * u ^ 2 * Real.exp (-0.1065 * u ^ 2) ≤
        EA T0 δ * Real.exp (-1.93 * ((τ - T0) / P)) := by
      rw [hEAeq, ← hdiff]
      calc 0.588 * u ^ 2 * Real.exp (-0.1065 * u ^ 2)
          ≤ 0.588 * (u0 ^ 2 * Real.exp (0.2 * (u - u0))) *
              Real.exp (-0.1065 * u0 ^ 2 + -2.13 * (u - u0)) := by
            gcongr
        _ = 0.588 * u0 ^ 2 * (Real.exp (-0.1065 * u0 ^ 2) *
              (Real.exp (0.2 * (u - u0)) * Real.exp (-2.13 * (u - u0)))) := by
            rw [Real.exp_add]; ring
        _ = _ := by rw [← Real.exp_add]; ring_nf
    have h4 : 0 ≤ EB T0 * Real.exp (-0.1398 * (τ - T0)) := by positivity
    linarith

/-- **Geometric window sums**: `Σ m_u E ρ^{k(u)} ≤ E(Z₀/(1 − ρ) + c/(1 − ρ)²)` if window `k` has total
weight `≤ Z₀ + c(k + 1)`. -/
theorem sum_geom_windows {S : Finset ℂ} (m : ℂ → ℝ) (hm : ∀ u ∈ S, 0 ≤ m u) (idx : ℂ → ℕ)
    {Z0 c E ρ : ℝ} (hZ0 : 0 ≤ Z0) (hc : 0 ≤ c) (hE : 0 ≤ E) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hZ : ∀ k : ℕ, ∑ u ∈ S.filter (fun u => idx u = k), m u ≤ Z0 + c * (k + 1)) :
    ∑ u ∈ S, m u * (E * ρ ^ idx u) ≤ E * (Z0 / (1 - ρ) + c / (1 - ρ) ^ 2) := by
  set K := (S.image idx).sup id + 1 with hK
  have hmaps : ∀ u ∈ S, idx u ∈ Finset.range K := by
    intro u hu
    rw [Finset.mem_range, hK, Nat.lt_succ_iff]
    exact Finset.le_sup (f := id) (Finset.mem_image_of_mem idx hu)
  have h1 : ∑ u ∈ S, m u * (E * ρ ^ idx u) =
      ∑ k ∈ Finset.range K, E * ρ ^ k * ∑ u ∈ S.filter (fun u => idx u = k), m u := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [(Finset.mem_filter.1 hu).2]; ring
  rw [h1]
  have hρn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
  have hs1 := summable_geometric_of_lt_one hρ0 hρ1
  have hs2 : Summable fun n : ℕ => (n : ℝ) * ρ ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hρn
  have hg1 : ∑ k ∈ Finset.range K, ρ ^ k ≤ 1 / (1 - ρ) := by
    rw [one_div, ← tsum_geometric_of_lt_one hρ0 hρ1]
    exact hs1.sum_le_tsum _ fun k _ => by positivity
  have hg2 : ∑ k ∈ Finset.range K, ((k : ℝ) + 1) * ρ ^ k ≤ 1 / (1 - ρ) ^ 2 := by
    have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) * ρ ^ n := by
      simpa [add_mul] using hs2.add hs1
    have ht : ∑' n : ℕ, ((n : ℝ) + 1) * ρ ^ n = 1 / (1 - ρ) ^ 2 := by
      simp_rw [add_mul, one_mul]
      rw [hs2.tsum_add hs1, (hasSum_coe_mul_geometric_of_norm_lt_one hρn).tsum_eq,
        tsum_geometric_of_lt_one hρ0 hρ1]
      have : (1 - ρ) ≠ 0 := by linarith
      field_simp; ring
    rw [← ht]
    exact hsum.sum_le_tsum _ fun k _ => by positivity
  calc ∑ k ∈ Finset.range K, E * ρ ^ k * ∑ u ∈ S.filter (fun u => idx u = k), m u
      ≤ ∑ k ∈ Finset.range K, E * ρ ^ k * (Z0 + c * (k + 1)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hZ k) (by positivity)
    _ = E * (Z0 * ∑ k ∈ Finset.range K, ρ ^ k + c * ∑ k ∈ Finset.range K, ((k : ℝ) + 1) * ρ ^ k) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ E * (Z0 * (1 / (1 - ρ)) + c * (1 / (1 - ρ) ^ 2)) := by gcongr
    _ = _ := by ring

/-! ## Window counts -/

theorem norm_le_of_re_im {z : ℂ} {a b r : ℝ} (hr : 0 ≤ r) (ha : |z.re| ≤ a) (hb : |z.im| ≤ b)
    (habr : a ^ 2 + b ^ 2 ≤ r ^ 2) : ‖z‖ ≤ r := by
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h3 : z.re ^ 2 ≤ a ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have h4 : z.im ^ 2 ≤ b ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg z) hr (by norm_num : (2:ℕ) ≠ 0)).1 (by nlinarith)

theorem BP_neg (N : ℕ) (c : ℝ) : BP N (-c) = BP N c := by unfold BP; rw [abs_neg]

theorem BP_pos (N : ℕ) [NeZero N] (c : ℝ) : 0 < BP N c := by linarith [one_le_BP (N := N) c]

theorem BP_mono (N : ℕ) [NeZero N] {c c' : ℝ} (h : |c| ≤ |c'|) : BP N c ≤ BP N c' := by
  unfold BP
  have hN : (0:ℝ) ≤ 1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by positivity
  have h1 : (1.25 * (|c| + 11)) ^ (10 : ℝ) ≤ (1.25 * (|c'| + 11)) ^ (10 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hN) h1 (by positivity) (by positivity)

theorem log_BP_mono (N : ℕ) [NeZero N] {c c' : ℝ} (h : |c| ≤ |c'|) :
    Real.log (BP N c / 0.355) ≤ Real.log (BP N c' / 0.355) :=
  Real.log_le_log (div_pos (BP_pos N c) (by norm_num))
    (div_le_div_of_nonneg_right (BP_mono N h) (by norm_num))

theorem log_BP_pos (N : ℕ) [NeZero N] (c : ℝ) : 0 < Real.log (BP N c / 0.355) := by
  apply Real.log_pos; rw [lt_div_iff₀ (by norm_num)]; linarith [one_le_BP (N := N) c]

/-- `log B'_{T₀+m} ≤ log B'_{T₀} + 11m/T₀`. -/
theorem log_BP_growth (N : ℕ) [NeZero N] {T0 m : ℝ} (hT0 : 0 < T0) (hm : 0 ≤ m) :
    Real.log (BP N (T0 + m) / 0.355) ≤ Real.log (BP N T0 / 0.355) + 11 * m / T0 := by
  have hA : (0:ℝ) < 1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1) := by
    have : (1:ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have e : ∀ c : ℝ, 0 ≤ c → Real.log (BP N c / 0.355) = Real.log (1400 * (N : ℝ) ^ 9 * ((N : ℝ) + 1)) +
      Real.log (c + 22) + 10 * Real.log (1.25 * (c + 11)) - Real.log 0.355 := by
    intro c hc
    unfold BP
    rw [abs_of_nonneg hc, Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
  rw [e _ (by linarith), e _ hT0.le]
  have h1 : Real.log (T0 + m + 22) - Real.log (T0 + 22) ≤ m / T0 := by
    rw [← Real.log_div (by linarith) (by linarith)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) hT0]; nlinarith
  have h2 : Real.log (1.25 * (T0 + m + 11)) - Real.log (1.25 * (T0 + 11)) ≤ m / T0 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) hT0]; nlinarith
  have : 11 * m / T0 = m / T0 + 10 * (m / T0) := by ring
  linarith

/-- The line window of `u` (for `|ℑu| ≤ T₀ < Jh`). -/
theorem mem_line_window {u : ℂ} {h T0 : ℝ} (hh : 0 < h) {J : ℕ} (hJ : T0 < J * h) (hu : |u.im| ≤ T0) :
    ((((⌊u.im / h⌋ + J).toNat : ℕ) : ℝ) - J) * h ≤ u.im ∧
      u.im ≤ ((((⌊u.im / h⌋ + J).toNat : ℕ) : ℝ) - J + 1) * h := by
  have hb := abs_le.1 hu
  have hl : -(J : ℝ) < u.im / h := by rw [lt_div_iff₀ hh]; linarith
  have hfl1 : -(J : ℤ) ≤ ⌊u.im / h⌋ := by rw [Int.le_floor]; push_cast; linarith
  have hnn : 0 ≤ ⌊u.im / h⌋ + J := by linarith
  have hk : (((⌊u.im / h⌋ + J).toNat : ℕ) : ℤ) = ⌊u.im / h⌋ + J := Int.toNat_of_nonneg hnn
  have hkR : (((⌊u.im / h⌋ + J).toNat : ℕ) : ℝ) = (⌊u.im / h⌋ : ℝ) + J := by exact_mod_cast hk
  rw [hkR]
  constructor
  · have := Int.floor_le (u.im / h)
    have : (⌊u.im / h⌋ : ℝ) * h ≤ u.im := by rwa [le_div_iff₀ hh] at this
    nlinarith
  · have := Int.lt_floor_add_one (u.im / h)
    have : u.im < ((⌊u.im / h⌋ : ℝ) + 1) * h := by rwa [div_lt_iff₀ hh] at this
    nlinarith

/-! ## The constants -/

/-- `J = ⌊T₀/3.48⌋ + 1` line windows of height `3.48` on each side. -/
noncomputable def Jl (T0 : ℝ) : ℕ := ⌊T0 / 3.48⌋₊ + 1

theorem lt_Jl {T0 : ℝ} (h : 0 ≤ T0) : T0 < Jl T0 * 3.48 := by
  unfold Jl; push_cast
  have := Nat.lt_floor_add_one (T0 / 3.48)
  rw [div_lt_iff₀ (by norm_num)] at this; linarith

/-- Zeros per line window (radius `2.3`). -/
noncomputable def ZL (N : ℕ) (T0 : ℝ) : ℝ :=
  Real.log (BP N (T0 + 3.48) / 0.355) / Real.log (10 / 2.3)
/-- Zeros per tail window (radius `3`) at `T₀`, and the growth rate. -/
noncomputable def Z3 (N : ℕ) (T0 : ℝ) : ℝ := Real.log (BP N T0 / 0.355) / Real.log (10 / 3)
noncomputable def c3 (T0 : ℝ) : ℝ := 11 * 4.4 / T0 / Real.log (10 / 3)

noncomputable def E0b (N : ℕ) : ℝ := 112 * (Real.log (BP N 0 / 0.355) / Real.log (10 / 3))
noncomputable def E1b (N : ℕ) (T0 : ℝ) : ℝ :=
  ZL N T0 * ((1 / 3.48) * √(2 * π * 0.6647 * (2 * (Jl T0 * 3.48))) +
    √(2 * π * 0.1707 * (2 * (Jl T0 * 3.48))))
noncomputable def rhoB : ℝ := Real.exp (-(0.1398 * 4.4))
noncomputable def rhoA (δ : ℝ) : ℝ := Real.exp (-(1.93 * 4.4 / (π * (|δ| + 1))))
noncomputable def E2b (N : ℕ) (T0 δ : ℝ) : ℝ :=
  EB T0 * (2 * Z3 N T0 / (1 - rhoB) + 2 * c3 T0 / (1 - rhoB) ^ 2) +
    EA T0 δ * (2 * Z3 N T0 / (1 - rhoA δ) + 2 * c3 T0 / (1 - rhoA δ) ^ 2)

theorem log_ratio_pos {r : ℝ} (hr : 0 < r) (hr10 : r < 10) : 0 < Real.log (10 / r) :=
  Real.log_pos (by rw [lt_div_iff₀ hr]; linarith)

theorem ZL_nonneg (N : ℕ) [NeZero N] (T0 : ℝ) : 0 ≤ ZL N T0 :=
  div_nonneg (log_BP_pos N _).le (log_ratio_pos (by norm_num) (by norm_num)).le

theorem Z3_nonneg (N : ℕ) [NeZero N] (T0 : ℝ) : 0 ≤ Z3 N T0 :=
  div_nonneg (log_BP_pos N _).le (log_ratio_pos (by norm_num) (by norm_num)).le

theorem c3_nonneg {T0 : ℝ} (h : 0 < T0) : 0 ≤ c3 T0 :=
  div_nonneg (by positivity) (log_ratio_pos (by norm_num) (by norm_num)).le

/-- **Tail window count**: rectangle zeros with `0 < ℜu < 1` and `⌊(|ℑu| − T₀)/4.4⌋ = k` have total
multiplicity `≤ 2 Z₃ + 2 c₃ (k + 1)`. -/
theorem count_tail_window {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T T0 : ℝ} (hT0 : 0 < T0) (S : Finset ℂ) (hS : S ⊆ zerosRect χ T)
    (hre : ∀ u ∈ S, 0 < u.re ∧ u.re < 1) (him : ∀ u ∈ S, T0 < |u.im|) (k : ℕ) :
    ∑ u ∈ S.filter (fun u => ⌊(|u.im| - T0) / 4.4⌋₊ = k), (multRect χ T u : ℝ) ≤
      2 * Z3 N T0 + 2 * c3 T0 * (k + 1) := by
  set F := S.filter (fun u => ⌊(|u.im| - T0) / 4.4⌋₊ = k) with hF
  set c := T0 + ((k : ℝ) + 1 / 2) * 4.4 with hc
  have hL3 := log_ratio_pos (r := 3) (by norm_num) (by norm_num)
  -- window position
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
      (∀ u ∈ F', ‖u - (2 + c' * I)‖ ≤ 3) → ∑ u ∈ F', (multRect χ T u : ℝ) ≤ Z3 N T0 + c3 T0 * (k + 1) := by
    intro F' hF' c' hc' hball
    have h1 := sum_multRect_le hχ hχ1 F' ((hF'.trans (Finset.filter_subset _ _)).trans hS) c'
      (r := 3) (by norm_num) (by norm_num) hball
    have h2 : Real.log (BP N c' / 0.355) ≤ Real.log (BP N T0 / 0.355) + 11 * (((k : ℝ) + 1 / 2) * 4.4) / T0 := by
      have e : BP N c' = BP N (T0 + ((k : ℝ) + 1 / 2) * 4.4) := by
        unfold BP; rw [hc', hc, abs_of_pos (by positivity : (0:ℝ) < T0 + ((k : ℝ) + 1 / 2) * 4.4)]
      rw [e]; exact log_BP_growth N hT0 (by positivity)
    have h3 : 11 * (((k : ℝ) + 1 / 2) * 4.4) / T0 ≤ 11 * 4.4 / T0 * (k + 1) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hT0]; nlinarith
    refine h1.trans ?_
    unfold Z3 c3
    rw [div_add' _ _ _ hL3.ne', div_le_div_iff_of_pos_right hL3]
    rw [show 11 * 4.4 / T0 / Real.log (10 / 3) * ((k : ℝ) + 1) * Real.log (10 / 3) = 11 * 4.4 / T0 * (k + 1) by
      field_simp]
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not F (fun u => 0 < u.im)]
  have hp := hcount (F.filter fun u => 0 < u.im) (Finset.filter_subset _ _) c
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

/-- **Line window count**: zeros on `ℜu = 1/2`, `|ℑu| ≤ T₀`, in line window `k` have total
multiplicity `≤ Z_L`. -/
theorem count_line_window {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {T T0 : ℝ} (hT0 : 0 ≤ T0) (S : Finset ℂ) (hS : S ⊆ zerosRect χ T)
    (hre : ∀ u ∈ S, u.re = 1 / 2) (him : ∀ u ∈ S, |u.im| ≤ T0) (k : ℕ) :
    ∑ u ∈ S.filter (fun u => (⌊u.im / 3.48⌋ + Jl T0).toNat = k), (multRect χ T u : ℝ) ≤ ZL N T0 := by
  set F := S.filter (fun u => (⌊u.im / 3.48⌋ + Jl T0).toNat = k) with hF
  rcases F.eq_empty_or_nonempty with hE | ⟨u0, hu0⟩
  · rw [hE, Finset.sum_empty]; exact ZL_nonneg N T0
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
  have h1 := sum_multRect_le hχ hχ1 F ((Finset.filter_subset _ _).trans hS) c (r := 2.3)
    (by norm_num) (by norm_num) hball
  have hcT : |c| ≤ |T0 + 3.48| := by
    have h0 := hwin u0 hu0
    have h0' := him u0 (Finset.mem_filter.1 hu0).1
    rw [abs_of_pos (by linarith : (0:ℝ) < T0 + 3.48)]
    have := abs_sub_abs_le_abs_sub c u0.im
    rw [abs_sub_comm] at this
    linarith
  refine h1.trans ?_
  unfold ZL
  exact div_le_div_of_nonneg_right (log_BP_mono N hcT)
    (log_ratio_pos (by norm_num) (by norm_num)).le

theorem rhoB_lt_one : rhoB < 1 := by
  unfold rhoB; rw [Real.exp_lt_one_iff]; norm_num
theorem rhoA_lt_one (δ : ℝ) : rhoA δ < 1 := by
  unfold rhoA; rw [Real.exp_lt_one_iff]
  have : 0 < 1.93 * 4.4 / (π * (|δ| + 1)) := by positivity
  linarith

/-- **The sum over zeros**: for `χ` primitive, `χ ≠ 1`, GRH up to `T₀ ≥ max(10π|δ|, 50)`, `x ≥ 1` and
every `T`, `|Σ_{ρ ∈ zerosRect χ T} m_ρ G_δ(ρ) x^ρ| ≤ E₀ + E₁ √x + E₂ x`. -/
theorem zero_sum_bound {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0)
    (hG : ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2) (T : ℝ) :
    ‖∑ u ∈ zerosRect χ T, (multRect χ T u : ℂ) * (Gr u δ 0 * (x : ℂ) ^ u)‖ ≤
      E0b N + √x * E1b N T0 + x * E2b N T0 δ := by
  set Z := zerosRect χ T with hZ
  set m : ℂ → ℝ := fun u => (multRect χ T u : ℝ) with hmdef
  have hm : ∀ u, 0 ≤ m u := fun u => Nat.cast_nonneg _
  have hx0 : 0 < x := by linarith
  have h50 : 50 ≤ T0 := (le_max_right _ _).trans hT0
  have hT00 : 0 < T0 := by linarith
  have h1 : ‖∑ u ∈ Z, (multRect χ T u : ℂ) * (Gr u δ 0 * (x : ℂ) ^ u)‖ ≤
      ∑ u ∈ Z, m u * (‖Gr u δ 0‖ * x ^ u.re) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0]
  refine h1.trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => u = 0),
    ← Finset.sum_filter_add_sum_filter_not (Z.filter fun u => ¬ u = 0) (fun u => |u.im| ≤ T0)]
  have hcases : ∀ u ∈ Z.filter (fun u => ¬ u = 0), χ.LFunction u = 0 ∧ 0 < u.re ∧ u.re < 1 := by
    intro u hu
    obtain ⟨huZ, hu0⟩ := Finset.mem_filter.1 hu
    obtain ⟨hL, -, hc⟩ := zerosRect_cases hχ hχ1 huZ
    rcases hc with h | h
    · exact absurd h hu0
    · exact ⟨hL, h⟩
  -- the zero at `0`
  have hA : ∑ u ∈ Z.filter (fun u => u = 0), m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ E0b N := by
    have hcount := sum_multRect_le hχ hχ1 (Z.filter fun u => u = 0) (Finset.filter_subset _ _) 0
      (r := 3) (by norm_num) (by norm_num) (fun u hu => by
        rw [(Finset.mem_filter.1 hu).2]; norm_num)
    have hG0 : ‖Gr 0 δ 0‖ ≤ 112 := by
      have := norm_G_uniform 0 δ (by simp) (by simp)
      simpa using this
    have hpt : ∀ u ∈ Z.filter (fun u => u = 0), m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ m u * 112 := by
      intro u hu
      rw [(Finset.mem_filter.1 hu).2, Complex.zero_re, Real.rpow_zero, mul_one]
      exact mul_le_mul_of_nonneg_left hG0 (hm 0)
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_mul]
    unfold E0b
    have : ∑ u ∈ Z.filter (fun u => u = 0), m u ≤ Real.log (BP N 0 / 0.355) / Real.log (10 / 3) := hcount
    nlinarith
  -- zeros on the critical line, `|γ| ≤ T₀`
  have hB : ∑ u ∈ (Z.filter fun u => ¬ u = 0).filter (fun u => |u.im| ≤ T0),
      m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ √x * E1b N T0 := by
    set S := (Z.filter fun u => ¬ u = 0).filter (fun u => |u.im| ≤ T0) with hS
    have hSZ : S ⊆ Z := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hre : ∀ u ∈ S, u.re = 1 / 2 := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
      obtain ⟨hL, hr1, hr2⟩ := hcases u hu1
      exact hG u hL hr1 hr2 hu2
    have him : ∀ u ∈ S, |u.im| ≤ T0 := fun u hu => (Finset.mem_filter.1 hu).2
    have heq : ∀ u ∈ S, m u * (‖Gr u δ 0‖ * x ^ u.re) = √x * (m u * ‖fline δ u.im‖) := by
      intro u hu
      have hu' : u = ((1 / 2 : ℝ) : ℂ) + (u.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre u hu]
      rw [hre u hu, ← Real.sqrt_eq_rpow, fline, ← hu']; ring
    rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    exact sum_window_fline_le m (fun u _ => hm u) (h := 3.48) (by norm_num) hT00.le (Jl T0)
      (lt_Jl hT00.le) him (ZL_nonneg N T0)
      (fun k => count_line_window hχ hχ1 hT00.le S hSZ hre him k) δ
  -- zeros above `T₀`
  have hC : ∑ u ∈ (Z.filter fun u => ¬ u = 0).filter (fun u => ¬ |u.im| ≤ T0),
      m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ x * E2b N T0 δ := by
    set S := (Z.filter fun u => ¬ u = 0).filter (fun u => ¬ |u.im| ≤ T0) with hS
    have hSZ : S ⊆ Z := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hre : ∀ u ∈ S, 0 < u.re ∧ u.re < 1 := fun u hu => (hcases u (Finset.mem_filter.1 hu).1).2
    have him : ∀ u ∈ S, T0 < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
    set idx : ℂ → ℕ := fun u => ⌊(|u.im| - T0) / 4.4⌋₊ with hidx
    have hidxle : ∀ u ∈ S, (idx u : ℝ) * 4.4 ≤ |u.im| - T0 := by
      intro u hu
      have h0 : 0 ≤ (|u.im| - T0) / 4.4 := div_nonneg (by linarith [him u hu]) (by norm_num)
      have := Nat.floor_le h0
      rwa [le_div_iff₀ (by norm_num)] at this
    have hpt : ∀ u ∈ S, m u * (‖Gr u δ 0‖ * x ^ u.re) ≤
        x * (m u * (EB T0 * rhoB ^ idx u) + m u * (EA T0 δ * rhoA δ ^ idx u)) := by
      intro u hu
      obtain ⟨hr1, hr2⟩ := hre u hu
      have hτ := him u hu
      have hGt := norm_G_tail u δ (by linarith) hr2.le hT0 hτ.le
      have hB' : Real.exp (-0.1398 * (|u.im| - T0)) ≤ rhoB ^ idx u := by
        unfold rhoB; rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        nlinarith [hidxle u hu]
      have hA' : EA T0 δ * Real.exp (-1.93 * ((|u.im| - T0) / (π * |δ|))) ≤
          EA T0 δ * rhoA δ ^ idx u := by
        by_cases hδ : δ = 0
        · unfold EA; simp [hδ]
        · refine mul_le_mul_of_nonneg_left ?_ (EA_nonneg T0 δ)
          unfold rhoA; rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.2
          have hδ0 : 0 < |δ| := abs_pos.2 hδ
          have hP : 0 < π * |δ| := by positivity
          have h1 : (idx u : ℝ) * 4.4 / (π * (|δ| + 1)) ≤ (|u.im| - T0) / (π * |δ|) := by
            calc (idx u : ℝ) * 4.4 / (π * (|δ| + 1)) ≤ (idx u : ℝ) * 4.4 / (π * |δ|) := by
                  apply div_le_div_of_nonneg_left (by positivity) hP; nlinarith [Real.pi_pos]
              _ ≤ _ := div_le_div_of_nonneg_right (hidxle u hu) hP.le
          have e : (idx u : ℝ) * -(1.93 * 4.4 / (π * (|δ| + 1))) =
              -1.93 * ((idx u : ℝ) * 4.4 / (π * (|δ| + 1))) := by ring
          rw [e]; nlinarith
      have hGb : ‖Gr u δ 0‖ ≤ EB T0 * rhoB ^ idx u + EA T0 δ * rhoA δ ^ idx u := by
        have := mul_le_mul_of_nonneg_left hB' (EB_nonneg hT00.le)
        linarith
      have hxr : x ^ u.re ≤ x := by
        calc x ^ u.re ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx hr2.le
          _ = x := Real.rpow_one x
      have hGn := norm_nonneg (Gr u δ 0)
      calc m u * (‖Gr u δ 0‖ * x ^ u.re) ≤ m u * ((EB T0 * rhoB ^ idx u + EA T0 δ * rhoA δ ^ idx u) * x) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hGb hxr (Real.rpow_nonneg hx0.le _) (hGn.trans hGb)) (hm u)
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    rw [Finset.sum_add_distrib]
    have hZw : ∀ k : ℕ, ∑ u ∈ S.filter (fun u => idx u = k), m u ≤ 2 * Z3 N T0 + 2 * c3 T0 * (k + 1) :=
      fun k => count_tail_window hχ hχ1 hT00 S hSZ hre him k
    have hZw' : ∀ k : ℕ, ∑ u ∈ S.filter (fun u => idx u = k), m u ≤ 2 * Z3 N T0 + 2 * c3 T0 * (k + 1) :=
      hZw
    have g1 := sum_geom_windows m (fun u _ => hm u) idx (Z0 := 2 * Z3 N T0) (c := 2 * c3 T0)
      (E := EB T0) (ρ := rhoB) (by linarith [Z3_nonneg N T0]) (by linarith [c3_nonneg hT00])
      (EB_nonneg hT00.le) (Real.exp_pos _).le rhoB_lt_one (fun k => by
        have := hZw' k; linarith)
    have g2 := sum_geom_windows m (fun u _ => hm u) idx (Z0 := 2 * Z3 N T0) (c := 2 * c3 T0)
      (E := EA T0 δ) (ρ := rhoA δ) (by linarith [Z3_nonneg N T0]) (by linarith [c3_nonneg hT00])
      (EA_nonneg T0 δ) (Real.exp_pos _).le (rhoA_lt_one δ) (fun k => by
        have := hZw' k; linarith)
    unfold E2b
    linarith
  linarith

end TernaryGoldbach.Explicit
