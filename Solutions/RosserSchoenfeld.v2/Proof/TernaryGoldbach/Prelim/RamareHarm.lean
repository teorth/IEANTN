import Mathlib

/-!
# Logarithm and harmonic-sum bounds for the proof of Ramaré's (12.12)

* `log(1 + 1/a)` between partial sums of the artanh series (`log_one_add_inv_ge`,
  `log_one_add_inv_le`, `log_one_add_inv_bounds`);
* `1/(2(n+1)) ≤ H_n − log n − γ ≤ 1/(2n)` for `n ≥ 1` (`harm_bounds`).
-/

open Real Finset Filter Topology

namespace TernaryGoldbach.Prelim.RamPf

/-- The artanh series for `log(1 + 1/a)`. -/
theorem hasSum_log {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
      (Real.log (1 + a⁻¹)) := Real.hasSum_log_one_add_inv ha

theorem log_term_nonneg {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) := by positivity

/-- `log(1 + 1/a) ≥ 2/(2a + 1)`. -/
theorem log_one_add_inv_ge {a : ℝ} (ha : 0 < a) : 2 / (2 * a + 1) ≤ Real.log (1 + a⁻¹) := by
  have := le_hasSum (hasSum_log ha) 0 (fun k _ => log_term_nonneg ha k)
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at this
  rw [div_eq_mul_one_div]; exact this

/-- `K` terms of the series and a geometric tail:
`∑_{k<K} t_k ≤ log(1 + 1/a) ≤ ∑_{k<K} t_k + (2/(2K+1)) y^{2K+1}/(1 − y²)`, `y = 1/(2a+1)`. -/
theorem log_one_add_inv_bounds {a : ℝ} (ha : 0 < a) (K : ℕ) :
    ∑ k ∈ range K, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) ≤
        Real.log (1 + a⁻¹) ∧
      Real.log (1 + a⁻¹) ≤ ∑ k ∈ range K, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1) +
        2 / (2 * K + 1) * (1 / (2 * a + 1)) ^ (2 * K + 1) / (1 - (1 / (2 * a + 1)) ^ 2) := by
  have h := hasSum_log ha
  refine ⟨sum_le_hasSum _ (fun k _ => log_term_nonneg ha k) h, ?_⟩
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  set f : ℕ → ℝ := fun k => (2 : ℝ) * (1 / (2 * k + 1)) * y ^ (2 * k + 1) with hf
  have htail := (hasSum_nat_add_iff' K).2 h
  -- `f (k + K) ≤ (2/(2K+1)) y^{2K+1} (y²)^k`
  have hg : HasSum (fun k : ℕ => 2 / (2 * K + 1) * y ^ (2 * K + 1) * (y ^ 2) ^ k)
      (2 / (2 * K + 1) * y ^ (2 * K + 1) / (1 - y ^ 2)) := by
    have := (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 / (2 * K + 1) * y ^ (2 * K + 1))
    rwa [← div_eq_mul_inv] at this
  have hle : ∀ k, f (k + K) ≤ 2 / (2 * K + 1) * y ^ (2 * K + 1) * (y ^ 2) ^ k := by
    intro k
    simp only [hf]
    have e : y ^ (2 * (↑(k + K) : ℕ) + 1) = y ^ (2 * K + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [show (2 : ℝ) * ((k + K : ℕ) : ℝ) + 1 = 2 * (k + K : ℕ) + 1 from rfl]
    have e2 : y ^ (2 * (k + K) + 1) = y ^ (2 * K + 1) * (y ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [e2]
    have hk : (2 : ℝ) * (1 / (2 * ((k + K : ℕ) : ℝ) + 1)) ≤ 2 / (2 * K + 1) := by
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hp : 0 ≤ y ^ (2 * K + 1) * (y ^ 2) ^ k := by positivity
    calc (2 : ℝ) * (1 / (2 * ((k + K : ℕ) : ℝ) + 1)) * (y ^ (2 * K + 1) * (y ^ 2) ^ k)
        ≤ 2 / (2 * K + 1) * (y ^ (2 * K + 1) * (y ^ 2) ^ k) := mul_le_mul_of_nonneg_right hk hp
      _ = _ := by ring
  have hT := hasSum_le hle htail hg
  linarith

/-- `log(1 + 1/a) ≤ 2/(2a+1) + 1/(6a(a+1)(2a+1))`. -/
theorem log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    Real.log (1 + a⁻¹) ≤ 2 / (2 * a + 1) + 1 / (6 * a * (a + 1) * (2 * a + 1)) := by
  have h := (log_one_add_inv_bounds ha 1).2
  simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, zero_add, div_one, mul_one,
    pow_one, Nat.cast_one] at h
  refine h.trans (le_of_eq ?_)
  have h1 : (2 * a + 1) ≠ 0 := by positivity
  have h3 : (1 : ℝ) - (1 / (2 * a + 1)) ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
    field_simp; ring
  have h4 : (2 : ℝ) / (2 + 1) * (1 / (2 * a + 1)) ^ (2 + 1) / (4 * a * (a + 1) / (2 * a + 1) ^ 2) =
      1 / (6 * a * (a + 1) * (2 * a + 1)) := by
    have : a + 1 ≠ 0 := by positivity
    rw [show (2 : ℕ) + 1 = 3 from rfl, div_pow, one_pow]
    field_simp; ring
  rw [h3, h4, mul_one_div]

/-! ### `H_n − log n − γ` -/

/-- `d_k = log(k+1) − log k − 1/(k+1)`. -/
theorem dk_bounds {k : ℕ} (hk : 1 ≤ k) :
    1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) ≤
        Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1) ∧
      Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1) ≤
        1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log ((k : ℝ) + 1) - Real.log k = Real.log (1 + (k : ℝ)⁻¹) := by
    rw [← Real.log_div (by positivity) hk0.ne']; congr 1; field_simp
  rw [hlog]
  have hl := log_one_add_inv_ge hk0
  have hu := log_one_add_inv_le hk0
  constructor
  · have : 1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2)) ≤ 2 / (2 * k + 1) - 1 / ((k : ℝ) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hk0]
    linarith
  · have : 2 / (2 * (k : ℝ) + 1) + 1 / (6 * k * (k + 1) * (2 * k + 1)) - 1 / ((k : ℝ) + 1) ≤
        1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) := by
      have e1 : 2 / (2 * (k : ℝ) + 1) + 1 / (6 * k * (k + 1) * (2 * k + 1)) - 1 / ((k : ℝ) + 1) =
          (6 * k + 1) / (6 * k * (k + 1) * (2 * k + 1)) := by field_simp; ring
      have e2 : 1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) = 3 * (2 * k + 1) / (6 * k * (k + 1) * (2 * k + 1)) := by
        field_simp; ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith

/-- `H_n − log n − (H_M − log M) = ∑_{n ≤ k < M} d_k`. -/
theorem harm_diff (n : ℕ) : ∀ M, n ≤ M →
    ((harmonic n : ℚ) : ℝ) - Real.log n - (((harmonic M : ℚ) : ℝ) - Real.log M) =
      ∑ k ∈ Ico n M, (Real.log ((k : ℝ) + 1) - Real.log k - 1 / ((k : ℝ) + 1)) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hnM ih =>
    rw [sum_Ico_succ_top hnM, ← ih, harmonic_succ]
    push_cast
    ring

theorem harm_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / (2 * ((n : ℝ) + 1)) ≤ ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant ∧
      ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant ≤ 1 / (2 * (n : ℝ)) := by
  set u : ℕ → ℝ := fun M => ((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniSeq' M with hu
  have hlim : Tendsto u atTop (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant)) :=
    tendsto_const_nhds.sub tendsto_eulerMascheroniSeq'
  have hseq : ∀ M, 1 ≤ M → eulerMascheroniSeq' M = ((harmonic M : ℚ) : ℝ) - Real.log M := by
    intro M hM; rw [eulerMascheroniSeq', if_neg (by omega)]
  -- the telescoped bounds for `M ≥ n`
  have hlow : ∀ M, n ≤ M → 1 / (2 * ((n : ℝ) + 1)) - 1 / (2 * ((M : ℝ) + 1)) ≤ u M := by
    intro M hM
    simp only [hu]
    rw [hseq M (le_trans hn hM), harm_diff n M hM]
    have hsum : ∑ k ∈ Ico n M, (1 / (2 * ((k : ℝ) + 1)) - 1 / (2 * ((k : ℝ) + 2))) =
        1 / (2 * ((n : ℝ) + 1)) - 1 / (2 * ((M : ℝ) + 1)) := by
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hnM ih => rw [sum_Ico_succ_top hnM, ih]; push_cast; ring
    rw [← hsum]
    exact sum_le_sum fun k hk => (dk_bounds (le_trans hn (mem_Ico.1 hk).1)).1
  have hup : ∀ M, n ≤ M → u M ≤ 1 / (2 * (n : ℝ)) - 1 / (2 * (M : ℝ)) := by
    intro M hM
    simp only [hu]
    rw [hseq M (le_trans hn hM), harm_diff n M hM]
    have hsum : ∑ k ∈ Ico n M, (1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1))) =
        1 / (2 * (n : ℝ)) - 1 / (2 * (M : ℝ)) := by
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hnM ih => rw [sum_Ico_succ_top hnM, ih]; push_cast; ring
    rw [← hsum]
    exact sum_le_sum fun k hk => (dk_bounds (le_trans hn (mem_Ico.1 hk).1)).2
  have hz1 : Tendsto (fun M : ℕ => 1 / (2 * ((M : ℝ) + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun M => ?_
    field_simp
  have hz2 : Tendsto (fun M : ℕ => 1 / (2 * (M : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun M => ?_
    field_simp
  constructor
  · have h1 : Tendsto (fun M => u M + 1 / (2 * ((M : ℝ) + 1))) atTop
        (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant + 0)) := hlim.add hz1
    rw [add_zero] at h1
    exact ge_of_tendsto h1 (eventually_atTop.2 ⟨n, fun M hM => by linarith [hlow M hM]⟩)
  · have h1 : Tendsto (fun M => u M + 1 / (2 * (M : ℝ))) atTop
        (𝓝 (((harmonic n : ℚ) : ℝ) - Real.log n - eulerMascheroniConstant + 0)) := hlim.add hz2
    rw [add_zero] at h1
    exact le_of_tendsto h1 (eventually_atTop.2 ⟨n, fun M hM => by linarith [hup M hM]⟩)

end TernaryGoldbach.Prelim.RamPf
