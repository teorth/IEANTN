/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import ZetaInstanceNeg

/-!
# Section 6: from the Fourier inequality and the contour shift to the explicit formula

§6 of Chirre–Helfgott proves Theorem 1.1 by feeding Proposition 2.4 (`prop_2_4_plus`,
`prop_2_4_minus`) the Graham–Vaaler majorant and minorant, recognising the resulting vertical
integral as the one Proposition 5.2 shifts, and evaluating the residues.

This file does that at `A = -ζ'/ζ` and for `σ < 1` only, which is all Corollary 1.2 needs; see
`progress.yaml` for why the exact form `eq:quentino` is not the target.

## The weights for `λ < 0`

`λ = 2π(σ-1)/T < 0`. The majorant and minorant of the truncated exponential are the reflections
`t ↦ ϕ_pm |λ| (±1) (-t)` of the port's positive-parameter approximants; on the segment
`s = 1 + it` they coincide with `Φ_λ(z(s))`, which is what `prop_5_2_zeta_neg` shifts.
-/

open Real Complex MeasureTheory FourierTransform

namespace CH2Section6

/-- The reflected Graham–Vaaler approximant, the `λ < 0` weight on the segment. -/
noncomputable def phiNeg (ν ε : ℝ) : ℝ → ℂ := fun t ↦ CH2.ϕ_pm ν ε (-t)

lemma fourier_phiNeg (ν ε y : ℝ) : 𝓕 (phiNeg ν ε) y = 𝓕 (CH2.ϕ_pm ν ε) (-y) := by
  simp only [Real.fourier_eq, phiNeg]
  rw [← integral_neg_eq_self]
  simp

lemma I'_neg {ν : ℝ} (hν : 0 < ν) (u : ℝ) : CH2Sol.I' (-ν) u = CH2.Inu ν (-u) := by
  unfold CH2Sol.I' CH2.Inu
  have h : (0 ≤ -ν * u) ↔ (0 ≤ -u) := by
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  simp only [h]
  by_cases hu : 0 ≤ -u
  · simp only [if_pos hu]; ring_nf
  · simp only [if_neg hu]

lemma phiNeg_majorant {ν : ℝ} (hν : 0 < ν) (y : ℝ) :
    CH2Sol.I' (-ν) y ≤ (𝓕 (phiNeg ν 1) y).re := by
  rw [I'_neg hν, fourier_phiNeg]
  exact (CH2.Inu_bounds ν (-y) hν).2

lemma phiNeg_minorant {ν : ℝ} (hν : 0 < ν) (y : ℝ) :
    (𝓕 (phiNeg ν (-1)) y).re ≤ CH2Sol.I' (-ν) y := by
  rw [I'_neg hν, fourier_phiNeg]
  exact (CH2.Inu_bounds ν (-y) hν).1

lemma phiNeg_zero_outside (ν ε : ℝ) {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) :
    phiNeg ν ε x = 0 := by
  unfold phiNeg CH2.ϕ_pm
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact hx ⟨by linarith, by linarith⟩

lemma phiNeg_measurable {ν : ℝ} (hν : 0 < ν) (ε : ℝ) : Measurable (phiNeg ν ε) :=
  (CH2.ϕ_continuous ν ε hν.ne').measurable.comp measurable_neg

lemma phiNeg_integrable {ν : ℝ} (hν : 0 < ν) (ε : ℝ) : Integrable (phiNeg ν ε) :=
  (CH2.varphi_integ ν ε hν.ne').comp_neg

lemma phiNeg_continuousAt {ν : ℝ} (hν : 0 < ν) (ε : ℝ) : ContinuousAt (phiNeg ν ε) 0 :=
  ((CH2.ϕ_continuous ν ε hν.ne').comp continuous_neg).continuousAt

/-- `𝓕 φ = O(y⁻²)`, in the form `prop_2_4` wants with `β = 2`. -/
lemma phiNeg_fourier_decay {ν : ℝ} (hν : 0 < ν) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 (phiNeg ν ε) y‖ ≤ C / |y| ^ (2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := CH2.varphi_fourier_bound ν ε hν hε
  refine ⟨C, fun y hy ↦ ?_⟩
  rw [fourier_phiNeg]
  refine (hC (-y)).trans ?_
  have hy2 : |y| ^ (2 : ℝ) = y ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hy2, neg_sq]
  have hpos : 0 < y ^ 2 := by positivity
  exact div_le_div_of_nonneg_left hC0 hpos (by linarith)

/-- `ϕ_pm ν ε 0 = ½(coth(ν/2) + ε)`. -/
lemma phiNeg_zero (ν ε : ℝ) : phiNeg ν ε 0 = (1 / 2) * (CH2.coth ((ν : ℂ) / 2) + ε) := by
  unfold phiNeg CH2.ϕ_pm
  rw [neg_zero, if_pos (by norm_num)]
  simp only [Real.sign_zero, ofReal_zero, zero_mul, add_zero, CH2.Phi_circ]
  norm_num

/-! ### `∑ Λ(n)/(n log² n) < ∞`

`prop_2_4` needs `∑ aₙ/(n logᵝ n)` summable with `β ∈ (1, 2]`, and the Fourier decay caps `β` at
`2`. For `aₙ = Λ(n)` this is borderline — `Λ(n) ≤ log n` alone gives the divergent `∑ 1/(n log n)` —
so it needs the prime structure, and Chebyshev's `ψ(x) ≤ (log 4 + 4)x` is enough: the dyadic block
`(2ʲ, 2ʲ⁺¹]` contributes at most `ψ(2ʲ⁺¹)/(2ʲ j² log² 2) ≤ 2(log 4 + 4)/(j² log² 2)`. -/

/-- A nonnegative sequence whose dyadic blocks are `O(1/j²)` is summable. -/
theorem summable_of_dyadic_blocks {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {C : ℝ}
    (hblock : ∀ j : ℕ, 1 ≤ j → ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), f n ≤ C / (j : ℝ) ^ 2) :
    Summable f := by
  have hC : 0 ≤ C := by
    have h := hblock 1 le_rfl
    have hnn : 0 ≤ ∑ n ∈ Finset.Ioc (2 ^ 1) (2 ^ (1 + 1)), f n :=
      Finset.sum_nonneg fun n _ ↦ hf n
    norm_num at h hnn
    linarith
  -- the partial sums up to `2^(J+1)`
  have hpart : ∀ J : ℕ, ∑ n ∈ Finset.Ioc 0 (2 ^ (J + 1)), f n
      ≤ ∑ n ∈ Finset.Ioc 0 2, f n + C * ∑ j ∈ Finset.Icc 1 J, 1 / (j : ℝ) ^ 2 := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← Finset.sum_Ioc_consecutive f (Nat.zero_le (2 ^ (J + 1)))
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)),
        Finset.sum_Icc_succ_top (by omega)]
      have hb := hblock (J + 1) (by omega)
      have hb' : C / ((J + 1 : ℕ) : ℝ) ^ 2 = C * (1 / ((J + 1 : ℕ) : ℝ) ^ 2) := by ring
      rw [hb'] at hb
      nlinarith [ih, hb]
  -- `∑ 1/j² ≤ 2`
  have key : ∀ K : ℕ, ∑ j ∈ Finset.Icc 1 (K + 1), 1 / (j : ℝ) ^ 2 ≤ 2 - 1 / ((K : ℝ) + 1) := by
    intro K
    induction K with
    | zero => norm_num
    | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have h1 : 1 / (((K + 1 + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / ((K : ℝ) + 1) - 1 / ((K : ℝ) + 2) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at h1 ⊢
      have h2 : (1 : ℝ) / ((K : ℝ) + 1 + 1) = 1 / ((K : ℝ) + 2) := by ring
      rw [h2]
      linarith
  have hbasel : ∀ J : ℕ, ∑ j ∈ Finset.Icc 1 J, 1 / (j : ℝ) ^ 2 ≤ 2 := by
    intro J
    cases J with
    | zero => simp
    | succ K =>
      have := key K
      have hpos : 0 < 1 / ((K : ℝ) + 1) := by positivity
      linarith
  refine summable_of_sum_range_le hf (c := f 0 + ∑ n ∈ Finset.Ioc 0 2, f n + C * 2) fun N ↦ ?_
  -- pick `J` with `N ≤ 2^(J+1)`
  have hN : N ≤ 2 ^ (N + 1) := by
    have := Nat.lt_two_pow_self (n := N)
    have : 2 ^ N ≤ 2 ^ (N + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
    omega
  have hsub : Finset.range N ⊆ insert 0 (Finset.Ioc 0 (2 ^ (N + 1))) := by
    intro n hn
    rw [Finset.mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Finset.mem_insert_of_mem (Finset.mem_Ioc.mpr ⟨h, by omega⟩)
  calc ∑ i ∈ Finset.range N, f i
      ≤ ∑ i ∈ insert 0 (Finset.Ioc 0 (2 ^ (N + 1))), f i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ hf i
    _ = f 0 + ∑ i ∈ Finset.Ioc 0 (2 ^ (N + 1)), f i := by
        rw [Finset.sum_insert (by simp)]
    _ ≤ f 0 + (∑ n ∈ Finset.Ioc 0 2, f n + C * ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) ^ 2) := by
        linarith [hpart N]
    _ ≤ f 0 + ∑ n ∈ Finset.Ioc 0 2, f n + C * 2 := by
        nlinarith [hbasel N, hC]

/-- **`∑ Λ(n)/(n log² n)` converges.** -/
theorem summable_vonMangoldt_div_log_sq :
    Summable (fun n : ℕ ↦ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
      / (n * Real.log n ^ (2 : ℝ))) := by
  have hf : ∀ n : ℕ, 0 ≤ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
      / (n * Real.log n ^ (2 : ℝ)) := fun n ↦ by
    apply div_nonneg (norm_nonneg _)
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast h)
      positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine summable_of_dyadic_blocks hf (C := 2 * (Real.log 4 + 4) / Real.log 2 ^ 2) ?_
  intro j hj
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hterm : ∀ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)),
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ / (n * Real.log n ^ (2 : ℝ))
        ≤ ArithmeticFunction.vonMangoldt n / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) ^ 2) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn2 : ((2 : ℝ) ^ j) < n := by exact_mod_cast hn.1
    have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn2
    have hlogn : (j : ℝ) * Real.log 2 ≤ Real.log n := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) hn2.le
    have hjl : (0 : ℝ) < (j : ℝ) * Real.log 2 := by positivity
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      show Real.log n ^ (2 : ℝ) = Real.log n ^ 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    apply div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    have h1 : ((j : ℝ) * Real.log 2) ^ 2 ≤ Real.log n ^ 2 := pow_le_pow_left₀ hjl.le hlogn 2
    exact mul_le_mul hn2.le h1 (by positivity) hnpos.le
  have hpsi : ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ArithmeticFunction.vonMangoldt n
      ≤ (Real.log 4 + 4) * (2 : ℝ) ^ (j + 1) := by
    have h := Chebyshev.psi_le_const_mul_self (x := (2 : ℝ) ^ (j + 1)) (by positivity)
    rw [Chebyshev.psi, show ⌊(2 : ℝ) ^ (j + 1)⌋₊ = 2 ^ (j + 1) by exact_mod_cast Nat.floor_natCast _] at h
    refine le_trans ?_ h
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg
    intro n hn
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨lt_of_le_of_lt (Nat.zero_le _) hn.1, hn.2⟩
  calc ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)),
        ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ / (n * Real.log n ^ (2 : ℝ))
      ≤ ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)),
          ArithmeticFunction.vonMangoldt n / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), ArithmeticFunction.vonMangoldt n)
          / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) ^ 2) := by
        rw [Finset.sum_div]
    _ ≤ (Real.log 4 + 4) * (2 : ℝ) ^ (j + 1) / ((2 : ℝ) ^ j * ((j : ℝ) * Real.log 2) ^ 2) := by
        gcongr
    _ = 2 * (Real.log 4 + 4) / Real.log 2 ^ 2 / (j : ℝ) ^ 2 := by
        rw [pow_succ]
        field_simp

end CH2Section6
