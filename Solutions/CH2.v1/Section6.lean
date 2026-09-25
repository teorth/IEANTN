/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import ZetaInstanceNeg
import IEANTN.Nodes.CH2.v2.Conclusions

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


/-! ### Proposition 2.4, from the imported node

`svm_bounds` feeds Proposition 2.4 its approximants. It used to call the proof in `Part1Fourier`
directly; it now takes the result as an imported conclusion, `CH2.v2.proposition_2_4_upper` and
`_lower`, so that CH2.v1's graph shows the edge. The adapters below restate the node's conclusions
in exactly the signature of `prop_2_4_plus` and `prop_2_4_minus`. They agree definitionally --
CH2.v2's own solution proves the node's statements from these by `exact`, and this goes the other
way -- so the adapter is the node's conclusion, repackaged.
-/

namespace CH2Sol

open Real MeasureTheory FourierTransform Chebyshev Asymptotics
open ArithmeticFunction hiding log
open Complex hiding log

theorem prop_2_4_plus_of_v2 (h : CH2.v2.proposition_2_4_upper) {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0)
    {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
    (ha : Summable (fun n : ℕ ↦ ‖(a n : ℂ)‖ / (n * Real.log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / (n ^ s : ℂ) - 1 / (s - 1)) { z | z.re > 1 })
    {φ_plus : ℝ → ℂ} (hφ_mes : Measurable φ_plus) (hφ_int : Integrable φ_plus)
    (hφ_cont : ContinuousAt φ_plus 0)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ_plus x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_plus y‖ ≤ C / |y| ^ β)
    (hI_le_Fourier : ∀ y : ℝ,
      let lambda := (2 * π * (σ - 1)) / T
      I' lambda y ≤ (𝓕 φ_plus y).re)
    (x : ℝ) (hx : 1 ≤ x) :
    S a σ x ≤
      ((2 * π * (x ^ (1 - σ) : ℝ) / T) * φ_plus 0).re +
      (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_plus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if σ < 1 then 1 / (1 - σ) else 0 :=
  h a T β σ G φ_plus x ⟨ha_pos, ha⟩ hT hβ hσ ⟨hG, hG'⟩
    ⟨hφ_mes, hφ_int, hφ_cont, hφ_supp, hφ_Fourier⟩ hI_le_Fourier hx

theorem prop_2_4_minus_of_v2 (h : CH2.v2.proposition_2_4_lower) {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0)
    {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
    (ha : Summable (fun n ↦ ‖(a n : ℂ)‖ / (n * Real.log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / (n ^ s : ℂ) - 1 / (s - 1)) { z | z.re > 1 })
    {φ_minus : ℝ → ℂ} (hφ_mes : Measurable φ_minus) (hφ_int : Integrable φ_minus)
    (hφ_cont : ContinuousAt φ_minus 0)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ_minus x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_minus y‖ ≤ C / |y| ^ β)
    (hFourier_le_I : ∀ y : ℝ,
      let lambda := (2 * π * (σ - 1)) / T
      (𝓕 φ_minus y).re ≤ I' lambda y)
    {x : ℝ} (hx : 1 ≤ x) :
    S a σ x ≥
      ((2 * π * (x ^ (1 - σ) : ℝ) / T) * φ_minus 0).re +
      (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_minus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if σ < 1 then 1 / (1 - σ) else 0 :=
  h a T β σ G φ_minus x ⟨ha_pos, ha⟩ hT hβ hσ ⟨hG, hG'⟩
    ⟨hφ_mes, hφ_int, hφ_cont, hφ_supp, hφ_Fourier⟩ hFourier_le_I hx

end CH2Sol

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

/-! ### `F` as `prop_2_4`'s `G` -/

open CH2ZetaInstance in
/-- `F` is continuous on the closed half-plane `Re s ≥ 1`: `ζ` has no zeros there, and the pole at
`1` is removed. -/
theorem F_continuousOn_right (T : ℝ) :
    ContinuousOn F {z : ℂ | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T} := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  by_cases h1 : z = 1
  · rw [h1]; exact analyticAt_F_one.continuousAt
  · exact (analyticAt_F_of_zeta_ne_zero h1 (riemannZeta_ne_zero_of_one_le_re hz.1)).continuousAt

open CH2ZetaInstance in
/-- On `Re s > 1`, `F(s) = ∑ Λ(n) n^{-s} - 1/(s-1)`. -/
theorem F_eqOn_dirichlet :
    Set.EqOn F
      (fun s ↦ ∑' n, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s) - 1 / (s - 1))
      {z : ℂ | z.re > 1} := by
  intro s hs
  have hs1 : 1 < s.re := hs
  have hne1 : s ≠ 1 := by intro h; rw [h] at hs1; simp at hs1
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  simp only
  rw [F, logDeriv_riemannZeta₁_eq hne1 hz, logDeriv_apply]
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
  have hts : LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s
      = ∑' n, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s) := by
    rw [LSeries]
    refine tsum_congr fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h, LSeries.term]
    · rw [LSeries.term_of_ne_zero h.ne']
  rw [← hts, hL]
  ring

/-! ### The vertical integral of `prop_2_4` is the one `prop_5_2` shifts -/

/-- On the segment, `Φ_λ(z(1 + it)) = ϕ_pm |λ| ε (-t/T)` for `λ < 0`. -/
theorem Phi_lambda_segment_neg (l : CH2.LadderParams) {lam ε : ℝ} (hlam : lam < 0) (t : ℝ)
    (ht : t ∈ Set.Icc (-l.T) l.T) :
    CH2.Phi_lambda lam ε (l.zOf (((1 : ℝ) : ℂ) + (t : ℂ) * I)) = phiNeg |lam| ε (t / l.T) := by
  have hT := l.hT
  have hz : l.zOf (((1 : ℝ) : ℂ) + (t : ℂ) * I) = ((t / l.T : ℝ) : ℂ) := by
    rw [CH2.LadderParams.zOf]
    have hTc : (l.T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
    push_cast
    field_simp
    ring
  have hmem : -1 ≤ -(t / l.T) ∧ -(t / l.T) ≤ 1 := by
    obtain ⟨h1, h2⟩ := ht
    constructor
    · rw [neg_le_neg_iff, div_le_one hT]; exact h2
    · rw [neg_le, le_div_iff₀ hT]; linarith
  rw [hz, CH2.Phi_lambda, phiNeg, CH2.ϕ_pm, if_pos hmem, CH2.sign_cast_neg_one hlam]
  simp only [Complex.ofReal_re, Real.sign_neg, Complex.ofReal_neg, neg_one_mul]

/-- **The identification.** `prop_2_4`'s integral is `2π` times the normalised vertical integral
that `prop_5_2_zeta_neg` controls. -/
theorem integral_segment_eq_intVerticalAt (l : CH2.LadderParams) {lam ε x : ℝ} (hlam : lam < 0) :
    (∫ t in Set.Icc (-l.T) l.T,
        phiNeg |lam| ε (t / l.T) * CH2ZetaInstance.F (1 + t * I) * ((x : ℂ) ^ (1 + (t : ℂ) * I)))
      = 2 * (π : ℂ) * ((2 * (π : ℂ) * I)⁻¹ * l.intVerticalAt 1
          (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s)) := by
  have hT := l.hT
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  rw [CH2.LadderParams.intVerticalAt, CH2.intVSeg,
    intervalIntegral.integral_of_le (by linarith : -l.T ≤ l.T),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_mul_const]
  have hcongr : (∫ t in Set.Icc (-l.T) l.T,
        CH2.Phi_lambda lam ε (l.zOf (((1 : ℝ) : ℂ) + (t : ℂ) * I))
          * CH2ZetaInstance.F (((1 : ℝ) : ℂ) + (t : ℂ) * I)
          * (x : ℂ) ^ (((1 : ℝ) : ℂ) + (t : ℂ) * I))
      = ∫ t in Set.Icc (-l.T) l.T,
        phiNeg |lam| ε (t / l.T) * CH2ZetaInstance.F (1 + t * I) * ((x : ℂ) ^ (1 + (t : ℂ) * I)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [Phi_lambda_segment_neg l hlam t ht, Complex.ofReal_one]
  rw [hcongr]
  generalize (∫ t in Set.Icc (-l.T) l.T,
      phiNeg |lam| ε (t / l.T) * CH2ZetaInstance.F (1 + t * I) * ((x : ℂ) ^ (1 + (t : ℂ) * I))) = X
  field_simp

/-! ### The two one-sided bounds -/

/-- `λ = 2π(σ-1)/T`. -/
noncomputable def lamOf (T σ : ℝ) : ℝ := 2 * π * (σ - 1) / T

theorem lamOf_neg {T σ : ℝ} (hT : 0 < T) (hσ : σ < 1) : lamOf T σ < 0 := by
  unfold lamOf
  apply div_neg_of_neg_of_pos _ hT
  have := Real.pi_pos
  nlinarith

theorem sigmaOf_lamOf (l : CH2.LadderParams) {σ : ℝ} (hσ : σ < 1) :
    l.sigmaOf (lamOf l.T σ) = σ := by
  have hT := l.hT
  rw [CH2.LadderParams.sigmaOf, abs_of_neg (lamOf_neg hT hσ), lamOf]
  have := Real.pi_pos
  field_simp
  ring

/-- The error term of `prop_5_2_zeta_neg`, named. -/
noncomputable def shiftError (l : CH2.LadderParams) (lam ε x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ((1 / l.T) *
        ((∫ t in Set.Ioi (0 : ℝ), t * ‖CH2ZetaInstance.F (1 - t + l.T * Complex.I)‖ * x ^ (1 - t)) +
          ∫ t in Set.Ioi (0 : ℝ), t * ‖CH2ZetaInstance.F (1 - t - l.T * Complex.I)‖ * x ^ (1 - t)) +
      2 * ‖l.intC (fun s ↦ CH2.Phi_star |lam| ε ((Real.sign lam : ℂ) * l.zOf s) *
          CH2ZetaInstance.F s * (x : ℂ) ^ s)‖)

/-- The residue sum of `prop_5_2_zeta_neg`, named. -/
noncomputable def shiftResidues (l : CH2.LadderParams) (lam ε x : ℝ) : ℂ :=
  sumResiduesIn (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s)
      (l.R \ l.RC) +
    l.sumResiduesLim
      (fun s ↦ CH2.Phi_circ |lam| ε ((Real.sign lam : ℂ) * l.zOf s) * CH2ZetaInstance.F s *
        (x : ℂ) ^ s) l.RC

/-- `ψ` for Section 6: the partial sum `∑_{n ≤ x} Λ(n) n^{-σ}`, as `prop_2_4` writes it. -/
noncomputable abbrev Svm (σ x : ℝ) : ℝ :=
  CH2Sol.S (fun n ↦ ArithmeticFunction.vonMangoldt n) σ x

/-- **The one-sided bounds for `σ ∈ [0, 1)`.** Proposition 2.4 with the reflected Graham–Vaaler
majorant and minorant, its segment integral shifted by `prop_5_2_zeta_neg`. What is left is the
residue sum, still in `sumResiduesIn` form, and the explicit error. -/
theorem svm_bounds
    (hfe : ZetaLogDeriv.v1.logDeriv_functional_equation)
    (hdig : GammaAsymptotics.v2.digamma_sub_log_isBigO_strip)
    (h24u : CH2.v2.proposition_2_4_upper)
    (h24l : CH2.v2.proposition_2_4_lower)
    {l : CH2.LadderParams} (hsig : l.σ = CH2ZetaInstance.sigmaZeta)
    (hTfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.T)
    (hdfree : ∀ z : ℂ, riemannZeta z = 0 → |z.im| ≠ l.δ)
    {σ x₀ x : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hσζ : riemannZeta (σ : ℂ) ≠ 0)
    (hx₀ : 1 < x₀) (hx : x₀ < x) :
    Svm σ x ≤ (2 * π * x ^ (1 - σ) / l.T) * (phiNeg |lamOf l.T σ| 1 0).re
        + 2 * π * x ^ (-σ) / l.T *
          ((shiftResidues l (lamOf l.T σ) 1 x).re + shiftError l (lamOf l.T σ) 1 x)
        - 1 / (1 - σ) ∧
    (2 * π * x ^ (1 - σ) / l.T) * (phiNeg |lamOf l.T σ| (-1) 0).re
        + 2 * π * x ^ (-σ) / l.T *
          ((shiftResidues l (lamOf l.T σ) (-1) x).re - shiftError l (lamOf l.T σ) (-1) x)
        - 1 / (1 - σ) ≤ Svm σ x := by
  have hT := l.hT
  set lam := lamOf l.T σ with hlam_def
  have hlam : lam < 0 := lamOf_neg hT hσ1
  have hν : 0 < |lam| := abs_pos.mpr hlam.ne
  have hlam_abs : lam = -|lam| := by rw [abs_of_neg hlam]; ring
  have hσ' : l.sigmaOf lam = σ := sigmaOf_lamOf l hσ1
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have ha_pos : ∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) ≥ 0 :=
    fun n ↦ ArithmeticFunction.vonMangoldt_nonneg
  have hsumm := summable_vonMangoldt_div_log_sq
  have hGc := F_continuousOn_right l.T
  have hGe := F_eqOn_dirichlet
  -- the shift, for each sign
  have hshift : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt 1 (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s *
            (x : ℂ) ^ s) - shiftResidues l lam ε x‖ ≤ shiftError l lam ε x := by
    intro ε hε
    have h := CH2ZetaInstance.prop_5_2_zeta_neg hfe hdig hsig hTfree hdfree hlam hε
      (by rw [hσ']; exact hσ0) (by rw [hσ']; exact hσζ) hx₀ hx
    unfold shiftResidues shiftError
    rw [show ∀ a b c : ℂ, a - (b + c) = a - b - c from fun a b c ↦ by ring]
    exact h
  -- `Re V ≤ Re Res + E` and `Re Res - E ≤ Re V`
  have hre_le : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt 1 (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s *
            (x : ℂ) ^ s)).re ≤ (shiftResidues l lam ε x).re + shiftError l lam ε x ∧
      (shiftResidues l lam ε x).re - shiftError l lam ε x ≤
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          l.intVerticalAt 1 (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s *
            (x : ℂ) ^ s)).re := by
    intro ε hε
    have h := hshift ε hε
    have hre := (Complex.abs_re_le_norm _).trans h
    rw [Complex.sub_re] at hre
    constructor <;> linarith [abs_le.mp hre]
  -- the segment integral as `2π V`
  have hseg : ∀ ε : ℝ, (∫ t in Set.Icc (-l.T) l.T,
        phiNeg |lam| ε (t / l.T) * CH2ZetaInstance.F (1 + t * I) * ((x : ℂ) ^ (1 + (t : ℂ) * I))).re
      = 2 * π * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * l.intVerticalAt 1
          (fun s ↦ CH2.Phi_lambda lam ε (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s)).re := by
    intro ε
    rw [integral_segment_eq_intVerticalAt l hlam]
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  have hσne : σ ≠ 1 := hσ1.ne
  constructor
  · have hP := CH2Sol.prop_2_4_plus_of_v2 h24u (a := fun n ↦ ArithmeticFunction.vonMangoldt n) ha_pos
      hT (by norm_num : (1 : ℝ) < 2) hσne hsumm hGc hGe
      (phiNeg_measurable hν 1) (phiNeg_integrable hν 1) (phiNeg_continuousAt hν 1)
      (fun x hx ↦ phiNeg_zero_outside |lam| 1 hx) (phiNeg_fourier_decay hν (Or.inl rfl))
      (fun y ↦ by
        show CH2Sol.I' (2 * π * (σ - 1) / l.T) y ≤ _
        rw [show 2 * π * (σ - 1) / l.T = -|lam| by rw [← hlam_abs]; rfl]
        exact phiNeg_majorant hν y)
      x hx1
    rw [if_pos hσ1] at hP
    have h1 := (hre_le 1 (Or.inl rfl)).1
    rw [hseg 1] at hP
    set V := ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * l.intVerticalAt 1
      (fun s ↦ CH2.Phi_lambda lam 1 (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s)).re with hV
    have hphi : (2 * (π : ℂ) * ((x ^ (1 - σ) : ℝ) : ℂ) / (l.T : ℂ) * phiNeg |lam| 1 0).re
        = (2 * π * x ^ (1 - σ) / l.T) * (phiNeg |lam| 1 0).re := by
      rw [show (2 * (π : ℂ) * ((x ^ (1 - σ) : ℝ) : ℂ) / (l.T : ℂ))
          = ((2 * π * x ^ (1 - σ) / l.T : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    have hc : (0 : ℝ) ≤ x ^ (-σ) / l.T * (2 * π) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hc
    have e1 : x ^ (-σ) / l.T * (2 * π * V) = (x ^ (-σ) / l.T * (2 * π)) * V := by ring
    have e2 : 2 * π * x ^ (-σ) / l.T * ((shiftResidues l lam 1 x).re + shiftError l lam 1 x)
        = (x ^ (-σ) / l.T * (2 * π)) * ((shiftResidues l lam 1 x).re + shiftError l lam 1 x) := by
      ring
    rw [hphi] at hP
    linarith [hP, h2, e1, e2]
  · have hM := CH2Sol.prop_2_4_minus_of_v2 h24l (a := fun n ↦ ArithmeticFunction.vonMangoldt n) ha_pos
      hT (by norm_num : (1 : ℝ) < 2) hσne hsumm hGc hGe
      (phiNeg_measurable hν (-1)) (phiNeg_integrable hν (-1)) (phiNeg_continuousAt hν (-1))
      (fun x hx ↦ phiNeg_zero_outside |lam| (-1) hx) (phiNeg_fourier_decay hν (Or.inr rfl))
      (fun y ↦ by
        show _ ≤ CH2Sol.I' (2 * π * (σ - 1) / l.T) y
        rw [show 2 * π * (σ - 1) / l.T = -|lam| by rw [← hlam_abs]; rfl]
        exact phiNeg_minorant hν y)
      hx1
    rw [if_pos hσ1] at hM
    have h1 := (hre_le (-1) (Or.inr rfl)).2
    rw [hseg (-1)] at hM
    set V := ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * l.intVerticalAt 1
      (fun s ↦ CH2.Phi_lambda lam (-1) (l.zOf s) * CH2ZetaInstance.F s * (x : ℂ) ^ s)).re with hV
    have hphi : (2 * (π : ℂ) * ((x ^ (1 - σ) : ℝ) : ℂ) / (l.T : ℂ) * phiNeg |lam| (-1) 0).re
        = (2 * π * x ^ (1 - σ) / l.T) * (phiNeg |lam| (-1) 0).re := by
      rw [show (2 * (π : ℂ) * ((x ^ (1 - σ) : ℝ) : ℂ) / (l.T : ℂ))
          = ((2 * π * x ^ (1 - σ) / l.T : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    have hc : (0 : ℝ) ≤ x ^ (-σ) / l.T * (2 * π) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 hc
    have e1 : x ^ (-σ) / l.T * (2 * π * V) = (x ^ (-σ) / l.T * (2 * π)) * V := by ring
    have e2 : 2 * π * x ^ (-σ) / l.T * ((shiftResidues l lam (-1) x).re - shiftError l lam (-1) x)
        = (x ^ (-σ) / l.T * (2 * π)) * ((shiftResidues l lam (-1) x).re
          - shiftError l lam (-1) x) := by
      ring
    rw [hphi] at hM
    linarith [hM, h2, e1, e2]

end CH2Section6
