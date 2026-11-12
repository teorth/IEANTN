import TernaryGoldbach.Statement

/-!
# The circle method (finite form)

For weights `a : ℕ → ℂ` supported on `[0, X]` let `S_a(α) = ∑_{n ≤ X} a(n) e(nα)`.  We prove:

* `integral_e_int`: orthogonality `∫₀¹ e(kα) dα = [k = 0]`;
* `circle_identity`: `∫₀¹ S_a S_b S_c e(-Nα) dα = ∑_{n₁+n₂+n₃=N} a(n₁) b(n₂) c(n₃)`;
* `integral_norm_sq_expSum`: Parseval, `∫₀¹ |S_a|² = ∑ |a(n)|²`;
* `setIntegral_norm_mul_norm_expSum_le`: `∫₀¹ |S_b||S_c| ≤ ‖b‖₂ ‖c‖₂`;
* `norm_integral_minor_le`: the minor arc contribution is `≤ (sup_𝔪 |S_a|) ‖b‖₂ ‖c‖₂`;
* `isSumOfThreePrimes_of_circle`: if the major arcs contribute more than this minor arc
  bound, and the weights are supported on primes, then `N` is a sum of three primes;
* `circle_identity_tsum`: the circle method identity for absolutely summable (infinitely
  supported) weights `T_a(α) = ∑' n, a(n) e(nα)`.

All of this is proved, with no `sorry`.
-/

open Complex MeasureTheory intervalIntegral Finset

namespace TernaryGoldbach

/-- The additive character `e(t) = exp(2πit)`. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * I * t)

theorem e_add (s t : ℝ) : e (s + t) = e s * e t := by
  simp only [e, ofReal_add, mul_add, Complex.exp_add]

theorem e_zero : e 0 = 1 := by simp [e]

theorem continuous_e : Continuous e := by
  unfold e; fun_prop

theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  simp [Complex.norm_exp]

/-- Orthogonality of additive characters on `[0, 1]`. -/
theorem integral_e_int (k : ℤ) :
    ∫ α in (0:ℝ)..1, e (k * α) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [e_zero]
  · have hc : (2 * Real.pi * I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, I_ne_zero, this]
    have : (fun α : ℝ => e (k * α)) = fun α : ℝ => Complex.exp ((2 * Real.pi * I * k) * α) := by
      funext α; simp only [e]; push_cast; ring_nf
    rw [this, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * I * k * ((1:ℝ):ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]; push_cast; ring_nf
    simp only [ofReal_one, mul_one] at h1
    simp [h1]

/-- A finite exponential sum `S(α) = ∑_{n ≤ X} a(n) e(nα)`. -/
noncomputable def expSum (X : ℕ) (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ range (X + 1), a n * e (n * α)

theorem continuous_expSum (X : ℕ) (a : ℕ → ℂ) : Continuous (expSum X a) := by
  unfold expSum
  exact continuous_finsetSum _ fun n _ =>
    continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))

theorem integral_const_mul_e_int (z : ℂ) (k : ℤ) :
    ∫ α in (0:ℝ)..1, z * e (k * α) = if k = 0 then z else 0 := by
  rw [intervalIntegral.integral_const_mul, integral_e_int]
  split_ifs <;> simp

theorem intervalIntegrable_const_mul_e (z : ℂ) (k : ℤ) :
    IntervalIntegrable (fun α : ℝ => z * e (k * α)) volume 0 1 :=
  (continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _

theorem integral_sum_e {ι : Type*} (s : Finset ι) (z : ι → ℂ) (k : ι → ℤ) :
    ∫ α in (0:ℝ)..1, ∑ i ∈ s, z i * e (k i * α) = ∑ i ∈ s, if k i = 0 then z i else 0 := by
  rw [intervalIntegral.integral_finsetSum fun i _ => intervalIntegrable_const_mul_e (z i) (k i)]
  exact sum_congr rfl fun i _ => integral_const_mul_e_int _ _

/-- **The circle method identity.**  The weighted number of representations
`∑_{n₁+n₂+n₃=N} a(n₁) b(n₂) c(n₃)` equals `∫₀¹ S_a(α) S_b(α) S_c(α) e(-Nα) dα`. -/
theorem circle_identity (X N : ℕ) (a b c : ℕ → ℂ) :
    ∫ α in (0:ℝ)..1, expSum X a α * expSum X b α * expSum X c α * e (-(N * α)) =
      ∑ n₁ ∈ range (X + 1), ∑ n₂ ∈ range (X + 1), ∑ n₃ ∈ range (X + 1),
        if n₁ + n₂ + n₃ = N then a n₁ * b n₂ * c n₃ else 0 := by
  have key : ∀ α : ℝ, expSum X a α * expSum X b α * expSum X c α * e (-(N * α)) =
      ∑ n₁ ∈ range (X + 1), ∑ n₂ ∈ range (X + 1), ∑ n₃ ∈ range (X + 1),
        a n₁ * b n₂ * c n₃ * e (((n₁ + n₂ + n₃ : ℕ) - N : ℤ) * α) := by
    intro α
    rw [expSum, expSum, expSum, sum_mul_sum, sum_mul, sum_mul]
    refine sum_congr rfl fun n₁ _ => ?_
    rw [sum_mul, sum_mul]
    refine sum_congr rfl fun n₂ _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun n₃ _ => ?_
    have : (((n₁ + n₂ + n₃ : ℕ) - N : ℤ) : ℝ) * α = n₁ * α + n₂ * α + n₃ * α + -(N * α) := by
      push_cast; ring
    rw [this, e_add, e_add, e_add]
    ring
  set R := range (X + 1)
  have flat : ∀ α : ℝ, expSum X a α * expSum X b α * expSum X c α * e (-(N * α)) =
      ∑ t ∈ R ×ˢ (R ×ˢ R), a t.1 * b t.2.1 * c t.2.2 *
        e (((t.1 + t.2.1 + t.2.2 : ℕ) - N : ℤ) * α) := by
    intro α
    rw [key, sum_product]
    refine sum_congr rfl fun n₁ _ => ?_
    rw [sum_product]
  simp_rw [flat]
  rw [integral_sum_e, sum_product]
  refine sum_congr rfl fun n₁ _ => ?_
  rw [sum_product]
  refine sum_congr rfl fun n₂ _ => sum_congr rfl fun n₃ _ => ?_
  simp only [sub_eq_zero, Nat.cast_inj]


theorem conj_e (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
  simp only [e, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, map_ofNat, ofReal_neg]
  ring_nf

/-- **Parseval's identity** for finite exponential sums. -/
theorem integral_norm_sq_expSum (X : ℕ) (a : ℕ → ℂ) :
    ∫ α in (0:ℝ)..1, ‖expSum X a α‖ ^ 2 = ∑ n ∈ range (X + 1), ‖a n‖ ^ 2 := by
  set R := range (X + 1)
  have key : ∀ α : ℝ, ((‖expSum X a α‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ R ×ˢ R, a t.1 * (starRingEnd ℂ) (a t.2) * e (((t.1 : ℤ) - t.2 : ℤ) * α) := by
    intro α
    rw [ofReal_pow, ← Complex.mul_conj', expSum, map_sum, sum_mul_sum, sum_product]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [map_mul, conj_e]
    have : (((m : ℤ) - n : ℤ) : ℝ) * α = m * α + -(n * α) := by push_cast; ring
    rw [this, e_add]
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  rw [integral_sum_e, sum_product]
  push_cast
  refine sum_congr rfl fun m _ => ?_
  rw [sum_eq_single m]
  · simp [Complex.mul_conj']
  · intro n _ hnm
    have : ((m : ℤ) - n) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (Ne.symm hnm)
    simp [this]
  · intro h; exact absurd ‹m ∈ R› h


theorem le_sqrt_mul_sqrt_of_forall {P A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 < t → P ≤ (t * A + C / t) / 2) : P ≤ √A * √C := by
  by_contra hP
  push Not at hP
  have hP0 : 0 < P := lt_of_le_of_lt (by positivity) hP
  rcases hA.eq_or_lt with hA0 | hA0
  · subst hA0
    have := h ((C + 1) / P) (by positivity)
    rw [mul_zero, zero_add, div_div_eq_mul_div] at this
    have h2 : C * P / (C + 1) < 2 * P := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  rcases hC.eq_or_lt with hC0 | hC0
  · subst hC0
    have := h (P / (A + 1)) (by positivity)
    rw [zero_div, add_zero, div_mul_eq_mul_div] at this
    have h2 : P * A / (A + 1) < 2 * P := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  have hsA := Real.sqrt_pos.2 hA0
  have hsC := Real.sqrt_pos.2 hC0
  have := h (√C / √A) (by positivity)
  have e1 : √C / √A * A = √A * √C := by
    field_simp; nlinarith [Real.mul_self_sqrt hA]
  have e2 : C / (√C / √A) = √A * √C := by
    field_simp; nlinarith [Real.mul_self_sqrt hC]
  rw [e1, e2] at this
  linarith


theorem setIntegral_norm_sq_expSum (X : ℕ) (a : ℕ → ℂ) :
    ∫ α in Set.Ioc (0:ℝ) 1, ‖expSum X a α‖ ^ 2 = ∑ n ∈ range (X + 1), ‖a n‖ ^ 2 := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_norm_sq_expSum]

/-- Cauchy–Schwarz combined with Parseval:
`∫₀¹ |S_b||S_c| ≤ (∑ |b(n)|²)^{1/2} (∑ |c(n)|²)^{1/2}`. -/
theorem setIntegral_norm_mul_norm_expSum_le (X : ℕ) (b c : ℕ → ℂ) :
    ∫ α in Set.Ioc (0:ℝ) 1, ‖expSum X b α‖ * ‖expSum X c α‖ ≤
      √(∑ n ∈ range (X + 1), ‖b n‖ ^ 2) * √(∑ n ∈ range (X + 1), ‖c n‖ ^ 2) := by
  have hb := (continuous_expSum X b).norm
  have hc := (continuous_expSum X c).norm
  apply le_sqrt_mul_sqrt_of_forall (sum_nonneg fun _ _ => by positivity)
    (sum_nonneg fun _ _ => by positivity)
  intro t ht
  rw [← setIntegral_norm_sq_expSum X b, ← setIntegral_norm_sq_expSum X c]
  calc ∫ α in Set.Ioc (0:ℝ) 1, ‖expSum X b α‖ * ‖expSum X c α‖
      ≤ ∫ α in Set.Ioc (0:ℝ) 1, (t * ‖expSum X b α‖ ^ 2 + ‖expSum X c α‖ ^ 2 / t) / 2 := by
        refine setIntegral_mono (hb.mul hc).integrableOn_Ioc
          (by fun_prop : Continuous fun α =>
            (t * ‖expSum X b α‖ ^ 2 + ‖expSum X c α‖ ^ 2 / t) / 2).integrableOn_Ioc ?_
        intro α
        set x := ‖expSum X b α‖
        set y := ‖expSum X c α‖
        have : 0 ≤ (t * x - y) ^ 2 / t := by positivity
        have e : (t * x - y) ^ 2 / t = t * x ^ 2 + y ^ 2 / t - 2 * (x * y) := by
          field_simp; ring
        linarith
    _ = (t * ∫ α in Set.Ioc (0:ℝ) 1, ‖expSum X b α‖ ^ 2) / 2 +
          ((∫ α in Set.Ioc (0:ℝ) 1, ‖expSum X c α‖ ^ 2) / t) / 2 := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_add, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_div,
          add_div]
        · exact (by fun_prop : Continuous fun α => t * ‖expSum X b α‖ ^ 2).integrableOn_Ioc
        · exact (by fun_prop : Continuous fun α => ‖expSum X c α‖ ^ 2 / t).integrableOn_Ioc
    _ = _ := by ring


/-- The integrand of the circle method. -/
noncomputable def circleIntegrand (X N : ℕ) (a b c : ℕ → ℂ) (α : ℝ) : ℂ :=
  expSum X a α * expSum X b α * expSum X c α * e (-(N * α))

theorem continuous_circleIntegrand (X N : ℕ) (a b c : ℕ → ℂ) :
    Continuous (circleIntegrand X N a b c) := by
  unfold circleIntegrand
  exact (((continuous_expSum X a).mul (continuous_expSum X b)).mul (continuous_expSum X c)).mul
    (continuous_e.comp (continuous_const.mul continuous_id).neg)

/-- **Minor arc bound.**  If `|S_a| ≤ B` on the minor arcs `𝔪 = (0,1] \ 𝔐`, then the minor
arc contribution is at most `B ‖b‖₂ ‖c‖₂`. -/
theorem norm_integral_minor_le (X N : ℕ) (a b c : ℕ → ℂ) {M : Set ℝ} (hM : MeasurableSet M)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ α ∈ Set.Ioc (0:ℝ) 1 \ M, ‖expSum X a α‖ ≤ B) :
    ‖∫ α in Set.Ioc (0:ℝ) 1 \ M, circleIntegrand X N a b c α‖ ≤
      B * (√(∑ n ∈ range (X + 1), ‖b n‖ ^ 2) * √(∑ n ∈ range (X + 1), ‖c n‖ ^ 2)) := by
  have hbc : Continuous fun α => B * (‖expSum X b α‖ * ‖expSum X c α‖) := by
    have := continuous_expSum X b; have := continuous_expSum X c; fun_prop
  calc ‖∫ α in Set.Ioc (0:ℝ) 1 \ M, circleIntegrand X N a b c α‖
      ≤ ∫ α in Set.Ioc (0:ℝ) 1 \ M, ‖circleIntegrand X N a b c α‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ α in Set.Ioc (0:ℝ) 1 \ M, B * (‖expSum X b α‖ * ‖expSum X c α‖) := by
        refine setIntegral_mono_on
          ((continuous_circleIntegrand X N a b c).norm.integrableOn_Ioc.mono_set Set.sdiff_subset)
          (hbc.integrableOn_Ioc.mono_set Set.sdiff_subset) (measurableSet_Ioc.diff hM) ?_
        intro α hα
        simp only [circleIntegrand, norm_mul, norm_e, mul_one]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (hB α hα) (by positivity)
    _ ≤ ∫ α in Set.Ioc (0:ℝ) 1, B * (‖expSum X b α‖ * ‖expSum X c α‖) :=
        setIntegral_mono_set hbc.integrableOn_Ioc
          (Filter.Eventually.of_forall fun _ => by positivity)
          (Set.sdiff_subset (s := Set.Ioc (0:ℝ) 1) (t := M)).eventuallyLE
    _ = B * ∫ α in Set.Ioc (0:ℝ) 1, ‖expSum X b α‖ * ‖expSum X c α‖ :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_norm_mul_norm_expSum_le X b c) hB0

/-- If the weighted representation count is nonzero and the weights are supported on primes,
then `N` is a sum of three primes. -/
theorem isSumOfThreePrimes_of_sum_ne_zero (X N : ℕ) (a b c : ℕ → ℂ)
    (ha : ∀ n, a n ≠ 0 → n.Prime) (hb : ∀ n, b n ≠ 0 → n.Prime) (hc : ∀ n, c n ≠ 0 → n.Prime)
    (h : (∑ n₁ ∈ range (X + 1), ∑ n₂ ∈ range (X + 1), ∑ n₃ ∈ range (X + 1),
        if n₁ + n₂ + n₃ = N then a n₁ * b n₂ * c n₃ else 0) ≠ 0) :
    IsSumOfThreePrimes N := by
  obtain ⟨n₁, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨n₂, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨n₃, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hN
  · refine ⟨n₁, n₂, n₃, ha _ ?_, hb _ ?_, hc _ ?_, hN⟩ <;> intro h0 <;> simp [h0] at h
  · exact absurd rfl h

/-- **The circle method criterion.**  Let `a, b, c` be weights supported on primes `≤ X`.
Split `(0, 1]` into major arcs `𝔐` and minor arcs `𝔪 = (0,1] \ 𝔐`.  If the major arc
contribution has real part `≥ L`, `|S_a| ≤ B` on the minor arcs, and
`B ‖b‖₂ ‖c‖₂ < L`, then `N` is a sum of three primes.

This is exactly the shape of Helfgott's argument: the paper's major-arc theorem gives `L`,
its minor-arc theorem gives `B`, and the remaining work is checking the final inequality. -/
theorem isSumOfThreePrimes_of_circle (X N : ℕ) (a b c : ℕ → ℂ)
    (ha : ∀ n, a n ≠ 0 → n.Prime) (hb : ∀ n, b n ≠ 0 → n.Prime) (hc : ∀ n, c n ≠ 0 → n.Prime)
    {M : Set ℝ} (hM : MeasurableSet M) {L B : ℝ} (hB0 : 0 ≤ B)
    (hmajor : L ≤ (∫ α in Set.Ioc (0:ℝ) 1 ∩ M, circleIntegrand X N a b c α).re)
    (hminor : ∀ α ∈ Set.Ioc (0:ℝ) 1 \ M, ‖expSum X a α‖ ≤ B)
    (hineq : B * (√(∑ n ∈ range (X + 1), ‖b n‖ ^ 2) * √(∑ n ∈ range (X + 1), ‖c n‖ ^ 2)) < L) :
    IsSumOfThreePrimes N := by
  apply isSumOfThreePrimes_of_sum_ne_zero X N a b c ha hb hc
  rw [← circle_identity]
  have hsplit := integral_inter_add_sdiff hM
    ((continuous_circleIntegrand X N a b c).integrableOn_Ioc (a := 0) (b := 1) (μ := volume))
  have htot : ∫ α in (0:ℝ)..1, expSum X a α * expSum X b α * expSum X c α * e (-(N * α)) =
      ∫ α in Set.Ioc (0:ℝ) 1, circleIntegrand X N a b c α :=
    intervalIntegral.integral_of_le zero_le_one
  rw [htot, ← hsplit]
  intro h0
  have hmin := norm_integral_minor_le X N a b c hM hB0 hminor
  have hre := congrArg Complex.re h0
  rw [add_re, zero_re] at hre
  have := neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hmin)
  linarith

/-! ## Absolutely convergent exponential series -/

/-- An absolutely convergent exponential series `T_a(α) = ∑ₙ a(n) e(nα)`. -/
noncomputable def expTsum (a : ℕ → ℂ) (α : ℝ) : ℂ := ∑' n, a n * e (n * α)

theorem norm_mul_e (z : ℂ) (t : ℝ) : ‖z * e t‖ = ‖z‖ := by
  rw [norm_mul, norm_e, mul_one]

theorem abs_e (t : ℝ) : ‖e t‖ = 1 := norm_e t

theorem continuous_expTsum {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) :
    Continuous (expTsum a) :=
  continuous_tsum (fun _ => continuous_const.mul (continuous_e.comp
    (continuous_const.mul continuous_id))) ha (fun _ _ => (norm_mul_e _ _).le)

theorem setIntegral_const_mul_e_int (z : ℂ) (k : ℤ) :
    ∫ α in Set.Ioc (0:ℝ) 1, z * e (k * α) = if k = 0 then z else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_const_mul_e_int]

/-- **Circle method identity for absolutely convergent series.** -/
theorem circle_identity_tsum (N : ℕ) {a b c : ℕ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hb : Summable fun n => ‖b n‖) (hc : Summable fun n => ‖c n‖) :
    IntegrableOn (fun α => expTsum a α * expTsum b α * expTsum c α * e (-(N * α)))
        (Set.Ioc 0 1) ∧
      ∫ α in Set.Ioc (0:ℝ) 1, expTsum a α * expTsum b α * expTsum c α * e (-(N * α)) =
        ∑ n₁ ∈ range (N + 1), ∑ n₂ ∈ range (N + 1), ∑ n₃ ∈ range (N + 1),
          if n₁ + n₂ + n₃ = N then a n₁ * b n₂ * c n₃ else 0 := by
  have hcont : Continuous fun α => expTsum a α * expTsum b α * expTsum c α * e (-(N * α)) :=
    (((continuous_expTsum ha).mul (continuous_expTsum hb)).mul (continuous_expTsum hc)).mul
      (continuous_e.comp (continuous_const.mul continuous_id).neg)
  refine ⟨hcont.integrableOn_Ioc, ?_⟩
  -- Summability of the coefficients of the triple product.
  have hab : Summable fun z : ℕ × ℕ => ‖a z.1‖ * ‖b z.2‖ :=
    summable_mul_of_summable_norm (f := fun n => ‖a n‖) (g := fun n => ‖b n‖)
      (by simpa using ha) (by simpa using hb)
  have habc : Summable fun t : (ℕ × ℕ) × ℕ => ‖a t.1.1‖ * ‖b t.1.2‖ * ‖c t.2‖ :=
    summable_mul_of_summable_norm (f := fun z : ℕ × ℕ => ‖a z.1‖ * ‖b z.2‖)
      (g := fun n => ‖c n‖) (by simpa using hab) (by simpa using hc)
  set F : (ℕ × ℕ) × ℕ → ℝ → ℂ := fun t α =>
    a t.1.1 * b t.1.2 * c t.2 * e (((t.1.1 + t.1.2 + t.2 : ℕ) - N : ℤ) * α)
  have hF : ∀ α : ℝ, expTsum a α * expTsum b α * expTsum c α * e (-(N * α)) = ∑' t, F t α := by
    intro α
    have h1 : Summable fun n => ‖a n * e (n * α)‖ := by simpa [norm_mul, abs_e] using ha
    have h2 : Summable fun n => ‖b n * e (n * α)‖ := by simpa [norm_mul, abs_e] using hb
    have h3 : Summable fun n => ‖c n * e (n * α)‖ := by simpa [norm_mul, abs_e] using hc
    have h12 : Summable fun z : ℕ × ℕ => ‖a z.1 * e (z.1 * α) * (b z.2 * e (z.2 * α))‖ := by
      simpa [norm_mul, abs_e] using hab
    rw [expTsum, expTsum, expTsum, tsum_mul_tsum_of_summable_norm h1 h2,
      tsum_mul_tsum_of_summable_norm h12 h3, ← tsum_mul_right]
    refine tsum_congr fun t => ?_
    simp only [F]
    have : (((t.1.1 + t.1.2 + t.2 : ℕ) - N : ℤ) : ℝ) * α =
        t.1.1 * α + t.1.2 * α + t.2 * α + -(N * α) := by push_cast; ring
    rw [this, e_add, e_add, e_add]
    ring
  simp_rw [hF]
  have hFint : ∀ t, Integrable (F t) (volume.restrict (Set.Ioc (0:ℝ) 1)) := fun t =>
    (continuous_const.mul (continuous_e.comp (continuous_const.mul continuous_id))).integrableOn_Ioc
  have hFnorm : ∀ t, ∫ α in Set.Ioc (0:ℝ) 1, ‖F t α‖ = ‖a t.1.1‖ * ‖b t.1.2‖ * ‖c t.2‖ := by
    intro t
    simp [F, norm_mul, abs_e]
  rw [← integral_tsum_of_summable_integral_norm hFint (by simpa only [hFnorm] using habc)]
  simp only [F, setIntegral_const_mul_e_int, sub_eq_zero, Nat.cast_inj]
  rw [tsum_eq_sum (s := (range (N + 1) ×ˢ range (N + 1)) ×ˢ range (N + 1))]
  · rw [sum_product, sum_product]
  · intro t ht
    rw [ite_eq_right]
    intro h
    apply ht
    simp only [mem_product, mem_range]
    omega

end TernaryGoldbach
