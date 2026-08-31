/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import WienerPort
import Mathlib.Algebra.Order.Field.Pointwise
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Meromorphic
import Mathlib.Data.Int.Star
import Mathlib.Data.PNat.Interval
import Mathlib.Data.Real.Sign
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Fourier core of Chirre-Helfgott, ported

`PrimeNumberTheoremAnd`'s `CH2_part1.lean` up to its "Extremal approximants" section, which is
Propositions 2.3 and 2.4 together with the machinery they rest on. The mathematics is theirs; what
changes here is that the file stands alone against Mathlib rather than against their development,
and that their `@[blueprint ...]` attributes -- LeanArchitect machinery that does not exist in this
repository -- are stripped.

Their `S` and `I'` are this node's `CH2.v2.partialSum` and `CH2.v2.truncExp`; `Solution.lean`
bridges the two.
-/


open Real

namespace CH2Sol

open Real MeasureTheory FourierTransform Chebyshev Asymptotics
open ArithmeticFunction hiding log
open Complex hiding log

lemma pnat_one_le (n : ℕ+) : 1 ≤ (n : ℕ) := n.2

lemma summable_nterm_of_log_weight {a : ℕ → ℂ} {β sig : ℝ}
    (hsig : 1 < sig) (ha : Summable (fun n : ℕ ↦ ‖a n‖ / (n * Real.log n ^ β))) :
    Summable (nterm a sig) := by
  have hs : 0 < sig - 1 := sub_pos.mpr hsig
  have hlo : (fun x : ℝ => Real.log x ^ β) =o[Filter.atTop] fun x => x ^ (sig - 1) :=
    isLittleO_log_rpow_rpow_atTop β hs
  have hlo_nat :
      (fun n : ℕ => Real.log (n : ℝ) ^ β) =o[Filter.atTop] fun n => (n : ℝ) ^ (sig - 1) :=
    hlo.comp_tendsto tendsto_natCast_atTop_atTop
  have hlog_le : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log (n : ℝ) ^ β‖ ≤ ‖(n : ℝ) ^ (sig - 1)‖ := by
    simpa using hlo_nat.bound (show (0 : ℝ) < 1 by norm_num)
  have h_event : ∀ᶠ n : ℕ in Filter.atTop,
      ‖(if n = 0 then 0 else ‖a n‖ / (n : ℝ) ^ sig)‖ ≤ ‖a n‖ / ((n : ℝ) * Real.log n ^ β) := by
    filter_upwards [hlog_le, Filter.eventually_ge_atTop (2 : ℕ)] with n hlog hn
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hpowpos : 0 < Real.log (n : ℝ) ^ β := Real.rpow_pos_of_pos hlogpos _
    have hlog_le' : Real.log (n : ℝ) ^ β ≤ (n : ℝ) ^ (sig - 1) := by
      rwa [Real.norm_of_nonneg hpowpos.le, Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hlog
    have hpow_split : (n : ℝ) ^ sig = (n : ℝ) * (n : ℝ) ^ (sig - 1) := by
      conv_lhs => rw [show sig = 1 + (sig - 1) by ring]; rw [Real.rpow_add hnpos, Real.rpow_one]
    rw [show (if n = 0 then 0 else ‖a n‖ / (n : ℝ) ^ sig) = ‖a n‖ / (n : ℝ) ^ sig from
        by simp [show n ≠ 0 by omega], Real.norm_of_nonneg (div_nonneg (norm_nonneg _)
        (Real.rpow_nonneg hnpos.le _)), hpow_split]
    exact div_le_div_of_nonneg_left (norm_nonneg (a n)) (mul_pos hnpos hpowpos)
      (mul_le_mul_of_nonneg_left hlog_le' hnpos.le)
  have hbase : Summable (fun n : ℕ ↦ if n = 0 then 0 else ‖a n‖ / n ^ sig) :=
    Summable.of_norm_bounded_eventually_nat ha h_event
  simpa [nterm] using! hbase

lemma fourier_scale_div_noscalar (φ : ℝ → ℂ) (T u : ℝ) (hT : 0 < T) :
    𝓕 (fun t : ℝ ↦ φ (t / T)) u = (T : ℂ) * 𝓕 φ (T * u) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have hcomp : (fun v : ℝ ↦ 𝐞 (-(v * u)) • φ (v / T)) =
      fun v : ℝ ↦ (fun z : ℝ ↦ 𝐞 (-(z * (T * u))) • φ z) (v / T) := by
    ext v; congr 2; simp [show (v / T) * (T * u) = v * u from by field_simp [hT.ne']]
  rw [hcomp]
  simpa [abs_of_pos hT, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
    Measure.integral_comp_div (g := fun z : ℝ ↦ 𝐞 (-(z * (T * u))) • φ z) T

theorem prop_2_3_1 {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (_hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ}
    (hG' : Set.EqOn G (fun s ↦ LSeries a s - 1 / (s - 1)) { z | z.re > 1 })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0) -- this hypothesis may be unnecessary
    (_hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x sig : ℝ) (hx : 0 < x) (hsig : 1 < sig) :
    (1 / (2 * π)) * ∑' (n : ℕ), (x : ℂ) * LSeries.term a sig n *
      𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        (∫ t in Set.Icc (-T) T, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I)) +
      (x ^ (2 - sig) / (2 * π * T) : ℝ) *
        (∫ u in Set.Ici (-log x), Real.exp (-u * (sig - 1)) *
          𝓕 (fun t : ℝ ↦ φ (t / T)) (u / (2 * π))) := by
  let phiScaled : ℝ → ℂ := fun t => φ (t / T)
  have hphiScaled_meas : Measurable phiScaled := by simp only [phiScaled]; fun_prop
  have hphiScaled_int : Integrable phiScaled :=
    (MeasureTheory.integrable_comp_mul_right_iff (g := φ) (inv_ne_zero hT.ne')).2 hφ_int |>.congr
      (by simp [phiScaled, div_eq_mul_inv])
  have hsummable : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm a σ') :=
    fun σ' hσ' => summable_nterm_of_log_weight hσ' ha
  have hfirst := @first_fourier x sig phiScaled a hsummable hphiScaled_int hx hsig
  have hsecond := @second_fourier phiScaled hphiScaled_meas hphiScaled_int x sig hx hsig
  have hxpow (t : ℝ) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  let C0 : ℝ := ∑' n : ℕ, nterm a sig n
  have hC0_nonneg : 0 ≤ C0 := tsum_nonneg fun n => by
    by_cases hn : n = 0 <;> simp [nterm, hn, div_nonneg, Real.rpow_nonneg]
  have hLS_bound (t : ℝ) : ‖LSeries a (sig + t * I)‖ ≤ C0 := by
    have hs_term : Summable (fun n : ℕ => ‖LSeries.term a (sig + t * I) n‖) := by
      convert hsummable sig hsig with n; simp [norm_term_eq_nterm_re]
    exact (norm_tsum_le_tsum_norm hs_term).trans (by simp [C0, norm_term_eq_nterm_re])
  have hLS_aesm : AEStronglyMeasurable (fun t : ℝ ↦ LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) :=
    (((continuous_LSeries_aux (hsummable sig hsig)).measurable.mul hphiScaled_meas).mul
      (continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])).measurable).aestronglyMeasurable
  have hLS_int : Integrable (fun t : ℝ ↦ LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) :=
    .mono' (hphiScaled_int.norm.const_mul C0) hLS_aesm (.of_forall fun t => by
      simp only [norm_mul, mul_assoc, hxpow, mul_one]
      exact mul_le_mul_of_nonneg_right (hLS_bound t) (norm_nonneg _))
  have hPole_denom_ne (t : ℝ) : sig + t * I - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hPole_bound (t : ℝ) : ‖1 / (sig + t * I - 1)‖ ≤ (sig - 1)⁻¹ := by
    have hσpos : 0 < sig - 1 := sub_pos.mpr hsig
    simpa [norm_div, one_div] using one_div_le_one_div_of_le hσpos
      (by simpa [abs_of_pos hσpos] using Complex.abs_re_le_norm (sig + t * I - 1))
  have hcontX : Continuous (fun t : ℝ => (x : ℂ) ^ (t * I)) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have hPole_aesm :
      AEStronglyMeasurable (fun t : ℝ ↦ (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) :=
    (((by simpa [one_div, Pi.inv_def] using Continuous.inv₀ (by fun_prop) (hPole_denom_ne) :
      Continuous (fun t : ℝ => (1 / (sig + t * I - 1) : ℂ))).measurable.mul hphiScaled_meas).mul
        hcontX.measurable).aestronglyMeasurable
  have hPole_int : Integrable (fun t : ℝ ↦ (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) :=
    .mono' (hphiScaled_int.norm.const_mul (sig - 1)⁻¹) hPole_aesm (.of_forall fun t => by
      simp only [norm_mul, mul_assoc, hxpow, mul_one]
      exact mul_le_mul_of_nonneg_right (hPole_bound t) (norm_nonneg _))
  have hG_rewrite :
      ∫ t : ℝ, phiScaled t * G (sig + t * I) * x ^ (t * I) =
        (∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
          ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
    rw [← integral_sub hLS_int hPole_int]; congr 1; ext t
    rw [hG' (by simp [hsig] : (sig + t * I).re > 1)]; ring
  have hIcc_to_univ :
      ∫ t in Set.Icc (-T) T, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) =
        ∫ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) := by
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (.of_forall fun t => ?_)
    by_cases ht : t ∈ Set.Icc (-T) T
    · simp [ht]
    · simp [ht, hφ_supp _ (show t / T ∉ Set.Icc (-1) 1 from by
        intro ⟨h1, h2⟩; exact ht ⟨by linarith [(le_div_iff₀ hT).mp h1],
          by linarith [(div_le_iff₀ hT).mp h2]⟩)]
  have hG_with_x :
      (1 / (2 * π * T)) *
          ∫ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) =
        (x / (2 * π * T) : ℂ) *
          ((∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
            ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) := by
    have hcpow (t : ℝ) : (x : ℂ) ^ (1 + ↑t * I) = x * x ^ (↑t * I) := by
      rw [Complex.cpow_add (x := (x : ℂ)) (y := (1 : ℂ)) (z := t * I)
        (by exact_mod_cast hx.ne')]; simp
    simp_rw [show ∀ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + ↑t * I) =
        (x : ℂ) * (phiScaled t * G (sig + t * I) * x ^ (↑t * I)) from
      fun t => by rw [hcpow]; simp only [phiScaled]; ring]
    rw [show (∫ (t : ℝ), (x : ℂ) * (phiScaled t * G (sig + t * I) * x ^ (↑t * I))) =
        (x : ℂ) * ∫ (t : ℝ), phiScaled t * G (sig + t * I) * x ^ (↑t * I) from
      MeasureTheory.integral_const_mul _ _]
    simp_rw [hG_rewrite]; ring
  have hPole_from_second :
      (x ^ (2 - sig) / (2 * π * T) : ℝ) * ∫ u in Set.Ici (-log x),
          Real.exp (-u * (sig - 1)) * 𝓕 phiScaled (u / (2 * π)) =
        (x / (2 * π * T) : ℂ) *
          ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
    have hpowx : (x ^ (2 - sig) * x ^ (sig - 1) : ℝ) = x := by
      rw [← Real.rpow_add hx]; norm_num
    calc (x ^ (2 - sig) / (2 * π * T) : ℝ) * ∫ u in Set.Ici (-log x),
            Real.exp (-u * (sig - 1)) * 𝓕 phiScaled (u / (2 * π))
        _ = ((x ^ (2 - sig) / (2 * π * T) * x ^ (sig - 1) : ℝ) : ℂ) *
              ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
            rw [hsecond]; push_cast; ring
        _ = _ := by rw [show (x ^ (2 - sig) / (2 * π * T) * x ^ (sig - 1) : ℝ) = x / (2 * π * T)
              from by rw [div_mul_eq_mul_div, hpowx]]; simp
  have hleft_scale :
      (1 / (2 * π)) * ∑' n : ℕ, (x : ℂ) * LSeries.term a sig n * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
        (x / (2 * π * T) : ℂ) *
          ∑' n : ℕ, LSeries.term a sig n * 𝓕 phiScaled ((1 / (2 * π)) * log (n / x)) := by
    have hS : ∑' n : ℕ, LSeries.term a sig n * 𝓕 phiScaled ((1 / (2 * π)) * log (n / x)) =
        (T : ℂ) * ∑' n : ℕ, LSeries.term a sig n * 𝓕 φ (T * ((1 / (2 * π)) * log (n / x))) := by
      rw [← tsum_mul_left]; congr with n
      simpa [phiScaled, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun z : ℂ => LSeries.term a sig n * z)
          (fourier_scale_div_noscalar φ T ((1 / (2 * π)) * log (↑n / x)) hT)
    simp_rw [hS, ← tsum_mul_left]; field_simp [hT.ne']
  rw [hleft_scale, hfirst]
  rw [show (x / (2 * π * T) : ℂ) * ∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I) =
      (x / (2 * π * T) : ℂ) * ((∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
        ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) +
      (x / (2 * π * T) : ℂ) * ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) from
    by rw [mul_sub, sub_add_cancel]]
  rw [← hG_with_x, ← hIcc_to_univ, ← hPole_from_second]

lemma rpow_neg_integrableAtFilter_atTop {β : ℝ} (hβ : 1 < β) :
    IntegrableAtFilter (fun y : ℝ ↦ |y| ^ (-β)) Filter.atTop volume := by
  refine ⟨Set.Ioi 1, Filter.Ioi_mem_atTop 1, ?_⟩
  rw [integrableOn_congr_fun (fun y hy ↦ ?_) measurableSet_Ioi]
  · rw [integrableOn_Ioi_rpow_iff zero_lt_one]; exact neg_lt_neg_iff.mpr hβ
  · exact congrArg (· ^ (-β)) (abs_of_pos (zero_lt_one.trans_le (Set.mem_Ioi.mp hy).le))

lemma fourier_integrable_of_rpow_decay {β : ℝ} (hβ : 1 < β)
    {φ : ℝ → ℂ} (hφ_int : Integrable φ)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β) :
    Integrable (𝓕 φ) := by
  obtain ⟨C, hC⟩ := hφ_Fourier
  have h_cont : Continuous (𝓕 φ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hφ_int
  have h_loc : LocallyIntegrable (𝓕 φ) := h_cont.locallyIntegrable
  have h_int_top := rpow_neg_integrableAtFilter_atTop hβ
  have h_int_bot : IntegrableAtFilter (fun y : ℝ ↦ |y| ^ (-β)) Filter.atBot volume := by
    rw [← Filter.map_neg_atTop, measurableEmbedding_neg.integrableAtFilter_iff_comap]
    have : (volume : Measure ℝ).comap Neg.neg = volume := by
      convert! (MeasurableEquiv.neg ℝ).map_symm.symm using 1; simp
    rw [this, Function.comp_def]; simp only [abs_neg]; exact h_int_top
  have h_bound : ∀ y ≠ 0, ‖𝓕 φ y‖ ≤ C * ‖|y| ^ (-β)‖ := fun y hy ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), rpow_neg (abs_nonneg y), ← div_eq_mul_inv]
    exact hC y hy
  apply h_loc.integrable_of_isBigO_atBot_atTop (g := fun y ↦ |y| ^ (-β)) (g' := fun y ↦ |y| ^ (-β))
  · apply IsBigO.of_bound C; filter_upwards [Filter.eventually_ne_atBot 0] with y hy using h_bound y hy
  · exact h_int_bot
  · apply IsBigO.of_bound C; filter_upwards [Filter.eventually_ne_atTop 0] with y hy using h_bound y hy
  · exact h_int_top

lemma pnat_atTop_eq_cofinite : (Filter.atTop : Filter ℕ+) = Filter.cofinite := by
  refine le_antisymm ?_ ?_
  · rw [Filter.le_cofinite_iff_compl_singleton_mem]
    intro n
    rw [Filter.mem_atTop_sets]
    use n + 1
    intro m hm
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (hm.trans_lt' (PNat.lt_add_right n 1)).ne'
  · intro s hs
    rw [Filter.mem_atTop_sets] at hs
    rw [Filter.mem_cofinite]
    obtain ⟨n, hn⟩ := hs
    apply Set.Finite.of_finite_image (f := ((↑) : ℕ+ → ℕ))
    · apply (Set.finite_lt_nat n).subset
      intro y hy
      obtain ⟨m, hm, rfl⟩ := hy
      exact not_le.mp (fun h_le ↦ hm (hn m h_le))
    · exact Set.injOn_subtype_val

lemma fourier_decay_isO_log_rpow
    {β : ℝ} (hβ : 1 < β) {T : ℝ} (hT : 0 < T)
    {x : ℝ} (hx : 0 < x) {φ : ℝ → ℂ}
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β) :
    (fun n : ℕ+ ↦ ‖𝓕 φ ((T / (2 * π)) * log (↑n / x))‖)
      =O[Filter.atTop] (fun n ↦ log (↑n) ^ (-β)) := by
  obtain ⟨C, hC⟩ := hφ_Fourier
  let y (n : ℕ+) : ℝ := (T / (2 * π)) * log (↑n / x)
  have h_y_pos : ∀ᶠ (n : ℕ+) in Filter.atTop, 0 < y n := by
    let n₀ : ℕ+ := ⟨⌊x⌋₊ + 1, Nat.succ_pos _⟩
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    have hnx : x < (n : ℝ) := by
      rw [← Nat.floor_lt hx.le]
      exact_mod_cast (Nat.lt_of_succ_le hn)
    apply mul_pos (by positivity)
    exact log_pos (by rwa [lt_div_iff₀ hx, one_mul])
  have h_y_ne_zero : ∀ᶠ (n : ℕ+) in Filter.atTop, y n ≠ 0 := h_y_pos.mono (fun n hn ↦ hn.ne')
  have h_y_ge : ∀ᶠ (n : ℕ+) in Filter.atTop, (T / (4 * π)) * log n ≤ y n := by
    let n₀ : ℕ+ := ⟨⌊x ^ 2⌋₊ + 2, Nat.succ_pos _⟩
    filter_upwards [Filter.eventually_ge_atTop n₀] with n hn
    have hn2 : x ^ 2 < (n : ℝ) := by
      rw [← Nat.floor_lt (sq_nonneg x)]
      have : ⌊x ^ 2⌋₊ + 2 ≤ (n : ℕ) := by exact_mod_cast hn
      linarith
    have hlog : log x ≤ (1 / 2) * log (n : ℝ) := by
      have : 2 * log x ≤ log (n : ℝ) := by
        rw [← log_rpow hx 2]
        exact log_le_log (by positivity) (by simp [hn2.le])
      linarith
    dsimp [y]
    calc (T / (2 * π)) * log (↑n / x)
          = (T / (2 * π)) * (log (n : ℝ) - log x) := by rw [log_div (by positivity) hx.ne']
        _ ≥ (T / (2 * π)) * (log (n : ℝ) - (1 / 2) * log (n : ℝ)) := by gcongr
        _ = (T / (4 * π)) * log (n : ℝ) := by ring
  have h_phi_le := h_y_ne_zero.mono (fun n hn ↦ hC (y n) hn)
  have h_y_inv_le : ∀ᶠ (n : ℕ+) in Filter.atTop,
      (y n)⁻¹ ^ β ≤ ((T / (4 * π)) * log n)⁻¹ ^ β := by
    filter_upwards [h_y_ge, Filter.eventually_ge_atTop (2 : ℕ+)] with n hn hn2
    have hlog_pos : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < (n : ℕ) from hn2))
    have h_rhs_pos : 0 < (T / (4 * π)) * log (n : ℝ) := mul_pos (by positivity) hlog_pos
    apply Real.rpow_le_rpow (inv_nonneg.mpr (h_rhs_pos.trans_le hn).le)
      ((inv_le_inv₀ (h_rhs_pos.trans_le hn) h_rhs_pos).mpr hn) (zero_le_one.trans hβ.le)
  apply IsBigO.of_bound (C * (T / (4 * π)) ^ (-β))
  filter_upwards [h_y_pos, h_phi_le, h_y_inv_le, Filter.eventually_ge_atTop (2 : ℕ+)]
    with n hy_pos hn_phi_le hn_inv_le hn2
  simp only [Real.norm_eq_abs, abs_norm]
  have h_log_n : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast n.2)
  apply hn_phi_le.trans
  rw [abs_of_pos hy_pos, div_eq_mul_inv, ← inv_rpow hy_pos.le, abs_of_nonneg (rpow_nonneg h_log_n _)]
  have h_rhs : (C * (T / (4 * π)) ^ (-β)) * log n ^ (-β) = C * ((T / (4 * π)) * log n)⁻¹ ^ β := by
    have h_rhs_pos : 0 < (T / (4 * π)) := by positivity
    have h_log_n_pos : 0 < log (n : ℝ) := log_pos (by exact_mod_cast (show 1 < (n : ℕ) from hn2))
    rw [mul_assoc, ← mul_rpow h_rhs_pos.le h_log_n,
        rpow_neg (mul_pos h_rhs_pos h_log_n_pos).le,
        ← inv_rpow (mul_pos h_rhs_pos h_log_n_pos).le]
  rw [h_rhs]
  apply mul_le_mul_of_nonneg_left hn_inv_le
  have hC_bound := hC 1 one_ne_zero
  rw [abs_one, one_rpow, div_one] at hC_bound
  exact (norm_nonneg _).trans hC_bound

-- This proof requires several `erw`'s because `Measure.setIntegral_comp_smul` is stated with `T • v`
lemma setIntegral_Ici_const_mul {T : ℝ} (hT : 0 < T) (f : ℝ → ℂ) (a : ℝ) :
    (T : ℂ) * ∫ v in Set.Ici a, f (T * v) = ∫ y in Set.Ici (T * a), f y := by
  erw [Measure.setIntegral_comp_smul volume f (Set.Ici a) hT.ne']
  rw [Module.finrank_self, pow_one, abs_of_pos (inv_pos.mpr hT), LinearOrderedField.smul_Ici hT]
  erw [Complex.real_smul]
  rw [← mul_assoc, show T * ((T⁻¹ : _) : ℂ) = 1 by norm_cast; field_simp, one_mul]

lemma prop_2_3_fourier_integral_ici_eq
    {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    {φ : ℝ → ℂ} (hφ_int : Integrable φ)
    (hφ_cont : ContinuousAt φ 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) :
    ∫ u in Set.Ici (-log x), 𝓕 (fun t:ℝ ↦ φ (t/T)) (u/(2*π)) =
      (2*π * (φ 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ y) : ℂ) := by
  let psi := fun t : ℝ ↦ φ (t / T)
  have h_int_Fphi : Integrable (𝓕 φ) := fourier_integrable_of_rpow_decay hβ hφ_int hφ_Fourier
  calc
    ∫ u in Set.Ici (-log x), 𝓕 psi (u / (2 * π))
    _ = (2 * π : ℂ) * ∫ v in Set.Ici (-log x / (2 * π)), 𝓕 psi v := by
      have h2pi : 0 < 2 * π := mul_pos (by linarith) Real.pi_pos
      simp_rw [← integral_indicator measurableSet_Ici]
      let g := (Set.Ici (-log x / (2 * π))).indicator (𝓕 psi)
      convert (Measure.integral_comp_div g (2 * π)) using 1
      · congr 1; ext u; dsimp [g]; simp [Set.indicator_apply, Set.mem_Ici, le_div_iff₀ h2pi]
      · simp only [g, abs_of_pos h2pi]
        exact_mod_cast rfl
    _ = (2 * π : ℂ) * ∫ v in Set.Ici (-log x / (2 * π)), (T : ℂ) * 𝓕 φ (T * v) := by
      congr 1; apply integral_congr_ae; filter_upwards with v
      rw [fourier_scale_div_noscalar φ T v hT]
    _ = (2 * π : ℂ) * ∫ y in Set.Ici (-T * log x / (2 * π)), 𝓕 φ y := by
      rw [show (∫ v in Set.Ici (-log x / (2 * π)), (T : ℂ) * 𝓕 φ (T * v)) =
          (T : ℂ) * ∫ v in Set.Ici (-log x / (2 * π)), 𝓕 φ (T * v) from
        MeasureTheory.integral_const_mul _ _, setIntegral_Ici_const_mul hT]
      congr 4; ring
    _ = (2 * π : ℂ) * ((∫ y, 𝓕 φ y) - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ y) := by
      congr 1
      rw [← MeasureTheory.setIntegral_univ, MeasureTheory.setIntegral_univ]
      rw [eq_sub_iff_add_eq, add_comm]
      rw [← MeasureTheory.setIntegral_union₀]
      · rw [Set.Iic_union_Ici, MeasureTheory.setIntegral_univ]
      · rw [MeasureTheory.AEDisjoint, Set.inter_comm, Set.Ici_inter_Iic, Set.Icc_self, MeasureTheory.measure_singleton]
      · exact measurableSet_Ici.nullMeasurableSet
      · exact h_int_Fphi.integrableOn
      · exact h_int_Fphi.integrableOn
    _ = (2 * π : ℂ) * (φ 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ y) := by
      have h_inv : ∫ y, 𝓕 φ y = φ 0 := by
        rw [← setIntegral_univ]
        trans 𝓕⁻ (𝓕 φ) 0
        · rw [Real.fourierInv_eq]; congr
          · simp
          · ext y; simp
        · rw [hφ_int.fourierInv_fourier_eq h_int_Fphi hφ_cont]
      congr 1; rw [h_inv]

lemma prop_2_3_tendsto_exp_damped_integral
    {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    {φ : ℝ → ℂ} (hφ_int : Integrable φ)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto
      (fun sig ↦ ∫ u in Set.Ici (-log x),
          Real.exp (-u * (sig - 1)) * 𝓕 (fun t : ℝ ↦ φ (t / T)) (u / (2 * π)))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (∫ u in Set.Ici (-log x), 𝓕 (fun t : ℝ ↦ φ (t / T)) (u / (2 * π)))) := by
  let psi := fun t : ℝ ↦ φ (t / T)
  have hpsi_int : Integrable psi := (MeasureTheory.integrable_comp_div_iff φ hT.ne').mpr hφ_int
  have h_int_Fphi : Integrable (𝓕 φ) := fourier_integrable_of_rpow_decay hβ hφ_int hφ_Fourier
  have h_int_Fpsi : Integrable (𝓕 psi) := by
    rw [show 𝓕 psi = fun y ↦ (T : ℂ) * 𝓕 φ (T * y) from funext (fourier_scale_div_noscalar φ T · hT)]
    exact (h_int_Fphi.comp_mul_left' hT.ne').const_mul T
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (bound := fun u ↦ max 1 x * ‖𝓕 psi (u / (2 * π))‖)
  · filter_upwards [self_mem_nhdsWithin] with sig _
    apply AEStronglyMeasurable.mul (by fun_prop)
    refine (Continuous.aestronglyMeasurable ?_).restrict
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hpsi_int).comp (continuous_id.div_const _)
  · filter_upwards [self_mem_nhdsWithin, Icc_mem_nhdsGT (one_lt_two)] with sig hsig1 hsig2
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with u hu
    rw [Complex.norm_mul]
    push_cast
    rw [Complex.norm_exp]
    norm_cast
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hsig0 : 0 ≤ sig - 1 := sub_nonneg.mpr (Set.mem_Ioi.mp hsig1).le
    have hsig_le : sig - 1 ≤ 1 := by linarith [Set.mem_Icc.mp hsig2]
    by_cases hu0 : 0 ≤ u
    · calc Real.exp (-u * (sig - 1))
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu0) hsig0)
        _ = 1 := Real.exp_zero
        _ ≤ max 1 x := le_max_left _ _
    · have : -u ≤ log x := by linarith [Set.mem_Ici.mp hu]
      have hx1 : 1 ≤ x := by
        contrapose! hu0
        have : 0 < -log x := neg_pos.mpr (Real.log_neg_iff hx |>.mpr hu0)
        linarith [Set.mem_Ici.mp hu]
      calc Real.exp (-u * (sig - 1))
        _ = Real.exp ((-u) * (sig - 1)) := by ring_nf
        _ ≤ Real.exp (log x * (sig - 1)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right this hsig0)
        _ ≤ Real.exp (log x * 1) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsig_le (Real.log_nonneg hx1))
        _ = x := by rw [mul_one, Real.exp_log hx]
        _ ≤ max 1 x := le_max_right _ _
  · exact (h_int_Fpsi.norm.comp_div (mul_pos zero_lt_two Real.pi_pos).ne').const_mul (max 1 x) |>.mono_measure Measure.restrict_le_self
  · filter_upwards [] with u
    have h_exp_lim : Filter.Tendsto (fun sig ↦ (rexp (-u * (sig - 1)) : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by
        have : (fun sig ↦ (rexp (-u * (sig - 1)) : ℂ)) 1 = 1 := by simp
        exact this ▸ (by fun_prop : Continuous (fun sig ↦ (rexp (-u * (sig-1)) : ℂ))).continuousAt.tendsto)
    convert h_exp_lim.mul_const (𝓕 psi (u / (2 * π))) using 1
    dsimp [psi]; simp

lemma prop_2_3_tendsto_polar_residual
    {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    {φ : ℝ → ℂ} (hφ_int : Integrable φ)
    (hφ_cont : ContinuousAt φ 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto
      (fun sig ↦ ((x ^ (2 - sig) / (2 * π * T) : ℝ) : ℂ) *
        ∫ u in Set.Ici (-log x), Real.exp (-u * (sig - 1)) * 𝓕 (fun t : ℝ ↦ φ (t / T)) (u / (2 * π)))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((φ 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ y) * (x / T))) := by
  have h_pre_lim : Filter.Tendsto (fun (sig : ℝ) ↦ ((x ^ (2 - sig) / (2 * π * T) : ℝ) : ℂ)) (nhdsWithin 1 (Set.Ioi 1)) (nhds (x / (2 * π * T) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    convert! (Complex.continuous_ofReal.continuousAt (x := x / (2 * π * T))).tendsto.comp ?_ using 1
    · push_cast; rfl
    refine Filter.Tendsto.div_const ?_ (2 * π * T)
    have h_pow_cont : ContinuousAt (fun (sig : ℝ) ↦ x ^ (2 - sig)) 1 := by
      apply (continuousAt_const_rpow hx.ne').comp
      exact continuousAt_const.sub continuousAt_id
    convert h_pow_cont.tendsto using 1
    norm_num
  have h_int_lim := prop_2_3_tendsto_exp_damped_integral hT hβ hφ_int hφ_Fourier x hx
  have h_int_val := prop_2_3_fourier_integral_ici_eq hT hβ hφ_int hφ_cont hφ_Fourier x
  convert Filter.Tendsto.mul h_pre_lim h_int_lim using 1
  · rw [h_int_val]; field_simp [Real.pi_pos.ne', hT.ne']

lemma prop_2_3_tendsto_G_integral
    {T : ℝ} (hT : 0 < T)
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0)
    (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto
      (fun (sig : ℝ) ↦ (1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I)))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ (t / T) * G (1 + t * I) * x ^ (1 + t * I)))) := by
  apply Filter.Tendsto.const_mul
  let K : Set ℂ := {z | z.re ∈ Set.Icc 1 2 ∧ z.im ∈ Set.Icc (-T) T}
  have hK_comp : IsCompact K := by
    have h_eq : K = (fun (x : ℝ × ℝ) ↦ (x.1 + x.2 * I : ℂ)) '' (Set.Icc 1 2 ×ˢ Set.Icc (-T) T) := by
      ext z; simp [K, Complex.ext_iff]; tauto
    rw [h_eq]
    apply IsCompact.image (isCompact_Icc.prod isCompact_Icc)
    fun_prop
  obtain ⟨M, hM_bound⟩ : ∃ M, ∀ z ∈ K, ‖G z‖ ≤ M :=
    hK_comp.exists_bound_of_continuousOn (hG.mono (fun z hz ↦ by
      simp [K, Set.mem_Icc] at hz; simp [Set.mem_Icc]; tauto))
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (bound := fun t ↦ ‖φ (t/T)‖ * M * x)
  · filter_upwards [self_mem_nhdsWithin, Icc_mem_nhdsGT (one_lt_two)] with sig hsig1 _hsig2
    refine (((hφ_mes.comp (measurable_id.div_const T)).aestronglyMeasurable).mul ?_).mul
      ((Continuous.const_cpow (by fun_prop) (.inl (ofReal_ne_zero.mpr hx.ne'))).stronglyMeasurable.aestronglyMeasurable)
    exact (hG.comp (by fun_prop) (fun t ht ↦ by
      simp only [ge_iff_le, Set.mem_Icc, Set.mem_setOf_eq, add_re, ofReal_re,
        mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im,
        zero_add]
      constructor
      · exact (Set.mem_Ioi.mp hsig1).le
      · exact ht)).aestronglyMeasurable measurableSet_Icc
  · filter_upwards [self_mem_nhdsWithin, Icc_mem_nhdsGT (one_lt_two)] with sig hsig1 hsig2
    refine Filter.Eventually.of_forall (fun t ↦ ?_)
    rw [Complex.norm_mul, Complex.norm_mul]
    have hx_norm : ‖(x : ℂ) ^ (1 + (t : ℂ) * I)‖ = x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_one]
    rw [hx_norm]
    by_cases hφ : φ (t / T) = 0
    · simp [hφ]
    have h_in_K : (sig : ℂ) + (t : ℝ) * I ∈ K := by
      simp only [K, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im, zero_add]
      refine ⟨hsig2, ?_⟩
      contrapose! hφ
      apply hφ_supp
      rw [Set.mem_Icc, not_and_or] at hφ ⊢
      rcases hφ with h | h
      · left; rw [le_div_iff₀ hT, neg_one_mul]; exact h
      · right; rw [div_le_iff₀ hT, one_mul]; exact h
    gcongr
    exact hM_bound _ h_in_K
  · exact ((hφ_int.norm.comp_div hT.ne').mono_measure Measure.restrict_le_self).mul_const M |>.mul_const x
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    apply Filter.Tendsto.mul
    · apply Filter.Tendsto.mul
      · exact tendsto_const_nhds
      · apply (hG.continuousWithinAt ?_).tendsto.comp
        · rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · refine tendsto_nhdsWithin_of_tendsto_nhds ?_
            exact (continuous_ofReal.add continuous_const).continuousAt
          · filter_upwards [self_mem_nhdsWithin] with sig hsig
            simp only [ge_iff_le, Set.mem_Ioi, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
              I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, Set.mem_Icc] at hsig ht ⊢
            constructor
            · linarith
            · tauto
        · simp only [ge_iff_le, Set.mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
            ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, mul_im, zero_add, Set.mem_Icc,
            Complex.one_re, Complex.one_im] at ht ⊢
          constructor
          · norm_num
          · tauto
    · exact tendsto_const_nhds

/-- Bounding the Dirichlet-Fourier series norm -/
lemma summable_dirichlet_fourier_bound
    {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {φ : ℝ → ℂ}
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    Summable (fun (n : ℕ+) ↦ ‖(x : ℂ)‖ * (‖a n‖ / (n : ℝ)) * ‖𝓕 φ ((T / (2 * π)) * log (n / x))‖) := by
  apply summable_of_isBigO ((summable_pnat_iff_summable_nat (f := fun n ↦ ‖a n‖ / (n * log n ^ β))).mpr ha)
  have h_bigO_phi := fourier_decay_isO_log_rpow hβ hT hx hφ_Fourier
  have h_prod := (Asymptotics.isBigO_const_mul_self ‖(x : ℂ)‖ (fun n : ℕ+ ↦ ‖a n‖ / (n : ℝ)) Filter.atTop).mul h_bigO_phi
  let b (n : ℕ+) := ‖(x : ℂ)‖ * (‖a n‖ / (n : ℝ)) * ‖𝓕 φ ((T / (2 * π)) * log (↑n / x))‖
  have h_bigO_b : (fun n ↦ b n) =O[Filter.atTop] (fun n ↦ ‖a n‖ / (n * log n ^ β)) := by
    dsimp [b]
    apply (Asymptotics.isBigO_congr Filter.EventuallyEq.rfl _).mpr h_prod
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ+)] with n hn
    have h_log_pos : 0 < log (n : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < (n : ℕ) from hn))
    rw [rpow_neg h_log_pos.le]; field_simp [h_log_pos.ne']
  rwa [pnat_atTop_eq_cofinite] at h_bigO_b

/-- Absolute convergence of the Dirichlet-Fourier series -/
lemma summable_dirichlet_fourier_complex
    {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {φ : ℝ → ℂ}
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    Summable (fun (n : ℕ+) ↦ a n * (x / n) * 𝓕 φ ((T / (2 * π)) * log (n / x))) := by
  apply Summable.of_norm
  convert summable_dirichlet_fourier_bound hT hβ ha hφ_Fourier x hx using 1
  ext n
  simp only [norm_mul, norm_div]
  norm_cast
  ring

lemma prop_2_3_tendsto_dirichlet_sum
    {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {φ : ℝ → ℂ}
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto
      (fun (sig : ℝ) ↦ (1 / (2 * π)) * ∑' (n : ℕ), (x : ℂ) * LSeries.term a sig n * 𝓕 φ ((T / (2 * π)) * log (n / x)))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((1 / (2 * π)) * ∑' (n : ℕ+), a n * (x / n) * 𝓕 φ ((T / (2 * π)) * log (n / x)))) := by
  apply Filter.Tendsto.const_mul
  let f (sig : ℝ) (n : ℕ+) : ℂ := (x : ℂ) * (a n / n ^ (sig : ℂ)) * 𝓕 φ ((T / (2 * π)) * log (n / x))
  have h_tsum_eq (sig : ℝ) : ∑' (n : ℕ), (x : ℂ) * LSeries.term a sig n * 𝓕 φ ((T / (2 * π)) * log (n / x)) = ∑' (n : ℕ+), f sig n := by
    let g (n : ℕ) := (x : ℂ) * LSeries.term a sig n * 𝓕 φ ((T / (2 * π)) * log (n / x))
    have hg0 : Function.support g ⊆ Set.range ((↑) : ℕ+ → ℕ) := by
      intro n hn; dsimp [g] at hn; rw [Function.mem_support] at hn
      contrapose! hn; rw [Set.mem_range, not_exists] at hn
      have : n = 0 := by
        by_contra h; exact absurd rfl (hn (Subtype.mk n (Nat.pos_of_ne_zero h)))
      rw [this, LSeries.term_zero]; simp
    rw [← tsum_subtype_eq_of_support_subset hg0]
    rw [← (Equiv.ofInjective PNat.val PNat.coe_injective).tsum_eq]
    congr; ext n; simp [g, f]
  simp_rw [h_tsum_eq]
  apply tendsto_tsum_of_dominated_convergence (bound := fun (n : ℕ+) ↦ ‖(x : ℂ)‖ * (‖a n‖ / (n : ℝ)) * ‖𝓕 φ ((T / (2 * π)) * log (n / x))‖)
  · exact summable_dirichlet_fourier_bound hT hβ ha hφ_Fourier x hx
  · intro n; dsimp [f]
    have h_lim : Filter.Tendsto (fun (sig : ℝ) ↦ (x : ℂ) * (a n / (n : ℂ) ^ (sig : ℂ))) (nhdsWithin 1 (Set.Ioi 1)) (nhds (a n * (x / n))) := by
      have h_pow_lim : Filter.Tendsto (fun (sig : ℝ) ↦ (n : ℂ) ^ (sig : ℂ)) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (n : ℂ)) := by
        have h_cont : ContinuousAt (fun (s : ℂ) ↦ (n : ℂ) ^ s) (1 : ℂ) := continuousAt_const_cpow (by simp [PNat.ne_zero n])
        have h_lim' := (h_cont.tendsto.comp Complex.continuous_ofReal.continuousAt).mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Set.Ioi 1))
        convert! h_lim' using 1
        ext; simp
      convert (tendsto_const_nhds (x := (x * a n : ℂ))).div h_pow_lim (by simp [PNat.ne_zero n]) using 1
      · ext y; simp; field_simp
      · field_simp
    convert h_lim.mul_const (𝓕 φ (↑T / (2 * ↑π) * Real.log (↑n / x))) using 1
  · filter_upwards [self_mem_nhdsWithin] with sig hsig n
    dsimp [f]
    rw [norm_mul, norm_mul, norm_div, norm_natCast_cpow_of_pos (PNat.pos n)]
    gcongr
    · convert! Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr n.2) hsig.le using 1
      · simp; rfl

theorem prop_2_3 {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n : ℕ ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / n ^ s - 1 / (s - 1)) { z | z.re > 1 })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_cont : ContinuousAt φ 0)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    (1 / (2 * π)) * ∑' (n : ℕ+), a n * (x / n) * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        (∫ t in Set.Icc (-T) T, φ (t/T) * G (1 + t * I) * x ^ (1 + t * I)) +
      (φ 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ y) * (x / T) := by
  have h_LHS_eq_RHS : (fun (sig : ℝ) ↦ (1 / (2 * π)) * ∑' (n : ℕ), (x : ℂ) * LSeries.term a sig n * 𝓕 φ ((T / (2 * π)) * log (n / x))) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      (fun (sig : ℝ) ↦ (1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I)) +
      ((x ^ (2 - sig) / (2 * π * T) : ℝ) : ℂ) * (∫ u in Set.Ici (-log x), Real.exp (-u * (sig - 1)) * 𝓕 (fun t : ℝ ↦ φ (t / T)) (u / (2 * π)))) := by
    filter_upwards [self_mem_nhdsWithin] with sig hsig
    refine prop_2_3_1 hT hβ ha ?_ hφ_mes hφ_int hφ_supp hφ_Fourier x sig hx hsig
    intro s hs; rw [hG' hs]; dsimp; congr 1; unfold LSeries; apply tsum_congr; intro n
    unfold LSeries.term; split_ifs with hn
    · subst hn; simp only [CharP.cast_eq_zero, div_eq_zero_iff, cpow_eq_zero_iff, ne_eq, true_and]
      apply Or.inr; intro h; subst h; simp at hs; linarith
    · rfl
  have h_LHS_tendsto := prop_2_3_tendsto_dirichlet_sum hT hβ ha hφ_Fourier x hx
  have h_RHS_first_tendsto := prop_2_3_tendsto_G_integral hT hG hφ_mes hφ_int hφ_supp x hx
  have h_RHS_second_tendsto := prop_2_3_tendsto_polar_residual hT hβ hφ_int hφ_cont hφ_Fourier x hx
  have h_RHS_tendsto := Filter.Tendsto.add h_RHS_first_tendsto h_RHS_second_tendsto
  exact tendsto_nhds_unique h_LHS_tendsto (h_RHS_tendsto.congr' h_LHS_eq_RHS.symm)


noncomputable def S (a : ℕ → ℝ) (σ x : ℝ) : ℝ :=
  if σ < 1 then ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n ^ σ : ℝ)
  else ∑' (n:ℕ), if n ≥ x then a n / (n ^ σ : ℝ) else 0

noncomputable def I' (lambda u : ℝ) : ℝ := -- use I' instead of I to avoid clash with Complex.I
  if 0 ≤ lambda * u then exp (-lambda * u) else 0

-- Lean 4.34 unfolds `ℕ+` to `{ n // 0 < n }` partway through this proof, after which no
-- `PNat` lemma applies. `PrimeNumberTheoremAnd` already carries this option twice in the
-- same material for the same reason.
set_option backward.isDefEq.respectTransparency false in
theorem S_eq_I (a : ℕ → ℝ) (s x T : ℝ) (hs : s ≠ 1) (hT : 0 < T) (hx : 0 < x) :
    let lambda := (2 * π * (s - 1)) / T
    S a s x = (x ^ (-s) : ℝ) * ∑' (n : ℕ+), a n * (x / n) * I' lambda ((T / (2 * π)) * log (n / x)) := by
  have lambda_mul_u {s T : ℝ} (hT : 0 < T) (u : ℝ) :
      2 * π * (s - 1) / T * (T / (2 * π) * u) = (s - 1) * u := by field_simp [pi_ne_zero]
  by_cases hs_lt : s < 1
  · have hS_def : S a s x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n ^ s : ℝ) := if_pos hs_lt
    have h_tsum_eq : x ^ (-s : ℝ) * ∑' n : ℕ+,
        a n * (x / n) * I' (2 * π * (s - 1) / T) ((T / (2 * π)) * log (n / x)) =
        x ^ (-s : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n) * (x / n) ^ (s - 1) := by
      have h_cond : x ^ (-s : ℝ) * ∑' n : ℕ+, a n * (x / n) * I' (2 * π * (s - 1) / T)
            ((T / (2 * π)) * log (n / x)) =
          x ^ (-s : ℝ) * ∑' n : ℕ+, if n ≤ ⌊x⌋₊ then a n * (x / n) * (x / n) ^ (s - 1) else 0 := by
        congr 1; congr 1 with n; unfold I'
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
        simp only [lambda_mul_u hT]
        split_ifs with h1 h2 h3
        · congr 1; rw [rpow_def_of_pos (div_pos hx hn_pos),
            show log (x / n) = log x - log n from log_div hx.ne' hn_pos.ne']
          congr 1; rw [show log (n / x) = log n - log x from
            log_div hn_pos.ne' hx.ne']
          field_simp [hT.ne']; ring
        · exact absurd h1 (not_le.mpr (mul_neg_of_neg_of_pos (sub_neg_of_lt hs_lt)
            (log_pos (by rw [lt_div_iff₀ hx]; linarith [Nat.lt_of_floor_lt (not_le.mp h2)]))))
        · exact absurd h1 (not_not.mpr (mul_nonneg_of_nonpos_of_nonpos (sub_neg_of_lt hs_lt).le
            (log_nonpos (div_pos hn_pos hx).le
              ((div_le_one hx).mpr (le_trans (Nat.cast_le.mpr h3) (Nat.floor_le hx.le))))))
        · simp
      rw [h_cond, tsum_eq_sum (s := Finset.Icc 1 ⟨⌊x⌋₊ + 1, Nat.succ_pos _⟩)]
      · congr 1; rw [← Finset.sum_filter]; field_simp
        refine Finset.sum_bij (fun n _ ↦ n) ?_ ?_ ?_ ?_
        · simp only [Finset.mem_filter, Finset.mem_Icc, pnat_one_le, true_and, and_imp]
          exact fun _ _ _ h ↦ h
        · exact fun _ _ _ _ h ↦ Subtype.val_injective h
        · simp only [Finset.mem_Icc, Finset.mem_filter, exists_prop, and_imp]
          exact fun b hb₁ hb₂ ↦
            ⟨⟨b, hb₁⟩, ⟨⟨pnat_one_le _, Nat.le_succ_of_le hb₂⟩, hb₂⟩, rfl⟩
        · simp only [Finset.mem_filter, Finset.mem_Icc, mul_assoc, mul_comm, implies_true]
      · simp +zetaDelta only [Finset.mem_Icc, ite_eq_right_iff,
          mul_eq_zero, div_eq_zero_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false] at *
        exact fun n hn₁ hn₂ ↦ False.elim (hn₁ ⟨pnat_one_le _, Nat.le_succ_of_le hn₂⟩)
    simp_all only [ne_eq, div_eq_mul_inv, rpow_neg hx.le, mul_left_comm, mul_comm,
      mul_inv_rev, mul_assoc, Finset.mul_sum ..]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn_pos : (0 : ℝ) < n := by norm_cast; linarith [Finset.mem_Icc.mp hn]
    rw [mul_rpow (by positivity) (by positivity), inv_rpow (by positivity)]
    ring_nf
    rw [rpow_add hx, rpow_neg_one, rpow_add hn_pos, rpow_neg_one]
    field_simp
  · have hs_def : S a s x = ∑' n : ℕ, if n ≥ x then a n / (n ^ s : ℝ) else 0 := by simp_all [S]
    have hs_ge : ∑' n : ℕ, (if n ≥ x then a n / (n ^ s : ℝ) else 0) =
        ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n / (n ^ s : ℝ) else 0) :=
      (Subtype.val_injective.tsum_eq fun n hn ↦
        ⟨⟨n, Nat.pos_of_ne_zero fun h ↦ by simp_all [Function.mem_support]⟩, rfl⟩).symm
    have hs_factor : ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n / (n ^ s : ℝ) else 0) =
        x ^ (-s) * ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n * (x / (n : ℝ)) * (x / (n : ℝ)) ^ (s - 1) else 0) := by
      rw [← tsum_mul_left]; congr; ext n
      split_ifs with h
      · have hn : (0 : ℝ) < n := by positivity
        rw [div_eq_mul_inv, div_rpow hx.le hn.le, rpow_sub_one hx.ne', rpow_sub_one hn.ne', rpow_neg hx.le]
        field_simp
      · simp
    convert hs_factor using 3
    · rw [hs_def, hs_ge]
    · ext n; simp only [I', lambda_mul_u hT]
      split_ifs <;> simp_all only [ne_eq, not_lt, ge_iff_le, Nat.cast_pos, PNat.pos,
        rpow_def_of_pos, div_pos_iff_of_pos_left, not_le, mul_zero, mul_eq_mul_left_iff]
      · exact Or.inl (by rw [show (n : ℝ) / x = (x / n)⁻¹ from (inv_div x n).symm, Real.log_inv]; field_simp)
      · linarith [mul_neg_of_pos_of_neg (sub_pos.mpr <| lt_of_le_of_ne hs_lt (Ne.symm ‹_›))
          (log_neg (by positivity : (0 : ℝ) < n / x) <| by rw [div_lt_one hx]; linarith)]
      · linarith [mul_nonneg (sub_nonneg.mpr hs_lt)
          (log_nonneg (by rw [le_div_iff₀ hx]; linarith : (1:ℝ) ≤ n / x))]

lemma I'_eq_exp_of_neg {lambda u0 : ℝ} (hlambda : lambda < 0) (hu0 : u0 ≤ 0) :
    Set.EqOn (I' lambda) (fun y ↦ Real.exp (-lambda * y)) (Set.Iic u0) := by
  intro y hy
  unfold I'
  rw [if_pos (mul_nonneg_of_nonpos_of_nonpos hlambda.le (hy.trans hu0))]

lemma I'_ae_zero_of_pos {lambda u0 : ℝ} (hlambda : 0 < lambda) (hu0 : u0 ≤ 0) :
    I' lambda =ᵐ[volume.restrict (Set.Iic u0)] 0 := by
  have h_ae_ne_zero : ∀ᵐ y ∂(volume.restrict (Set.Iic u0)), y ≠ 0 := by
    refine ae_restrict_of_ae (ae_iff.mpr ?_)
    rw [show {a : ℝ | ¬a ≠ 0} = {0} by ext a; simp]; exact Real.volume_singleton
  filter_upwards [ae_restrict_mem measurableSet_Iic, h_ae_ne_zero] with y hy hy_ne_zero
  unfold I'
  rw [if_neg (not_le.mpr (mul_neg_of_pos_of_neg hlambda (lt_of_le_of_ne (hy.trans hu0) hy_ne_zero)))]
  simp

lemma integrableOn_I'_Iic {lambda u0 : ℝ} (hlambda : lambda ≠ 0) (hu0 : u0 ≤ 0) :
    IntegrableOn (I' lambda) (Set.Iic u0) := by
  by_cases hlambda_neg : lambda < 0
  · exact (integrableOn_exp_mul_Iic (neg_pos.mpr hlambda_neg) u0).congr_fun
      (I'_eq_exp_of_neg hlambda_neg hu0).symm measurableSet_Iic
  · exact MeasureTheory.Integrable.congr (integrable_zero (ε' := ℝ) (μ := volume.restrict (Set.Iic u0)))
      (I'_ae_zero_of_pos (lt_of_le_of_ne (not_lt.mp hlambda_neg) hlambda.symm) hu0).symm

lemma integral_Iic_I'_of_neg {lambda u0 : ℝ} (hlambda : lambda < 0) (hu0 : u0 ≤ 0) :
    ∫ y in Set.Iic u0, I' lambda y = Real.exp (-lambda * u0) / (-lambda) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic (I'_eq_exp_of_neg hlambda hu0)]
  exact integral_exp_mul_Iic (a := -lambda) (neg_pos.mpr hlambda) u0

lemma complex_residual_algebraic_identity {x σ T : ℝ} (hx : 0 < x) (hT : T ≠ 0) (A B C : ℂ) :
    ((x ^ (-σ) : ℝ) : ℂ) * (2 * π * ((1 / (2 * π * T)) * B + (A - C) * (x / T))) =
    ((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * A +
    ((x ^ (-σ) / T : ℝ) : ℂ) * B -
    ((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * C := by
  push_cast
  rw [show ((x ^ (1 - σ) : ℝ) : ℂ) = ((x ^ (-σ) : ℝ) : ℂ) * (x : ℂ) by
    norm_cast; rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one, mul_comm]]
  field_simp [hT, Real.pi_pos.ne']
  ring

lemma integral_Iic_I'_eq {T σ : ℝ} (hT : 0 < T) (hσ : σ ≠ 1) (x : ℝ) (hx : 1 ≤ x) :
    (2 * π * (x ^ (1 - σ) : ℝ) / T) * ∫ y in Set.Iic (-T * log x / (2 * π)), I' ((2 * π * (σ - 1)) / T) y =
      if σ < 1 then 1 / (1 - σ) else 0 := by
  let lambda := (2 * π * (σ - 1)) / T
  let u0 := -T * log x / (2 * π)
  have hu0 : u0 ≤ 0 := by
    dsimp [u0]; rw [neg_mul, neg_div]
    exact neg_nonpos.mpr (div_nonneg (mul_nonneg hT.le (log_nonneg hx)) (by positivity))
  by_cases hσ_lt : σ < 1
  · simp only [hσ_lt, ite_true]
    have hlambda_neg : lambda < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (sub_neg_of_lt hσ_lt)) hT
    rw [integral_Iic_I'_of_neg hlambda_neg hu0]
    have h_exp_val : Real.exp (-lambda * u0) = x ^ (σ - 1) := by
      rw [Real.rpow_def_of_pos (by linarith [hx])]
      congr 1; dsimp [lambda, u0]; field_simp [hT.ne', Real.pi_pos.ne']
    rw [h_exp_val]
    have h_final : (2 * π * x ^ (1 - σ) / T) * (x ^ (σ - 1) / (-lambda)) = 1 / (1 - σ) := by
      dsimp [lambda]; field_simp [hT.ne', Real.pi_pos.ne', (sub_pos.mpr hσ_lt).ne']
      rw [mul_assoc, ← Real.rpow_add (by linarith [hx])]
      ring_nf; rw [Real.rpow_zero, add_comm, ← sub_eq_add_neg]
      field_simp [sub_ne_zero.mpr hσ]
    exact h_final
  · have hσ_gt : 1 < σ := lt_of_le_of_ne (not_lt.mp hσ_lt) hσ.symm
    have hlambda_pos : 0 < lambda :=
      div_pos (mul_pos (by positivity) (sub_pos.mpr (by linarith [hσ_gt]))) hT
    rw [MeasureTheory.integral_eq_zero_of_ae (I'_ae_zero_of_pos hlambda_pos hu0)]
    simp only [hσ_lt, ite_false, mul_zero]

lemma I'_mul_le_rpow_of_one_lt {a_n x T σ : ℝ} (ha_pos : 0 ≤ a_n)
    (hT : 0 < T) (hx : 1 ≤ x) (n : ℕ+) :
    a_n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x)) ≤ a_n * (x ^ σ) * (1 / (n : ℝ) ^ σ) := by
  unfold I'
  split_ifs with h_cond
  · rcases eq_or_lt_of_le ha_pos with rfl | ha_pos'
    · simp
    · have h_arg : -(2 * π * (σ - 1) / T) * (T / (2 * π) * log (n / x)) = -((σ - 1) * log (n / x)) := by
        field_simp [Real.pi_pos.ne', hT.ne']
      convert! le_refl (a_n * x ^ σ * (1 / (n : ℝ) ^ σ)) using 1
      rw [h_arg, ← neg_mul, ← Real.log_rpow (by positivity), Real.exp_log (by positivity),
        Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by positivity)]
      field_simp
      simp_rw [mul_comm (n : ℝ), mul_comm x]
      rw [← Real.rpow_add_one (by positivity), ← Real.rpow_add_one (by positivity)]
      ring_nf
  · simp only [mul_zero, one_div]
    have : 0 < x := zero_lt_one.trans_le hx
    positivity

lemma prop_2_4_plus_fourier_bound {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
  {φ_plus : ℝ → ℂ} (hφ_int : Integrable φ_plus)
  (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_plus y‖ ≤ C / |y| ^ β)
  (hI_le_Fourier : ∀ y : ℝ, I' ((2 * π * (σ - 1)) / T) y ≤ (𝓕 φ_plus y).re)
  (x : ℝ) (hx : 1 ≤ x) :
  (if σ < 1 then 1 / (1 - σ) else 0) ≤
    (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_plus y)).re := by
  have h_int_Fphi : Integrable (𝓕 φ_plus) := fourier_integrable_of_rpow_decay hβ hφ_int hφ_Fourier
  let lambda := (2 * π * (σ - 1)) / T
  let u0 := -T * log x / (2 * π)
  have hu0 : u0 ≤ 0 := by
    dsimp [u0]; rw [neg_mul, neg_div]; apply neg_nonpos.mpr
    apply div_nonneg (mul_nonneg hT.le (log_nonneg hx)) (by positivity)
  have h_re_mul : (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_plus y)).re =
      (2 * π * (x ^ (1 - σ) : ℝ) / T) * (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_plus y).re := by
    simp
  have h_re_int : (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_plus y).re =
      ∫ y in Set.Iic (-T * log x / (2 * π)), (𝓕 φ_plus y).re := (integral_re h_int_Fphi.integrableOn).symm
  rw [h_re_mul, h_re_int]
  have h_int_le : ∫ y in Set.Iic (-T * log x / (2 * π)), I' ((2 * π * (σ - 1)) / T) y ≤
      ∫ y in Set.Iic (-T * log x / (2 * π)), (𝓕 φ_plus y).re := by
    apply MeasureTheory.setIntegral_mono_on₀
    · have hlambda_ne : lambda ≠ 0 := by
        dsimp [lambda]; refine div_ne_zero ?_ hT.ne'; exact mul_ne_zero (by positivity) (sub_ne_zero.mpr hσ)
      exact integrableOn_I'_Iic hlambda_ne hu0
    · exact h_int_Fphi.re.integrableOn
    · exact measurableSet_Iic.nullMeasurableSet
    · exact fun y _ ↦ hI_le_Fourier y
  have h_I_int : (if σ < 1 then 1 / (1 - σ) else 0) ≤
      (2 * π * (x ^ (1 - σ) : ℝ) / T) * ∫ y in Set.Iic (-T * log x / (2 * π)), I' ((2 * π * (σ - 1)) / T) y :=
    (integral_Iic_I'_eq hT hσ x hx).ge
  calc (if σ < 1 then 1 / (1 - σ) else 0)
    _ ≤ (2 * π * (x ^ (1 - σ) : ℝ) / T) * ∫ y in Set.Iic (-T * log x / (2 * π)), I' ((2 * π * (σ - 1)) / T) y := h_I_int
    _ ≤ (2 * π * (x ^ (1 - σ) : ℝ) / T) * ∫ y in Set.Iic (-T * log x / (2 * π)), (𝓕 φ_plus y).re := by
      apply mul_le_mul_of_nonneg_left h_int_le (by positivity)

theorem prop_2_4_plus {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0) {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
    (ha : Summable (fun n : ℕ ↦ ‖(a n : ℂ)‖ / (n * log n ^ β)))
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
      if σ < 1 then 1 / (1 - σ) else 0 := by
  have h_summable : Summable (fun n : ℕ+ ↦ (a n : ℂ) * (x / n) * 𝓕 φ_plus ((T / (2 * π)) * log (n / x))) :=
    summable_dirichlet_fourier_complex hT hβ ha hφ_Fourier x (zero_lt_one.trans_le hx)
  have h_sum_RHS : Summable (fun n : ℕ+ ↦ a n * (x / n) * (𝓕 φ_plus ((T / (2 * π)) * log (n / x))).re) := by
    convert h_summable.map Complex.reCLM Complex.reCLM.continuous using 1
    ext n
    norm_cast
    simp only [Function.comp_apply, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have h_pointwise : ∀ (n : ℕ+), a n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x)) ≤
      a n * (x / n) * (𝓕 φ_plus ((T / (2 * π)) * log (n / x))).re := by
    intro n
    apply mul_le_mul_of_nonneg_left
    · exact hI_le_Fourier ((T / (2 * π)) * log (n / x))
    · exact mul_nonneg (ha_pos _) (by positivity)
  have h_sum_LHS : Summable (fun (n : ℕ+) ↦ a n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x))) := by
    apply Summable.of_nonneg_of_le
    · intro n
      apply mul_nonneg (mul_nonneg (ha_pos _) (div_nonneg (zero_le_one.trans hx) (by positivity)))
      unfold I'; split_ifs <;> positivity
    · exact h_pointwise
    · exact h_sum_RHS
  have h_sum_total : ∑' (n : ℕ+), (a n : ℂ) * (x / n) * 𝓕 φ_plus ((T / (2 * π)) * log (n / x)) =
      2 * π * ((1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ_plus (t / T) * G (1 + t * I) * x ^ (1 + t * I)) +
      (φ_plus 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_plus y) * (x / T)) := by
    have h_sum_eq := prop_2_3 hT hβ ha hG hG' hφ_mes hφ_int hφ_cont hφ_supp hφ_Fourier x (by positivity)
    rw [← h_sum_eq]
    field_simp [Real.pi_pos.ne']
    congr 1
    ext x; ring_nf
  calc S a σ x
    _ ≤ (x ^ (-σ) : ℝ) * ∑' (n : ℕ+), a n * (x / n) * (𝓕 φ_plus ((T / (2 * π)) * log (n / x))).re := by
      rw [S_eq_I a σ x T hσ hT (by linarith [hx])]
      apply mul_le_mul_of_nonneg_left
      · exact Summable.tsum_le_tsum h_pointwise h_sum_LHS h_sum_RHS
      · positivity
    _ = (x ^ (-σ) : ℝ) * (∑' (n : ℕ+), (a n : ℂ) * (x / n) * 𝓕 φ_plus ((T / (2 * π)) * log (n / x))).re := by
      rw [Complex.re_tsum h_summable]
      congr with n
      ring_nf; simp
    _ = (x ^ (-σ) : ℝ) * (2 * π * ((1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ_plus (t / T) * G (1 + t * I) * x ^ (1 + t * I)) +
        (φ_plus 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_plus y) * (x / T))).re := by rw [h_sum_total]
    _ = (((x ^ (-σ) : ℝ) : ℂ) * (2 * π * ((1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ_plus (t / T) * G (1 + t * I) * x ^ (1 + t * I)) +
        (φ_plus 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_plus y) * (x / T)))).re := by rw [← Complex.re_ofReal_mul]
    _ = (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * φ_plus 0).re +
        (((x ^ (-σ) / T : ℝ) : ℂ) * (∫ t in Set.Icc (-T) T, φ_plus (t / T) * G (1 + t * I) * x ^ (1 + t * I))).re -
        (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_plus y)).re := by
      rw [complex_residual_algebraic_identity (zero_lt_one.trans_le hx) hT.ne']
      simp only [Complex.add_re, Complex.sub_re]
    _ ≤ (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * φ_plus 0).re +
        (((x ^ (-σ) / T : ℝ) : ℂ) * (∫ t in Set.Icc (-T) T, φ_plus (t / T) * G (1 + t * I) * x ^ (1 + t * I))).re -
        (if σ < 1 then 1 / (1 - σ) else 0) := by
      gcongr
      exact prop_2_4_plus_fourier_bound hT hβ hσ hφ_int hφ_Fourier hI_le_Fourier x hx
    _ ≤ _ := by
      gcongr; norm_cast
      rw [Complex.re_ofReal_mul]

lemma prop_2_4_minus_fourier_bound {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
  {φ_minus : ℝ → ℂ} (hφ_int : Integrable φ_minus)
  (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_minus y‖ ≤ C / |y| ^ β)
  (hFourier_le_I : ∀ y : ℝ, (𝓕 φ_minus y).re ≤ I' ((2 * π * (σ - 1)) / T) y)
  (x : ℝ) (hx : 1 ≤ x) :
  (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y)).re ≤
    if σ < 1 then 1 / (1 - σ) else 0 := by
  have h_int_Fphi : Integrable (𝓕 φ_minus) := fourier_integrable_of_rpow_decay hβ hφ_int hφ_Fourier
  let lambda := (2 * π * (σ - 1)) / T
  let u0 := -T * log x / (2 * π)
  have hu0 : u0 ≤ 0 := by
    dsimp [u0]; rw [neg_mul, neg_div]; apply neg_nonpos.mpr
    apply div_nonneg (mul_nonneg hT.le (log_nonneg hx)) (by positivity)
  have h_re_mul : (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y)).re =
      (2 * π * (x ^ (1 - σ) : ℝ) / T) * (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y).re := by
    simp
  have h_re_int : (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y).re =
      ∫ y in Set.Iic (-T * log x / (2 * π)), (𝓕 φ_minus y).re := (integral_re h_int_Fphi.integrableOn).symm
  rw [h_re_mul, h_re_int]
  have h_int_le : ∫ y in Set.Iic (-T * log x / (2 * π)), (𝓕 φ_minus y).re ≤
      ∫ y in Set.Iic (-T * log x / (2 * π)), I' ((2 * π * (σ - 1)) / T) y :=
    MeasureTheory.setIntegral_mono_on₀ h_int_Fphi.re.integrableOn
      (integrableOn_I'_Iic (div_ne_zero (mul_ne_zero (by positivity) (sub_ne_zero.mpr hσ)) hT.ne') hu0)
      measurableSet_Iic.nullMeasurableSet (fun y _ ↦ hFourier_le_I y)
  have h_I_int : (2 * π * (x ^ (1 - σ) : ℝ) / T) * ∫ y in Set.Iic (-T * log x / (2 * π)), I' ((2 * π * (σ - 1)) / T) y ≤
      (if σ < 1 then 1 / (1 - σ) else 0) :=
    (integral_Iic_I'_eq hT hσ x hx).le
  calc (2 * π * (x ^ (1 - σ) : ℝ) / T) * ∫ y in Set.Iic (-T * log x / (2 * π)), (𝓕 φ_minus y).re
    _ ≤ (2 * π * (x ^ (1 - σ) : ℝ) / T) * ∫ y in Set.Iic (-T * log x / (2 * π)), I' ((2 * π * (σ - 1)) / T) y :=
      mul_le_mul_of_nonneg_left h_int_le (by positivity)
    _ ≤ (if σ < 1 then 1 / (1 - σ) else 0) := h_I_int

lemma summable_I'_residual {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0)
    {T β σ : ℝ} (hT : 0 < T) (hσ : σ ≠ 1)
    (ha : Summable (fun n ↦ ‖(a n : ℂ)‖ / (n * log n ^ β)))
    {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun (n : ℕ+) ↦ a n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x))) := by
  by_cases hσ_lt : σ < 1
  · apply summable_of_hasFiniteSupport
    have h_support : Function.support (fun (n : ℕ+) ↦ a n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x))) ⊆ Set.Iic (⟨⌊x⌋₊, Nat.floor_pos.mpr hx⟩ : ℕ+) := by
      intro n hn
      rw [Function.mem_support] at hn
      have hI : I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x)) ≠ 0 := by
        contrapose! hn; simp [hn]
      unfold I' at hI
      split_ifs at hI with h_cond
      · have h_const : (2 * π * (σ - 1) / T) * (T / (2 * π) * log (n / x)) = (σ - 1) * log (n / x) := by
          field_simp [Real.pi_pos.ne', hT.ne']
        rw [h_const] at h_cond
        have h_log : log (n / x) ≤ 0 :=
          nonpos_of_mul_nonneg_right h_cond (sub_neg_of_lt hσ_lt)
        exact Nat.le_floor ((div_le_one (zero_lt_one.trans_le hx)).mp
          ((log_le_log_iff (div_pos (Nat.cast_pos.mpr n.pos) (zero_lt_one.trans_le hx)) zero_lt_one).mp (h_log.trans_eq Real.log_one.symm)))
      · exact absurd rfl hI
    exact (Set.finite_Iic _).subset h_support
  · have hσ_gt : 1 < σ := lt_of_le_of_ne (not_lt.mp hσ_lt) hσ.symm
    have h_bound : ∀ (n : ℕ+), a n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x)) ≤ a n * (x ^ σ) * (1 / (n : ℝ) ^ σ) :=
      fun n ↦ I'_mul_le_rpow_of_one_lt (ha_pos n) hT hx n
    apply Summable.of_nonneg_of_le
    · intro n
      unfold I'
      split_ifs
      · exact mul_nonneg (mul_nonneg (ha_pos n) (div_nonneg (zero_lt_one.trans_le hx).le (by positivity))) (by positivity)
      · simp
    · exact h_bound
    · have h_summable_nterm : Summable (fun n : ℕ+ ↦ (a n : ℝ) / (n : ℝ) ^ σ) := by
        convert! (summable_pnat_iff_summable_nat (f := nterm (fun n ↦ ↑(a n)) σ)).mpr ?_ using 1
        · ext n ; simp only [nterm, PNat.ne_zero, ↓reduceIte, norm_real, norm_eq_abs]
          rw [abs_of_nonneg (ha_pos _)]
        · exact summable_nterm_of_log_weight hσ_gt ha
      convert! h_summable_nterm.mul_left (x ^ σ) using 1
      ext n
      ring

theorem prop_2_4_minus {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0) {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
    (ha : Summable (fun n ↦ ‖(a n : ℂ)‖ / (n * log n ^ β)))
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
      if σ < 1 then 1 / (1 - σ) else 0 := by
  have h_summable : Summable (fun n : ℕ+ ↦ (a n : ℂ) * (x / n) * 𝓕 φ_minus ((T / (2 * π)) * log (n / x))) :=
    summable_dirichlet_fourier_complex hT hβ ha hφ_Fourier x (zero_lt_one.trans_le hx)
  have h_sum_eq : (1 / (2 * π) : ℂ) * ∑' (n : ℕ+), a n * (x / n) * 𝓕 φ_minus ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ_minus (t / T) * G (1 + t * I) * x ^ (1 + t * I)) +
      (φ_minus 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y) * (x / T) :=
    prop_2_3 hT hβ ha hG hG' hφ_mes hφ_int hφ_cont hφ_supp hφ_Fourier x (zero_lt_one.trans_le hx)
  have h_sum_total : ∑' (n : ℕ+), (a n : ℂ) * (x / n) * 𝓕 φ_minus ((T / (2 * π)) * log (n / x)) =
      2 * π * ((1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ_minus (t / T) * G (1 + t * I) * x ^ (1 + t * I)) +
      (φ_minus 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y) * (x / T)) := by
    rw [← h_sum_eq]
    field_simp [Real.pi_pos.ne']
    congr 1; ext x; ring_nf
  have h_sum_LHS : Summable (fun n : ℕ+ ↦ a n * (x / n) * (𝓕 φ_minus ((T / (2 * π)) * log (n / x))).re) := by
    convert h_summable.map Complex.reCLM Complex.reCLM.continuous using 1
    ext n; simp
  have h_sum_RHS : Summable (fun (n : ℕ+) ↦ a n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x))) :=
    summable_I'_residual ha_pos hT hσ ha hx
  have h_pointwise : ∀ (n : ℕ+), a n * (x / n) * (𝓕 φ_minus ((T / (2 * π)) * log (n / x))).re ≤
      a n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x)) :=
    fun n ↦ mul_le_mul_of_nonneg_left (hFourier_le_I ((T / (2 * π)) * log (n / x)))
      (mul_nonneg (ha_pos n) (div_nonneg (zero_lt_one.trans_le hx).le (by positivity)))
  calc S a σ x
    _ = (x ^ (-σ) : ℝ) * ∑' (n : ℕ+), a n * (x / n) * I' ((2 * π * (σ - 1)) / T) ((T / (2 * π)) * log (n / x)) := S_eq_I a σ x T hσ hT (zero_lt_one.trans_le hx)
    _ ≥ (x ^ (-σ) : ℝ) * ∑' (n : ℕ+), a n * (x / n) * (𝓕 φ_minus ((T / (2 * π)) * log (n / x))).re :=
      ge_iff_le.mpr (mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum h_pointwise h_sum_LHS h_sum_RHS) (by positivity))
    _ = (x ^ (-σ) : ℝ) * (∑' (n : ℕ+), (a n : ℂ) * (x / n) * 𝓕 φ_minus ((T / (2 * π)) * log (n / x))).re := by
      rw [Complex.re_tsum h_summable]
      congr with n
      ring_nf; simp
    _ = (x ^ (-σ) : ℝ) * (2 * π * ((1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ_minus (t / T) * G (1 + t * I) * x ^ (1 + t * I)) +
        (φ_minus 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y) * (x / T))).re := by rw [h_sum_total]
    _ = (((x ^ (-σ) : ℝ) : ℂ) * (2 * π * ((1 / (2 * π * T)) * (∫ t in Set.Icc (-T) T, φ_minus (t / T) * G (1 + t * I) * x ^ (1 + t * I)) +
        (φ_minus 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y) * (x / T)))).re := by rw [← Complex.re_ofReal_mul]
    _ = (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * φ_minus 0).re +
        (((x ^ (-σ) / T : ℝ) : ℂ) * (∫ t in Set.Icc (-T) T, φ_minus (t / T) * G (1 + t * I) * x ^ (1 + t * I))).re -
        (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * (∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ_minus y)).re := by
      rw [complex_residual_algebraic_identity (zero_lt_one.trans_le hx) hT.ne']
      simp only [Complex.add_re, Complex.sub_re]
    _ ≥ (((2 * π * (x ^ (1 - σ) : ℝ) / T) : ℂ) * φ_minus 0).re +
        (((x ^ (-σ) / T : ℝ) : ℂ) * (∫ t in Set.Icc (-T) T, φ_minus (t / T) * G (1 + t * I) * x ^ (1 + t * I))).re -
        (if σ < 1 then 1 / (1 - σ) else 0) := by
      gcongr
      exact prop_2_4_minus_fourier_bound hT hβ hσ hφ_int hφ_Fourier (fun y ↦ hFourier_le_I y) x hx
    _ ≥ _ := by
      gcongr; norm_cast
      rw [Complex.re_ofReal_mul]

end CH2Sol
