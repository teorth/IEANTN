/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.InfiniteSum.Real
import IEANTN.Nodes.CotangentSeries.v1.Conclusions

/-!
# Solution: `CotangentSeries.v1`

`cot_series_rep'` is Euler's partial-fraction expansion. For `‖z‖ < 1` each term
`1/(z - n) + 1/(z + n)` equals `-2z/(n² - z²)`, and that expands as a geometric series
in `(z/n)²`. The double sum of norms is bounded by a product of a geometric series and a
`p`-series, so the sums may be interchanged, and the inner sum over `n` is `ζ(2k+2)`.

Nothing here is a new identity.
-/

open Complex Real
open scoped Nat

namespace CotangentSeries.v1.Dev

private lemma not_integer {z : ℂ} (hz0 : z ≠ 0) (hznorm : ‖z‖ < 1) : z ∈ integerComplement := by
  rw [mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hnorm : (n.natAbs : ℝ) < 1 := by
    have : ‖(n : ℂ)‖ < 1 := by simpa [hn] using hznorm
    simpa [Complex.norm_intCast, Int.natCast_natAbs] using this
  have hn0 : n = 0 := Int.natAbs_eq_zero.mp (Nat.lt_one_iff.mp (by exact_mod_cast hnorm))
  exact hz0 (by simpa [hn0] using hn.symm)

private lemma pow_ne {z : ℂ} (hznorm : ‖z‖ < 1) (n : ℕ) : (n + 1 : ℂ) ^ 2 ≠ z ^ 2 := by
  intro h
  have hnorm : ((n + 1 : ℕ) : ℝ) ^ 2 = ‖z‖ ^ 2 := by
    have hnorm := congrArg norm h
    rw [norm_pow, norm_pow, ← Nat.cast_add_one, Complex.norm_natCast] at hnorm
    exact hnorm
  have hleft : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 :=
    one_le_pow₀ (by exact_mod_cast Nat.succ_pos n)
  linarith [pow_lt_one₀ (norm_nonneg z) hznorm two_ne_zero]

private noncomputable def term (z : ℂ) (k n : ℕ) : ℂ :=
  2 * z ^ (2 * k + 1) / (n + 1 : ℂ) ^ (2 * k + 2)

private lemma cotTerm_eq {z : ℂ} (hz : z ∈ integerComplement) (n : ℕ) :
    cotTerm z n = -(2 * z / ((n + 1 : ℂ) ^ 2 - z ^ 2)) := by
  have h1 : z - (n + 1 : ℂ) ≠ 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hz (-(n + 1 : ℤ))
  have h2 : z + (n + 1 : ℂ) ≠ 0 := by
    simpa using integerComplement_add_ne_zero hz (n + 1 : ℤ)
  simp only [cotTerm]
  rw [div_add_div _ _ h1 h2]
  have hden : (n + 1 : ℂ) ^ 2 - z ^ 2 ≠ 0 := by
    have hprod : z ^ 2 - (n + 1 : ℂ) ^ 2 ≠ 0 := by
      have hmul := mul_ne_zero h1 h2
      rw [show (z - (n + 1 : ℂ)) * (z + (n + 1)) = z ^ 2 - (n + 1) ^ 2 by ring] at hmul
      exact hmul
    rw [← neg_sub]
    exact neg_ne_zero.mpr hprod
  field_simp [h1, h2, hden]
  ring_nf

private lemma geom_hasSum {z : ℂ} (hznorm : ‖z‖ < 1) (n : ℕ) :
    HasSum (fun k => term z k n) (2 * z / ((n + 1 : ℂ) ^ 2 - z ^ 2)) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.add_one_ne_zero n
  set ξ : ℂ := z / (n + 1)
  have hξ : ‖ξ ^ 2‖ < 1 := by
    have hle : ‖ξ‖ ≤ ‖z‖ := by
      rw [norm_div]
      have hden : (1 : ℝ) ≤ ‖(n + 1 : ℂ)‖ := by
        rw [← Nat.cast_add_one, Complex.norm_natCast]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact div_le_self (norm_nonneg _) hden
    simpa [norm_pow] using pow_lt_one₀ (norm_nonneg _) (lt_of_le_of_lt hle hznorm) two_ne_zero
  have hgeom := (hasSum_geometric_of_norm_lt_one hξ).mul_left (2 * z / (n + 1) ^ 2)
  have hfun : ∀ k, term z k n = (2 * z / (n + 1) ^ 2) * (ξ ^ 2) ^ k := by
    intro k
    simp only [term, ξ, div_eq_mul_inv]
    have hidx : (2 * k + 2 : ℕ) = 2 + 2 * k := by omega
    rw [pow_add z (2 * k) 1, pow_one, hidx, pow_add ((n + 1 : ℂ)) 2 (2 * k), mul_inv]
    ring_nf
  have hden : (n + 1 : ℂ) ^ 2 - z ^ 2 ≠ 0 := sub_ne_zero.mpr (pow_ne hznorm n)
  have hval : (2 * z / (n + 1) ^ 2) * (1 - ξ ^ 2)⁻¹ =
      2 * z / ((n + 1) ^ 2 - z ^ 2) := by
    simp only [ξ]
    field_simp [hn, hden]
  have hgeom' : HasSum (fun k => term z k n)
      ((2 * z / (n + 1) ^ 2) * (1 - ξ ^ 2)⁻¹) := by
    refine hgeom.congr_fun ?_
    intro k
    exact hfun k
  simpa [hval] using hgeom'

private lemma summable_inv_sq_shift : Summable fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2 := by
  have hseries : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    (summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hinj : Function.Injective (fun n : ℕ => n + 1) := Nat.succ_injective
  simpa [Function.comp_def] using
    (hseries.comp_injective (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) hinj)

private lemma norm_summable {z : ℂ} (hznorm : ‖z‖ < 1) :
    Summable fun p : ℕ × ℕ => ‖term z p.1 p.2‖ := by
  let r : ℝ := ‖z‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hznorm two_ne_zero
  let phi : ℕ × ℕ → ℝ := fun p => 2 * r ^ (2 * p.1 + 1) / (p.2 + 1 : ℝ) ^ (2 * p.1 + 2)
  have hsq : Summable fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2 := summable_inv_sq_shift
  have hinner : ∀ k, Summable fun n => phi (k, n) := by
    intro k
    refine Summable.of_nonneg_of_le (fun n : ℕ => ?_) (fun n : ℕ => ?_)
      (hsq.mul_left (2 * r ^ (2 * k + 1)))
    · unfold phi
      positivity
    · have hden : (n + 1 : ℝ) ^ 2 ≤ (n + 1 : ℝ) ^ (2 * k + 2) :=
        pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (by omega)
      have hpos : 0 ≤ 2 * r ^ (2 * k + 1) := by positivity
      calc
        phi (k, n) = 2 * r ^ (2 * k + 1) / (n + 1 : ℝ) ^ (2 * k + 2) := by
          unfold phi
          rfl
        _ ≤ 2 * r ^ (2 * k + 1) / (n + 1 : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left hpos (by positivity) hden
        _ = 2 * r ^ (2 * k + 1) * (1 / (n + 1 : ℝ) ^ 2) := by
          rw [div_eq_mul_inv, one_div]
  let S : ℝ := ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ 2
  have houter : Summable fun k => ∑' n, phi (k, n) := by
    have hbound : ∀ k, ∑' n, phi (k, n) ≤ 2 * r ^ (2 * k + 1) * S := by
      intro k
      have hle : ∀ n : ℕ, phi (k, n) ≤ 2 * r ^ (2 * k + 1) * (1 / (n + 1 : ℝ) ^ 2) := by
        intro n
        have hden : (n + 1 : ℝ) ^ 2 ≤ (n + 1 : ℝ) ^ (2 * k + 2) :=
          pow_le_pow_right₀ (by exact_mod_cast Nat.succ_pos n) (by omega)
        have hpos : 0 ≤ 2 * r ^ (2 * k + 1) := by positivity
        calc
          phi (k, n) = 2 * r ^ (2 * k + 1) / (n + 1 : ℝ) ^ (2 * k + 2) := by
            unfold phi
            rfl
          _ ≤ 2 * r ^ (2 * k + 1) / (n + 1 : ℝ) ^ 2 :=
            div_le_div_of_nonneg_left hpos (by positivity) hden
          _ = 2 * r ^ (2 * k + 1) * (1 / (n + 1 : ℝ) ^ 2) := by
            rw [div_eq_mul_inv, one_div]
      refine ((hinner k).tsum_mono (hsq.mul_left (2 * r ^ (2 * k + 1))) hle).trans ?_
      simp only [S]
      rw [← tsum_mul_left]
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun n => ?_) hbound ?_
    · unfold phi
      positivity
    · have hgeom : Summable fun k : ℕ => (r ^ 2) ^ k :=
        summable_geometric_of_lt_one (by positivity) hr2
      have hrewrite : ∀ k, 2 * r ^ (2 * k + 1) * S = (2 * S * r) * (r ^ 2) ^ k := by
        intro k
        have : r ^ (2 * k + 1) = r * (r ^ 2) ^ k := by
          rw [pow_succ', pow_mul, mul_comm]
        rw [this]
        ring
      simpa [hrewrite] using hgeom.mul_left (2 * S * r)
  have hphi : Summable phi :=
    (summable_prod_of_nonneg (fun _ => by unfold phi; positivity)).mpr ⟨hinner, houter⟩
  have hnorm : (fun p : ℕ × ℕ => ‖term z p.1 p.2‖) = phi := by
    ext p
    simp only [phi, r, term]
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_two, ← Nat.cast_add_one p.2,
      Complex.norm_natCast, Nat.cast_add_one]
  rw [hnorm]
  exact hphi

private lemma zeta_term {z : ℂ} (k : ℕ) :
    2 * riemannZeta (2 * (k : ℂ) + 2) * z ^ (2 * k + 1) = ∑' n, term z k n := by
  have hs : 1 < re (2 * (k + 1 : ℂ)) := by
    have hre : (2 * (k + 1 : ℂ)).re = (2 * (k + 1) : ℝ) := by
      simp [Complex.mul_re, Complex.natCast_re, Complex.add_re, Complex.one_re]
    rw [hre]
    norm_cast
    omega
  have harg : (2 * (k + 1 : ℂ)) = (2 * (k + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  have hzeta : riemannZeta (2 * (k + 1 : ℕ)) =
      ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (2 * (k + 1) : ℕ) := by
    rw [harg] at hs
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    refine tsum_congr fun n => ?_
    have hexp : (2 * ((k + 1 : ℕ) : ℂ)) = ((2 * (k + 1) : ℕ) : ℂ) := by
      push_cast
      ring
    rw [hexp, ← cpow_natCast]
  have hcast : (2 * (k : ℂ) + 2) = (2 * (k + 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hcast, hzeta, ← tsum_mul_left, ← tsum_mul_right]
  refine congr_arg tsum ?_
  funext n
  simp only [term]
  have hexp : (2 * (k + 1) : ℕ) = 2 * k + 2 := by omega
  rw [hexp]
  ring

private lemma family_summable {z : ℂ} (hznorm : ‖z‖ < 1) :
    Summable fun p : ℕ × ℕ => term z p.1 p.2 :=
  (summable_norm_iff).mp (norm_summable hznorm)

theorem proof : CotangentSeries.v1.cot_series_zeta_values := by
  intro z hz0 hznorm
  have hzZ : z ∈ integerComplement := CotangentSeries.v1.Dev.not_integer hz0 hznorm
  have hrep := cot_series_rep' hzZ
  have hfam := CotangentSeries.v1.Dev.family_summable hznorm
  have h1 k := hfam.comp_injective (Prod.mk_right_injective k)
  have h2 n := hfam.comp_injective (Prod.mk_left_injective n)
  have hcomm : (∑' n, ∑' k, term z k n) = ∑' k, ∑' n, term z k n := by
    have hkn := hfam.tsum_prod' h1
    have hswap : Summable fun p : ℕ × ℕ => term z p.2 p.1 :=
      (Equiv.prodComm ℕ ℕ).summable_iff.mp hfam
    have hnk := hswap.tsum_prod' fun n => hswap.comp_injective (Prod.mk_right_injective n)
    have hsame : (∑' p : ℕ × ℕ, term z p.1 p.2) = ∑' p : ℕ × ℕ, term z p.2 p.1 :=
      ((Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ => term z p.1 p.2)).symm
    exact (((hkn.symm.trans hsame).trans hnk).symm)
  have hslice : ∀ n, (∑' k, term z k n) = 2 * z / ((n + 1 : ℂ) ^ 2 - z ^ 2) :=
    fun n => (CotangentSeries.v1.Dev.geom_hasSum hznorm n).tsum_eq
  have hleft : (∑' n, ∑' k, term z k n) = 1 / z - π * cot (π * z) := by
    simp_rw [hslice]
    rw [← neg_sub, hrep]
    have hterm : ∀ n, cotTerm z n = -(2 * z / ((n + 1 : ℂ) ^ 2 - z ^ 2)) :=
      fun n => CotangentSeries.v1.Dev.cotTerm_eq hzZ n
    simp_rw [hterm, tsum_neg]
    ring
  have hright : (∑' k, ∑' n, term z k n) =
      ∑' k : ℕ, 2 * riemannZeta (2 * (k : ℂ) + 2) * z ^ (2 * k + 1) := by
    refine tsum_congr fun k => ?_
    exact (CotangentSeries.v1.Dev.zeta_term (z := z) k).symm
  have hgoal : Summable fun k : ℕ =>
      2 * riemannZeta (2 * (k : ℂ) + 2) * z ^ (2 * k + 1) := by
    have hsliceNorm : Summable fun k => ∑' n, ‖term z k n‖ := by
      have hprod := (summable_prod_of_nonneg (fun _ : ℕ × ℕ => norm_nonneg _)).mp
        (CotangentSeries.v1.Dev.norm_summable hznorm)
      exact hprod.2
    refine Summable.of_norm_bounded hsliceNorm ?_
    intro k
    rw [show 2 * riemannZeta (2 * (k : ℂ) + 2) * z ^ (2 * k + 1) = ∑' n, term z k n from
      CotangentSeries.v1.Dev.zeta_term (z := z) k]
    exact norm_tsum_le_tsum_norm (Summable.norm (h1 k))
  rw [Summable.hasSum_iff hgoal]
  rw [← hright, ← hcomm, hleft]

end CotangentSeries.v1.Dev

theorem CotangentSeries.v1.challenge_cot_series_zeta_values :
    CotangentSeries.v1.cot_series_zeta_values :=
  CotangentSeries.v1.Dev.proof
