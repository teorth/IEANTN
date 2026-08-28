/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import PsiToTheta
import Dawson

/-!
# Lemma 12: the integral of an admissible bound

The analytic heart of the `θ → π` conversion. Partial summation produces
`∫ (θ(t) − t)/(t log²t) dt`, and the whole difficulty is bounding it without losing the admissible
shape. The paper's Lemma 12 does it in five steps, and this file follows them:

1. bound the integrand by the admissible bound, leaving `(Aθ/R^B) ∫ (log t)^{B−2} e^{−C√(log t/R)}`;
2. substitute `t = e^{u²}`, giving `2(Aθ/R^B) ∫ u^{2B−3} e^{u² − Cu/√R} du`;
3. replace `u^{2B−3}` by its maximum `mFactor`;
4. complete the square, `u² − Cu/√R = (u − C/(2√R))² − C²/(4R)`;
5. translate and evaluate, which is where the Dawson function appears.

## A hypothesis the paper does not state

Step 5 discards the lower endpoint:

`∫_{a−d}^{b−d} e^{v²} dv ≤ ∫_0^{b−d} e^{v²} dv`,  where `a = √(log x₀)`, `d = C/(2√R)`.

That holds only if `a − d ≥ 0`. If `a < d` the left integral is strictly *larger*, because the
integrand is positive and the extra piece is traversed forwards — so the paper's inequality, and
hence its Lemma 12, is false without

`C/(2√R) ≤ √(log x₀)`,  equivalently  `x₀ ≥ exp(C²/(4R))`.

The published statement carries no such hypothesis; `hC` below is it. In every application the
margin is enormous — Corollary 23 has `C = 1`, `R = 5.5666305`, so the requirement is `x₀ ≥ 1.046`
— which is presumably why it was never noticed. Theorem 3's own second threshold
`x₁ ≥ exp((1 + C/(2√R))²)` is a strictly stronger condition of the same shape, which suggests the
authors had the issue in view at that point and not at this one.

Found here by formalizing rather than by reading — the statement audit did not flag it, and neither
did the earlier draft of this file. But it was **not a new observation**:
`PrimeNumberTheoremAnd`'s `lemma_12` already carries `2 ≤ x₀` and `0 ≤ √(log x₀) − C/(2√R)`, and its
`theorem_3` a note saying those conditions "are not present in the source material [FKS2]". The gap
in the published paper is real and now independently confirmed; the credit for noticing it is not
ours.
-/

namespace FKS2Sol

open Real IEANTN intervalIntegral
open FKS2.v1 (dawson)

/-- `m(x₀, x) = max((log x₀)^{(2B-3)/2}, (log x)^{(2B-3)/2})`, the paper's (alpha_def).

A `max` rather than an evaluation because the exponent `(2B-3)/2` changes sign with `B`: the
substituted integrand `u^{2B-3}` is increasing for `B > 3/2` and decreasing for `B < 3/2`, so
neither endpoint dominates in general. -/
noncomputable def mFactor (B x₀ x : ℝ) : ℝ :=
  max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2))

/-- `(log t)^{(2B-3)/2} ≤ mFactor B x₀ x` throughout `[x₀, x]` — the paper's "note that
`u^{2B-3} ≤ m(x₀,x)`". -/
theorem rpow_log_le_mFactor {B x₀ x t : ℝ} (h₀ : 1 < x₀) (ht₀ : x₀ ≤ t) (htx : t ≤ x) :
    (log t) ^ ((2 * B - 3) / 2) ≤ mFactor B x₀ x := by
  have hl₀ : 0 < log x₀ := log_pos h₀
  have hlt : log x₀ ≤ log t := log_le_log (by linarith) ht₀
  have hltx : log t ≤ log x := log_le_log (by linarith) htx
  unfold mFactor
  rcases le_or_gt 0 ((2 * B - 3) / 2) with hr | hr
  · exact le_max_of_le_right (rpow_le_rpow (by linarith) hltx hr)
  · exact le_max_of_le_left (rpow_le_rpow_of_nonpos hl₀ hlt hr.le)

/-- `∫₀^v e^{s²} ds = e^{v²} D₊(v)`: the Dawson function is exactly this integral, rescaled. -/
theorem integral_exp_sq_eq (v : ℝ) :
    (∫ s in (0 : ℝ)..v, exp (s ^ 2)) = exp (v ^ 2) * dawson v := by
  unfold dawson
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- The integrand left after bounding `Eθ` and pulling out `Aθ/R^B`. -/
noncomputable def Gint (B C R t : ℝ) : ℝ := (log t) ^ (B - 2) * exp (-C * sqrt (log t / R))

theorem continuousOn_Gint (B C R : ℝ) :
    ContinuousOn (Gint B C R) {t : ℝ | 1 < t} := by
  intro t ht
  have ht' : 1 < t := ht
  have hne : t ≠ 0 := by linarith
  have hlog : 0 < log t := log_pos ht'
  have h1 : ContinuousAt (fun s : ℝ => (log s) ^ (B - 2)) t :=
    (continuousAt_log hne).rpow_const (Or.inl hlog.ne')
  have h2 : ContinuousAt (fun s : ℝ => exp (-C * sqrt (log s / R))) t :=
    Real.continuous_exp.continuousAt.comp (continuousAt_const.mul
      (continuous_sqrt.continuousAt.comp ((continuousAt_log hne).div_const R)))
  exact (h1.mul h2).continuousWithinAt

theorem integral_Gint_subst {B C R x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    (∫ t in x₀..x, Gint B C R t)
      = ∫ u in sqrt (log x₀)..sqrt (log x), exp (u ^ 2) * (2 * u) * Gint B C R (exp (u ^ 2)) := by
  have hx1 : 1 < x := lt_of_lt_of_le hx₀ hx
  have ha : exp (sqrt (log x₀) ^ 2) = x₀ := by
    rw [sq_sqrt (log_pos hx₀).le, Real.exp_log (by linarith)]
  have hb : exp (sqrt (log x) ^ 2) = x := by
    rw [sq_sqrt (log_pos hx1).le, Real.exp_log (by linarith)]
  have hderiv : ∀ u ∈ Set.uIcc (sqrt (log x₀)) (sqrt (log x)),
      HasDerivAt (fun y : ℝ => exp (y ^ 2)) (exp (u ^ 2) * (2 * u)) u := by
    intro u _
    have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
    exact hsq.exp
  have hcont' : ContinuousOn (fun u : ℝ => exp (u ^ 2) * (2 * u))
      (Set.uIcc (sqrt (log x₀)) (sqrt (log x))) :=
    ((Real.continuous_exp.comp (continuous_pow 2)).mul (continuous_const.mul continuous_id)).continuousOn
  have hab : sqrt (log x₀) ≤ sqrt (log x) :=
    sqrt_le_sqrt (log_le_log (by linarith) hx)
  have ha0 : 0 < sqrt (log x₀) := sqrt_pos.mpr (log_pos hx₀)
  have himg : (fun y : ℝ => exp (y ^ 2)) '' Set.uIcc (sqrt (log x₀)) (sqrt (log x))
      ⊆ {t : ℝ | 1 < t} := by
    rintro t ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le hab] at hu
    have hupos : 0 < u := lt_of_lt_of_le ha0 hu.1
    show 1 < exp (u ^ 2)
    calc (1 : ℝ) = exp 0 := Real.exp_zero.symm
      _ < exp (u ^ 2) := Real.exp_lt_exp.mpr (pow_pos hupos 2)
  have hsub := integral_deriv_smul_comp' hderiv hcont'
    ((continuousOn_Gint B C R).mono himg)
  rw [ha, hb] at hsub
  simpa using hsub.symm

theorem Gint_subst_eq {B C R u : ℝ} (hR : 0 < R) (hu : 0 < u) :
    exp (u ^ 2) * (2 * u) * Gint B C R (exp (u ^ 2))
      = 2 * u ^ (2 * B - 3) * exp (u ^ 2 - C * u / sqrt R) := by
  have hsr : 0 < sqrt R := sqrt_pos.mpr hR
  -- `u ^ 2` is npow on the left and rpow on the right; they print identically, so the conversion
  -- has to be a named step rather than a rewrite that could fire on either.
  have key : ((u : ℝ) ^ (2 : ℕ)) ^ (B - 2) = u ^ (2 * (B - 2)) := by
    rw [← rpow_natCast u 2, ← rpow_mul hu.le]
    norm_num
  have key2 : u ^ (2 * B - 3) = u * u ^ (2 * (B - 2)) := by
    rw [show (2 * B - 3 : ℝ) = 1 + 2 * (B - 2) by ring, rpow_add hu, rpow_one]
  have key3 : exp (u ^ 2) * exp (-C * (u / sqrt R)) = exp (u ^ 2 - C * u / sqrt R) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold Gint
  rw [Real.log_exp, sqrt_div (by positivity), sqrt_sq hu.le, key, key2, ← key3]
  ring

/-- Dropping the lower endpoint of `∫ e^{v²}`, valid only when that endpoint is nonnegative.

This is the step that needs `hC` in `integral_theta_bound`; see the module docstring. -/
theorem integral_exp_sq_le_dawson {p q : ℝ} (hp : 0 ≤ p) :
    (∫ v in p..q, exp (v ^ 2)) ≤ exp (q ^ 2) * dawson q := by
  have hint : ∀ r s : ℝ, IntervalIntegrable (fun v : ℝ => exp (v ^ 2)) MeasureTheory.volume r s :=
    fun r s ↦ continuous_exp_sq.intervalIntegrable r s
  have hsplit : (∫ v in (0 : ℝ)..q, exp (v ^ 2)) - (∫ v in (0 : ℝ)..p, exp (v ^ 2))
      = ∫ v in p..q, exp (v ^ 2) :=
    intervalIntegral.integral_interval_sub_left (hint 0 q) (hint 0 p)
  have hp0 : 0 ≤ ∫ v in (0 : ℝ)..p, exp (v ^ 2) :=
    intervalIntegral.integral_nonneg hp fun _ _ ↦ (exp_pos _).le
  rw [← hsplit, integral_exp_sq_eq]
  linarith

/-- The exponentials of the final step collapse to `x · exp(-C√(log x / R))`. -/
theorem exp_square_collapse {C R x : ℝ} (hR : 0 < R) (hx : 1 < x) :
    exp (-(C ^ 2 / (4 * R))) * exp ((sqrt (log x) - C / (2 * sqrt R)) ^ 2)
      = x * exp (-C * sqrt (log x / R)) := by
  have hL : 0 < log x := log_pos hx
  have hsr : 0 < sqrt R := sqrt_pos.mpr hR
  have hsq : sqrt R ^ 2 = R := sq_sqrt hR.le
  have hLs : sqrt (log x) ^ 2 = log x := sq_sqrt hL.le
  have hsr0 : sqrt R ≠ 0 := hsr.ne'
  have h1 : exp (-(C ^ 2 / (4 * R))) * exp ((sqrt (log x) - C / (2 * sqrt R)) ^ 2)
      = exp (log x - C / sqrt R * sqrt (log x)) := by
    rw [← Real.exp_add]
    congr 1
    -- Make the two roots opaque before rewriting `R` and `log x`, or the rewrite fires inside
    -- them; same trap as `deriv_g`.
    set r := sqrt R with hr
    set L := sqrt (log x) with hLdef
    rw [← hsq, ← hLs]
    field_simp
    ring
  have h2 : x * exp (-C * sqrt (log x / R)) = exp (log x - C / sqrt R * sqrt (log x)) := by
    rw [Real.exp_sub, Real.exp_log (by linarith : (0 : ℝ) < x), sqrt_div hL.le,
      show -C * (sqrt (log x) / sqrt R) = -(C / sqrt R * sqrt (log x)) by ring, Real.exp_neg]
    ring
  rw [h1, h2]

theorem mFactor_pos {B x₀ x : ℝ} (h₀ : 1 < x₀) (hx : x₀ ≤ x) : 0 < mFactor B x₀ x := by
  have : 0 < log x₀ := log_pos h₀
  exact lt_of_lt_of_le (rpow_pos_of_pos this _) (le_max_left _ _)

/-- Steps 3-7 of Lemma 12: from the substituted integral to the Dawson bound. -/
theorem integral_subst_le {B C R x₀ x : ℝ} (hR : 0 < R) (hx₀ : 1 < x₀) (hx : x₀ ≤ x)
    (hC : C / (2 * sqrt R) ≤ sqrt (log x₀)) :
    (∫ u in sqrt (log x₀)..sqrt (log x), 2 * u ^ (2 * B - 3) * exp (u ^ 2 - C * u / sqrt R))
      ≤ 2 * mFactor B x₀ x * (x * exp (-C * sqrt (log x / R)))
        * dawson (sqrt (log x) - C / (2 * sqrt R)) := by
  have hx1 : 1 < x := lt_of_lt_of_le hx₀ hx
  have ha0 : 0 < sqrt (log x₀) := sqrt_pos.mpr (log_pos hx₀)
  have hab : sqrt (log x₀) ≤ sqrt (log x) := sqrt_le_sqrt (log_le_log (by linarith) hx)
  have hm0 : 0 < mFactor B x₀ x := mFactor_pos hx₀ hx
  set a := sqrt (log x₀) with ha
  set b := sqrt (log x) with hb
  set d := C / (2 * sqrt R) with hd
  set m := mFactor B x₀ x with hmdef
  -- Step 3->4: replace u^{2B-3} by its maximum.
  have hpt : ∀ u ∈ Set.Icc a b,
      2 * u ^ (2 * B - 3) * exp (u ^ 2 - C * u / sqrt R)
        ≤ 2 * m * exp (u ^ 2 - C * u / sqrt R) := by
    intro u hu
    have hupos : 0 < u := lt_of_lt_of_le ha0 hu.1
    have ht₀ : x₀ ≤ exp (u ^ 2) := by
      have : exp (a ^ 2) = x₀ := by
        rw [sq_sqrt (log_pos hx₀).le, Real.exp_log (by linarith)]
      rw [← this]
      exact Real.exp_le_exp.mpr (by nlinarith [hu.1, ha0])
    have htx : exp (u ^ 2) ≤ x := by
      have : exp (b ^ 2) = x := by
        rw [sq_sqrt (log_pos hx1).le, Real.exp_log (by linarith)]
      rw [← this]
      exact Real.exp_le_exp.mpr (by nlinarith [hu.2, hupos])
    have hbound := rpow_log_le_mFactor (B := B) hx₀ ht₀ htx
    rw [Real.log_exp] at hbound
    have hconv : ((u : ℝ) ^ (2 : ℕ)) ^ ((2 * B - 3) / 2) = u ^ (2 * B - 3) := by
      rw [← rpow_natCast u 2, ← rpow_mul hupos.le]
      congr 1
      push_cast
      ring
    rw [hconv] at hbound
    have := exp_pos (u ^ 2 - C * u / sqrt R)
    nlinarith [hbound, this]
  -- integrability of both sides
  have hcf : ContinuousOn (fun u : ℝ => 2 * u ^ (2 * B - 3) * exp (u ^ 2 - C * u / sqrt R))
      (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro u hu
    have hupos : 0 < u := lt_of_lt_of_le ha0 hu.1
    have h1 : ContinuousAt (fun y : ℝ => (2 : ℝ) * y ^ (2 * B - 3)) u :=
      continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hupos.ne'))
    have h2 : ContinuousAt (fun y : ℝ => exp (y ^ 2 - C * y / sqrt R)) u :=
      Real.continuous_exp.continuousAt.comp
        ((continuousAt_pow u 2).sub ((continuousAt_const.mul continuousAt_id).div_const _))
    exact (h1.mul h2).continuousWithinAt
  have hcg : Continuous (fun u : ℝ => 2 * m * exp (u ^ 2 - C * u / sqrt R)) :=
    continuous_const.mul (Real.continuous_exp.comp (by fun_prop))
  have hstep1 : (∫ u in a..b, 2 * u ^ (2 * B - 3) * exp (u ^ 2 - C * u / sqrt R))
      ≤ ∫ u in a..b, 2 * m * exp (u ^ 2 - C * u / sqrt R) :=
    intervalIntegral.integral_mono_on hab hcf.intervalIntegrable
      (hcg.intervalIntegrable _ _) hpt
  -- complete the square
  have hsr : (0 : ℝ) < sqrt R := sqrt_pos.mpr hR
  have hsq2 : sqrt R ^ 2 = R := sq_sqrt hR.le
  have hsq : ∀ u : ℝ, exp (u ^ 2 - C * u / sqrt R)
      = exp (-(C ^ 2 / (4 * R))) * exp ((u - d) ^ 2) := by
    intro u
    rw [← Real.exp_add]
    congr 1
    rw [hd]
    field_simp
    nlinarith [hsq2]
  have hstep2 : (∫ u in a..b, 2 * m * exp (u ^ 2 - C * u / sqrt R))
      = 2 * m * exp (-(C ^ 2 / (4 * R))) * ∫ u in a..b, exp ((u - d) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun u _ ↦ by rw [hsq u]; ring
  have hstep3 : (∫ u in a..b, exp ((u - d) ^ 2)) = ∫ v in (a - d)..(b - d), exp (v ^ 2) :=
    intervalIntegral.integral_comp_sub_right (fun v ↦ exp (v ^ 2)) d
  have hstep4 : (∫ v in (a - d)..(b - d), exp (v ^ 2)) ≤ exp ((b - d) ^ 2) * dawson (b - d) :=
    integral_exp_sq_le_dawson (by linarith)
  calc (∫ u in a..b, 2 * u ^ (2 * B - 3) * exp (u ^ 2 - C * u / sqrt R))
      ≤ ∫ u in a..b, 2 * m * exp (u ^ 2 - C * u / sqrt R) := hstep1
    _ = 2 * m * exp (-(C ^ 2 / (4 * R))) * ∫ u in a..b, exp ((u - d) ^ 2) := hstep2
    _ = 2 * m * exp (-(C ^ 2 / (4 * R))) * ∫ v in (a - d)..(b - d), exp (v ^ 2) := by rw [hstep3]
    _ ≤ 2 * m * exp (-(C ^ 2 / (4 * R))) * (exp ((b - d) ^ 2) * dawson (b - d)) :=
        mul_le_mul_of_nonneg_left hstep4 (by positivity)
    _ = 2 * m * (x * exp (-C * sqrt (log x / R))) * dawson (b - d) := by
        rw [hb, hd, ← exp_square_collapse hR hx1]; ring

theorem admissibleBound_div_log_sq {A B C R t : ℝ} (hR : 0 < R) (ht : 1 < t) :
    admissibleBound A B C R t / (log t) ^ 2 = A * R ^ (-B) * Gint B C R t := by
  have hlog : 0 < log t := log_pos ht
  have hRB : (0 : ℝ) < R ^ B := rpow_pos_of_pos hR B
  have hL2 : (0 : ℝ) < (log t) ^ (2 : ℕ) := pow_pos hlog 2
  have hsplit : (log t) ^ B / (log t) ^ (2 : ℕ) = (log t) ^ (B - 2) := by
    rw [← rpow_natCast (log t) 2, ← rpow_sub hlog]
    congr 1
  have hs : (log t / R) ^ ((1 : ℝ) / 2) = sqrt (log t / R) := (sqrt_eq_rpow _).symm
  unfold admissibleBound Gint
  rw [hs, div_rpow hlog.le hR.le, rpow_neg hR.le, ← hsplit]
  field_simp

theorem intervalIntegrable_theta_integrand {x₀ x : ℝ} (hx₀ : 1 < x₀) (hx : x₀ ≤ x) :
    IntervalIntegrable (fun t : ℝ => |Chebyshev.theta t - t| / (t * (log t) ^ 2))
      MeasureTheory.volume x₀ x := by
  have hθ : IntervalIntegrable Chebyshev.theta MeasureTheory.volume x₀ x :=
    Chebyshev.theta_mono.intervalIntegrable
  have hid : IntervalIntegrable (fun t : ℝ => t) MeasureTheory.volume x₀ x :=
    continuous_id.intervalIntegrable _ _
  have habs : IntervalIntegrable (fun t : ℝ => |Chebyshev.theta t - t|)
      MeasureTheory.volume x₀ x := (hθ.sub hid).abs
  have hcont : ContinuousOn (fun t : ℝ => (t * (log t) ^ 2)⁻¹) (Set.uIcc x₀ x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hx₀ ht.1
    have hlog : 0 < log t := log_pos ht1
    have hne : t * (log t) ^ 2 ≠ 0 := by positivity
    exact ((continuousAt_id.mul
      ((continuousAt_log (by linarith)).pow 2)).inv₀ hne).continuousWithinAt
  simpa [div_eq_mul_inv] using habs.mul_continuousOn hcont

/-- **Lemma 12.** The integral partial summation produces, bounded via the Dawson function.

See the module docstring for `hC`, which the published statement omits and without which the
paper's final step is false. -/
theorem integral_theta_bound {Aθ B C R x₀ : ℝ} (hR : 0 < R) (hx₀ : 1 < x₀)
    (hC : C / (2 * sqrt R) ≤ sqrt (log x₀))
    (h : HasClassicalBound Eθ Aθ B C R x₀) {x : ℝ} (hx : x₀ ≤ x) :
    (∫ t in x₀..x, |Chebyshev.theta t - t| / (t * (log t) ^ 2)) ≤
      2 * Aθ / R ^ B * x * mFactor B x₀ x * exp (-C * sqrt (log x / R)) *
        dawson (sqrt (log x) - C / (2 * sqrt R)) := by
  have hx1 : 1 < x := lt_of_lt_of_le hx₀ hx
  have hlog₀ : 0 < log x₀ := log_pos hx₀
  have ha0 : 0 < sqrt (log x₀) := sqrt_pos.mpr hlog₀
  have hab : sqrt (log x₀) ≤ sqrt (log x) := sqrt_le_sqrt (log_le_log (by linarith) hx)
  have hsubIcc : Set.Icc x₀ x ⊆ {t : ℝ | 1 < t} := fun t ht ↦ lt_of_lt_of_le hx₀ ht.1
  -- `Aθ` is nonnegative because the error term it bounds is.
  have hA : 0 ≤ Aθ := by
    have h0 := h x₀ (le_refl x₀)
    have hE : 0 ≤ Eθ x₀ := by unfold Eθ; positivity
    have hq : 0 < log x₀ / R := by positivity
    have hpos : 0 < (log x₀ / R) ^ B * exp (-C * (log x₀ / R) ^ ((1 : ℝ) / 2)) := by positivity
    unfold admissibleBound at h0
    nlinarith [h0, hE, hpos]
  have hcontRHS : ContinuousOn (fun t : ℝ => admissibleBound Aθ B C R t / (log t) ^ 2)
      (Set.uIcc x₀ x) := by
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.congr ?_ fun t ht ↦ admissibleBound_div_log_sq hR (hsubIcc ht)
    exact continuousOn_const.mul ((continuousOn_Gint B C R).mono hsubIcc)
  have hstep1 : (∫ t in x₀..x, |Chebyshev.theta t - t| / (t * (log t) ^ 2))
      ≤ ∫ t in x₀..x, admissibleBound Aθ B C R t / (log t) ^ 2 := by
    refine intervalIntegral.integral_mono_on hx (intervalIntegrable_theta_integrand hx₀ hx)
      hcontRHS.intervalIntegrable fun t ht ↦ ?_
    have hlogt : 0 < log t := log_pos (hsubIcc ht)
    have heq : |Chebyshev.theta t - t| / (t * (log t) ^ 2) = Eθ t / (log t) ^ 2 := by
      unfold Eθ; rw [div_div]
    rw [heq]
    gcongr
    exact h t ht.1
  have hstep2 : (∫ t in x₀..x, admissibleBound Aθ B C R t / (log t) ^ 2)
      = Aθ * R ^ (-B) * ∫ t in x₀..x, Gint B C R t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx] at ht
    exact admissibleBound_div_log_sq hR (hsubIcc ht)
  have hstep3 : (∫ t in x₀..x, Gint B C R t)
      = ∫ u in sqrt (log x₀)..sqrt (log x),
          2 * u ^ (2 * B - 3) * exp (u ^ 2 - C * u / sqrt R) := by
    rw [integral_Gint_subst hx₀ hx]
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [Set.uIcc_of_le hab] at hu
    exact Gint_subst_eq hR (lt_of_lt_of_le ha0 hu.1)
  have hcoef : 0 ≤ Aθ * R ^ (-B) := mul_nonneg hA (rpow_pos_of_pos hR (-B)).le
  calc (∫ t in x₀..x, |Chebyshev.theta t - t| / (t * (log t) ^ 2))
      ≤ ∫ t in x₀..x, admissibleBound Aθ B C R t / (log t) ^ 2 := hstep1
    _ = Aθ * R ^ (-B) * ∫ t in x₀..x, Gint B C R t := hstep2
    _ = Aθ * R ^ (-B) * ∫ u in sqrt (log x₀)..sqrt (log x),
          2 * u ^ (2 * B - 3) * exp (u ^ 2 - C * u / sqrt R) := by rw [hstep3]
    _ ≤ Aθ * R ^ (-B) * (2 * mFactor B x₀ x * (x * exp (-C * sqrt (log x / R)))
          * dawson (sqrt (log x) - C / (2 * sqrt R))) :=
        mul_le_mul_of_nonneg_left (integral_subst_le hR hx₀ hx hC) hcoef
    _ = 2 * Aθ / R ^ B * x * mFactor B x₀ x * exp (-C * sqrt (log x / R))
          * dawson (sqrt (log x) - C / (2 * sqrt R)) := by
        rw [rpow_neg hR.le]
        field_simp

end FKS2Sol
