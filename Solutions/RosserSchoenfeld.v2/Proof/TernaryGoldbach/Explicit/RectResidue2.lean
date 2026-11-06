import TernaryGoldbach.Explicit.RectResidue

/-!
# Residue theorem for `f'/f · (s − p)⁻¹`

`∮ (f'/f)(s) (s − p)⁻¹ ds = 2πi (f'/f(p) + Σ_{zeros u inside} m_u/(u − p))` for `p` strictly inside the
rectangle, `f(p) ≠ 0`.
-/

open Complex Set Metric
open scoped Real Interval

namespace TernaryGoldbach.Explicit

theorem rectInt_inv_sub_outside {z w u : ℂ} (hu : u ∉ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
    rectInt (fun s => (s - u)⁻¹) z w = 0 := by
  refine Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun s => (s - u)⁻¹) z w ?_
  intro s hs
  have hsu : s - u ≠ 0 := sub_ne_zero.2 (fun h => hu (h ▸ hs))
  exact ((differentiableAt_id.sub_const u).inv hsu).differentiableWithinAt

theorem rectIntegrable_inv_sub {z w u : ℂ}
    (hu1 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) (hu2 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u)
    (hu3 : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) (hu4 : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) :
    RectIntegrable (fun s => (s - u)⁻¹) z w := by
  have h := rectIntegrable_mul_inv_sub (h := fun _ => (1 : ℂ)) (z := z) (w := w) continuousOn_const
    hu1 hu2 hu3 hu4
  simpa using h

/-- **Residue theorem for `f'/f · (s − p)⁻¹`**. -/
theorem rectInt_logDeriv_inv_sub {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hfc : f c ≠ 0) {z w : ℂ} (hzw1 : z.re < w.re) (hzw2 : z.im < w.im)
    (hrect : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ ball c (R / 2)) (hbd : NoZerosOnSides f z w)
    {p : ℂ} (hp1 : z.re < p.re) (hp2 : p.re < w.re) (hp3 : z.im < p.im) (hp4 : p.im < w.im)
    (hfp : f p ≠ 0) :
    rectInt (fun s => logDeriv f s * (s - p)⁻¹) z w = 2 * π * I * (logDeriv f p +
      ∑ u ∈ (zerosIn f c R (R / 2)).filter
        (fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im),
        ((divB f c R u).toNat : ℂ) * (u - p)⁻¹) := by
  classical
  obtain ⟨g, hg, hg0, hfg⟩ := factor_ball hf hfc hR
  set Z := zerosIn f c R (R / 2) with hZ
  set Rect := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hRect
  have hRb : Rect ⊆ ball c R := hrect.trans (ball_subset_ball (by linarith))
  have hfu : ∀ u ∈ Z, f u = 0 := by
    intro u hu
    have hu' := (mem_zerosIn hu).2
    have hucR : u ∈ closedBall c R := by
      rw [mem_closedBall, dist_eq_norm]; linarith [(mem_zerosIn hu).1]
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (closedBall c R)) hucR] at hu'
    by_contra hne
    exact hu' (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)
  have hdec : ∀ s ∈ Rect, f s ≠ 0 →
      logDeriv f s = ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) / (s - u) + logDeriv g s := by
    intro s hs hfs
    have hsZ : ∀ u ∈ Z, s ≠ u := fun u hu h => hfs (h ▸ hfu u hu)
    have hsb : s ∈ ball c R := hRb hs
    have hsb2 : s ∈ ball c (R / 2) := hrect hs
    have hPs : Pin f c R s ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hsZ u hu))
    have hgs : g s ≠ 0 := hg0 s hsb2
    have hloc : f =ᶠ[nhds s] fun w => Pin f c R w * g w := by
      filter_upwards [isOpen_ball.mem_nhds hsb] with v hv
      exact hfg v (ball_subset_closedBall hv)
    have hPd : DifferentiableAt ℂ (Pin f c R) s := by
      have : Pin f c R = fun w => ∏ u ∈ Z, (w - u) ^ (divB f c R u).toNat := rfl
      rw [this]
      exact DifferentiableAt.fun_finsetProd fun u _ => (differentiableAt_id.sub_const u).pow _
    have hgd : DifferentiableAt ℂ g s := (hg s (ball_subset_closedBall hsb)).differentiableAt
    rw [(logDeriv_congr_nhds hloc).eq_of_nhds,
      show (fun w => Pin f c R w * g w) = Pin f c R * g from rfl,
      logDeriv_mul (f := Pin f c R) (g := g) s hPs hgs hPd hgd, logDeriv_Pin hsZ]
  have hside1 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ∈ Rect := fun x hx =>
    mem_reProdIm.2 ⟨by simpa using hx, by simp [left_mem_uIcc]⟩
  have hside2 : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ∈ Rect := fun x hx =>
    mem_reProdIm.2 ⟨by simpa using hx, by simp [right_mem_uIcc]⟩
  have hside3 : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ∈ Rect := fun y hy =>
    mem_reProdIm.2 ⟨by simp [right_mem_uIcc], by simpa using hy⟩
  have hside4 : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ∈ Rect := fun y hy =>
    mem_reProdIm.2 ⟨by simp [left_mem_uIcc], by simpa using hy⟩
  have hpR : p ∈ Rect := mem_reProdIm.2 ⟨Set.mem_uIcc.2 (Or.inl ⟨hp1.le, hp2.le⟩),
    Set.mem_uIcc.2 (Or.inl ⟨hp3.le, hp4.le⟩)⟩
  have hpZ : ∀ u ∈ Z, u - p ≠ 0 := fun u hu h => hfp (by rw [← sub_eq_zero.1 h]; exact hfu u hu)
  set S : ℂ := ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ with hS
  set F : ℂ → ℂ := fun s => (∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ * (s - u)⁻¹) +
    (logDeriv g s - S) * (s - p)⁻¹ with hF
  have hpt : ∀ s ∈ Rect, f s ≠ 0 → s ≠ p → logDeriv f s * (s - p)⁻¹ = F s := by
    intro s hs hfs hsp
    rw [hdec s hs hfs]
    simp only [hF, hS]
    have hsZ : ∀ u ∈ Z, s - u ≠ 0 := fun u hu h => hfs (by rw [sub_eq_zero.1 h]; exact hfu u hu)
    have hsp' : s - p ≠ 0 := sub_ne_zero.2 hsp
    rw [add_mul, sub_mul, Finset.sum_mul, Finset.sum_mul]
    have : ∀ u ∈ Z, ((divB f c R u).toNat : ℂ) / (s - u) * (s - p)⁻¹ =
        ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ * (s - u)⁻¹ -
          ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ * (s - p)⁻¹ := by
      intro u hu
      have h1 := hsZ u hu
      have h2 := hpZ u hu
      field_simp
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    ring
  obtain ⟨b1, b2, b3, b4⟩ := hbd
  have hpb : (∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ p) ∧ (∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ p) ∧
      (∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ p) ∧ (∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ p) := by
    obtain ⟨c1, c2, c3, c4⟩ := mem_rect_boundary_ne hp1 hp2 hp3 hp4
    exact ⟨fun x _ => c1 x, fun x _ => c2 x, fun y _ => c3 y, fun y _ => c4 y⟩
  rw [rectInt_congr' (g := F) (fun x hx => hpt _ (hside1 x hx) (b1 x hx) (hpb.1 x hx))
    (fun x hx => hpt _ (hside2 x hx) (b2 x hx) (hpb.2.1 x hx))
    (fun y hy => hpt _ (hside3 y hy) (b3 y hy) (hpb.2.2.1 y hy))
    (fun y hy => hpt _ (hside4 y hy) (b4 y hy) (hpb.2.2.2 y hy))]
  have hnot : ∀ u ∈ Z, (∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) ∧
      (∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u) ∧
      (∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) ∧ (∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) := by
    intro u hu
    refine ⟨fun x hx h' => b1 x hx (h' ▸ hfu u hu), fun x hx h' => b2 x hx (h' ▸ hfu u hu),
      fun y hy h' => b3 y hy (h' ▸ hfu u hu), fun y hy h' => b4 y hy (h' ▸ hfu u hu)⟩
  have hint_u : ∀ u ∈ Z, RectIntegrable (fun s => ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ * (s - u)⁻¹) z w :=
    fun u hu => (rectIntegrable_inv_sub (hnot u hu).1 (hnot u hu).2.1 (hnot u hu).2.2.1
      (hnot u hu).2.2.2).const_mul _
  -- `(g'/g − S)` is holomorphic on a neighbourhood of the rectangle
  set U : Set ℂ := ball c (R / 2) with hU
  have hUo : IsOpen U := isOpen_ball
  have hgdiff : DifferentiableOn ℂ (fun s => logDeriv g s - S) U := by
    intro s hs
    have hga : AnalyticAt ℂ g s := hg s (ball_subset_closedBall (ball_subset_ball (by linarith) hs))
    have hgs : g s ≠ 0 := hg0 s hs
    have : DifferentiableAt ℂ (logDeriv g) s := by
      have e : logDeriv g = fun s => deriv g s / g s := rfl
      rw [e]; exact hga.deriv.differentiableAt.div hga.differentiableAt hgs
    exact (this.sub_const S).differentiableWithinAt
  have hint_g : RectIntegrable (fun s => (logDeriv g s - S) * (s - p)⁻¹) z w :=
    rectIntegrable_mul_inv_sub (hgdiff.continuousOn.mono hrect) hpb.1 hpb.2.1 hpb.2.2.1 hpb.2.2.2
  have hint_sum : RectIntegrable
      (fun s => ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ * (s - u)⁻¹) z w := by
    have key : ∀ (φ : ℝ → ℂ) (a b : ℝ),
        (∀ u ∈ Z, IntervalIntegrable (fun t => ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ * (φ t - u)⁻¹)
          MeasureTheory.volume a b) →
        IntervalIntegrable (fun t => ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ * (φ t - u)⁻¹)
          MeasureTheory.volume a b := by
      intro φ a b hφ
      have := IntervalIntegrable.sum Z fun u hu => hφ u hu
      convert this using 1
      ext t; simp [Finset.sum_apply]
    exact ⟨key _ _ _ fun u hu => (hint_u u hu).1, key _ _ _ fun u hu => (hint_u u hu).2.1,
      key _ _ _ fun u hu => (hint_u u hu).2.2.1, key _ _ _ fun u hu => (hint_u u hu).2.2.2⟩
  rw [hF, rectInt_add' hint_sum hint_g, rectInt_mul_inv_sub hUo hrect hgdiff hp1 hp2 hp3 hp4,
    rectInt_finset_sum Z _ hint_u]
  have hterm : ∀ u ∈ Z, rectInt (fun s => ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ * (s - u)⁻¹) z w =
      if z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im then
        2 * π * I * (((divB f c R u).toNat : ℂ) * (u - p)⁻¹) else 0 := by
    intro u hu
    rw [rectInt_const_mul]
    split_ifs with hin
    · rw [rectInt_inv_sub hin.1 hin.2.1 hin.2.2.1 hin.2.2.2]; ring
    · by_cases huR : u ∈ Rect
      · exfalso
        rcases mem_rect_cases huR hzw1 hzw2 with h' | h' | h' | h' | h'
        · exact hin h'
        · exact (hnot u hu).1 u.re (by
            rw [mem_reProdIm] at huR; exact huR.1) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.1 u.re (by
            rw [mem_reProdIm] at huR; exact huR.1) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.2.1 u.im (by
            rw [mem_reProdIm] at huR; exact huR.2) (by apply Complex.ext <;> simp [h'])
        · exact (hnot u hu).2.2.2 u.im (by
            rw [mem_reProdIm] at huR; exact huR.2) (by apply Complex.ext <;> simp [h'])
      · rw [rectInt_inv_sub_outside huR, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  -- `logDeriv g p = logDeriv f p + S`
  have hgp : logDeriv g p = logDeriv f p + S := by
    rw [hdec p hpR hfp, hS]
    have : ∑ u ∈ Z, ((divB f c R u).toNat : ℂ) / (p - u) = -∑ u ∈ Z, ((divB f c R u).toNat : ℂ) * (u - p)⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u hu => ?_
      have := hpZ u hu
      have h2 : p - u ≠ 0 := by intro h; apply this; rw [sub_eq_zero.1 h, sub_self]
      field_simp
      ring
    rw [this]; ring
  rw [hgp, ← Finset.mul_sum]
  ring

end TernaryGoldbach.Explicit
