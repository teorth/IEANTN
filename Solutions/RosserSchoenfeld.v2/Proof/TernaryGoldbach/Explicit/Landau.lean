import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Landau's lemma: `f'/f` near a point, minus the nearby zeros, is small

For `f` entire with `f(c) ≠ 0` and `|f| ≤ B` on `|z − c| ≤ R`:
`|f'/f(z) − Σ_{|ρ − c| < R/2} m_ρ/(z − ρ)| ≤ 48 log(B/|f(c)|)/R` for `|z − c| ≤ R/4`
([MV07, Lemma 6.3], with explicit constants). Proof: factor `f = P_in · g` on `|z − c| ≤ R`
(`MeromorphicOn.extract_zeros_poles`), bound `|g/g(c)| ≤ B/|f(c)|` by the maximum principle, take
`h = log(g/g(c))` on `|z − c| < R/2`, and apply Borel–Carathéodory and a Cauchy estimate to `h`.
-/

open Complex Metric Set Filter Topology

namespace TernaryGoldbach.Explicit

variable {f : ℂ → ℂ} {c : ℂ} {R : ℝ}

/-- The divisor of `f` on `closedBall c R`. -/
noncomputable abbrev divB (f : ℂ → ℂ) (c : ℂ) (R : ℝ) := MeromorphicOn.divisor f (closedBall c R)

theorem divB_finite (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : (divB f c R).support.Finite :=
  (divB f c R).finiteSupport (isCompact_closedBall c R)

/-- The zeros of `f` in `‖u − c‖ < r` among those in `closedBall c R`. -/
noncomputable def zerosIn (f : ℂ → ℂ) (c : ℂ) (R r : ℝ) : Finset ℂ :=
  (divB_finite f c R).toFinset.filter fun u => ‖u - c‖ < r

theorem preperfect_closedBall (hR : 0 < R) : Preperfect (closedBall c R) := by
  rw [← closure_ball c hR.ne']
  exact (isOpen_ball.preperfect).perfect_closure.acc

/-- **Factorization**: `f = (Π_{|u − c| < R/2} (z − u)^{m_u}) · g` on `closedBall c R`, `g` analytic
there and zero-free on `ball c (R/2)`. -/
theorem factor_ball (hf : Differentiable ℂ f) (hfc : f c ≠ 0) (hR : 0 < R) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧ (∀ z ∈ ball c (R / 2), g z ≠ 0) ∧
      ∀ z ∈ closedBall c R,
        f z = (∏ u ∈ zerosIn f c R (R / 2), (z - u) ^ (divB f c R u).toNat) * g z := by
  have hfa : AnalyticOnNhd ℂ f (closedBall c R) := fun z _ => hf.analyticAt z
  have hfa' : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hc0 : analyticOrderAt f c ≠ ⊤ := by
    rw [(hf.analyticAt c).analyticOrderAt_eq_zero.2 hfc]; simp
  have h₂f : ∀ u : closedBall c R, meromorphicOrderAt f u ≠ ⊤ := fun u => by
    rw [(hf.analyticAt u).meromorphicOrderAt_eq]
    have := hfa'.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ c)
      (mem_univ (u : ℂ)) hc0
    intro h
    apply this
    cases hk : analyticOrderAt f u <;> simp_all
  obtain ⟨g, hg, hg0, hfg⟩ := hfa.meromorphicOn.extract_zeros_poles h₂f (divB_finite f c R)
  set D := divB f c R with hD
  set S := (divB_finite f c R).toFinset with hS
  have hDnn : ∀ u, 0 ≤ D u := fun u => (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa) u
  -- the factorized rational function as a finite product
  have hP : ∀ z, (∏ᶠ u, (· - u) ^ D u) z = ∏ u ∈ S, (z - u) ^ (D u).toNat := by
    intro z
    rw [Function.FactorizedRational.finprod_eq_fun (divB_finite f c R)]
    simp only
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · refine Finset.prod_congr rfl fun u _ => ?_
      rw [← zpow_natCast, Int.toNat_of_nonneg (hDnn u)]
    · intro u hu
      rw [Function.mem_mulSupport] at hu
      simp only [hS, Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0; apply hu; rw [h0, zpow_zero]
  -- genuine equality on the closed ball
  have heq : ∀ z ∈ closedBall c R, f z = (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z := by
    intro z hz
    have hPa : AnalyticAt ℂ (fun z => (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z) z := by
      refine AnalyticAt.mul ?_ (hg z hz)
      exact Finset.analyticAt_fun_prod _ fun u _ => ((analyticAt_id.sub analyticAt_const).pow _)
    have hfg' : f =ᶠ[codiscreteWithin (closedBall c R)]
        (fun z => (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z) := by
      refine hfg.trans (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.smul_apply', smul_eq_mul]
      rw [hP w]
    have h := (hf.analyticAt z).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      hPa.meromorphicAt hz (preperfect_closedBall hR) hfg'
    exact tendsto_nhds_unique ((hf.continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
      (hPa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr' h.symm)
  -- split off the zeros outside `R/2`
  set Sout := S.filter fun u => ¬ ‖u - c‖ < R / 2
  refine ⟨fun z => (∏ u ∈ Sout, (z - u) ^ (D u).toNat) * g z, ?_, ?_, ?_⟩
  · intro z hz
    refine AnalyticAt.mul ?_ (hg z hz)
    exact Finset.analyticAt_fun_prod _ fun u _ => ((analyticAt_id.sub analyticAt_const).pow _)
  · intro z hz
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ ?_)
      (hg0 ⟨z, ball_subset_closedBall (ball_subset_ball (by linarith) hz)⟩)
    intro h
    rw [sub_eq_zero] at h
    rw [Finset.mem_filter] at hu
    rw [mem_ball, dist_eq_norm, h] at hz
    exact hu.2 hz
  · intro z hz
    rw [heq z hz, zerosIn, ← mul_assoc, Finset.prod_filter_mul_prod_filter_not]

/-- The zero-polynomial `Π_{u ∈ Z} (z − u)^{m_u}`. -/
noncomputable def Pin (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∏ u ∈ zerosIn f c R (R / 2), (z - u) ^ (divB f c R u).toNat

theorem mem_zerosIn {f : ℂ → ℂ} {c u : ℂ} {R r : ℝ} (hu : u ∈ zerosIn f c R r) :
    ‖u - c‖ < r ∧ divB f c R u ≠ 0 := by
  rw [zerosIn, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support] at hu
  exact ⟨hu.2, hu.1⟩

theorem ne_of_mem_zerosIn (hf : Differentiable ℂ f) (hfc : f c ≠ 0) {u : ℂ} {r : ℝ}
    (hu : u ∈ zerosIn f c R r) : u ≠ c := by
  rintro rfl
  apply (mem_zerosIn hu).2
  by_cases hcR : u ∈ closedBall u R
  · rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (closedBall u R)) hcR,
      (hf.analyticAt u).analyticOrderAt_eq_zero.2 hfc]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hcR

theorem logDeriv_Pin {z : ℂ} (hz : ∀ u ∈ zerosIn f c R (R / 2), z ≠ u) :
    logDeriv (Pin f c R) z = ∑ u ∈ zerosIn f c R (R / 2), ((divB f c R u).toNat : ℂ) / (z - u) := by
  have e : Pin f c R = ∏ u ∈ zerosIn f c R (R / 2), (fun z => (z - u) ^ (divB f c R u).toNat) := by
    ext w; simp [Pin, Finset.prod_apply]
  rw [e, logDeriv_prod (f := fun (u : ℂ) (w : ℂ) => (w - u) ^ (divB f c R u).toNat) (x := z)
    (fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hz u hu)))
    (fun u _ => (differentiableAt_id.sub_const u).pow _)]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hd : DifferentiableAt ℂ (fun w : ℂ => w - u) z := differentiableAt_id.sub_const u
  rw [logDeriv_fun_pow hd, logDeriv_apply, deriv_sub_const, deriv_id'']
  ring

set_option maxHeartbeats 1000000 in
/-- **Landau's lemma.** `f` entire, `f(c) ≠ 0`, `|f| ≤ B` on `|z − c| ≤ R`, `|f(c)| < B`. For
`|z − c| ≤ R/4` with `f(z) ≠ 0`:
`|f'(z)/f(z) − Σ_{|ρ−c|<R/2} m_ρ/(z − ρ)| ≤ 48 log(B/|f(c)|)/R`. -/
theorem landau (hf : Differentiable ℂ f) (hfc : f c ≠ 0) (hR : 0 < R) {B : ℝ}
    (hB : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) (hBc : ‖f c‖ < B) {z : ℂ} (hz : z ∈ closedBall c (R / 4))
    (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ u ∈ zerosIn f c R (R / 2), ((divB f c R u).toNat : ℂ) / (z - u)‖ ≤
      48 * Real.log (B / ‖f c‖) / R := by
  obtain ⟨g, hg, hg0, hfg⟩ := factor_ball hf hfc hR
  set Z := zerosIn f c R (R / 2) with hZ
  set A := Real.log (B / ‖f c‖) with hA
  have hfc0 : 0 < ‖f c‖ := norm_pos_iff.2 hfc
  have hA0 : 0 < A := Real.log_pos (by rw [one_lt_div hfc0]; exact hBc)
  have hcR : c ∈ closedBall c R := mem_closedBall_self hR.le
  have hfg' : ∀ w ∈ closedBall c R, f w = Pin f c R w * g w := hfg
  -- `P(c) ≠ 0`, `g(c) ≠ 0`
  have hPc : Pin f c R c ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 (ne_of_mem_zerosIn hf hfc hu).symm)
  have hgc : g c ≠ 0 := hg0 c (mem_ball_self (by linarith))
  -- maximum principle: `|g| ≤ (B/|f c|)|g c|` on the closed ball
  have hgd : DifferentiableOn ℂ g (closedBall c R) := hg.differentiableOn
  have hmax : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B / ‖Pin f c R c‖ := by
    intro w hw
    have hdc : DiffContOnCl ℂ g (ball c R) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball c hR.ne']; exact hgd
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc (fun v hv => ?_)
      (by rw [closure_ball c hR.ne']; exact hw)
    rw [frontier_ball c hR.ne', mem_sphere, dist_eq_norm] at hv
    have hvR : v ∈ closedBall c R := by rw [mem_closedBall, dist_eq_norm, hv]
    have hPv : ‖Pin f c R c‖ ≤ ‖Pin f c R v‖ := by
      simp only [Pin, norm_prod, norm_pow]
      refine Finset.prod_le_prod₀ (fun u _ => by positivity) fun u hu => ?_
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
      have h1 := (mem_zerosIn hu).1
      have h2 : ‖v - c‖ ≤ ‖v - u‖ + ‖u - c‖ := by
        calc ‖v - c‖ = ‖(v - u) + (u - c)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [norm_sub_rev c u]; linarith
    have hPv0 : 0 < ‖Pin f c R c‖ := norm_pos_iff.2 hPc
    have := hB v hvR
    rw [hfg' v hvR, norm_mul] at this
    rw [le_div_iff₀ hPv0]
    calc ‖g v‖ * ‖Pin f c R c‖ ≤ ‖g v‖ * ‖Pin f c R v‖ := mul_le_mul_of_nonneg_left hPv (norm_nonneg _)
      _ = ‖Pin f c R v‖ * ‖g v‖ := by ring
      _ ≤ B := this
  have hgc' : ‖g c‖ = ‖f c‖ / ‖Pin f c R c‖ := by
    rw [hfg' c hcR, norm_mul]; field_simp
  -- a logarithm of `g/g(c)` on `ball c (R/2)`
  set r := R / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : ball c r ⊆ closedBall c R := fun w hw =>
    ball_subset_closedBall (ball_subset_ball (by rw [hr]; linarith) hw)
  have hqd : DifferentiableOn ℂ (fun w => deriv g w / g w) (ball c r) := by
    intro w hw
    have hga : AnalyticAt ℂ g w := hg w (hball hw)
    exact (hga.deriv.differentiableAt.div hga.differentiableAt (hg0 w hw)).differentiableWithinAt
  obtain ⟨H, hHc, hH⟩ := hqd.isExactOn_ball.with_val_at c 0
  have hexp : ∀ w ∈ ball c r, g w = g c * Complex.exp (H w) := by
    have hE : ∀ w ∈ ball c r, HasDerivAt (fun w => g w * Complex.exp (-H w)) 0 w := by
      intro w hw
      have hga : HasDerivAt g (deriv g w) w := (hg w (hball hw)).differentiableAt.hasDerivAt
      have := hga.mul (hH w hw).neg.cexp
      refine this.congr_deriv ?_
      have hgw := hg0 w hw
      field_simp
      ring
    intro w hw
    have h := isOpen_ball.is_const_of_deriv_eq_zero (isPreconnected_ball : IsPreconnected (ball c r))
      (f := fun w => g w * Complex.exp (-H w))
      (fun w hw => (hE w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hE w hw).deriv) hw (mem_ball_self hr0)
    simp only [hHc, neg_zero, Complex.exp_zero, mul_one] at h
    calc g w = g w * Complex.exp (-H w) * Complex.exp (H w) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = g c * Complex.exp (H w) := by rw [h]
  have hReH : ∀ w ∈ ball c r, (H w).re ≤ A := by
    intro w hw
    have h1 : ‖g w‖ = ‖g c‖ * Real.exp (H w).re := by
      rw [hexp w hw, norm_mul, Complex.norm_exp]
    have h2 := hmax w (hball hw)
    have hgc0 : 0 < ‖g c‖ := norm_pos_iff.2 hgc
    rw [hA, Real.le_log_iff_exp_le (div_pos (by linarith) hfc0)]
    rw [h1, hgc'] at h2
    have hPc0 : 0 < ‖Pin f c R c‖ := norm_pos_iff.2 hPc
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hPc0] at h2
    rw [le_div_iff₀ hfc0]; linarith
  -- Borel–Carathéodory on `ball c r`
  have hBC : ∀ w ∈ closedBall c (3 * R / 8), ‖H w‖ ≤ 6 * A := by
    intro w hw
    have hFd : DifferentiableOn ℂ (fun v => H (c + v)) (ball 0 r) := by
      intro v hv
      have hv' : c + v ∈ ball c r := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; rwa [mem_ball, dist_zero_right] at hv
      exact ((hH _ hv').differentiableAt.comp v
        (differentiableAt_const _ |>.add differentiableAt_id)).differentiableWithinAt
    have hFre : Set.MapsTo (fun v => H (c + v)) (ball 0 r) {z | z.re ≤ A} := by
      intro v hv
      have hv' : c + v ∈ ball c r := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; rwa [mem_ball, dist_zero_right] at hv
      exact hReH _ hv'
    have hwv : w - c ∈ ball (0:ℂ) r := by
      rw [mem_ball, dist_zero_right]
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [hr]; linarith
    have h := Complex.borelCaratheodory_zero hA0 hFd hFre hr0 hwv (by simp [hHc])
    simp only [add_sub_cancel] at h
    have hn : ‖w - c‖ ≤ 3 * R / 8 := by rwa [mem_closedBall, dist_eq_norm] at hw
    refine h.trans ?_
    rw [div_le_iff₀ (by rw [hr]; linarith)]
    rw [hr]; nlinarith [norm_nonneg (w - c)]
  -- Cauchy estimate at `z`
  have hzc : ‖z - c‖ ≤ R / 4 := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hzr : z ∈ ball c r := by rw [mem_ball, dist_eq_norm, hr]; linarith
  have hderiv : ‖deriv H z‖ ≤ 6 * A / (R / 8) := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) ?_ (fun w hw => ?_)
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z (by linarith : R / 8 ≠ 0)]
      intro w hw
      refine (hH w ?_).differentiableAt.differentiableWithinAt
      rw [mem_closedBall, dist_eq_norm] at hw
      rw [mem_ball, dist_eq_norm, hr]
      have : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
        calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    · refine hBC w ?_
      rw [mem_sphere, dist_eq_norm] at hw
      rw [mem_closedBall, dist_eq_norm]
      have : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
        calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
  -- identify `H'(z) = f'/f(z) − P'/P(z)`
  have hzZ : ∀ u ∈ Z, z ≠ u := by
    intro u hu h
    rw [h] at hfz
    apply hfz
    have hu' := (mem_zerosIn hu).2
    have hucR : u ∈ closedBall c R := by
      rw [mem_closedBall, dist_eq_norm]; linarith [(mem_zerosIn hu).1]
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => hf.analyticAt z : AnalyticOnNhd ℂ f (closedBall c R)) hucR] at hu'
    by_contra hne
    exact hu' (by rw [(hf.analyticAt u).analyticOrderAt_eq_zero.2 hne]; simp)
  have hPz : Pin f c R z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (sub_ne_zero.2 (hzZ u hu))
  have hgz : g z ≠ 0 := hg0 z hzr
  have hloc : f =ᶠ[𝓝 z] fun w => Pin f c R w * g w := by
    have : ball c R ∈ 𝓝 z := isOpen_ball.mem_nhds (by rw [mem_ball, dist_eq_norm]; linarith)
    filter_upwards [this] with w hw
    exact hfg' w (ball_subset_closedBall hw)
  have hPd : DifferentiableAt ℂ (Pin f c R) z := by
    have : Pin f c R = fun w => ∏ u ∈ Z, (w - u) ^ (divB f c R u).toNat := rfl
    rw [this]
    exact DifferentiableAt.fun_finsetProd fun u _ => (differentiableAt_id.sub_const u).pow _
  have hgd' : DifferentiableAt ℂ g z := (hg z (hball hzr)).differentiableAt
  have hlog : logDeriv f z = logDeriv (Pin f c R) z + deriv H z := by
    rw [(logDeriv_congr_nhds hloc).eq_of_nhds]
    have := logDeriv_mul (f := Pin f c R) (g := g) z hPz hgz hPd hgd'
    rw [show (fun w => Pin f c R w * g w) = Pin f c R * g from rfl, this, (hH z hzr).deriv,
      logDeriv_apply g]
  rw [hlog, logDeriv_Pin hzZ, add_sub_cancel_left]
  refine hderiv.trans (le_of_eq ?_)
  field_simp
  ring

end TernaryGoldbach.Explicit
