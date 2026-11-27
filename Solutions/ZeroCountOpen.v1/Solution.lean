/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Doolan
-/
import IEANTN.Nodes.ZeroCountOpen.v1.Conclusions
import IEANTN.Nodes.ZetaZeroes.v1.Conclusions

/-!
# Solution: `ZeroCountOpen.v1`

Proves the same declarations `Challenge.lean` states. Does not import the challenge module.

## The argument

`finite_Ioc`: the zeroes with `0 < Im ρ ≤ b` are finitely many. They lie off the real axis, so in
the closed strip `0 ≤ Re ≤ 1` (`zeroes_off_axis_in_strip`), and outside a small ball around `1`,
since `(s - 1) ζ(s) → 1` there (Mathlib's `riemannZeta_residue_one`). That set is compact and misses
the pole, so `finite_zeroes_on_compact` applies.

`exists_closed_eq_open`: take `s₀` the largest ordinate below `T` (or anything below `T` if there
is none). For `s ∈ (s₀, T)` the zero sets `0 < Im ρ ≤ s` and `0 < Im ρ < T` are *equal*, so the two
`tsum`s are the same sum. No summability is needed for this step, only the finiteness that makes
`s₀ < T`.

`ioc_bound_to_ioo`: the bound at each `s ∈ (max s₀ t₀, T)` reads `|zetaN T - M s| ≤ B s`; let
`s ↑ T`.

The applications are immediate, except `rvm_error_bound_open` at `T = 1`, where there is no room
below `T`: there `zetaN 1 ≤ zetaNClosed 1` (a sub-sum of a finite sum with nonnegative
multiplicities) gives the upper side, and `zetaN 1 ≥ 0 ≥ rvmMain 1 - 2` the lower.
-/

open Real IEANTN Filter Topology Set

namespace ZeroCountOpenSolution


variable (hfin : ZetaZeroes.v1.finite_zeroes_on_compact)
  (hstrip : ZetaZeroes.v1.zeroes_off_axis_in_strip)

/-- `ζ` has no zeroes in a punctured ball around `1`. -/
theorem exists_ball_no_zero : ∃ r > 0, ∀ z : ℂ, ‖z - 1‖ < r → riemannZeta z ≠ 0 := by
  have h := riemannZeta_residue_one
  have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
    h.eventually (isOpen_ne.mem_nhds (one_ne_zero (α := ℂ)) )
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨r, hr, fun z hz hzero ↦ ?_⟩
  by_cases h1 : z = 1
  · subst h1
    exact riemannZeta_one_ne_zero hzero
  · have := hball ⟨by rwa [Metric.mem_ball, dist_eq_norm], h1⟩
    simp [hzero] at this

include hfin hstrip in
/-- The zeroes with `0 < Im ≤ b` are finitely many. -/
theorem finite_Ioc (b : ℝ) : (zetaZeroesIn Set.univ (Set.Ioc 0 b)).Finite := by
  obtain ⟨r, hr, hno⟩ := exists_ball_no_zero
  set K : Set ℂ := {w | 0 ≤ w.re ∧ w.re ≤ 1 ∧ 0 ≤ w.im ∧ w.im ≤ |b| ∧ r ≤ ‖w - 1‖} with hK
  have hKc : IsCompact K := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    refine ⟨(isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          ((isClosed_le Complex.continuous_im continuous_const).inter
            (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)))), ?_⟩
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1 + |b|, fun w hw ↦ ?_⟩
    obtain ⟨h0, h1, h2, h3, -⟩ := hw
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 1 + |b| := by rw [abs_of_nonneg h0, abs_of_nonneg h2]; linarith
  have h1K : (1 : ℂ) ∉ K := fun h ↦ by
    have := h.2.2.2.2; simp at this; linarith
  refine (hfin K hKc h1K).subset ?_
  rintro w ⟨-, ⟨hw0, hw1⟩, hw⟩
  have hs := hstrip w hw hw0.ne'
  refine ⟨⟨hs.1, hs.2, hw0.le, hw1.trans (le_abs_self b), ?_⟩, hw⟩
  by_contra hlt
  exact hno w (not_le.mp hlt) hw

/-- The sum over zeroes depends only on the set of zeroes. -/
theorem zsum_congr {J J' : Set ℝ} (h : zetaZeroesIn Set.univ J = zetaZeroesIn Set.univ J')
    (f : ℂ → ℝ) : zetaZeroesSum Set.univ J f = zetaZeroesSum Set.univ J' f := by
  unfold zetaZeroesSum; rw [h]

include hfin hstrip in
/-- **The key step.** Below any `T > 0` there is `s₀ < T`, `0 ≤ s₀`, with `zetaNClosed s = zetaN T`
for every `s ∈ (s₀, T)`. -/
theorem exists_closed_eq_open (T : ℝ) :
    ∃ s₀ < T, ∀ s, s₀ < s → s < T → ZeroCount.v1.zetaNClosed s = zetaN T := by
  set F := (finite_Ioc hfin hstrip T).toFinset.filter (fun ρ ↦ ρ.im < T)
  by_cases hF : F.Nonempty
  · set s₀ := F.sup' hF (fun ρ ↦ ρ.im)
    have hs₀ : s₀ < T := (Finset.sup'_lt_iff hF).mpr fun ρ hρ ↦ (Finset.mem_filter.mp hρ).2
    refine ⟨s₀, hs₀, fun s hs hsT ↦ ?_⟩
    unfold ZeroCount.v1.zetaNClosed zetaN
    refine zsum_congr ?_ _
    ext ρ
    simp only [zetaZeroesIn, Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h0, h1⟩, hz⟩; exact ⟨⟨h0, h1.trans_lt hsT⟩, hz⟩
    · rintro ⟨⟨h0, h1⟩, hz⟩
      have hmem : ρ ∈ F := by
        refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ?_, h1⟩
        exact ⟨Set.mem_univ _, ⟨h0, h1.le⟩, hz⟩
      exact ⟨⟨h0, (Finset.le_sup' (fun ρ : ℂ ↦ ρ.im) hmem).trans hs.le⟩, hz⟩
  · refine ⟨min 0 (T - 1), by
      rcases le_or_gt 0 (T - 1) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h.le]; linarith, fun s hs hsT ↦ ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty] at hF
    unfold ZeroCount.v1.zetaNClosed zetaN
    refine zsum_congr ?_ _
    ext ρ
    simp only [zetaZeroesIn, Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h0, h1⟩, hz⟩; exact ⟨⟨h0, h1.trans_lt hsT⟩, hz⟩
    · rintro ⟨⟨h0, h1⟩, hz⟩
      have hmem : ρ ∈ F := by
        refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ?_, h1⟩
        exact ⟨Set.mem_univ _, ⟨h0, h1.le⟩, hz⟩
      simp [hF] at hmem

include hfin hstrip in
theorem ioc_bound_to_ioo : ZeroCountOpen.v1.ioc_bound_to_ioo := by
  intro M B t₀ T ht₀ hM hB hbd
  obtain ⟨s₀, hs₀, heq⟩ := exists_closed_eq_open hfin hstrip T
  have hlim : Tendsto (fun s ↦ |zetaN T - M s| - B s) (𝓝[<] T) (𝓝 (|zetaN T - M T| - B T)) :=
    (((continuous_const.sub continuous_id).abs.continuousAt.comp hM).sub hB).tendsto.mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] T, |zetaN T - M s| - B s ≤ 0 := by
    have hmem : Set.Ioo (max s₀ t₀) T ∈ 𝓝[<] T := Ioo_mem_nhdsLT (max_lt hs₀ ht₀)
    filter_upwards [hmem] with s ⟨hs, hsT⟩
    rw [← heq s ((le_max_left _ _).trans_lt hs) hsT]
    linarith [hbd s ((le_max_right _ _).trans_lt hs) hsT]
  have := le_of_tendsto hlim hev
  linarith

theorem zetaOrder_nonneg {ρ : ℂ} (hρ : ρ ≠ 1) : 0 ≤ zetaOrder ρ := by
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun z hz ↦
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have ha : AnalyticAt ℂ riemannZeta ρ := hd.analyticAt (isOpen_compl_singleton.mem_nhds hρ)
  rw [zetaOrder, ha.meromorphicOrderAt_eq]
  rcases analyticOrderAt riemannZeta ρ with _ | n
  · exact le_refl 0
  · exact Int.natCast_nonneg n

theorem zsum_one_nonneg {J : Set ℝ} (hJ : J ⊆ Set.Ioi 0) :
    0 ≤ zetaZeroesSum Set.univ J (fun _ ↦ (1 : ℝ)) := by
  unfold zetaZeroesSum
  refine tsum_nonneg fun ρ ↦ ?_
  have him : 0 < (ρ : ℂ).im := hJ ρ.2.2.1
  have h1 : (ρ : ℂ) ≠ 1 := by intro h; rw [h] at him; simp at him
  have := zetaOrder_nonneg h1
  simp only [one_mul]; exact_mod_cast this

theorem zsum_eq_sum {J : Set ℝ} (hf : (zetaZeroesIn Set.univ J).Finite) (f : ℂ → ℝ) :
    zetaZeroesSum Set.univ J f = ∑ ρ ∈ hf.toFinset, f ρ * (zetaOrder ρ : ℝ) := by
  unfold zetaZeroesSum
  rw [tsum_subtype (zetaZeroesIn Set.univ J) (fun ρ ↦ f ρ * (zetaOrder ρ : ℝ)),
    tsum_eq_sum (s := hf.toFinset)]
  · exact Finset.sum_congr rfl fun ρ hρ ↦
      Set.indicator_of_mem ((Set.Finite.mem_toFinset hf).mp hρ) _
  · intro ρ hρ
    exact Set.indicator_of_notMem (fun h ↦ hρ ((Set.Finite.mem_toFinset hf).mpr h)) _

include hfin hstrip in
theorem zetaN_le_closed (T : ℝ) : zetaN T ≤ ZeroCount.v1.zetaNClosed T := by
  have hc := finite_Ioc hfin hstrip T
  have ho : (zetaZeroesIn Set.univ (Set.Ioo 0 T)).Finite :=
    hc.subset fun ρ ⟨h1, ⟨h2, h3⟩, h4⟩ ↦ ⟨h1, ⟨h2, h3.le⟩, h4⟩
  unfold zetaN ZeroCount.v1.zetaNClosed
  rw [zsum_eq_sum ho, zsum_eq_sum hc]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ρ hρ _ ↦ ?_
  · intro ρ hρ
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := (Set.Finite.mem_toFinset ho).mp hρ
    exact (Set.Finite.mem_toFinset hc).mpr ⟨h1, ⟨h2, h3.le⟩, h4⟩
  · obtain ⟨-, ⟨h2, -⟩, -⟩ := (Set.Finite.mem_toFinset hc).mp hρ
    have h1 : ρ ≠ 1 := by rintro rfl; simp at h2
    have := zetaOrder_nonneg h1
    simp only [one_mul]; exact_mod_cast this

theorem rvmMain_continuousAt {T : ℝ} (hT : 0 < T) : ContinuousAt ZeroCount.v1.rvmMain T := by
  unfold ZeroCount.v1.rvmMain
  have hπ := Real.pi_pos
  have : ContinuousAt (fun t : ℝ ↦ log (t / (2 * π))) T :=
    (continuousAt_id.div_const _).log (by positivity)
  exact ((continuousAt_id.div_const _).mul this).sub (continuousAt_id.div_const _) |>.add
    continuousAt_const

theorem rvmMain_one_le : ZeroCount.v1.rvmMain 1 ≤ 7 / 8 := by
  unfold ZeroCount.v1.rvmMain
  have hπ := Real.two_le_pi
  have hlog : log (1 / (2 * π)) ≤ 0 :=
    Real.log_nonpos (by positivity) (by rw [div_le_one (by positivity)]; linarith)
  have : 1 / (2 * π) * log (1 / (2 * π)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog
  have : 0 ≤ 1 / (2 * π) := by positivity
  linarith

include hfin hstrip in
theorem rvm_error_bound_open (hrvm : ZeroCount.v1.rvm_error_bound) :
    ZeroCountOpen.v1.rvm_error_bound_open := by
  intro T hT
  rcases hT.lt_or_eq with hT | rfl
  · refine ioc_bound_to_ioo hfin hstrip ZeroCount.v1.rvmMain (fun t ↦ (1 / 5) * log t + 2) 1 T hT
      (rvmMain_continuousAt (by linarith))
      ((continuousAt_const.mul (continuousAt_log (by linarith))).add continuousAt_const)
      fun t ht _ ↦ hrvm t ht.le
  · have hup := hrvm 1 le_rfl
    have hle := zetaN_le_closed hfin hstrip 1
    have h0 : 0 ≤ zetaN 1 := zsum_one_nonneg fun x hx ↦ hx.1
    have hm := rvmMain_one_le
    rw [abs_le] at hup ⊢
    simp only [log_one, mul_zero, zero_add] at hup ⊢
    constructor <;> linarith [hup.1, hup.2]

include hfin hstrip in
theorem hasRvMBound (hrvm : ZeroCount.v1.rvm_error_bound) : ZeroCountOpen.v1.hasRvMBound := by
  intro T hT
  have := rvm_error_bound_open hfin hstrip hrvm T (by linarith)
  unfold rvmBound
  unfold ZeroCount.v1.rvmMain at this
  simpa using this

end ZeroCountOpenSolution

/-! ### The challenge declarations -/

theorem ZeroCountOpen.v1.challenge_ioc_bound_to_ioo
    (zetazeroes_v1_finite_zeroes_on_compact : ZetaZeroes.v1.finite_zeroes_on_compact)
    (zetazeroes_v1_zeroes_off_axis_in_strip : ZetaZeroes.v1.zeroes_off_axis_in_strip) :
    ZeroCountOpen.v1.ioc_bound_to_ioo :=
  ZeroCountOpenSolution.ioc_bound_to_ioo zetazeroes_v1_finite_zeroes_on_compact
    zetazeroes_v1_zeroes_off_axis_in_strip

theorem ZeroCountOpen.v1.challenge_rvm_error_bound_open
    (zerocount_v1_rvm_error_bound : ZeroCount.v1.rvm_error_bound)
    (zetazeroes_v1_finite_zeroes_on_compact : ZetaZeroes.v1.finite_zeroes_on_compact)
    (zetazeroes_v1_zeroes_off_axis_in_strip : ZetaZeroes.v1.zeroes_off_axis_in_strip) :
    ZeroCountOpen.v1.rvm_error_bound_open :=
  ZeroCountOpenSolution.rvm_error_bound_open zetazeroes_v1_finite_zeroes_on_compact
    zetazeroes_v1_zeroes_off_axis_in_strip zerocount_v1_rvm_error_bound

theorem ZeroCountOpen.v1.challenge_hasRvMBound
    (zerocount_v1_rvm_error_bound : ZeroCount.v1.rvm_error_bound)
    (zetazeroes_v1_finite_zeroes_on_compact : ZetaZeroes.v1.finite_zeroes_on_compact)
    (zetazeroes_v1_zeroes_off_axis_in_strip : ZetaZeroes.v1.zeroes_off_axis_in_strip) :
    ZeroCountOpen.v1.hasRvMBound :=
  ZeroCountOpenSolution.hasRvMBound zetazeroes_v1_finite_zeroes_on_compact
    zetazeroes_v1_zeroes_off_axis_in_strip zerocount_v1_rvm_error_bound

#print axioms ZeroCountOpen.v1.challenge_ioc_bound_to_ioo
#print axioms ZeroCountOpen.v1.challenge_rvm_error_bound_open
#print axioms ZeroCountOpen.v1.challenge_hasRvMBound
