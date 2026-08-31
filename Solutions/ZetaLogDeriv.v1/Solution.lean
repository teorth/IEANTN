/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib
import IEANTN.Nodes.ZetaLogDeriv.v1.Conclusions

/-!
# Solution: `ZetaLogDeriv.v1`

The functional equation for zeta, differentiated.

The proof is Mathlib's own `riemannZeta_one_sub` put through `logDeriv`, factor by factor. The
only step with any content is getting a *neighbourhood* of `s` on which the functional equation
holds, since `logDeriv` of a product needs the identity nearby, not merely at the point.

The obvious neighbourhood is the complement of the integers, open because
`isClosed_range_intCast`. That is not quite enough here: the conclusion's hypotheses admit even
integers `s ≥ 2` — at `s = 2` every side condition holds, `cos (π * 2 / 2) = -1 ≠ 0` included — and
those are integers. So the set used instead is `{z | 1 < z.re} ∪ (range Int.cast)ᶜ`, a union of two
opens. `riemannZeta_one_sub` applies on both pieces: on the half-plane because `-n` and `1` all
have real part at most `1`, and on the complement because neither is an integer. And `s` lies in
it — if `s` is not an integer the second piece contains it, and if it is, the hypotheses force it
past `2`.

`ζ(1-s) ≠ 0` is never needed, though the statement divides by it: the functional equation writes
`ζ(1-s)` as a product of factors already known nonzero here.
-/

open scoped Real
open Complex Filter Topology

namespace Solution.ZetaLogDeriv

/-- The identity in `logDeriv` form, which is the shape Mathlib's lemmas are stated in. -/
theorem logDeriv_riemannZeta_one_sub {s : ℂ} (hsn : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) (hcos : Complex.cos (π * s / 2) ≠ 0) :
    logDeriv riemannZeta s =
      -logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - digamma s
        + π / 2 * Complex.tan (π * s / 2) := by
  have hs0 : s ≠ 0 := by simpa using hsn 0
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero hsn
  have h2π : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hcpow : (2 * (π : ℂ)) ^ (-s) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, h2π]
  have hUopen : IsOpen ({z : ℂ | 1 < z.re} ∪ (Set.range ((↑) : ℤ → ℂ))ᶜ) :=
    (isOpen_lt continuous_const Complex.continuous_re).union
      isClosed_range_intCast.isOpen_compl
  have hsU : s ∈ ({z : ℂ | 1 < z.re} ∪ (Set.range ((↑) : ℤ → ℂ))ᶜ) := by
    by_cases h : s ∈ Set.range ((↑) : ℤ → ℂ)
    · obtain ⟨k, rfl⟩ := h
      refine Or.inl ?_
      have hk0 : 0 < k := by
        by_contra hk
        push_neg at hk
        obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
        exact hsn m (by push_cast; ring)
      have hk1 : k ≠ 1 := fun h => hs1 (by exact_mod_cast h)
      have hk2 : (1 : ℤ) < k := by omega
      simpa using (by exact_mod_cast hk2 : (1 : ℝ) < (k : ℝ))
    · exact Or.inr h
  have hEq : (fun z => riemannZeta (1 - z)) =ᶠ[𝓝 s]
      (fun z => 2 * (2 * π) ^ (-z) * Gamma z * Complex.cos (π * z / 2) * riemannZeta z) := by
    filter_upwards [hUopen.mem_nhds hsU] with z hzU
    rcases hzU with hlt | hnot
    · simp only [Set.mem_setOf_eq] at hlt
      refine riemannZeta_one_sub (fun n hn => ?_) (fun hn => ?_)
      · rw [hn] at hlt; simp at hlt; linarith
      · rw [hn] at hlt; simp at hlt
    · simp only [Set.mem_compl_iff, Set.mem_range, not_exists] at hnot
      exact riemannZeta_one_sub (fun n h => hnot (-n) (by simp [h])) (fun h => hnot 1 (by simp [h]))
  have hlog := (logDeriv_congr_nhds hEq).eq_of_nhds
  have hLHS : logDeriv (fun z => riemannZeta (1 - z)) s = -logDeriv riemannZeta (1 - s) := by
    rw [show (fun z => riemannZeta (1 - z)) = riemannZeta ∘ (fun z => 1 - z) from rfl,
      logDeriv_comp (differentiableAt_riemannZeta (by simpa [sub_eq_iff_eq_add] using hs0))
        (by fun_prop)]; simp
  have hcpowLog : logDeriv (fun z => (2 * (π : ℂ)) ^ (-z)) s = -Complex.log (2 * π) := by
    rw [logDeriv_apply, ((hasDerivAt_neg' s).const_cpow (Or.inl h2π)).deriv]; field_simp
  have hcosLog : logDeriv (fun z => Complex.cos (π * z / 2)) s
      = -(π / 2 * Complex.tan (π * s / 2)) := by
    have hinner : HasDerivAt (fun z : ℂ => (π : ℂ) * z / 2) (π / 2) s := by
      simpa using ((hasDerivAt_id s).const_mul (π : ℂ)).div_const 2
    rw [logDeriv_apply, hinner.ccos.deriv, Complex.tan_eq_sin_div_cos]; field_simp
  rw [hLHS] at hlog
  have hdΓ : DifferentiableAt ℂ Gamma s := differentiableAt_Gamma s hsn
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hd2π : DifferentiableAt ℂ (fun z => (2 * (π : ℂ)) ^ (-z)) s :=
    ((hasDerivAt_neg' s).const_cpow (Or.inl h2π)).differentiableAt
  rw [logDeriv_fun_mul s (by simp [hcpow, hΓ, hcos]) hz (by fun_prop) (by fun_prop),
      logDeriv_fun_mul s (by simp [hcpow, hΓ]) hcos (by fun_prop) (by fun_prop),
      logDeriv_fun_mul s (by simp [hcpow]) hΓ (by fun_prop) (by fun_prop),
      logDeriv_fun_mul s two_ne_zero hcpow (by fun_prop) (by fun_prop)] at hlog
  rw [logDeriv_const, hcpowLog, show logDeriv Gamma s = digamma s from rfl, hcosLog] at hlog
  simp only [Pi.zero_apply] at hlog
  linear_combination -hlog

end Solution.ZetaLogDeriv

/-- The node's conclusion, which spells `logDeriv` out as `deriv f / f`. -/
theorem ZetaLogDeriv.v1.challenge_logDeriv_functional_equation :
    ZetaLogDeriv.v1.logDeriv_functional_equation := by
  intro s hsn hs1 hz hcos
  simpa only [logDeriv_apply] using
    Solution.ZetaLogDeriv.logDeriv_riemannZeta_one_sub hsn hs1 hz hcos
