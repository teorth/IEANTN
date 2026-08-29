/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Support

/-!
# Corollary 14

`Eθ` obeys the classical bound with `A = 121.0961`, `B = 3/2`, `C = 2`, `R = 5.5666305`, for all
`x ≥ 2`.

Two ranges. Above `e³⁰` it is Proposition 13 applied to `FKS`'s bound, with the multiplier at most
`6.3376·10⁻⁷` — which is what carries `A` from `121.096` to `121.0961` and no further. Below `e³⁰`
the asymptotic bound is at least `1`, so `BKLNW`'s `Eθ ≤ 1` covers the range outright.

**Proposition 13 arrives as a hypothesis**, because it is now a conclusion of `FKS2.v2` and this
conclusion imports it. Previously it was a lemma in this same solution.

`BKLNW.v1.corollary_5_1` is applied at `b = 30`, inside its range `7 ≤ b ≤ 38 log 10`.
-/

namespace FKS2Sol

open Real IEANTN

theorem corollary_14
    (hprop13 : FKS2.v2.proposition_13)
    (hpsi : FKS.v1.psi_classical_bound)
    (hconv : BKLNW.v1.corollary_5_1)
    (hsmall : BKLNW.v1.theta_error_le_one)
    (hnu : FKS2Numerics.v1.nu_asymp_e30_le)
    (hfloor : FKS2Numerics.v1.theta_asymp_ge_one_below_e30) :
    FKS2.v1.corollary_14 := by
  intro x hx
  by_cases hle : x ≤ exp 30
  · have hf := hfloor x ⟨hx, hle⟩
    simp only [IEANTN.margin, pow_zero, one_mul] at hf
    exact (hsmall x hx hle).trans hf
  · have hgt : exp 30 < x := lt_of_not_ge hle
    have h13 := hprop13 121.096 (3 / 2) 2 5.5666305 (1 + 1.93378e-8) (BKLNW.v1.a₂ 30) (exp 30)
      (by norm_num) (by norm_num) (by norm_num)
      (exp_le_exp.mpr (by norm_num)) (by norm_num) BKLNW_a₂_nonneg
      (fun y hy ↦ (hconv 30 (by norm_num) (by nlinarith [one_le_log_ten]) y hy).le)
      hpsi
    refine (h13 x hgt.le).trans ?_
    have hx1 : (1 : ℝ) < x := lt_trans (by nlinarith [Real.add_one_le_exp (30 : ℝ)]) hgt
    refine admissibleBound_mono_A (by norm_num) hx1 ?_
    rw [nuAsymp_e30_eq]
    have := hnu
    unfold FKS2Numerics.v1.nu_asymp_e30_le at this
    simp only [IEANTN.margin, pow_zero, one_mul] at this
    nlinarith [this]

end FKS2Sol
