/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Port.RS13.Reduction

set_option maxRecDepth 100000

namespace RS5Historical.Theorem13
open Real Chebyshev Finset ArithmeticFunction

/-- All possible proper prime powers below the analytic threshold. Primality
and the generated powers are evaluated by Lean, not trusted external data. -/
@[irreducible] def candidates : Finset ℕ :=
  (((Icc 2 216).filter Nat.Prime).product (Icc 2 15)).image (fun q => q.1 ^ q.2)
    |>.filter (fun n => n ≤ 46656)

theorem mem_candidates_iff {n : ℕ} :
    n ∈ candidates ↔ IsPrimePow n ∧ ¬ Nat.Prime n ∧ n ≤ 46656 := by
  classical
  rw [candidates, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨p, k⟩, hpk, rfl⟩, hn⟩
    obtain ⟨hp, hk⟩ := Finset.mem_product.mp hpk
    have hprime := (Finset.mem_filter.mp hp).2
    have hk := Finset.mem_Icc.mp hk
    refine ⟨(isPrimePow_nat_iff _).2 ⟨p, k, hprime, by omega, rfl⟩, ?_, hn⟩
    exact Nat.Prime.not_prime_pow hk.1
  · rintro ⟨hn, hnp, hbound⟩
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
    have hk2 : 2 ≤ k := by
      by_contra h
      have he : k = 1 := by omega
      simp only [he, pow_one] at hnp
      exact hnp hp
    have hp2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.one_le hk2
    have hp216 : p ≤ 216 := by
      rw [pow_two] at hp2
      nlinarith
    have hk15 : k ≤ 15 := by
      by_contra h
      have he : (2 : ℕ) ^ 16 ≤ p ^ k :=
        (Nat.pow_le_pow_left hp.two_le 16).trans (Nat.pow_le_pow_right hp.one_le (by omega))
      norm_num at he
      omega
    exact ⟨⟨(p,k), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp.two_le, hp216⟩, hp⟩, Finset.mem_Icc.mpr ⟨hk2, hk15⟩⟩, rfl⟩, hbound⟩

theorem candidate_pos {n : ℕ} (hn : n ∈ candidates) : 0 < n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 (mem_candidates_iff.1 hn).1
  exact pow_pos hp.pos _

/-- Endpoint convention is explicit: a jump at n contributes exactly when n≤x. -/
theorem gap_eq_sum_candidates {x : ℝ} (hx : x ≤ 46656) :
    ψ x - θ x = ∑ n ∈ candidates, if (n : ℝ) ≤ x then Real.log (n.minFac : ℝ) else 0 := by
  classical
  rw [psi_sub_theta_eq_sum_not_prime]
  simp_rw [vonMangoldt_apply]
  rw [← sum_filter]
  have he : ((Ioc 0 ⌊x⌋₊).filter (fun n => ¬ Nat.Prime n)).filter IsPrimePow =
      candidates.filter (fun n : ℕ => (n : ℝ) ≤ x) := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_candidates_iff]
    constructor
    · rintro ⟨⟨⟨hn0, hnx⟩, hnp⟩, hn⟩
      have hr : (n : ℝ) ≤ x := (Nat.le_floor_iff' hn0.ne').1 hnx
      refine ⟨⟨hn, hnp, ?_⟩, hr⟩
      exact_mod_cast hr.trans hx
    · rintro ⟨⟨hn, hnp, hN⟩, hnx⟩
      have hmem : n ∈ candidates := mem_candidates_iff.2 ⟨hn, hnp, hN⟩
      exact ⟨⟨⟨candidate_pos hmem, Nat.le_floor hnx⟩, hnp⟩, hn⟩
  rw [he, sum_filter]

/-- Checking the finite jump points suffices for all real x in the finite range. -/
theorem finite_jump_bound {c x : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (hN : x ≤ 46656)
    (hpoints : ∀ n ∈ candidates, ψ (n : ℝ) - θ (n : ℝ) ≤ c * sqrt n) :
    ψ x - θ x ≤ c * sqrt x := by
  classical
  let s := candidates.filter (fun n : ℕ => (n : ℝ) ≤ x)
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hm : m ∈ s := max'_mem s hs
    have hmC := (mem_filter.1 hm).1
    have hmx := (mem_filter.1 hm).2
    have hmN : (m : ℝ) ≤ 46656 := by exact_mod_cast (mem_candidates_iff.1 hmC).2.2
    have he : ψ x - θ x = ψ (m : ℝ) - θ (m : ℝ) := by
      rw [gap_eq_sum_candidates hN, gap_eq_sum_candidates hmN]
      apply sum_congr rfl
      intro n hn
      have hiff : (n : ℝ) ≤ x ↔ (n : ℝ) ≤ m := by
        constructor
        · intro hnx
          exact_mod_cast le_max' s n (mem_filter.2 ⟨hn, hnx⟩)
        · exact fun h => h.trans hmx
      simp only [hiff]
    rw [he]
    exact (hpoints m hmC).trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hmx) hc)
  · have he : ψ x - θ x = 0 := by
      rw [gap_eq_sum_candidates hN]
      apply sum_eq_zero
      intro n hn
      have hnx : ¬ (n : ℝ) ≤ x := by
        intro h
        exact hs ⟨n, mem_filter.2 ⟨hn, h⟩⟩
      simp only [if_neg hnx]
    rw [he]
    positivity

end RS5Historical.Theorem13
