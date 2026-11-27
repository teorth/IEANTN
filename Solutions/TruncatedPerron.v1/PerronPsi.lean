/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Doolan
-/
import IEANTN.Nodes.TruncatedPerron.v1.Conclusions
import PerronDev

/-!
# The truncated Perron formula for `ψ`

`perron_psi_of_general` derives `TruncatedPerron.v1.perron_psi` from
`TruncatedPerron.v1.perron_general` with `aₙ = Λ(n)`, `σ₀ = c = 1 + 1/log x`, and the constant
`C = 400`. Write `ℓ = log x`, so `x^c = e·x`.

Each term `Λ(n) (x/n)^c K(x/n)` of the error is bounded as follows.

* `n = x`: `Λ(x) · c/(πT) ≤ ℓ/T`.
* `n ≤ x/2` or `n ≥ 2x`: `|log(x/n)| ≥ log 2`, and `Λ(n) ≤ log n ≤ 2ℓ n^{1/(2ℓ)}`, so the term is
  at most `4 (xℓ/T) n^{-(1+1/(2ℓ))}`. Summed, using `∑ n^{-p} ≤ 1 + 1/(p-1)`, that is
  `≤ 4 (xℓ/T)(1 + 2ℓ)`.
* `x/2 < n < 2x`, `n ≠ x`: `|log(x/n)| ≥ |x-n|/(2x)`, `(x/n)^c ≤ 8` and `Λ(n) ≤ 2ℓ`, so the term
  is at most `16ℓ · min(1, x/(T|x-n|))`. When `|x-n| < 1` and `Λ(n) ≠ 0`, `n` is a prime power
  other than `x`, so `|x-n| ≥ ⟨x⟩` and the term is at most `16ℓ min(1, x/(T⟨x⟩))`; there are at
  most two such `n`. The others give `16ℓ (x/T) ∑ 1/|x-n| ≤ 16ℓ (x/T) · 3(1 + log 2x)`.

`⟨x⟩ > 0` because every natural number `q ≠ x` has `|x - q| ≥ min(⌊x⌋+1-x, x-⌊x⌋ or 1)`.
-/

open Complex Real MeasureTheory

namespace TruncPerronPsi

open TruncatedPerron.v1 ArithmeticFunction

noncomputable section

/-! ### A p-series bound -/

lemma sum_range_rpow_le {p : ℝ} (hp : 1 < p) (a : ℕ) :
    ∑ i ∈ Finset.range a, ((i : ℝ) + 2) ^ (-p) ≤ 1 / (p - 1) := by
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-p)) (Set.Icc 1 (1 + a)) := by
    intro s hs t _ hst
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hs.1]) hst (by linarith)
  have h : ∑ i ∈ Finset.range a, (fun t : ℝ => t ^ (-p)) (1 + ↑(i + 1)) ≤
      ∫ t in (1 : ℝ)..1 + a, (fun t : ℝ => t ^ (-p)) t := hanti.sum_le_integral
  have e : ∀ i ∈ Finset.range a, (fun t : ℝ => t ^ (-p)) (1 + ↑(i + 1)) = ((i : ℝ) + 2) ^ (-p) := by
    intro i _; simp only []; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl e] at h
  refine h.trans ?_
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + (a : ℝ)) := by
    intro h0
    rcases Set.mem_uIcc.mp h0 with h0 | h0 <;> linarith [h0.1, h0.2, (Nat.cast_nonneg a : (0:ℝ) ≤ a)]
  simp only []
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), Real.one_rpow]
  have hq : 0 < p - 1 := by linarith
  have hb : 0 ≤ ((1 : ℝ) + a) ^ (-(p - 1)) := Real.rpow_nonneg (by positivity) _
  rw [show -p + 1 = -(p - 1) by ring, div_neg, ← neg_div, neg_sub]
  exact (div_le_div_iff_of_pos_right hq).mpr (by linarith)

lemma tsum_rpow_le {p : ℝ} (hp : 1 < p) : ∑' n : ℕ, (n : ℝ) ^ (-p) ≤ 1 + 1 / (p - 1) := by
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) fun n => ?_
  have hmono : ∑ i ∈ Finset.range n, (i : ℝ) ^ (-p) ≤ ∑ i ∈ Finset.range (n + 2), (i : ℝ) ^ (-p) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun i _ _ => Real.rpow_nonneg (Nat.cast_nonneg i) _
  refine hmono.trans ?_
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h := sum_range_rpow_le hp n
  have e : ∀ i ∈ Finset.range n, ((i + 1 + 1 : ℕ) : ℝ) ^ (-p) = ((i : ℝ) + 2) ^ (-p) := by
    intro i _; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl e]
  simp only [zero_add, Nat.cast_one, Real.one_rpow, Nat.cast_zero,
    Real.zero_rpow (by linarith : -p ≠ 0)]
  linarith

/-! ### Elementary inequalities -/

lemma abs_sub_le_mul_abs_log {x n : ℝ} (hx : 0 < x) (hn : 0 < n) :
    |x - n| ≤ max x n * |Real.log (x / n)| := by
  rcases le_total n x with h | h
  · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hx hn)
    have hlog : 0 ≤ Real.log (x / n) := Real.log_nonneg ((one_le_div hn).mpr h)
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg hlog, max_eq_left h]
    rw [inv_div] at h1
    calc x - n = x * (1 - n / x) := by field_simp
      _ ≤ x * Real.log (x / n) := mul_le_mul_of_nonneg_left h1 hx.le
  · have h1 := Real.log_le_sub_one_of_pos (div_pos hx hn)
    have hlog : Real.log (x / n) ≤ 0 :=
      Real.log_nonpos (div_nonneg hx.le hn.le) ((div_le_one hn).mpr h)
    rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos hlog, max_eq_right h]
    calc -(x - n) = n * (1 - x / n) := by field_simp; ring
      _ ≤ n * -Real.log (x / n) := mul_le_mul_of_nonneg_left (by linarith) hn.le

/-! ### The distance `⟨x⟩` to the nearest other prime power -/

/-- `⟨x⟩`, as in the statement of `perron_psi`. -/
def distPP (x : ℝ) : ℝ := sInf {d : ℝ | ∃ q : ℕ, IsPrimePow q ∧ (q : ℝ) ≠ x ∧ d = |x - q|}

lemma dist_lower {x : ℝ} (hx : 0 ≤ x) :
    ∃ d0 > 0, ∀ q : ℕ, (q : ℝ) ≠ x → d0 ≤ |x - q| := by
  obtain ⟨m, hm⟩ : ∃ m, m = ⌊x⌋₊ := ⟨_, rfl⟩
  have hm1 : (m : ℝ) ≤ x := hm ▸ Nat.floor_le hx
  have hm2 : x < m + 1 := hm ▸ Nat.lt_floor_add_one x
  refine ⟨min ((m : ℝ) + 1 - x) (if x = m then 1 else x - m), lt_min (by linarith) ?_, ?_⟩
  · split_ifs with h
    · norm_num
    · exact sub_pos.mpr (lt_of_le_of_ne hm1 (Ne.symm h))
  intro q hq
  rcases lt_trichotomy q m with h | rfl | h
  · have : (q : ℝ) + 1 ≤ m := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · rw [abs_of_nonneg (by linarith), if_neg (Ne.symm hq)]
    exact min_le_right _ _
  · have : (m : ℝ) + 1 ≤ q := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    exact (min_le_left _ _).trans (by linarith)

lemma distPP_pos {x : ℝ} (hx : 0 ≤ x) : 0 < distPP x := by
  obtain ⟨d0, hd0, hd⟩ := dist_lower hx
  have hne : Set.Nonempty {d : ℝ | ∃ q : ℕ, IsPrimePow q ∧ (q : ℝ) ≠ x ∧ d = |x - q|} := by
    by_cases h2 : (2 : ℝ) = x
    · exact ⟨_, 3, Nat.prime_three.isPrimePow, by rw [← h2]; norm_num, rfl⟩
    · exact ⟨_, 2, Nat.prime_two.isPrimePow, by push_cast; exact h2, rfl⟩
  exact lt_of_lt_of_le hd0 (le_csInf hne (by rintro d ⟨q, -, hq, rfl⟩; exact hd q hq))

lemma distPP_le {x : ℝ} {q : ℕ} (hq : IsPrimePow q) (hqx : (q : ℝ) ≠ x) :
    distPP x ≤ |x - q| :=
  csInf_le ⟨0, by rintro d ⟨q, -, -, rfl⟩; exact abs_nonneg _⟩ ⟨q, hq, hqx, rfl⟩

/-! ### The harmonic part -/

lemma sum_range_inv_le (N : ℕ) :
    ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  simp only [harmonic] at h
  push_cast at h
  simpa only [one_div] using h

lemma harmonic_part {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (hN : ⌊x⌋₊ ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (if 1 ≤ |x - n| then 1 / |x - n| else 0) ≤ 3 * (1 + Real.log N) := by
  obtain ⟨m, hm⟩ : ∃ m, m = ⌊x⌋₊ := ⟨_, rfl⟩
  rw [← hm] at hN
  have hm1 : (m : ℝ) ≤ x := hm ▸ Nat.floor_le hx
  have hm2 : x < m + 1 := hm ▸ Nat.lt_floor_add_one x
  let h1 : ℕ → ℝ := fun n => if n < m then 1 / ((m : ℝ) - n) else 0
  let h2 : ℕ → ℝ := fun n => if m < n then 2 / ((n : ℝ) - m) else 0
  have h1nn : ∀ n, 0 ≤ h1 n := by
    intro n; simp only [h1]; split_ifs with h
    · have : (n : ℝ) < m := by exact_mod_cast h
      exact div_nonneg zero_le_one (by linarith)
    · exact le_rfl
  have h2nn : ∀ n, 0 ≤ h2 n := by
    intro n; simp only [h2]; split_ifs with h
    · have : (m : ℝ) < n := by exact_mod_cast h
      exact div_nonneg zero_le_two (by linarith)
    · exact le_rfl
  have hpt : ∀ n ∈ Finset.Icc 1 N, (if 1 ≤ |x - n| then 1 / |x - n| else 0) ≤ h1 n + h2 n := by
    intro n _
    split_ifs with hg
    · rcases lt_trichotomy n m with h | rfl | h
      · have hc : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
        have hh2 : h2 n = 0 := by simp only [h2]; rw [if_neg (by omega)]
        have hh1 : h1 n = 1 / ((m : ℝ) - n) := by simp only [h1]; rw [if_pos h]
        rw [hh1, hh2, add_zero, abs_of_nonneg (by linarith)]
        exact one_div_le_one_div_of_le (by linarith) (by linarith)
      · exfalso
        rw [abs_of_nonneg (by linarith)] at hg
        linarith
      · have hc : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
        have hh1 : h1 n = 0 := by simp only [h1]; rw [if_neg (by omega)]
        have hh2 : h2 n = 2 / ((n : ℝ) - m) := by simp only [h2]; rw [if_pos h]
        have hg' : 1 ≤ (n : ℝ) - x := by rw [abs_of_nonpos (by linarith)] at hg; linarith
        rw [hh1, hh2, zero_add, abs_of_nonpos (by linarith)]
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
    · exact add_nonneg (h1nn n) (h2nn n)
  refine (Finset.sum_le_sum hpt).trans ?_
  have hsub : Finset.Icc 1 N ⊆ Finset.range (N + 1) := by
    intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
    fun n _ _ => add_nonneg (h1nn n) (h2nn n)).trans ?_
  rw [Finset.sum_add_distrib]
  have hH := sum_range_inv_le N
  have hA : ∑ n ∈ Finset.range (N + 1), h1 n ≤ ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m ≤ N + 1)]
    have hz : ∑ n ∈ Finset.Ico m (N + 1), h1 n = 0 :=
      Finset.sum_eq_zero fun n hn => by
        simp only [h1]; rw [if_neg (by rw [Finset.mem_Ico] at hn; omega)]
    rw [hz, add_zero]
    have he : ∑ n ∈ Finset.range m, h1 n = ∑ i ∈ Finset.range m, 1 / ((i : ℝ) + 1) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [h1]
      rw [if_pos (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring_nf
    rw [he]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun i _ _ => by positivity
  have hB : ∑ n ∈ Finset.range (N + 1), h2 n ≤ 2 * ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ N + 1)]
    have hz : ∑ n ∈ Finset.range (m + 1), h2 n = 0 :=
      Finset.sum_eq_zero fun n hn => by
        simp only [h2]; rw [if_neg (by rw [Finset.mem_range] at hn; omega)]
    rw [hz, zero_add, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    have he : ∀ k ∈ Finset.range (N + 1 - (m + 1)), h2 (m + 1 + k) = 2 * (1 / ((k : ℝ) + 1)) := by
      intro k _
      simp only [h2]
      rw [if_pos (by omega)]
      push_cast; ring_nf
    rw [Finset.sum_congr rfl he]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      fun i _ _ => by positivity
  linarith

/-! ### `ψ₀` as the weighted sum -/

lemma psi0_eq {x : ℝ} (hx : 1 ≤ x) :
    (((Chebyshev.psi x - (if (⌊x⌋₊ : ℝ) = x then vonMangoldt ⌊x⌋₊ / 2 else 0) : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * (vonMangoldt n : ℂ) := by
  have hpsi : Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n := by
    rw [Chebyshev.psi]; congr 1
  have hm1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  rw [hpsi]
  by_cases h : (⌊x⌋₊ : ℝ) = x
  · rw [if_pos h]
    have hm : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
    have hmem : ⌊x⌋₊ ∈ Finset.Icc 1 ⌊x⌋₊ := Finset.mem_Icc.mpr ⟨hm, le_rfl⟩
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem, if_pos h]
    have hrest : ∀ n ∈ (Finset.Icc 1 ⌊x⌋₊).erase ⌊x⌋₊,
        (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * (vonMangoldt n : ℂ) = (vonMangoldt n : ℂ) := by
      intro n hn
      rw [if_neg, one_mul]
      rw [← h]; exact_mod_cast Finset.ne_of_mem_erase hn
    rw [Finset.sum_congr rfl hrest]
    push_cast; ring
  · rw [if_neg h, sub_zero]
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_neg, one_mul]
    intro hnx
    apply h
    have h1 : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    linarith

/-! ### The termwise bound -/

/-- The bound for the `n`-th error term: a far part `U n` plus a near part supported on
`1 ≤ n ≤ ⌊2x⌋`. -/
lemma term_le {x T : ℝ} (hx : 2 ≤ x) (hT : 1 ≤ T) (n : ℕ) :
    ‖(vonMangoldt n : ℂ)‖ * (x / n) ^ (1 + 1 / Real.log x) *
        (if (n : ℝ) = x then (1 + 1 / Real.log x) / (π * T)
          else min 1 (1 / (π * T * |Real.log (x / n)|))) ≤
      4 * (x * Real.log x / T) * (n : ℝ) ^ (-(1 + 1 / Real.log x / 2)) +
      (if n ∈ Finset.Icc 1 ⌊2 * x⌋₊ then
        16 * Real.log x / T + 16 * Real.log x * (if |x - n| < 1 then min 1 (x / (T * distPP x)) else 0) +
          16 * Real.log x * (x / T) * (if 1 ≤ |x - n| then 1 / |x - n| else 0)
        else 0) := by
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set ℓ := Real.log x with hℓdef
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hx
  have hl2 := Real.log_two_gt_d9
  have hℓ0 : 0 < ℓ := by linarith
  have hℓh : 1 / 2 < ℓ := by linarith
  have hinv : 1 / ℓ < 2 := by rw [div_lt_iff₀ hℓ0]; linarith
  set c := 1 + 1 / ℓ with hc
  have hc0 : 0 ≤ c := by positivity
  have hc3 : c ≤ 3 := by linarith
  have hπ := Real.pi_gt_three
  have hD := distPP_pos hx0.le
  have hM0 : 0 ≤ min 1 (x / (T * distPP x)) :=
    le_min zero_le_one (div_nonneg hx0.le (mul_nonneg hT0.le hD.le))
  have hU0 : 0 ≤ 4 * (x * ℓ / T) * (n : ℝ) ^ (-(1 + 1 / ℓ / 2)) := by positivity
  have hV0 : 0 ≤ (if n ∈ Finset.Icc 1 ⌊2 * x⌋₊ then
        16 * ℓ / T + 16 * ℓ * (if |x - n| < 1 then min 1 (x / (T * distPP x)) else 0) +
          16 * ℓ * (x / T) * (if 1 ≤ |x - n| then 1 / |x - n| else 0)
        else 0) := by
    split_ifs
    all_goals first
      | exact le_rfl
      | exact add_nonneg (add_nonneg (by positivity) (mul_nonneg (by positivity) hM0))
          (mul_nonneg (by positivity) (by positivity))
      | exact add_nonneg (add_nonneg (by positivity) (mul_nonneg (by positivity) hM0))
          (mul_nonneg (by positivity) le_rfl)
      | exact add_nonneg (add_nonneg (by positivity) (mul_nonneg (by positivity) le_rfl))
          (mul_nonneg (by positivity) (by positivity))
      | exact add_nonneg (add_nonneg (by positivity) (mul_nonneg (by positivity) le_rfl))
          (mul_nonneg (by positivity) le_rfl)
  rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  -- trivial terms
  by_cases hΛ : vonMangoldt n = 0
  · rw [hΛ, zero_mul, zero_mul]; exact add_nonneg hU0 hV0
  have hpp : IsPrimePow n := vonMangoldt_ne_zero_iff.mp hΛ
  have hn : n ≠ 0 := fun h => by rw [h] at hpp; exact not_isPrimePow_zero hpp
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hΛn : vonMangoldt n ≤ Real.log n := vonMangoldt_le_log
  have hΛ0 : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
  have hmem_of : (n : ℝ) ≤ 2 * x → n ∈ Finset.Icc 1 ⌊2 * x⌋₊ := fun h =>
    Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hn, Nat.le_floor h⟩
  by_cases hnx : (n : ℝ) = x
  · -- the term `n = x`
    rw [if_pos hnx, if_pos (hmem_of (by linarith))]
    have hy : x / n = 1 := by rw [hnx, div_self hx0.ne']
    rw [hy, Real.one_rpow, mul_one]
    have hlog : vonMangoldt n ≤ ℓ := by rw [hℓdef, ← hnx]; exact hΛn
    have h1 : c / (π * T) ≤ 1 / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]; nlinarith
    have h2 : vonMangoldt n * (c / (π * T)) ≤ ℓ * (1 / T) :=
      mul_le_mul hlog h1 (by positivity) hℓ0.le
    have h3 : 0 ≤ 16 * ℓ * (if |x - n| < 1 then min 1 (x / (T * distPP x)) else 0) := by
      split_ifs; exact mul_nonneg (by positivity) hM0; simp
    have h4 : 0 ≤ 16 * ℓ * (x / T) * (if 1 ≤ |x - n| then 1 / |x - n| else 0) := by
      split_ifs; positivity; simp
    have h5 : ℓ * (1 / T) ≤ 16 * ℓ / T := by
      rw [mul_one_div]; exact div_le_div_of_nonneg_right (by linarith) hT0.le
    linarith
  rw [if_neg hnx]
  have hd : 0 < |x - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hnx))
  have hK0 : 0 ≤ min 1 (1 / (π * T * |Real.log (x / n)|)) :=
    le_min zero_le_one (by positivity)
  by_cases hnear : x / 2 < n ∧ (n : ℝ) < 2 * x
  · -- `n` near `x`
    obtain ⟨hn1, hn2⟩ := hnear
    rw [if_pos (hmem_of hn2.le)]
    have hlogn : vonMangoldt n ≤ 2 * ℓ := by
      calc vonMangoldt n ≤ Real.log n := hΛn
        _ ≤ Real.log (2 * x) := Real.log_le_log hnpos hn2.le
        _ = Real.log 2 + ℓ := Real.log_mul (by norm_num) hx0.ne'
        _ ≤ 2 * ℓ := by linarith
    have h8 : (x / n) ^ c ≤ 8 := by
      have hxn : x / n ≤ 2 := by rw [div_le_iff₀ hnpos]; linarith
      calc (x / n) ^ c ≤ (2 : ℝ) ^ c := Real.rpow_le_rpow (div_nonneg hx0.le hnpos.le) hxn hc0
        _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc3
        _ = 8 := by norm_num
    have hlogabs := abs_sub_le_mul_abs_log hx0 hnpos
    have hmax : max x n ≤ 2 * x := max_le (by linarith) hn2.le
    have hl : 0 < |Real.log (x / n)| := by
      rcases (abs_nonneg (Real.log (x / n))).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hlogabs; linarith
    have hK : min 1 (1 / (π * T * |Real.log (x / n)|)) ≤ min 1 (x / (T * |x - n|)) := by
      refine min_le_min_left 1 ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : |x - n| ≤ 2 * x * |Real.log (x / n)| :=
        hlogabs.trans (mul_le_mul_of_nonneg_right hmax (abs_nonneg _))
      nlinarith [mul_le_mul_of_nonneg_left h2 hT0.le, mul_pos (mul_pos hx0 hT0) hl]
    have hmain : vonMangoldt n * (x / n) ^ c * min 1 (1 / (π * T * |Real.log (x / n)|)) ≤
        16 * ℓ * min 1 (x / (T * |x - n|)) := by
      calc _ ≤ (2 * ℓ) * 8 * min 1 (x / (T * |x - n|)) :=
            mul_le_mul (mul_le_mul hlogn h8 (Real.rpow_nonneg (div_nonneg hx0.le hnpos.le) _)
              (by linarith)) hK hK0 (by linarith)
        _ = 16 * ℓ * min 1 (x / (T * |x - n|)) := by ring
    have hV1 : 0 ≤ 16 * ℓ / T := by positivity
    by_cases hd1 : |x - n| < 1
    · rw [if_pos hd1, if_neg (not_le.mpr hd1), mul_zero, add_zero]
      have hDle := distPP_le hpp hnx
      have hm : min 1 (x / (T * |x - n|)) ≤ min 1 (x / (T * distPP x)) :=
        min_le_min_left 1 (div_le_div_of_nonneg_left hx0.le (by positivity)
          (mul_le_mul_of_nonneg_left hDle hT0.le))
      have := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ 16 * ℓ)
      linarith
    · rw [if_neg hd1, if_pos (not_lt.mp hd1), mul_zero, add_zero]
      have hm : min 1 (x / (T * |x - n|)) ≤ x / T * (1 / |x - n|) := by
        refine (min_le_right _ _).trans (le_of_eq ?_)
        field_simp
      have := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ 16 * ℓ)
      have e : 16 * ℓ * (x / T * (1 / |x - n|)) = 16 * ℓ * (x / T) * (1 / |x - n|) := by ring
      linarith
  · -- `n` far from `x`
    rw [not_and_or, not_lt, not_lt] at hnear
    have hlog2 : Real.log 2 ≤ |Real.log (x / n)| := by
      rcases hnear with h | h
      · have h2 : 2 ≤ x / n := by rw [le_div_iff₀ hnpos]; linarith
        rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
        exact Real.log_le_log (by norm_num) h2
      · have h2 : x / n ≤ 1 / 2 := by rw [div_le_iff₀ hnpos]; linarith
        have hneg : Real.log (x / n) ≤ -Real.log 2 := by
          calc Real.log (x / n) ≤ Real.log (1 / 2) := Real.log_le_log (div_pos hx0 hnpos) h2
            _ = -Real.log 2 := by rw [one_div, Real.log_inv]
        rw [abs_of_neg (by linarith)]; linarith
    have hK : min 1 (1 / (π * T * |Real.log (x / n)|)) ≤ 1 / (π * T * Real.log 2) :=
      (min_le_right _ _).trans (one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left hlog2 (by positivity)))
    set ε := 1 / ℓ / 2 with hε
    have hε0 : 0 < ε := by positivity
    have hΛ' : vonMangoldt n ≤ (n : ℝ) ^ ε / ε := hΛn.trans (Real.log_le_rpow_div hnpos.le hε0)
    have hx1 : x ^ (1 / ℓ) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hx0]; congr 1; show ℓ * (1 / ℓ) = 1; field_simp
    have hxc : (x / n) ^ c = x * Real.exp 1 / (n : ℝ) ^ c := by
      rw [Real.div_rpow hx0.le hnpos.le]; congr 1; rw [hc, Real.rpow_add hx0, Real.rpow_one, hx1]
    have hnc : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hnpos c
    have e2 : (n : ℝ) ^ (-(1 + ε)) = (n : ℝ) ^ ε / (n : ℝ) ^ c := by
      rw [← Real.rpow_sub hnpos]; congr 1; rw [hc, hε]; ring
    have hcoef : 2 * Real.exp 1 / (π * Real.log 2) ≤ 4 := by
      have := mul_le_mul hπ.le hl2.le (by norm_num) Real.pi_pos.le
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.exp_one_lt_d9]
    have hℓne : ℓ ≠ 0 := hℓ0.ne'
    have hTne : T ≠ 0 := hT0.ne'
    have hπne : π ≠ 0 := Real.pi_pos.ne'
    have hl2ne : Real.log 2 ≠ 0 := by positivity
    have hncne : (n : ℝ) ^ c ≠ 0 := hnc.ne'
    calc vonMangoldt n * (x / n) ^ c * min 1 (1 / (π * T * |Real.log (x / n)|))
        ≤ ((n : ℝ) ^ ε / ε) * (x * Real.exp 1 / (n : ℝ) ^ c) * (1 / (π * T * Real.log 2)) := by
          rw [hxc]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hΛ' (by positivity)) hK hK0 (by positivity)
      _ = (2 * Real.exp 1 / (π * Real.log 2)) * (x * ℓ / T) * ((n : ℝ) ^ ε / (n : ℝ) ^ c) := by
          rw [hε]; field_simp
      _ ≤ 4 * (x * ℓ / T) * ((n : ℝ) ^ ε / (n : ℝ) ^ c) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)
      _ = 4 * (x * ℓ / T) * (n : ℝ) ^ (-(1 + ε)) := by rw [e2]
      _ ≤ _ := le_add_of_nonneg_right hV0

/-! ### Summing the bound -/

lemma rhs_bound {x T : ℝ} (hx : 2 ≤ x) (hT : 1 ≤ T) :
    ∑' n : ℕ, ‖(vonMangoldt n : ℂ)‖ * (x / n) ^ (1 + 1 / Real.log x) *
        (if (n : ℝ) = x then (1 + 1 / Real.log x) / (π * T)
          else min 1 (1 / (π * T * |Real.log (x / n)|))) ≤
      400 * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T * distPP x))) := by
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have hfUV := term_le hx hT
  set ℓ := Real.log x with hℓdef
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) hx
  have hl2 := Real.log_two_gt_d9
  have hℓ0 : 0 < ℓ := by linarith
  have hD := distPP_pos hx0.le
  set M := min 1 (x / (T * distPP x)) with hMdef
  have hM0 : 0 ≤ M := le_min zero_le_one (div_nonneg hx0.le (mul_nonneg hT0.le hD.le))
  set N := ⌊2 * x⌋₊ with hNdef
  set f : ℕ → ℝ := fun n => ‖(vonMangoldt n : ℂ)‖ * (x / n) ^ (1 + 1 / ℓ) *
        (if (n : ℝ) = x then (1 + 1 / ℓ) / (π * T)
          else min 1 (1 / (π * T * |Real.log (x / n)|))) with hfdef
  set U : ℕ → ℝ := fun n => 4 * (x * ℓ / T) * (n : ℝ) ^ (-(1 + 1 / ℓ / 2)) with hUdef
  set V : ℕ → ℝ := fun n => if n ∈ Finset.Icc 1 N then
        16 * ℓ / T + 16 * ℓ * (if |x - n| < 1 then M else 0) +
          16 * ℓ * (x / T) * (if 1 ≤ |x - n| then 1 / |x - n| else 0) else 0 with hVdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [f]
    refine mul_nonneg (mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (div_nonneg hx0.le (Nat.cast_nonneg n)) _)) ?_
    split_ifs
    · positivity
    · exact le_min zero_le_one (by positivity)
  have hp : 1 < 1 + 1 / ℓ / 2 := by have : 0 < 1 / ℓ / 2 := by positivity
                                    linarith
  have hUs : Summable U := (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have hVs : Summable V := summable_of_ne_finset_zero (s := Finset.Icc 1 N) fun n hn => if_neg hn
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hfUV (hUs.add hVs)
  have h1 : ∑' n, f n ≤ ∑' n, U n + ∑' n, V n := by
    rw [← hUs.tsum_add hVs]; exact hfs.tsum_le_tsum hfUV (hUs.add hVs)
  have hU : ∑' n, U n ≤ 4 * (x * ℓ / T) * (1 + 2 * ℓ) := by
    simp only [U]
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ((tsum_rpow_le hp).trans (le_of_eq ?_)) (by positivity)
    field_simp
    ring
  have hV : ∑' n, V n = ∑ n ∈ Finset.Icc 1 N, (16 * ℓ / T + 16 * ℓ * (if |x - n| < 1 then M else 0) +
      16 * ℓ * (x / T) * (if 1 ≤ |x - n| then 1 / |x - n| else 0)) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 N) fun n hn => if_neg hn]
    exact Finset.sum_congr rfl fun n hn => if_pos hn
  have hN1 : (N : ℝ) ≤ 2 * x := Nat.floor_le (by linarith)
  have hN0 : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
  have hcard : ∑ _n ∈ Finset.Icc 1 N, (16 * ℓ / T) = N * (16 * ℓ / T) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hnear : ∑ n ∈ Finset.Icc 1 N, (if |x - n| < 1 then M else 0) ≤ 2 * M := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsub : (Finset.Icc 1 N).filter (fun n : ℕ => |x - n| < 1) ⊆ {⌊x⌋₊, ⌊x⌋₊ + 1} := by
      intro n hn
      rw [Finset.mem_filter, abs_lt] at hn
      have a1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
      have a2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
      have b1 : ⌊x⌋₊ < n + 1 := by
        have : (⌊x⌋₊ : ℝ) < n + 1 := by linarith [hn.2.1]
        exact_mod_cast this
      have b2 : n < ⌊x⌋₊ + 2 := by
        have : (n : ℝ) < ⌊x⌋₊ + 2 := by linarith [hn.2.2]
        exact_mod_cast this
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hc : (((Finset.Icc 1 N).filter (fun n : ℕ => |x - n| < 1)).card : ℝ) ≤ 2 := by
      have : ((Finset.Icc 1 N).filter (fun n : ℕ => |x - n| < 1)).card ≤ 2 :=
        (Finset.card_le_card hsub).trans Finset.card_le_two
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hc hM0
  have hharm := harmonic_part hx0.le N (Nat.floor_mono (by linarith : x ≤ 2 * x))
  have hlogN : Real.log N ≤ 2 * ℓ := by
    calc Real.log N ≤ Real.log (2 * x) := Real.log_le_log (by exact_mod_cast hN0) hN1
      _ = Real.log 2 + ℓ := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ 2 * ℓ := by linarith
  have h3 : ∑ n ∈ Finset.Icc 1 N, (if 1 ≤ |x - n| then 1 / |x - n| else 0) ≤ 3 * (1 + 2 * ℓ) :=
    hharm.trans (by linarith)
  have hVb : ∑' n, V n ≤ N * (16 * ℓ / T) + 16 * ℓ * (2 * M) +
      16 * ℓ * (x / T) * (3 * (1 + 2 * ℓ)) := by
    rw [hV, Finset.sum_add_distrib, Finset.sum_add_distrib, hcard, ← Finset.mul_sum,
      ← Finset.mul_sum]
    exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnear (by positivity)))
      (mul_le_mul_of_nonneg_left h3 (by positivity))
  obtain ⟨P, hP⟩ : ∃ P, P = x * ℓ / T := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hP ▸ by positivity
  have hNb : (N : ℝ) * (16 * ℓ / T) ≤ 32 * P := by
    calc _ ≤ 2 * x * (16 * ℓ / T) := mul_le_mul_of_nonneg_right hN1 (by positivity)
      _ = 32 * P := by rw [hP]; ring
  have e1 : x * ℓ ^ 2 / T = P * ℓ := by rw [hP]; ring
  have e2 : 16 * ℓ * (x / T) = 16 * P := by rw [hP]; ring
  rw [← hP] at hU
  rw [e2] at hVb
  show ∑' n, f n ≤ _
  rw [e1]
  have hP2 : P ≤ 2 * P * ℓ := by nlinarith
  nlinarith [mul_nonneg hℓ0.le hM0, mul_nonneg hP0 hℓ0.le]

/-! ### The formula -/

theorem perron_psi_of_general (hG : perron_general) : perron_psi := by
  refine ⟨400, fun x T hx hT => ?_⟩
  have hx0 : 0 < x := by linarith
  have hℓ0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hc1 : (1 : ℝ) < 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := by positivity
    linarith
  have habs : LSeries.abscissaOfAbsConv (fun n ↦ (vonMangoldt n : ℂ)) <
      ((1 + 1 / Real.log x : ℝ) : EReal) := by
    refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => LSeriesSummable_vonMangoldt (by simpa using hy)) ?_
    exact_mod_cast hc1
  have h := hG (fun n ↦ (vonMangoldt n : ℂ)) (1 + 1 / Real.log x) x T (by linarith) habs hx0
    (by linarith)
  rw [psi0_eq (by linarith)]
  exact h.trans (rhs_bound hx hT)

end

end TruncPerronPsi
