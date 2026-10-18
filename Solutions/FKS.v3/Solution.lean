/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcos Adriano
-/
import IEANTN.Bridges.FKS.ClassicalToAllX
import IEANTN.Nodes.BKLNW.v1.Conclusions
import IEANTN.Nodes.FKS.v3.Conclusions
import IEANTN.Nodes.FKSNumerics.v1.Conclusions

/-!
# Solution: `FKS.v3`

Proves the same declarations `Challenge.lean` states. Do **not** import the challenge module --
Comparator compares two modules declaring the same names, so importing it would collide.

The classical bound `Eψ x ≤ 121.096 (log x / R)^{3/2} exp(−2 √(log x / R))`, `R = 5.5666305`, for
`x ≥ 2`, assembled from four ranges:

* `[2, e⁴⁰]`: Mathlib's Chebyshev bound gives `Eψ x ≤ 2` (`Eψ_le_two`), and the right-hand side
  stays above `2` (`two_le_admissibleBound` up to `e³⁰`, one more piece to `e⁴⁰`);
* `[e⁴⁰, e²¹⁰⁰]`: the rows `(40, 1.93378e-8)` and `(1000, 1.94751e-12)` of `BKLNW.v1.table8`, with
  the right-hand side bounded below piecewise in `s = √(log x / R)`, since `exp 1 < 2.7182818286`;
  the tightest piece clears `1.94751e-12` by a factor of 2.9;
* `[e²¹⁰⁰, e²⁰⁰⁰⁰⁰]`: `FKSNumerics.v1.psi_classical_mid_range`, at `margin 0`;
* `[e²⁰⁰⁰⁰⁰, ∞)`: `FKSNumerics.v1.psi_classical_above_e200000`, at `margin 0`, and
  `121.0360 ≤ 121.096`.

The all-`x` bound then follows by `IEANTN.Bridges.FKS.admissibleBound_lt_all_x`, the rescaling the
paper's proof of Lemma 5.3 performs. The first two ranges are the proof posted on issue #52 as
`ClassicalUpToE2100.lean`, which Lemma 5.2 of the paper would have covered and cannot, being false
as printed near `x = 2`.
-/

namespace FKSv3Assembly

open IEANTN IEANTN.Bridges.FKS Real

/-- One piece: if `a² ≤ log x / R ≤ (k/2)²`, the classical right-hand side is at least
`A a³ / 2.7182818286ᵏ`. -/
lemma admissibleBound_ge_piece {A x a : ℝ} {k : ℕ} (hA : 0 ≤ A) (hx : 1 < x) (ha : 0 ≤ a)
    (has : a ^ 2 ≤ log x / 5.5666305) (hsk : log x / 5.5666305 ≤ ((k : ℝ) / 2) ^ 2) :
    A * a ^ 3 / 2.7182818286 ^ k ≤ admissibleBound A (3 / 2) 2 5.5666305 x := by
  have ht0 : 0 ≤ log x / 5.5666305 := div_nonneg (log_pos hx).le (by norm_num)
  unfold admissibleBound
  set t := log x / 5.5666305 with ht
  set s := t ^ ((1 : ℝ) / 2) with hs
  have hs0 : 0 ≤ s := rpow_nonneg ht0 _
  have hs2 : s ^ 2 = t := by
    rw [hs, ← rpow_natCast, ← rpow_mul ht0]
    norm_num
  have ht32 : t ^ ((3 : ℝ) / 2) = s ^ 3 := by
    rw [hs, ← rpow_natCast, ← rpow_mul ht0]
    norm_num
  rw [ht32]
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
  have has' : a ≤ s := by nlinarith
  have hsk' : 2 * s ≤ k := by nlinarith
  have h1 : a ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ ha has' 3
  have h2 : exp (-(k : ℝ)) ≤ exp (-2 * s) := exp_le_exp.mpr (by linarith)
  have h3 : 1 / 2.7182818286 ^ k ≤ exp (-(k : ℝ)) := by
    rw [exp_neg, ← exp_one_pow, one_div]
    exact inv_anti₀ (pow_pos (exp_pos 1) k) (pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le k)
  calc A * a ^ 3 / 2.7182818286 ^ k = A * a ^ 3 * (1 / 2.7182818286 ^ k) := by ring
    _ ≤ A * s ^ 3 * exp (-2 * s) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) (h3.trans h2) (by positivity)
          (mul_nonneg hA (pow_nonneg hs0 3))

/-- The classical right-hand side stays above `2` on `[2, e⁴⁰]`. -/
lemma two_le_admissibleBound_e40 {x : ℝ} (hx : 2 ≤ x) (hx40 : x ≤ exp 40) :
    2 ≤ admissibleBound 121.096 (3 / 2) 2 5.5666305 x := by
  rcases le_or_gt x (exp 30) with h30 | h30
  · exact two_le_admissibleBound hx h30
  have hx1 : 1 < x := by linarith
  have hl30 : 30 < log x := by
    have := log_lt_log (exp_pos 30) h30
    rwa [log_exp] at this
  have hl40 : log x ≤ 40 := by
    have := log_le_log (by linarith) hx40
    rwa [log_exp] at this
  refine le_trans ?_ (admissibleBound_ge_piece (a := 2.32) (k := 6) (by norm_num) hx1
    (by norm_num) ?_ ?_)
  · norm_num
  · rw [le_div_iff₀ (by norm_num)]
    norm_num
    linarith
  · rw [div_le_iff₀ (by norm_num)]
    norm_num
    linarith

/-- **The classical bound on `[2, e²¹⁰⁰]`**, from Mathlib and the rows `b = 40` and `b = 1000` of
`BKLNW.v1.table8`. -/
theorem classical_bound_two_to_e2100 (h : BKLNW.v1.table8_psi_bound_above) :
    ∀ x : ℝ, 2 ≤ x → x ≤ exp 2100 → Eψ x ≤ admissibleBound 121.096 (3 / 2) 2 5.5666305 x := by
  intro x hx hx2100
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  rcases le_or_gt x (exp 40) with h40 | h40
  · exact (Eψ_le_two hx).trans (two_le_admissibleBound_e40 hx h40)
  have hl40 : 40 < log x := by
    have := log_lt_log (exp_pos 40) h40
    rwa [log_exp] at this
  have hl2100 : log x ≤ 2100 := by
    have := log_le_log hx0 hx2100
    rwa [log_exp] at this
  have hx25000 : x ≤ exp 25000 := hx2100.trans (exp_le_exp.mpr (by norm_num))
  -- a row `(b, ε)` of Table 8 with `e^b ≤ x` gives `Eψ x ≤ ε`
  have row : ∀ (b : ℕ) (ε : ℝ), (b, ε) ∈ BKLNW.v1.table8 → exp (b : ℝ) ≤ x → Eψ x ≤ ε := by
    intro b ε hmem hb
    have hrow := h (b, ε) hmem x hb hx25000
    unfold Eψ
    rw [div_le_iff₀ hx0]
    exact hrow
  rcases le_or_gt x (exp 1000) with h1000 | h1000
  · -- `[e⁴⁰, e¹⁰⁰⁰]`: the row `(40, 1.93378e-8)`
    have hl1000 : log x ≤ 1000 := by
      have := log_le_log hx0 h1000
      rwa [log_exp] at this
    refine (row 40 1.93378e-8 (by simp [BKLNW.v1.table8]) (by exact_mod_cast h40.le)).trans ?_
    rcases le_or_gt (log x / 5.5666305) 100 with h10 | h10
    · refine le_trans ?_ (admissibleBound_ge_piece (a := 2.5) (k := 20) (by norm_num) hx1
        (by norm_num) ?_ ?_)
      · norm_num
      · rw [le_div_iff₀ (by norm_num)]
        norm_num
        linarith
      · rw [show (((20 : ℕ) : ℝ) / 2) ^ 2 = 100 by norm_num]
        exact h10
    · refine le_trans ?_ (admissibleBound_ge_piece (a := 10) (k := 27) (by norm_num) hx1
        (by norm_num) ?_ ?_)
      · norm_num
      · rw [show (10 : ℝ) ^ 2 = 100 by norm_num]
        exact h10.le
      · rw [div_le_iff₀ (by norm_num)]
        norm_num
        linarith
  · -- `[e¹⁰⁰⁰, e²¹⁰⁰]`: the row `(1000, 1.94751e-12)`
    have hl1000 : 1000 < log x := by
      have := log_lt_log (exp_pos 1000) h1000
      rwa [log_exp] at this
    refine (row 1000 1.94751e-12 (by simp [BKLNW.v1.table8])
      (by exact_mod_cast h1000.le)).trans ?_
    rcases le_or_gt (log x / 5.5666305) 256 with h16 | h16
    · refine le_trans ?_ (admissibleBound_ge_piece (a := 13.4) (k := 32) (by norm_num) hx1
        (by norm_num) ?_ ?_)
      · norm_num
      · rw [le_div_iff₀ (by norm_num)]
        norm_num
        linarith
      · rw [show (((32 : ℕ) : ℝ) / 2) ^ 2 = 256 by norm_num]
        exact h16
    · refine le_trans ?_ (admissibleBound_ge_piece (a := 16) (k := 39) (by norm_num) hx1
        (by norm_num) ?_ ?_)
      · norm_num
      · rw [show (16 : ℝ) ^ 2 = 256 by norm_num]
        exact h16.le
      · rw [div_le_iff₀ (by norm_num)]
        norm_num
        linarith

/-- For `x > 1` the classical right-hand side is monotone in `A`: the other two factors are
non-negative. (Below `x = 1` the `rpow` of a negative base would make this false.) -/
lemma admissibleBound_le_of_le {A A' x : ℝ} (hAA : A ≤ A') (hx : 1 < x) :
    admissibleBound A (3 / 2) 2 5.5666305 x ≤ admissibleBound A' (3 / 2) 2 5.5666305 x := by
  unfold admissibleBound
  have ht : 0 ≤ log x / 5.5666305 := div_nonneg (log_pos hx).le (by norm_num)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA (rpow_nonneg ht _))
    (exp_pos _).le

/-- **The assembly**: the classical bound from `x₀ = 2`, from Table 8 and the two `FKSNumerics`
claims. Both numerical claims are consumed at `margin 0`. -/
theorem classical_bound (hB : BKLNW.v1.table8_psi_bound_above)
    (hmid : FKSNumerics.v1.psi_classical_mid_range)
    (htop : FKSNumerics.v1.psi_classical_above_e200000) :
    HasClassicalBound Eψ 121.096 (3 / 2) 2 5.5666305 2 := by
  intro x hx
  rcases le_or_gt x (exp 2100) with h1 | h1
  · exact classical_bound_two_to_e2100 hB x hx h1
  rcases le_or_gt x (exp 200000) with h2 | h2
  · simpa [margin] using hmid x ⟨h1.le, h2⟩
  · have h := htop x h2.le
    simp only [margin, pow_zero, one_mul] at h
    have hx1 : 1 < x := by
      have := add_one_le_exp (200000 : ℝ)
      linarith
    exact h.trans (admissibleBound_le_of_le (by norm_num) hx1)

end FKSv3Assembly

theorem FKS.v3.challenge_psi_classical_bound
    (bklnw_v1_table8_psi_bound_above : BKLNW.v1.table8_psi_bound_above)
    (fksnumerics_v1_psi_classical_mid_range : FKSNumerics.v1.psi_classical_mid_range)
    (fksnumerics_v1_psi_classical_above_e200000 : FKSNumerics.v1.psi_classical_above_e200000) :
    FKS.v3.psi_classical_bound :=
  FKSv3Assembly.classical_bound bklnw_v1_table8_psi_bound_above
    fksnumerics_v1_psi_classical_mid_range fksnumerics_v1_psi_classical_above_e200000

theorem FKS.v3.challenge_psi_bound_all_x
    (bklnw_v1_table8_psi_bound_above : BKLNW.v1.table8_psi_bound_above)
    (fksnumerics_v1_psi_classical_mid_range : FKSNumerics.v1.psi_classical_mid_range)
    (fksnumerics_v1_psi_classical_above_e200000 : FKSNumerics.v1.psi_classical_above_e200000) :
    FKS.v3.psi_bound_all_x := by
  intro x hx
  have h := FKS.v3.challenge_psi_classical_bound bklnw_v1_table8_psi_bound_above
    fksnumerics_v1_psi_classical_mid_range fksnumerics_v1_psi_classical_above_e200000 x hx.le
  exact h.trans_lt (IEANTN.Bridges.FKS.admissibleBound_lt_all_x (by linarith))
