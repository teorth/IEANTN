/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Shifts

/-!
# The two bounds the criterion combines

`sq_pi_lt` squares the upper estimate for `π(x)`; `ex_pi_gt` applies the lower estimate at `x/e`
and rescales. Their difference is a single quotient over `(log x)^7`, and the criterion's
hypothesis is exactly what makes that quotient negative.

`ex_pi_gt` splits on the sign of `m`, and that split is the erratum: the `nonneg` branch is the
paper's own argument, and the `neg` branch — the one every application actually needs — uses
`DudekPlattSol.shift_m_lower_of_nonpos` in place of the truncation the paper reuses there.

The mathematics is `PrimeNumberTheoremAnd`'s, from its `Ramanujan` namespace. Only the vocabulary
differs: its `pi` is this repository's `IEANTN.primeCounting` — the same definition,
`Nat.primeCounting ⌊x⌋₊` — and its `ε`, `ε'`, `εneg`, `εlower` are this node's `εUpper`, `εPos`,
`εNeg`, `εLower`.
-/

open Real IEANTN DudekPlatt.v3

namespace DudekPlattSol

theorem sq_pi_lt (M_a x_a : ℝ) (hupper : ∀ x > x_a, primeCounting x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) :
    ∀ x > x_a, primeCounting x ^ 2 < x ^ 2 * (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 64 / log x ^ 6 + εUpper M_a x / log x ^ 7) := by
  intro x hx
  have sq_algebra (M l : ℝ) : ((Nat.factorial 0 : ℝ) / l ^ 1 + (Nat.factorial 1 : ℝ) / l ^ 2 + (Nat.factorial 2 : ℝ) / l ^ 3 + (Nat.factorial 3 : ℝ) / l ^ 4 + (Nat.factorial 4 : ℝ) / l ^ 5 + M / l ^ 6) ^ 2
    = 1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 64 / l ^ 6 + (72 + 2 * M + (2 * M + 132) / l + (4 * M + 288) / l ^ 2 + (12 * M + 576) / l ^ 3 + (48 * M) / l ^ 4 + M ^ 2 / l ^ 5) / l ^ 7 := by
    ring
  have h_nonneg_pi : 0 ≤ primeCounting x := by
    unfold IEANTN.primeCounting
    exact_mod_cast Nat.zero_le (⌊x⌋₊.primeCounting)
  have h_pos_rhs : 0 < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) := by
    linarith [h_nonneg_pi, hupper x hx]
  have h_sum_eq : ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) = (Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have h_main1 : ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) ^ 2 = 1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 64 / log x ^ 6 + εUpper M_a x / log x ^ 7 := by
    simpa [εUpper] using sq_algebra M_a (log x)
  have h_eq : x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) := by
    rw [h_sum_eq]; ring
  have h1'' : primeCounting x < x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) := by
    simpa only [h_eq] using hupper x hx
  have h_pos1 : 0 < x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) := by
    simpa only [h_eq] using h_pos_rhs
  have h2 : primeCounting x ^ 2 < (x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6)) ^ 2 :=
    sq_lt_sq.mpr (by simpa only [abs_of_nonneg h_nonneg_pi, abs_of_pos h_pos1] using h1'')
  have h4 : (x * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6)) ^ 2 = x ^ 2 * ((Nat.factorial 0 : ℝ) / log x ^ 1 + (Nat.factorial 1 : ℝ) / log x ^ 2 + (Nat.factorial 2 : ℝ) / log x ^ 3 + (Nat.factorial 3 : ℝ) / log x ^ 4 + (Nat.factorial 4 : ℝ) / log x ^ 5 + M_a / log x ^ 6) ^ 2 := by ring
  simpa only [h4, h_main1] using h2

theorem ex_pi_gt_nonneg
    (m_a x_a : ℝ)
    (hm : 0 ≤ m_a)
    (hlower : ∀ x > x_a,
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (m_a * x / log x ^ 6) < primeCounting x) :
    ∀ x > exp 1 * x_a,
      exp 1 * x / log x * primeCounting (x / exp 1) >
        x ^ 2 * (
          1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5
          + 65 / log x ^ 6 + εPos m_a x / log x ^ 7) := by
  intro x hx
  have hxa_ge_one : 1 ≤ x_a := by
    by_contra hxa
    have hlt : x_a < 1 := lt_of_not_ge hxa
    have hbad := hlower 1 hlt
    have hpi1 : primeCounting 1 = 0 := by
      unfold IEANTN.primeCounting
      norm_num
    have hleft0 :
        (1 : ℝ) * ∑ k ∈ Finset.range 5, (k.factorial / log (1 : ℝ) ^ (k + 1))
          + (m_a * (1 : ℝ) / log (1 : ℝ) ^ 6) = 0 := by
      norm_num
    linarith
  have hxe : exp 1 < x := by
    have h1 : exp 1 ≤ exp 1 * x_a := by
      nlinarith [hxa_ge_one, exp_pos (1 : ℝ)]
    grind
  have hlog_gt1 : 1 < log x := by
    simpa using log_lt_log (show 0 < exp 1 by positivity) hxe
  have hlog_pos : 0 < log x := by linarith
  have hx_pos : 0 < x := lt_trans (exp_pos 1) hxe
  have hy_gt : x / exp 1 > x_a := by
    have hmul : x_a * exp 1 < x := by simpa [mul_comm] using hx
    exact (lt_div_iff₀ (exp_pos 1)).2 hmul
  have hlow := hlower (x / exp 1) hy_gt
  have hmul_pos : 0 < exp 1 * x / log x :=
    div_pos (mul_pos (exp_pos 1) hx_pos) hlog_pos
  have hmul := mul_lt_mul_of_pos_left hlow hmul_pos
  have hlog_div : log (x / exp 1) = log x - 1 := by
    rw [log_div (show x ≠ 0 by linarith) (show exp 1 ≠ 0 by positivity), log_exp]
  have hfrom0 :
      exp 1 * x / log x *
        ((x / exp 1) * ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
          + (m_a * (x / exp 1) / (log x - 1) ^ 6))
      < exp 1 * x / log x * primeCounting (x / exp 1) := by
    simpa [hlog_div] using hmul
  let S : ℝ := ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
  have hfrom :
      x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6))
      < exp 1 * x / log x * primeCounting (x / exp 1) := by
    have hleft :
        exp 1 * x / log x * ((x / exp 1) * S + (m_a * (x / exp 1) / (log x - 1) ^ 6))
        = x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6)) := by
      field_simp [hlog_pos.ne', show (exp 1 : ℝ) ≠ 0 by positivity]
    simpa [S, hleft] using hfrom0
  have hsum :
      S =
        1 / (log x - 1) + 1 / (log x - 1) ^ 2 + 2 / (log x - 1) ^ 3 +
        6 / (log x - 1) ^ 4 + 24 / (log x - 1) ^ 5 := by
    dsimp [S]
    simp [Finset.sum_range_succ, Nat.factorial]
  have hfac :
      (1 / log x) * S
      ≥
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
            30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7 := by
    simpa [hsum] using shift_factorial_lower (log x) hlog_gt1
  have hmterm :
      m_a / (log x * (log x - 1) ^ 6)
      ≥ m_a / log x ^ 7 := by
    simpa using shift_m_lower_of_nonneg m_a (log x) hm hlog_gt1
  have hcore65 :
      (1 / log x) * (S + m_a / (log x - 1) ^ 6)
      ≥
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + εPos m_a x / log x ^ 7 := by
    have hsplit :
        (1 / log x) * (S + m_a / (log x - 1) ^ 6)
        = (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := by
      calc
        (1 / log x) * (S + m_a / (log x - 1) ^ 6)
            = (1 / log x) * S + (1 / log x) * (m_a / (log x - 1) ^ 6) := by ring
        _ = (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := by
          field_simp [hlog_pos.ne']
    have hsum' := add_le_add hfac hmterm
    have hsum'' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + m_a / log x ^ 7
        ≤ (1 / log x) * (S + m_a / (log x - 1) ^ 6) := by
      calc
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
          + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + m_a / log x ^ 7
            ≤ (1 / log x) * S + m_a / (log x * (log x - 1) ^ 6) := hsum'
        _ = (1 / log x) * (S + m_a / (log x - 1) ^ 6) := hsplit.symm
    calc
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + εPos m_a x / log x ^ 7
          =
            1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
              + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
                  30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
              + m_a / log x ^ 7 := by
                simp [εPos]
                ring
      _ ≤ (1 / log x) * (S + m_a / (log x - 1) ^ 6) := hsum''
  have htarget_le :
      x ^ 2 *
          (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            εPos m_a x / log x ^ 7)
      ≤ x ^ 2 * ((1 / log x) * (S + m_a / (log x - 1) ^ 6)) :=
    mul_le_mul_of_nonneg_left hcore65 (sq_nonneg x)
  grind

theorem ex_pi_gt_neg
    (m xₐ : ℝ)
    (hm : m ≤ 0)
    (hxₐ : 1 < xₐ)
    (hlower : ∀ x > xₐ,
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (m * x / log x ^ 6) < primeCounting x) :
    ∀ x > exp 1 * xₐ,
      exp 1 * x / log x * primeCounting (x / exp 1) >
        x ^ 2 * (
          1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5
          + 65 / log x ^ 6 + εNeg m xₐ x / log x ^ 7) := by
  intro x hx
  have hxe : exp 1 < x := by
    have h1 : exp 1 ≤ exp 1 * xₐ := by
      nlinarith [hxₐ, exp_pos (1 : ℝ)]
    grind
  have hlog_gt1 : 1 < log x := by
    simpa using log_lt_log (show 0 < exp 1 by positivity) hxe
  have hlog_pos : 0 < log x := by linarith
  have hx_pos : 0 < x := lt_trans (exp_pos 1) hxe
  have hy_gt : x / exp 1 > xₐ := by
    have hmul : xₐ * exp 1 < x := by simpa [mul_comm] using hx
    exact (lt_div_iff₀ (exp_pos 1)).2 hmul
  have hlow := hlower (x / exp 1) hy_gt
  have hmul_pos : 0 < exp 1 * x / log x :=
    div_pos (mul_pos (exp_pos 1) hx_pos) hlog_pos
  have hmul := mul_lt_mul_of_pos_left hlow hmul_pos
  have hlog_div : log (x / exp 1) = log x - 1 := by
    rw [log_div (show x ≠ 0 by linarith) (show exp 1 ≠ 0 by positivity), log_exp]
  have hfrom0 :
      exp 1 * x / log x *
        ((x / exp 1) * ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
          + (m * (x / exp 1) / (log x - 1) ^ 6))
      < exp 1 * x / log x * primeCounting (x / exp 1) := by
    simpa [hlog_div] using hmul
  let S : ℝ := ∑ k ∈ Finset.range 5, (k.factorial / (log x - 1) ^ (k + 1))
  have hfrom :
      x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6))
      < exp 1 * x / log x * primeCounting (x / exp 1) := by
    have hleft :
        exp 1 * x / log x * ((x / exp 1) * S + (m * (x / exp 1) / (log x - 1) ^ 6))
        = x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6)) := by
      field_simp [hlog_pos.ne', show (exp 1 : ℝ) ≠ 0 by positivity]
    simpa [S, hleft] using hfrom0
  have hsum :
      S =
        1 / (log x - 1) + 1 / (log x - 1) ^ 2 + 2 / (log x - 1) ^ 3 +
        6 / (log x - 1) ^ 4 + 24 / (log x - 1) ^ 5 := by
    dsimp [S]
    simp [Finset.sum_range_succ, Nat.factorial]
  have hfac :
      (1 / log x) * S
      ≥
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
            30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7 := by
    simpa [hsum] using shift_factorial_lower (log x) hlog_gt1
  have hxₐ_log_pos : 0 < log xₐ := log_pos hxₐ
  have hlogxₐ_le : log xₐ + 1 ≤ log x := by
    have hmul : exp 1 * xₐ < x := by simpa [mul_comm] using hx
    have hlog := log_lt_log (show 0 < exp 1 * xₐ by positivity) hmul
    have hlog_mul : log (exp 1 * xₐ) = log xₐ + 1 := by
      rw [log_mul (by positivity) (by positivity), log_exp]
      ring
    linarith
  have hmterm :
      m / (log x * (log x - 1) ^ 6)
      ≥ ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7 := by
    simpa using shift_m_lower_of_nonpos m xₐ (log x) hm hxₐ_log_pos hlogxₐ_le
  have hcore :
      (1 / log x) * (S + m / (log x - 1) ^ 6)
      ≥
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6
        + εNeg m xₐ x / log x ^ 7 := by
    have hsplit :
        (1 / log x) * (S + m / (log x - 1) ^ 6)
        = (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := by
      calc
        (1 / log x) * (S + m / (log x - 1) ^ 6)
            = (1 / log x) * S + (1 / log x) * (m / (log x - 1) ^ 6) := by ring
        _ = (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := by
          field_simp [hlog_pos.ne']
    have hsum' := add_le_add hfac hmterm
    have hsum'' :
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7
        ≤ (1 / log x) * (S + m / (log x - 1) ^ 6) := by
      calc
        1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
              30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
          + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7
            ≤ (1 / log x) * S + m / (log x * (log x - 1) ^ 6) := hsum'
        _ = (1 / log x) * (S + m / (log x - 1) ^ 6) := hsplit.symm
    calc
      1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
          εNeg m xₐ x / log x ^ 7
          =
            1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
              (206 + 364 / log x + 381 / log x ^ 2 + 238 / log x ^ 3 + 97 / log x ^ 4 +
                30 / log x ^ 5 + 8 / log x ^ 6) / log x ^ 7
              + ((1 + 1 / log xₐ) ^ 6 * m) / log x ^ 7 := by
                simp [εNeg]
                ring
      _ ≤ (1 / log x) * (S + m / (log x - 1) ^ 6) := hsum''
  have htarget_le :
      x ^ 2 *
          (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5 + 65 / log x ^ 6 +
            εNeg m xₐ x / log x ^ 7)
      ≤ x ^ 2 * ((1 / log x) * (S + m / (log x - 1) ^ 6)) :=
    mul_le_mul_of_nonneg_left hcore (sq_nonneg x)
  grind

/-- The lower bound, split on the sign of `m`. **The split is the erratum.** -/
theorem ex_pi_gt (m xₐ : ℝ) (hxₐ : 1 < xₐ)
    (hlower : ∀ x > xₐ, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
      + (m * x / log x ^ 6) < primeCounting x) :
    ∀ x > exp 1 * xₐ,
      exp 1 * x / log x * primeCounting (x / exp 1) >
        x ^ 2 * (1 / log x ^ 2 + 2 / log x ^ 3 + 5 / log x ^ 4 + 16 / log x ^ 5
          + 65 / log x ^ 6 + εLower m xₐ x / log x ^ 7) := by
  by_cases hm : 0 ≤ m
  · intro x hx
    simpa [εLower, hm] using ex_pi_gt_nonneg m xₐ hm hlower x hx
  · intro x hx
    simpa [εLower, hm] using ex_pi_gt_neg m xₐ (le_of_not_ge hm) hxₐ hlower x hx

end DudekPlattSol
