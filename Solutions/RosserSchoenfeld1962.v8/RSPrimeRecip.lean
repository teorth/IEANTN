/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright
-/
import Mathlib
import LeanCert.Tactic.IntervalAuto

/-!
# Rosser–Schoenfeld 1962, equation (3.19): `∑_{p ≤ x} 1/p > log log x` for `x > 1`

Elementary proof, independent of any explicit zero-free region or numerical prime tables.

* Legendre: `v_p(N!) ≤ N/(p-1)`, so `N log N - N ≤ log N! ≤ N · S N` with
  `S N = ∑_{p ≤ N} log p / (p - 1)`; hence `S N ≥ log N - 1`.
* Discrete partial summation against `1 / log n`: with `Q N = ∑_{p ≤ N} 1/(p-1)`,
  `H N = Q N - S N / log N - (1 + 1/T) / log N - log log N` is nondecreasing for `N ≥ T`.
* `∑ 1/p = Q - ∑ 1/(p(p-1))`, and the last sum is at most `∑_{p ≤ 13} 1/(p(p-1)) + 1/13`.
* One numerical check at `T = 30` and the range `2 ≤ N < 30` are done by LeanCert's
  `interval_decide` in kernel mode (no `native_decide`, standard axioms only).
-/

namespace RSPrimeRecip

open Real Finset

/-- Sum of `g p` over primes `p ≤ N`, written so that `sum_range_succ` applies. -/
noncomputable def psum (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), if n.Prime then g n else 0

lemma psum_succ (g : ℕ → ℝ) (N : ℕ) :
    psum g (N + 1) = psum g N + if (N + 1).Prime then g (N + 1) else 0 := by
  simp only [psum]
  rw [sum_range_succ]

lemma psum_eq_filter (g : ℕ → ℝ) (N : ℕ) :
    psum g N = ∑ p ∈ filter Nat.Prime (Iic N), g p := by
  rw [psum, sum_ite, sum_const_zero, add_zero, Nat.range_succ_eq_Iic]

/-- `∑_{p ≤ N} log p / (p - 1)`. -/
noncomputable def S (N : ℕ) : ℝ := psum (fun p => log p / ((p : ℝ) - 1)) N
/-- `∑_{p ≤ N} 1 / (p - 1)`. -/
noncomputable def Q (N : ℕ) : ℝ := psum (fun p => 1 / ((p : ℝ) - 1)) N
/-- `∑_{p ≤ N} 1 / p`. -/
noncomputable def P (N : ℕ) : ℝ := psum (fun p => 1 / (p : ℝ)) N
/-- `∑_{p ≤ N} 1 / (p (p - 1))`. -/
noncomputable def R (N : ℕ) : ℝ := psum (fun p => 1 / ((p : ℝ) * ((p : ℝ) - 1))) N

lemma P_eq (N : ℕ) : P N = Q N - R N := by
  simp only [P, Q, R, psum, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with hn
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have h1 : (n : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (n : ℝ) ≠ 0 := by linarith
    field_simp
  · simp

/-- Legendre's formula gives `log N! ≤ N · S N`. -/
lemma log_factorial_le (N : ℕ) : log (N.factorial : ℝ) ≤ N * S N := by
  rw [log_nat_eq_sum_factorization,
    Finsupp.sum_of_support_subset _ (s := filter Nat.Prime (Iic N)) ?_ _ (by simp)]
  · rw [S, psum_eq_filter, mul_sum]
    refine sum_le_sum fun p hp => ?_
    simp only [mem_filter, mem_Iic] at hp
    have hpp := hp.2
    have h1 := Nat.factorization_factorial_le_div_pred hpp N
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hv : ((N.factorial).factorization p : ℝ) ≤ N / ((p : ℝ) - 1) := by
      calc ((N.factorial).factorization p : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
        _ = N / ((p : ℝ) - 1) := by rw [Nat.cast_sub hpp.one_le]; simp
    have hlog : 0 ≤ log p := log_natCast_nonneg p
    calc ((N.factorial).factorization p : ℝ) * log p ≤ N / ((p : ℝ) - 1) * log p :=
          mul_le_mul_of_nonneg_right hv hlog
      _ = N * (log p / (p - 1)) := by ring
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    simp [hpp, (Nat.Prime.dvd_factorial hpp).mp hd]

/-- `N log N - N ≤ log N!` (from `N^N / N! ≤ e^N`). -/
lemma log_factorial_ge (N : ℕ) : N * log N - N ≤ log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (x := (N : ℝ)) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < (N : ℝ) ^ N / N.factorial := by positivity
  have := Real.log_le_log hpos h
  rw [Real.log_exp, Real.log_div (by positivity) hf.ne', Real.log_pow] at this
  linarith

/-- Chebyshev-type lower bound `S N ≥ log N - 1`. -/
lemma S_ge (N : ℕ) (hN : 1 ≤ N) : log N - 1 ≤ S N := by
  have h := (log_factorial_ge N).trans (log_factorial_le N)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have : 0 ≤ (N : ℝ) * (S N - (log N - 1)) := by linarith
  linarith [(mul_nonneg_iff_of_pos_left hNpos).mp this]

/-- Partial summation step: `Q (N+1) - S (N+1) / log (N+1) = Q N - S N / log (N+1)`. -/
lemma QS_succ (N : ℕ) (hN : 1 ≤ N) :
    Q (N + 1) - S (N + 1) / log ((N : ℝ) + 1) = Q N - S N / log ((N : ℝ) + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < log ((N : ℝ) + 1) := log_pos (by linarith)
  by_cases hp : (N + 1).Prime
  · simp only [Q, S, psum_succ, hp, ↓reduceIte]
    push_cast
    have e : (N : ℝ) + 1 - 1 = N := by ring
    rw [e]
    field_simp
    ring
  · simp only [Q, S, psum_succ, hp, ↓reduceIte, add_zero]

lemma log_succ_sub_le (N : ℕ) (hN : 1 ≤ N) : log ((N : ℝ) + 1) - log N ≤ 1 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← log_div (by positivity) hNpos.ne']
  have := log_le_sub_one_of_pos (show 0 < ((N : ℝ) + 1) / N by positivity)
  have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
  linarith

/-- The key real inequality behind monotonicity of `H`. -/
lemma step_ineq (S L L' t : ℝ) (hL : 0 < L) (hLL : L ≤ L') (hd : L' - L ≤ t)
    (hS : L - 1 ≤ S) :
    log L' - log L ≤ S * (1 / L - 1 / L') + (1 + t) * (1 / L - 1 / L') := by
  have hL' : 0 < L' := by linarith
  have hlog : log L' - log L ≤ (L' - L) / L := by
    rw [← log_div hL'.ne' hL.ne']
    have := log_le_sub_one_of_pos (div_pos hL' hL)
    have e : L' / L - 1 = (L' - L) / L := by field_simp
    linarith
  set w := (L' - L) / (L * L') with hw_def
  have hw : 0 ≤ w := div_nonneg (by linarith) (by positivity)
  have hu : 1 / L - 1 / L' = w := by rw [hw_def]; field_simp
  have hdL : (L' - L) / L = w * L' := by rw [hw_def]; field_simp
  rw [hu]
  have h1 : (L - 1) * w ≤ S * w := mul_le_mul_of_nonneg_right hS hw
  have h2 : w * L' ≤ w * (L + t) := mul_le_mul_of_nonneg_left (by linarith) hw
  nlinarith

/-- The monotone quantity of the partial summation argument. -/
noncomputable def H (T N : ℕ) : ℝ :=
  Q N - S N / log N - (1 + 1 / (T : ℝ)) / log N - log (log N)

lemma H_mono (T N : ℕ) (hT : 1 ≤ T) (hTN : T ≤ N) (hN : 2 ≤ N) : H T N ≤ H T (N + 1) := by
  have hNpos : (1 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < log (N : ℝ) := log_pos hNpos
  have hLL : log (N : ℝ) ≤ log ((N : ℝ) + 1) := log_le_log (by linarith) (by linarith)
  have hd : log ((N : ℝ) + 1) - log N ≤ 1 / (T : ℝ) := by
    refine (log_succ_sub_le N (by omega)).trans ?_
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    exact one_div_le_one_div_of_le hT' (by exact_mod_cast hTN)
  have key := step_ineq (S N) (log N) (log ((N : ℝ) + 1)) (1 / (T : ℝ)) hL hLL hd
    (S_ge N (by omega))
  have hQS := QS_succ N (by omega)
  simp only [H]
  push_cast
  have e1 : S N / log (N : ℝ) - S N / log ((N : ℝ) + 1) =
      S N * (1 / log (N : ℝ) - 1 / log ((N : ℝ) + 1)) := by ring
  have e2 : (1 + 1 / (T : ℝ)) / log (N : ℝ) - (1 + 1 / (T : ℝ)) / log ((N : ℝ) + 1) =
      (1 + 1 / (T : ℝ)) * (1 / log (N : ℝ) - 1 / log ((N : ℝ) + 1)) := by ring
  linarith

lemma H_ge (T : ℕ) (hT : 2 ≤ T) : ∀ N, T ≤ N → H T T ≤ H T N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact le_rfl
  | succ N hTN ih => exact ih.trans (H_mono T N (by omega) hTN (by omega))

lemma Q_ge (T N : ℕ) (hT : 2 ≤ T) (hTN : T ≤ N) :
    log (log N) + 1 + H T T + 1 / (T * log N) ≤ Q N := by
  have hN : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos hN
  have hS := S_ge N (by omega)
  have hH := H_ge T hT N hTN
  have hdiv : (log N - 1) / log N ≤ S N / log N := div_le_div_of_nonneg_right hS hL.le
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have e : (log (N : ℝ) - 1) / log N + (1 + 1 / (T : ℝ)) / log N = 1 + 1 / (T * log N) := by
    field_simp
    ring
  simp only [H] at hH ⊢
  linarith

lemma R_succ_le (N : ℕ) (hN : 1 ≤ N) :
    R (N + 1) + 1 / ((N : ℝ) + 1) ≤ R N + 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hp : (N + 1).Prime
  · simp only [R, psum_succ, hp, ↓reduceIte]
    push_cast
    have e : 1 / (((N : ℝ) + 1) * ((N : ℝ) + 1 - 1)) + 1 / ((N : ℝ) + 1) = 1 / N := by
      have : (N : ℝ) + 1 - 1 = N := by ring
      rw [this]
      field_simp
      ring
    linarith
  · simp only [R, psum_succ, hp, ↓reduceIte, add_zero]
    have : 1 / ((N : ℝ) + 1) ≤ 1 / N := one_div_le_one_div_of_le hNpos (by linarith)
    linarith

lemma R_le (N : ℕ) (hN : 13 ≤ N) : R N + 1 / (N : ℝ) ≤ R 13 + 1 / 13 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have := R_succ_le N (by omega)
    push_cast
    linarith

lemma numeric_aux (A L ll q c : ℝ) (hL : 0 < L) (h : A + 31 / 30 ≤ (1 + q - c - ll) * L) :
    c ≤ 1 + (q - A / L - 31 / 30 / L - ll) := by
  have e : A / L + 31 / 30 / L = (A + 31 / 30) / L := by ring
  have := (div_le_iff₀ hL).mpr h
  linarith

/-- The single numerical input at `T = 30` (LeanCert, kernel-checked). -/
lemma numeric_core :
    (log 2 + log 3 * (1 / 2) + log 5 * (1 / 4) + log 7 * (1 / 6) + log 11 * (1 / 10) +
      log 13 * (1 / 12) + log 17 * (1 / 16) + log 19 * (1 / 18) + log 23 * (1 / 22) +
      log 29 * (1 / 28)) + 31 / 30 ≤
      (1 + 127469 / 55440 - 962 / 1155 - log (log 30)) * log 30 := by
  interval_decide (trust := kernel)

lemma numeric : R 13 + 1 / 13 ≤ 1 + H 30 30 := by
  simp only [H, Q, S, R, psum, sum_range_succ, sum_range_zero]
  norm_num
  refine numeric_aux _ _ _ _ _ (log_pos (by norm_num)) ?_
  convert numeric_core using 2
  ring

lemma large (N : ℕ) (hN : 30 ≤ N) : log (log ((N : ℝ) + 1)) ≤ P N := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos hN1
  have hQ := Q_ge 30 N (by norm_num) hN
  have hR := R_le N (by omega)
  have hnum := numeric
  have hNpos : (0 : ℝ) < N := by linarith
  have hinv : 0 < 1 / (N : ℝ) := by positivity
  -- log log (N+1) - log log N ≤ (log (N+1) - log N) / log N ≤ 1 / (30 log N)
  have hL' : 0 < log ((N : ℝ) + 1) := log_pos (by linarith)
  have hjump : log (log ((N : ℝ) + 1)) - log (log N) ≤ 1 / (30 * log N) := by
    rw [← log_div hL'.ne' hL.ne']
    have h1 := log_le_sub_one_of_pos (div_pos hL' hL)
    have h2 := log_succ_sub_le N (by omega)
    have h3 : 1 / (N : ℝ) ≤ 1 / 30 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
    have e : log ((N : ℝ) + 1) / log N - 1 = (log ((N : ℝ) + 1) - log N) / log N := by
      field_simp
    have h4 : (log ((N : ℝ) + 1) - log N) / log N ≤ (1 / 30) / log N :=
      div_le_div_of_nonneg_right (h2.trans h3) hL.le
    have e2 : (1 / 30 : ℝ) / log N = 1 / (30 * log N) := by field_simp
    linarith
  rw [P_eq]
  push_cast at hQ
  linarith

lemma small (N : ℕ) (h2 : 2 ≤ N) (h30 : N < 30) : log (log ((N : ℝ) + 1)) ≤ P N := by
  interval_cases N <;>
  · simp only [P, psum, sum_range_succ, sum_range_zero]
    norm_num
    interval_decide (trust := kernel)

/-- **Rosser–Schoenfeld 1962, equation (3.19).** For `x > 1`, `∑_{p ≤ x} 1/p > log log x`. -/
theorem sum_inv_prime_gt_loglog (x : ℝ) (hx : 1 < x) :
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), (1 / (p : ℝ)) > log (log x) := by
  rw [← psum_eq_filter]
  change log (log x) < P ⌊x⌋₊
  set N := ⌊x⌋₊ with hN_def
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hx.le)
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlogx : 0 < log x := log_pos hx
  rcases Nat.lt_or_ge N 2 with hN | hN
  · -- N = 1: no primes, and `log log x < 0` since `log x < log 2 < 1`.
    have hN1' : N = 1 := by omega
    have hP : P N = 0 := by rw [hN1']; simp [P, psum, sum_range_succ, Nat.not_prime_one]
    rw [hP]
    have hx2 : x < 2 := by rw [hN1'] at hxN; norm_num at hxN; exact hxN
    have hlog2 : log x < 1 := by
      have := log_lt_log (by linarith) hx2
      have h2 : log (2 : ℝ) < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    exact log_neg hlogx hlog2
  · have hkey : log (log x) < log (log ((N : ℝ) + 1)) :=
      log_lt_log hlogx (log_lt_log (by linarith) hxN)
    rcases Nat.lt_or_ge N 30 with h30 | h30
    · exact hkey.trans_le (small N hN h30)
    · exact hkey.trans_le (large N h30)

end RSPrimeRecip
