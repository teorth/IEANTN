/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Max113.Lower
import RS12.PsiWitness

namespace RS12Max113
open Chebyshev Real ArithmeticFunction

set_option Elab.async false
set_option maxRecDepth 100000

/-- Verify a supplied binary exponent instead of computing a large binary logarithm. -/
private theorem log_le_units {p u : ℕ} (hp : 0 < p) (hb : p ^ 256 < 2 ^ u) :
    log (p : ℝ) ≤ (u : ℝ) * 693148 / 256000000 := by
  have hr : (p : ℝ)^256 ≤ (2 : ℝ)^u := by exact_mod_cast hb.le
  have hl := Real.log_le_log (show (0 : ℝ) < (p : ℝ)^256 by positivity) hr
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  have hc := mul_le_mul_of_nonneg_left RS12Factorial.kernel_log_two
    (Nat.cast_nonneg u : (0 : ℝ) ≤ u)
  nlinarith only [hl, hc]

-- Same factor-witness convention as v1: k=0 means a proper coprime factor;
-- k>0 means n=a^k. No primality test is required for either case.
private def checkFactor (n a k : ℕ) : Bool :=
  if k = 0 then decide (1 < a ∧ a < n ∧ n % a = 0 ∧ Nat.gcd a (n / a) = 1)
  else decide (0 < a ∧ a ^ k = n)

private def checkTerm (n : ℕ) (code : ℕ × ℕ × ℕ) : Bool :=
  if n = 1 then code.2.2 == 0 else
    checkFactor n code.1 code.2.1 &&
      (if code.2.1 = 0 then true else decide (code.1 ^ 256 < 2 ^ code.2.2))

private theorem checkTerm_sound {n : ℕ} {code : ℕ × ℕ × ℕ}
    (hc : checkTerm n code = true) :
    vonMangoldt n ≤ (code.2.2 : ℝ) * 693148 / 256000000 := by
  rcases code with ⟨a, k, u⟩
  by_cases hn : n = 1
  · subst n
    simp only [vonMangoldt_apply_one]
    positivity
  · simp only [checkTerm, hn, ite_false, Bool.and_eq_true] at hc
    by_cases hk : k = 0
    · have hf : 1 < a ∧ a < n ∧ n % a = 0 ∧ Nat.gcd a (n / a) = 1 := by
        simpa only [checkFactor, hk, ite_true, decide_eq_true_eq] using hc.1
      rw [RS12PsiInteger.vonMangoldt_eq_zero_of_coprime_factors
        hf.1 hf.2.1 hf.2.2.1 hf.2.2.2]
      positivity
    · have hf : 0 < a ∧ a ^ k = n := by
        simpa only [checkFactor, hk, ite_false, decide_eq_true_eq] using hc.1
      have hb : a ^ 256 < 2 ^ u := by
        simpa only [hk, ite_false, decide_eq_true_eq] using hc.2
      rw [← hf.2, vonMangoldt_apply_pow hk]
      exact vonMangoldt_le_log.trans (log_le_units hf.1 hb)

/-- Supplied units are checked term by term, together with every required strict slope. -/
def checkSmall (start : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → ℕ → Bool
  | [], acc, target => decide (acc ≤ target)
  | code :: us, acc, target =>
    let next := start + 1
    let acc' := acc + code.2.2
    checkTerm next code && ((decide (next = 113 ∨ 693148 * acc' < 265937920 * next)) &&
      checkSmall next us acc' target)

theorem checkSmall_sound {start acc target : ℕ} {us : List (ℕ × ℕ × ℕ)}
    (hc : checkSmall start us acc target = true)
    (ha : ψ (start : ℕ) ≤ (acc : ℝ) * 693148 / 256000000) :
    ψ (start + us.length : ℕ) ≤ (target : ℝ) * 693148 / 256000000 ∧
      ∀ n : ℕ, start < n → n ≤ start + us.length → n ≠ 113 →
        ψ (n : ℝ) < 1.03882 * n := by
  induction us generalizing start acc with
  | nil =>
    have he : (acc : ℝ) ≤ target := by
      exact_mod_cast (show acc ≤ target by simpa [checkSmall] using hc)
    constructor
    · simpa using ha.trans (by gcongr)
    · intro n hlo hhi; simp only [List.length_nil, Nat.add_zero] at hhi; omega
  | cons code us ih =>
    simp only [checkSmall, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hn : ψ (start + 1 : ℕ) ≤
        ((acc + code.2.2 : ℕ) : ℝ) * 693148 / 256000000 := by
      rw [RS12PsiInteger.psi_succ]
      have ht := checkTerm_sound hc.1
      push_cast
      linarith
    have ht := ih hc.2.2 hn
    constructor
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ht.1
    · intro n hlo hhi hne
      by_cases he : n = start + 1
      · subst n
        have hb := hc.2.1.resolve_left hne
        have hr : (693148 : ℝ) * ((acc : ℝ) + code.2.2) <
            265937920 * ((start : ℝ) + 1) := by exact_mod_cast hb
        push_cast at hn ⊢
        nlinarith
      · exact ht.2 n (by omega) (by simp only [List.length_cons] at hhi; omega) hne

/-- Join two checked small intervals. -/
theorem small_join {lo mid hi : ℕ}
    (hl : ∀ n : ℕ, lo < n → n ≤ mid → n ≠ 113 → ψ (n : ℝ) < 1.03882 * n)
    (hr : ∀ n : ℕ, mid < n → n ≤ hi → n ≠ 113 → ψ (n : ℝ) < 1.03882 * n) :
    ∀ n : ℕ, lo < n → n ≤ hi → n ≠ 113 → ψ (n : ℝ) < 1.03882 * n := by
  intro n hlo hhi hne
  by_cases hm : n ≤ mid
  · exact hl n hlo hm hne
  · exact hr n (by omega) hhi hne

end RS12Max113
