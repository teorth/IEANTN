/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Interval.Counting
import LeanCert.Core.IntervalRat.Taylor

namespace RSInterval
open Real

/-- Each supplied prime lies in `(x,2x]` throughout `[a/2,b/2)`.
Checking primality and adjacent strict ordering suffices; completeness of the list is unnecessary. -/
def Certificate (a b L : ℕ) (ps : List ℕ) : Prop :=
  ps.IsChain (· < ·) ∧
  (∀ p ∈ ps, p.Prime ∧ b ≤ 2*p ∧ p ≤ a) ∧
  3*b*1000 < 10*L*ps.length

/-- A linear traversal of adjacent pairs, evaluated without constructing proof terms. -/
def ascending : List ℕ → Bool
  | [] => true
  | [_] => true
  | p :: q :: ps => decide (p < q) && ascending (q :: ps)

lemma ascending_sound : ∀ ps : List ℕ, ascending ps = true → ps.IsChain (· < ·)
  | [], _ => by simp
  | [_], _ => by simp
  | p :: q :: ps, h => by
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.isChain_cons_cons.mpr ⟨h.1, ascending_sound (q :: ps) h.2⟩

/-- Trial division only through the square root; the default proof-valued primality
instance tests every smaller divisor and is unsuitable for these certificates. -/
def primeCheck (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range (Nat.sqrt p + 1)).all (fun d => decide (d < 2 ∨ p % d ≠ 0))

lemma primeCheck_sound {p : ℕ} (h : primeCheck p = true) : p.Prime := by
  simp only [primeCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨h.1, fun d hd2 hd => ?_⟩
  have he := (h.2 d (by omega)).resolve_left (not_lt.mpr hd2)
  simpa only [Nat.dvd_iff_mod_eq_zero] using he

/-- Each prime test is evaluated in a small independent kernel reduction. -/
def checkPrimes (a b : ℕ) (ps : List ℕ) : Bool :=
  ps.all (fun p => primeCheck p && decide (b ≤ 2*p ∧ p ≤ a))

lemma checkPrimes_append (a b : ℕ) (ps qs : List ℕ) :
    checkPrimes a b (ps ++ qs) = (checkPrimes a b ps && checkPrimes a b qs) := by
  simp only [checkPrimes, List.all_append]

lemma certificate_of_checks {a b L : ℕ} {ps : List ℕ}
    (hs : ascending ps = true) (hp : checkPrimes a b ps = true)
    (hn : 3*b*1000 < 10*L*ps.length) : Certificate a b L ps := by
  simp only [checkPrimes, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨ascending_sound ps hs,
    fun p h => ⟨primeCheck_sound (hp p h).1, (hp p h).2⟩, hn⟩

lemma certificate_sound {a b L : ℕ} {ps : List ℕ} (ha : 0 < a) (hL : 0 < L)
    (hc : Certificate a b L ps) (hl : (L:ℝ)/1000 ≤ log ((a:ℝ)/2))
    (x : ℝ) (hax : (a:ℝ)/2 ≤ x) (hxb : x < (b:ℝ)/2) :
    3*x/(5*log x) < IEANTN.primeCounting (2*x) - IEANTN.primeCounting x := by
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have hx0 : 0 < x := by linarith
  have hlog : (L:ℝ)/1000 ≤ log x := hl.trans (log_le_log (by positivity) hax)
  have hlog0 : 0 < log x := by
    have : (0:ℝ)<L := by exact_mod_cast hL
    linarith
  have hn : (ps.length : ℝ) ≤ IEANTN.primeCounting (2*x) - IEANTN.primeCounting x := by
    apply list_le_count hx0.le (by linarith) ps hc.1
    intro p hp
    obtain ⟨hp, hb, hap⟩ := hc.2.1 p hp
    have hb' : (b:ℝ) ≤ 2*p := by exact_mod_cast hb
    have hap' : (p:ℝ) ≤ a := by exact_mod_cast hap
    exact ⟨hp, by linarith, by linarith⟩
  refine lt_of_lt_of_le ?_ hn
  rw [div_lt_iff₀ (by positivity : 0 < 5*log x)]
  have he : (3:ℝ)*b*1000 < 10*L*ps.length := by exact_mod_cast hc.2.2
  nlinarith [mul_le_mul_of_nonneg_right hlog (show (0:ℝ) ≤ ps.length by positivity)]

lemma log_lower_dyadic (a k : ℕ) (h : 2^(k+1) ≤ a) :
    ((693*k : ℕ):ℝ)/1000 ≤ log ((a:ℝ)/2) := by
  have hpow : (2:ℝ)^k ≤ (a:ℝ)/2 := by
    have h' : (2:ℝ)^(k+1) ≤ a := by exact_mod_cast h
    rw [pow_succ] at h'; linarith
  have hlog := log_le_log (by positivity : (0:ℝ)<2^k) hpow
  rw [log_pow] at hlog
  have ht := mul_le_mul_of_nonneg_left (le_of_lt log_two_gt_d9) (show (0:ℝ) ≤ k by positivity)
  push_cast
  nlinarith

open LeanCert.Core IntervalRat in
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma log_lower_small (a : ℕ) (ha : 41 ≤ a) :
    (3000:ℝ)/1000 ≤ log ((a:ℝ)/2) := by
  have hlo : (3:ℚ) ≤ (logPointComputable (41/2) 20).lo := by decide +kernel
  have hr := (mem_logPointComputable (q := (41/2)) (by norm_num) 20).1
  have hlo' : (3:ℝ) ≤ ((logPointComputable (41/2) 20).lo:ℝ) := by exact_mod_cast hlo
  have he : (3:ℝ) ≤ log (41/2) := by norm_num at hr; exact hlo'.trans hr
  norm_num
  refine he.trans (log_le_log (by norm_num) ?_)
  have : (41:ℝ) ≤ a := by exact_mod_cast ha
  linarith

end RSInterval
