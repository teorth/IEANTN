/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import IEANTN.Vocabulary.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Finite.All
import IEANTN.Nodes.RosserSchoenfeld1962.v7.Conclusions

namespace RS39
open Real Chebyshev Finset

lemma theta_double (n : ℕ) : θ (2*n) ≤ θ n + 2*n*log 2 := by
  have hb := primorial_add_le (le_refl n)
  have hc := Nat.choose_le_two_pow (n+n) n
  have hp := primorial_pos n
  have hp2 := primorial_pos (n+n)
  have hl := log_le_log (show (0:ℝ) < primorial (n+n) by exact_mod_cast hp2)
    (show (primorial (n+n):ℝ) ≤ (primorial n:ℝ) * (2:ℝ)^(n+n) by
      exact_mod_cast hb.trans (Nat.mul_le_mul_left _ hc))
  rw [log_mul (by exact_mod_cast hp.ne') (by positivity), log_pow] at hl
  rw [show (2:ℝ)*n = ((n+n:ℕ):ℝ) by push_cast; ring]
  simp only [theta_eq_log_primorial, Nat.floor_natCast]
  convert hl using 1 <;> push_cast <;> ring_nf

lemma theta_succ (n : ℕ) : θ (n+1) ≤ θ n + log (n+1) := by
  simp only [theta, ← Nat.cast_add_one, Nat.floor_natCast, sum_filter]
  rw [sum_Ioc_succ_top (Nat.zero_le n)]
  simp only [Nat.cast_add, Nat.cast_one]
  split_ifs <;> have := log_nonneg (show (1:ℝ) ≤ n+1 by have := Nat.cast_nonneg (α := ℝ) n; linarith) <;> linarith

lemma theta_interval {x : ℝ} (hx : 1 < x) :
    θ (2*x) - θ x ≤ 2*(x+1)*log 2 + log (x+1) := by
  let n := ⌊x⌋₊
  have hn : (n:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hn' : x < (n:ℝ)+1 := Nat.lt_floor_add_one x
  have h1 := theta_double (n+1)
  have h2 := theta_succ n
  have hm := theta_mono (show 2*x ≤ 2*((n:ℝ)+1) by linarith)
  have hlow := theta_mono hn
  have hlog := log_le_log (show (0:ℝ)<n+1 by positivity) (show (n:ℝ)+1≤x+1 by linarith)
  push_cast at h1
  have hmul := mul_le_mul_of_nonneg_right (show 2*((n:ℝ)+1)≤2*(x+1) by linarith)
    (log_nonneg (by norm_num : (1:ℝ)≤2))
  linarith

lemma count_mul_log_le {x : ℝ} (hx : 1 < x) :
    (IEANTN.primeCounting (2*x) - IEANTN.primeCounting x) * log x ≤
      θ (2*x) - θ x := by
  have hs := Nat.primesLE_mono (Nat.floor_mono (show x ≤ 2*x by linarith))
  rw [theta_eq_sum_primesLE, theta_eq_sum_primesLE, ← sum_sdiff_eq_sub hs]
  have hc : IEANTN.primeCounting (2*x) - IEANTN.primeCounting x =
      ((Nat.primesLE ⌊2*x⌋₊ \ Nat.primesLE ⌊x⌋₊).card : ℝ) := by
    rw [card_sdiff_of_subset hs, Nat.primesLE_card_eq_primeCounting,
      Nat.primesLE_card_eq_primeCounting, Nat.cast_sub (Nat.monotone_primeCounting (Nat.floor_mono (by linarith : x≤2*x)))]
    rfl
  rw [hc, ← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum
  intro p hp
  obtain ⟨hp, hnp⟩ := mem_sdiff.mp hp
  obtain ⟨_, hprime⟩ := Nat.mem_primesLE.mp hp
  apply log_le_log (by linarith)
  by_contra h
  exact hnp (Nat.mem_primesLE.mpr ⟨Nat.le_floor (le_of_not_ge h), hprime⟩)

lemma large {x : ℝ} (hx : 1024 ≤ x) :
    IEANTN.primeCounting (2*x) - IEANTN.primeCounting x < 7*x/(5*log x) := by
  have hx1 : 1 < x := by linarith
  have hL : 0 < log x := log_pos hx1
  have h1 := count_mul_log_le hx1
  have h2 := theta_interval hx1
  have h3 := log_le_sub_one_of_pos (show 0 < (x+1)/1024 by positivity)
  rw [log_div (by positivity) (by norm_num), show (1024:ℝ) = 2^10 by norm_num,
    log_pow] at h3
  have h4 := log_two_lt_d9
  apply (lt_div_iff₀ (by positivity : 0 < 5*log x)).mpr
  have h5 : 0 ≤ (x-1024) * ((694/1000 : ℝ) - log 2) := by
    apply mul_nonneg (by linarith) (by linarith)
  norm_num at h3
  nlinarith

lemma positive {x : ℝ} (hx : 1 < x) :
    0 < IEANTN.primeCounting (2*x) - IEANTN.primeCounting x := by
  have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (by omega)
  have hpm : p ≤ ⌊2*x⌋₊ := Nat.le_floor (by
    have h1 : (p:ℝ) ≤ 2*(⌊x⌋₊:ℝ) := by exact_mod_cast hpn
    have h2 := Nat.floor_le (show 0 ≤ x by linarith)
    linarith)
  have ha := Nat.count_monotone Nat.Prime (Nat.succ_le_of_lt hnp)
  have hb := Nat.count_strict_mono hp (Nat.lt_succ_of_le hpm)
  have h : Nat.primeCounting ⌊x⌋₊ < Nat.primeCounting ⌊2*x⌋₊ := ha.trans_lt hb
  apply sub_pos.mpr
  dsimp [IEANTN.primeCounting]
  exact_mod_cast h

lemma small (hcert : ∀ n ∈ Finset.Icc 2 1023,
    (Nat.primeCounting (2*n+1) - Nat.primeCounting n) * (Nat.log 2 (n+1)+1) ≤ 2*n)
    {x : ℝ} (hx : 1 < x) (hxsmall : x < 1024) :
    IEANTN.primeCounting (2*x) - IEANTN.primeCounting x < 7*x/(5*log x) := by
  have hx0 : 0 ≤ x := by linarith
  have hL : 0 < log x := log_pos hx
  have hd := positive hx
  have h2 := log_two_lt_d9
  apply (lt_div_iff₀ (by positivity : 0 < 5*log x)).mpr
  by_cases hsmall : x < 2
  · have hp : IEANTN.primeCounting (2*x) ≤ 2 := by
      have hf : ⌊2*x⌋₊ ≤ 4 := Nat.floor_le_of_le (by norm_num; linarith)
      have hc := Nat.monotone_primeCounting hf
      have h4 : Nat.primeCounting 4 = 2 := by decide +kernel
      rw [h4] at hc
      dsimp [IEANTN.primeCounting]
      exact_mod_cast hc
    have hpx : 0 ≤ IEANTN.primeCounting x := Nat.cast_nonneg _
    have hl := log_le_log (by linarith : 0<x) hsmall.le
    nlinarith
  let n := ⌊x⌋₊
  let k := Nat.log 2 (n+1)+1
  let c := Nat.primeCounting (2*n+1) - Nat.primeCounting n
  have hn : 2 ≤ n := Nat.le_floor (le_of_not_gt hsmall)
  have hn' : n ≤ 1023 := by
    have : n < 1024 := (Nat.floor_lt hx0).mpr hxsmall
    omega
  have hcert' := hcert n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)
  have hnlow : (n:ℝ) ≤ x := Nat.floor_le hx0
  have hnup : x < (n:ℝ)+1 := Nat.lt_floor_add_one x
  have hcount : IEANTN.primeCounting (2*x) - IEANTN.primeCounting x ≤ c := by
    have hf : ⌊2*x⌋₊ ≤ 2*n+1 := by
      have : ⌊2*x⌋₊ < 2*n+2 := (Nat.floor_lt (by positivity)).mpr (by push_cast; linarith)
      omega
    have hm := Nat.monotone_primeCounting hf
    have hsub := Nat.monotone_primeCounting (show n ≤ 2*n+1 by omega)
    dsimp [IEANTN.primeCounting, c]
    rw [Nat.cast_sub hsub]
    exact sub_le_sub_right (by exact_mod_cast hm) _
  have hcpos : 0 < (c:ℝ) := hd.trans_le hcount
  have hkpos : 0 < (k:ℝ) := by dsimp [k]; positivity
  have hlog : log x < (k:ℝ) * (7/10:ℝ) := by
    have hpow := Nat.lt_pow_succ_log_self (by norm_num : 1<2) (n+1)
    have hxpow : x < (2:ℝ)^k := by
      have : (n:ℝ)+1 < (2:ℝ)^k := by exact_mod_cast hpow
      linarith
    have hl := log_lt_log (by linarith : 0<x) hxpow
    rw [log_pow] at hl
    have hh := mul_pos hkpos (show 0 < (7/10:ℝ)-log 2 by linarith)
    nlinarith
  have hck : (c:ℝ)*(k:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast hcert'
  have hprod := mul_lt_mul_of_pos_left hlog hcpos
  have hcountlog := mul_le_mul_of_nonneg_right hcount hL.le
  nlinarith

end RS39

/-- Rosser–Schoenfeld 1962, Corollary 3, complete equation (3.9). -/
theorem RosserSchoenfeld1962.v7.challenge_equation_3_9 :
    RosserSchoenfeld1962.v7.equation_3_9 := by
  intro x hx
  refine ⟨RS39.positive hx, ?_⟩
  by_cases h : x < 1024
  · exact RS39.small RS39.finite_certificate hx h
  · exact RS39.large (le_of_not_gt h)
