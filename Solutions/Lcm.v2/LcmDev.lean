/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import IEANTN.Nodes.Lcm.v2.Conclusions

namespace LcmDev

open ArithmeticFunction hiding log
open Finset Nat Real



def σ : ArithmeticFunction ℕ := sigma 1

noncomputable abbrev σnorm (n : ℕ) : ℝ := (σ n : ℝ) / (n : ℝ)

def HighlyAbundant (N : ℕ) : Prop :=
  ∀ m : ℕ, m < N → σ m < σ N


def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm _root_.id





structure Criterion where
  n : ℕ
  hn : n ≥ 1
  p : Fin 3 → ℕ
  hp : ∀ i, Nat.Prime (p i)
  hp_mono : StrictMono p
  q : Fin 3 → ℕ
  hq : ∀ i, Nat.Prime (q i)
  hq_mono : StrictMono q
  h_ord_1 : √(n : ℝ) < p 0
  h_ord_2 : p 2 < q 0
  h_ord_3 : q 2 < n
  h_crit : ∏ i, (1 + (1 : ℝ) / q i) ≤
    (∏ i, (1 + (1 : ℝ) / (p i * (p i + 1)))) * (1 + (3 : ℝ) / (8 * n)) *
      (1 - 4 * (∏ i, (p i : ℝ)) / ∏ i, (q i : ℝ))

theorem Criterion.prod_p_le_prod_q (c : Criterion) : 4 * ∏ i, c.p i < ∏ i, c.q i := by
  have hBC_pos : 0 < (∏ i, (1 + (1 : ℝ) / (c.p i * (c.p i + 1)))) * (1 + 3 / (8 * c.n)) := by
    positivity
  have hR_pos : 0 < 1 - 4 * (∏ i, (c.p i : ℝ)) / ∏ i, (c.q i : ℝ) := by
    by_contra h
    exact absurd (c.h_crit.trans (mul_nonpos_of_nonneg_of_nonpos hBC_pos.le (not_lt.mp h)))
      (not_le.mpr <| prod_pos fun i _ ↦ by positivity)
  rw [sub_pos, div_lt_one <| prod_pos fun i _ ↦ cast_pos.mpr (c.hq i).pos] at hR_pos
  exact_mod_cast hR_pos

lemma Criterion.p_gt_two (c : Criterion) (i : Fin 3) : 2 < c.p i := by
  have h_pi_gt_two : ∀ i, 1 < c.p i := fun i ↦ Nat.Prime.one_lt (c.hp i)
  by_contra h_contra
  interval_cases _ : c.p i; iterate 2 grind
  · have := c.h_ord_1; have := c.h_ord_2; have := c.h_ord_3; fin_cases i
    · simp_all only [Fin.isValue, Fin.zero_eta, cast_ofNat]
      rw [Real.sqrt_lt] at * <;> norm_cast at * <;>
      linarith [h_pi_gt_two 0, h_pi_gt_two 1, h_pi_gt_two 2, c.hp_mono (show 0 < 1 by decide),
        c.hp_mono (show 1 < 2 by decide), c.hq_mono (show 0 < 1 by decide),
        c.hq_mono (show 1 < 2 by decide)]
    · grind [c.hp_mono (show 0 < 1 by decide) , c.hp_mono (show 1 < 2 by decide)]
    · grind [h_pi_gt_two 0, h_pi_gt_two 1, h_pi_gt_two 2, c.hp_mono (show 0 < 1 by decide),
        c.hp_mono (show 1 < 2 by decide)]

lemma Criterion.q_gt_two (c : Criterion) (i : Fin 3) : 2 < c.q i := by
  have h_q_gt_two : ∀ i, 2 < c.q i := fun i ↦ by
    have h_q_gt_p : ∀ i, c.p 2 < c.q i := fun i ↦ by
      fin_cases i <;> linarith! [c.hp_mono <| show 0 < 1 by decide, c.hp_mono <|
        show 1 < 2 by decide, c.hq_mono <| show 0 < 1 by decide, c.hq_mono <|
        show 1 < 2 by decide, c.h_ord_2, c.h_ord_3]
    grind [c.p_gt_two 2]
  exact h_q_gt_two i


noncomputable def Criterion.L' (c : Criterion) : ℕ := L c.n / ∏ i, c.q i

lemma Criterion.prod_q_dvd_L (c : Criterion) : ∏ i, c.q i ∣ L c.n :=
  Fintype.prod_dvd_of_isRelPrime (fun i j h ↦ coprime_iff_isRelPrime.mp <|
    (coprime_primes (c.hq i) (c.hq j)).mpr (c.hq_mono.injective.ne h)) fun i ↦ dvd_lcm <|
      mem_Icc.mpr ⟨(c.hq i).one_le, (c.hq_mono.monotone (Fin.le_last i)).trans c.h_ord_3.le⟩

lemma Criterion.L_pos (c : Criterion) : 0 < L c.n :=
  lt_of_lt_of_le Nat.zero_lt_one <| one_le_iff_ne_zero.mpr fun h ↦ by simp_all [L]

lemma Criterion.L'_pos (c : Criterion) : 0 < c.L' :=
  div_pos (le_of_dvd c.L_pos c.prod_q_dvd_L) (prod_pos fun i _ ↦ (c.hq i).pos)

lemma Criterion.L_eq_prod_q_mul_L' (c : Criterion) : L c.n = (∏ i, c.q i) * c.L' := by
  rw [L', Nat.mul_div_cancel' c.prod_q_dvd_L]

lemma Criterion.val_two_L' (c : Criterion) : (c.L').factorization 2 = Nat.log 2 c.n := by
  have h_lcm : ∀ n : ℕ, n ≥ 1 → Nat.factorization (L n) 2 = Nat.log 2 n := by
    have h_lcm_exp : ∀ n : ℕ, n ≥ 1 → (Nat.factorization (Finset.lcm (Finset.Icc 1 n)
        (fun x ↦ x)) 2) = Finset.sup (Finset.Icc 1 n) (fun x ↦ Nat.factorization x 2) := by
      intros n hn
      have h_lcm_exp : ∀ {S : Finset ℕ}, (∀ x ∈ S, x ≠ 0) → (Nat.factorization (Finset.lcm S
          (fun x ↦ x)) 2) = Finset.sup S (fun x ↦ Nat.factorization x 2) := by
        intro S hS
        induction S using Finset.induction with
        | empty => simp
        | insert x S hxS ih =>
            simp_all only [lcm_insert]
            erw [Nat.factorization_lcm] <;> simp_all
      exact h_lcm_exp fun x hx ↦ by linarith [Finset.mem_Icc.mp hx]
    have h_sup : ∀ n : ℕ, n ≥ 1 → Finset.sup (Finset.Icc 1 n) (fun x ↦ Nat.factorization x 2) =
       Nat.log 2 n := fun n hn ↦ by
      apply le_antisymm
      · exact Finset.sup_le fun x hx ↦ Nat.le_log_of_pow_le (by decide) <|
          Nat.le_trans (Nat.le_of_dvd (by linarith [Finset.mem_Icc.mp hx])
          <| Nat.ordProj_dvd _ _) <| by linarith [Finset.mem_Icc.mp hx]
      · refine le_trans ?_ (Finset.le_sup <| Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ zero_lt_two,
          Nat.pow_log_le_self 2 <| by linarith⟩)
        norm_num [Nat.Prime.factorization_self (prime_two)]
    aesop
  rw [show c.L' = L c.n / (∏ i, c.q i) by rfl, Nat.factorization_div] <;> norm_num [h_lcm, c.hn]
  · rw [Nat.factorization_eq_zero_of_not_dvd] <;> norm_num [Fin.prod_univ_three]
    norm_num [Nat.mul_mod, Nat.mod_mod, Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (c.hq 0)
      (by linarith [c.p_gt_two 0, c.q_gt_two 0])), Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (c.hq 1)
      (by linarith [c.p_gt_two 1, c.q_gt_two 1])), Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two (c.hq 2)
      (by linarith [c.p_gt_two 2, c.q_gt_two 2]))]
  · exact prod_q_dvd_L c

lemma Criterion.val_p_L' (c : Criterion) (i : Fin 3) : (c.L').factorization (c.p i) = 1 := by
  have h_pi_factor : Nat.factorization (L c.n) (c.p i) = 1 := by
    have h_prime_factor : ∀ {p : ℕ}, Nat.Prime p → Real.sqrt c.n < p → p < c.n →
        (Nat.factorization (L c.n)) p = 1 := @fun p hp hp_sqrt hp_lt_n ↦ by
      have h_prime_factor : (Nat.factorization (L c.n)) p = 1 := by
        have h_prime_factor_def : (Nat.factorization (L c.n)) p = Finset.sup (Finset.Icc 1 c.n)
            (fun i ↦ Nat.factorization i p) := by
          have h_prime_factor_def : (Nat.factorization (Finset.lcm (Finset.Icc 1 c.n) (fun i ↦ i)))
              p = Finset.sup (Finset.Icc 1 c.n) (fun i ↦ Nat.factorization i p) := by
            have h_lcm_factorization : ∀ {S : Finset ℕ}, (∀ i ∈ S, i ≠ 0) →
                (Nat.factorization (Finset.lcm S (fun i ↦ i))) p =
                Finset.sup S (fun i ↦ Nat.factorization i p) := by
              intros S hS_nonzero
              induction S using Finset.induction with
              | empty => simp [Finset.lcm]
              | insert i S hiS ih =>
                  by_cases hi : i = 0
                  · simp_all
                  simp only [lcm_insert]
                  erw [Nat.factorization_lcm] <;> simp_all
            exact h_lcm_factorization fun i hi ↦ by linarith [Finset.mem_Icc.mp hi]
          exact h_prime_factor_def
        have h_prime_power : ∀ i ∈ Finset.Icc 1 c.n, Nat.factorization i p ≤ 1 := fun i hi ↦ by
          have h_prime_power : p^2 > c.n := by
            rw [Real.sqrt_lt] at hp_sqrt <;> norm_cast at * <;> nlinarith only [hp_sqrt, hp_lt_n]
          exact le_of_not_gt fun h ↦ absurd (Nat.dvd_trans (pow_dvd_pow p h) (Nat.ordProj_dvd i p))
            (Nat.not_dvd_of_pos_of_lt (Finset.mem_Icc.mp hi |>.1)
            (by nlinarith [Finset.mem_Icc.mp hi |>.2]))
        refine h_prime_factor_def.trans (le_antisymm (Finset.sup_le h_prime_power) ?_)
        exact le_trans (by norm_num [hp]) (Finset.le_sup (f := fun i ↦ Nat.factorization i p)
          (Finset.mem_Icc.mpr ⟨hp.pos, hp_lt_n.le⟩))
      exact (Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd ((h_prime_factor.symm))) p)).symm
    apply h_prime_factor (c.hp i) (c.h_ord_1.trans_le (by
      exact_mod_cast c.hp_mono.monotone (Nat.zero_le _))) (by
        have := c.h_ord_2; have := c.h_ord_3; fin_cases i <;> linarith! [c.hp_mono <|
          show 0 < 1 by decide, c.hp_mono <| show 1 < 2 by decide, c.hq_mono <|
          show 0 < 1 by decide, c.hq_mono <| show 1 < 2 by decide])
  have h_pi_factor_L' : Nat.factorization (L c.n) (c.p i) = Nat.factorization (c.L')
      (c.p i) + Nat.factorization (∏ i, c.q i) (c.p i) := by
    have h_pi_factor_L' : Nat.factorization (L c.n) = Nat.factorization (c.L') +
        Nat.factorization (∏ i, c.q i) := by
      rw [← Nat.factorization_mul] <;> norm_num [c.L'_pos.ne']
      · rw [mul_comm, Criterion.L_eq_prod_q_mul_L']
      · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.Prime.ne_zero (c.hq i)
    aesop
  have h_pi_not_div_q : ∀ j, ¬(c.p i ∣ c.q j) := by
    intro j hj; have := c.hq j; have := c.hp i; simp_all only [Nat.prime_dvd_prime_iff_eq]
    have := c.h_ord_2; have := c.h_ord_3; fin_cases i <;> fin_cases j <;> linarith! [c.hp_mono <|
      show 0 < 1 by decide, c.hp_mono <| show 1 < 2 by decide, c.hq_mono <|
      show 0 < 1 by decide, c.hq_mono <| show 1 < 2 by decide]
  simp_all [Fin.prod_univ_three,Nat.factorization_mul,Nat.Prime.ne_zero (c.hq _),
    Nat.factorization_eq_zero_of_not_dvd (h_pi_not_div_q _)]

theorem Criterion.ln_eq (c : Criterion) : L c.n = c.q 0 * c.q 1 * c.q 2 * c.L' := by
  rw [L', ← Fin.prod_univ_three, Nat.mul_div_cancel' <| Fintype.prod_dvd_of_isRelPrime ?_ ?_]
  · refine fun i j h ↦ Nat.coprime_iff_isRelPrime.mp ?_
    exact Nat.coprime_primes (c.hq i) (c.hq j) |>.mpr <| c.hq_mono.injective.ne h
  refine fun i ↦
    Finset.dvd_lcm <| Finset.mem_Icc.mpr ⟨c.hq i |>.one_le, le_trans ?_ c.h_ord_3.le⟩
  exact c.hq_mono.monotone <| Fin.le_last i

theorem Criterion.q_not_dvd_L' (c : Criterion) : ∀ i, ¬(c.q i ∣ c.L') := by
  intro i hqi
  have hn_lt_q_sq := Real.lt_sq_of_sqrt_lt <| c.h_ord_1.trans_le <| cast_le.mpr <|
    show c.p 0 ≤ c.q i by
      grw [c.hp_mono.monotone <| Fin.zero_le 2, c.h_ord_2, c.hq_mono.monotone <| Fin.zero_le i]
  norm_cast at hn_lt_q_sq
  suffices ¬(c.q i) ^ 2 ∣ L c.n from this <| Nat.pow_two _ ▸ by
    refine mul_dvd_mul_right (Finset.dvd_prod_of_mem c.q <| Finset.mem_univ i) _ |>.trans ?_
    exact Fin.prod_univ_three c.q ▸ c.ln_eq ▸ mul_dvd_mul_left _ hqi

  set p : ℕ := c.q i
  have hp : Nat.Prime p := c.hq i

  -- 1) prime power divides binary lcm iff divides one side
  have pow_dvd_lcm_iff (a b k : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
      p ^ k ∣ Nat.lcm a b ↔ (p ^ k ∣ a ∨ p ^ k ∣ b) := by
    refine ⟨?_, by grind [dvd_trans, Nat.dvd_lcm_left, Nat.dvd_lcm_right]⟩
    grind [Prime.pow_dvd_iff_le_factorization, lcm_ne_zero, Nat.factorization_lcm, Finsupp.sup_apply]

  -- 2) prime power divides finset-lcm -> appears in some member
  have exists_mem_of_pow_dvd_finset_lcm (s : Finset ℕ) (hs_nz : ∀ x ∈ s, x ≠ 0) (k)
      (hk : 0 < k) (h : p ^ k ∣ s.lcm _root_.id) : ∃ m ∈ s, p ^ k ∣ m := by
    induction s using Finset.induction with
    | empty =>
      have := one_lt_pow hk.ne' hp.one_lt |>.trans_le <| le_of_dvd zero_lt_one h
      contradiction
    | insert a s ha ih =>
      have ha0 := hs_nz _ <| mem_insert_self a s
      have hs_nz' := (hs_nz · <| mem_insert_of_mem ·)
      have hs0 := lcm_ne_zero_iff.mpr hs_nz'
      have := (pow_dvd_lcm_iff _ _ k ha0 hs0).1 <| by simpa using! h
      rcases this with hpa | hps
      · exact ⟨a, mem_insert_self a s, hpa⟩
      · have ⟨m, hmS, hpm⟩ := ih hs_nz' hps
        exact ⟨m, mem_insert_of_mem hmS, hpm⟩

  intro hq2
  have ⟨m, hmIcc, hpm⟩ := exists_mem_of_pow_dvd_finset_lcm _ (by grind) 2 zero_lt_two hq2
  refine not_lt_of_ge ?_ hn_lt_q_sq
  refine le_trans (le_of_dvd ?_ hpm) (Finset.mem_Icc.mp hmIcc).2
  exact succ_le_iff.mp (Finset.mem_Icc.mp hmIcc).1

theorem Criterion.σnorm_ln_eq (c : Criterion) :
    σnorm (L c.n) = σnorm c.L' * ∏ i, (1 + (1 : ℝ) / c.q i) := by
  have hcop : ∀ i j, i ≠ j → (c.q i).Coprime (c.q j) := fun i j h ↦
    (coprime_primes (c.hq i) (c.hq j)).mpr (c.hq_mono.injective.ne h)
  have hcopL' : ∀ i, (c.q i).Coprime c.L' := fun i ↦
    (c.hq i).coprime_iff_not_dvd.mpr (c.q_not_dvd_L' i)
  have hσ_prime : ∀ i, sigma 1 (c.q i) = 1 + c.q i := fun i ↦ by
    rw [← pow_one (c.q i), sigma_one_apply_prime_pow (c.hq i)]
    simp [reduceAdd, geom_sum_two, pow_one, add_comm]
  simp only [σnorm, σ, c.L_eq_prod_q_mul_L', Fin.prod_univ_three]
  rw [show c.q 0 * c.q 1 * c.q 2 * c.L' = (c.q 0 * c.q 1 * c.q 2) * c.L' by ring,
      isMultiplicative_sigma.map_mul_of_coprime (coprime_mul_iff_left.mpr
        ⟨coprime_mul_iff_left.mpr ⟨hcopL' 0, hcopL' 1⟩, hcopL' 2⟩),
      show c.q 0 * c.q 1 * c.q 2 = c.q 0 * (c.q 1 * c.q 2) by ring,
      isMultiplicative_sigma.map_mul_of_coprime (coprime_mul_iff_right.mpr
        ⟨hcop 0 1 Fin.zero_ne_one, hcop 0 2 <| not_eq_of_beq_eq_false rfl⟩),
      isMultiplicative_sigma.map_mul_of_coprime (hcop 1 2 <| not_eq_of_beq_eq_false rfl),
      hσ_prime, hσ_prime, hσ_prime]
  have hq_ne : ∀ i, (c.q i : ℝ) ≠ 0 := fun i ↦ (cast_pos.mpr (c.hq i).pos).ne'
  field_simp [hq_ne, (cast_pos.mpr c.L'_pos).ne']
  grind

def Criterion.m (c : Criterion) : ℕ := (∏ i, c.q i) / (4 * ∏ i, c.p i)

def Criterion.r (c : Criterion) : ℕ := (∏ i, c.q i) % (4 * ∏ i, c.p i)

theorem Criterion.r_ge (c : Criterion) : 0 < c.r := by
  simp only [r, Nat.pos_iff_ne_zero, ne_eq]
  intro h
  have h_dvd : c.p 2 ∣ ∏ i, c.q i :=
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ 2)).trans <|
      (Nat.dvd_mul_left _ 4).trans (Nat.dvd_of_mod_eq_zero h)
  obtain ⟨i, _, hi⟩ := (c.hp 2).prime.exists_mem_finset_dvd h_dvd
  have : c.p 2 = c.q i := ((c.hq i).dvd_iff_eq (c.hp 2).ne_one).mp hi |>.symm
  exact absurd this (c.h_ord_2.trans_le (c.hq_mono.monotone (zero_le i))).ne

theorem Criterion.r_le (c : Criterion) : c.r < 4 * ∏ i, c.p i :=
  mod_lt _ <| mul_pos (zero_lt_succ 3) <| Finset.prod_pos <| fun i _ ↦ Prime.pos (c.hp i)

theorem Criterion.prod_q_eq (c : Criterion) : ∏ i, c.q i = (4 * ∏ i, c.p i) * c.m + c.r := by
  simp only [m, r, Nat.div_add_mod]

noncomputable def Criterion.M (c : Criterion) : ℕ := (4 * ∏ i, c.p i) * c.m * c.L'

lemma Criterion.m_pos (c : Criterion) : 0 < c.m :=
  Nat.div_pos c.prod_p_le_prod_q.le (mul_pos (zero_lt_succ 3) (prod_pos fun i _ ↦ (c.hp i).pos))

lemma Criterion.M_pos (c : Criterion) : 0 < c.M :=
  mul_pos (mul_pos (mul_pos (zero_lt_succ 3) (prod_pos fun i _ ↦ (c.hp i).pos)) c.m_pos) c.L'_pos

lemma Criterion.val_two_M_ge_L' (c : Criterion) : (c.M).factorization 2 ≥ (c.L').factorization 2 + 2
    := by
  rw [show c.M = (4 * ∏ i, c.p i) * c.m * c.L' from rfl, Nat.factorization_mul]
  · simp only [Fin.prod_univ_three, ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero,
      Nat.Prime.ne_zero (c.hp _), or_self, not_false_eq_true, Nat.ne_of_gt (Criterion.m_pos c),
      factorization_mul]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow]; norm_num; ring_nf;
      linarith [Nat.Prime.factorization_self (prime_two)]
  · simp only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, prod_eq_zero_iff, mem_univ,
    true_and, false_or, not_or, not_exists]
    exact ⟨fun i ↦ Nat.Prime.ne_zero (c.hp i), Nat.ne_of_gt (c.m_pos)⟩
  · exact Nat.ne_of_gt <| c.L'_pos

lemma Criterion.val_p_M_ge_two (c : Criterion) (i : Fin 3) : (c.M).factorization (c.p i) ≥ 2 := by
  have h_pi_factorization_M : (Nat.factorization (c.M)) (c.p i) =
      (Nat.factorization (4 * ∏ i, c.p i)) (c.p i) + (Nat.factorization (c.m)) (c.p i) +
      (Nat.factorization (c.L')) (c.p i) := by
    rw [show c.M = (4 * ∏ i, c.p i) * c.m * c.L' by
          exact Nat.add_zero (((4 * ∏ i, c.p i) * c.m).mul c.L'), Nat.factorization_mul,
            Nat.factorization_mul]
    iterate 3 simp [Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.Prime.ne_zero (c.hp i),
      Nat.ne_of_gt (Criterion.m_pos c)]
    · simp only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or, not_or]
      exact ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ Nat.Prime.ne_zero (c.hp i),
        Nat.ne_of_gt (c.m_pos)⟩
    · exact Nat.ne_of_gt (Criterion.L'_pos c)
  simp_all only [Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ i),
    ge_iff_le, val_p_L' c i, reduceLeDiff]
  rw [Nat.factorization_mul] <;> norm_num
  · rw [Nat.factorization_mul]
    · exact le_add_of_le_of_nonneg (le_add_of_nonneg_of_le (Nat.zero_le _)
        (Nat.one_le_iff_ne_zero.mpr <| by simp [c.hp i])) (Nat.zero_le _)
    · simp only [ne_eq, prod_eq_zero_iff, mem_sdiff, mem_univ, mem_singleton, true_and,
      not_exists, not_and]
      exact fun x hx ↦ Nat.Prime.ne_zero (c.hp x)
    · exact Nat.Prime.ne_zero (c.hp i)
  · exact ⟨Finset.prod_ne_zero_iff.mpr fun j hj ↦ Nat.Prime.ne_zero (c.hp j),
      Nat.Prime.ne_zero (c.hp i)⟩

theorem Criterion.M_lt (c : Criterion) : c.M < L c.n := by
  calc c.M < ((4 * ∏ i, c.p i) * c.m + c.r) * c.L' :=
        mul_lt_mul_of_pos_right (Nat.lt_add_of_pos_right c.r_ge) c.L'_pos
    _ = (∏ i, c.q i) * c.L' := by rw [← c.prod_q_eq]
    _ = L c.n := c.L_eq_prod_q_mul_L'.symm

theorem Criterion.Ln_div_M_gt (c : Criterion) : (1 : ℝ) < L c.n / c.M := by
  rw [one_lt_div (cast_pos.mpr c.M_pos)]
  exact_mod_cast c.M_lt

theorem Criterion.Ln_div_M_lt (c : Criterion) :
    L c.n / c.M < (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i))⁻¹ := by
  have hprod_q_pos_R : (0 : ℝ) < (∏ i, c.q i) :=
    cast_pos.mpr <| prod_pos fun i _ ↦ (c.hq i).pos
  have hLM_eq :
      (L c.n : ℝ) / c.M = ((∏ i, c.q i) : ℝ) / (((4 * ∏ i, c.p i) * c.m) : ℕ) := by
    simp only [c.L_eq_prod_q_mul_L', M, cast_mul]
    have hL'_ne : (c.L' : ℝ) ≠ 0 := cast_ne_zero.mpr c.L'_pos.ne'
    field_simp
    congr 1
    exact prod_natCast univ c.q
  have hLM_eq' : (L c.n : ℝ) / c.M = (1 - (c.r : ℝ) / (∏ i, c.q i))⁻¹ := by
    have hprod_q_eq_R : ((∏ i, c.q i) : ℝ) = ((4 * ∏ i, c.p i) * c.m : ℕ) + c.r := by
      exact_mod_cast c.prod_q_eq
    have h4pm_pos : 0 < (4 * ∏ i, c.p i) * c.m := mul_pos
      (mul_pos (by norm_num) <| prod_pos fun i _ ↦ (c.hp i).pos) c.m_pos
    rw [hLM_eq, hprod_q_eq_R]
    have hne : (((4 * ∏ i, c.p i) * c.m : ℕ) : ℝ) ≠ 0 := cast_ne_zero.mpr h4pm_pos.ne'
    have hsum_pos : (0 : ℝ) < ((4 * ∏ i, c.p i) * c.m : ℕ) + c.r := by positivity
    field_simp
    simp_all
  have h1_sub_pos : (0 : ℝ) < 1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i) := by
    rw [sub_pos, div_lt_one hprod_q_pos_R]; exact_mod_cast c.prod_p_le_prod_q
  have hsub_lt : 1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i) <
      1 - (c.r : ℝ) / (∏ i, c.q i) := by gcongr; exact_mod_cast c.r_le
  rw [hLM_eq']
  have hinv := one_div_lt_one_div_of_lt h1_sub_pos hsub_lt
  simp only [one_div] at hinv
  convert hinv using 2


theorem Criterion.not_highlyAbundant_1 (c : Criterion)
    (h : σnorm c.M * (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) ≥ σnorm (L c.n)) :
    ¬HighlyAbundant (L c.n) := by
  intro hHA
  have hM_pos : (0 : ℝ) < c.M := cast_pos.mpr c.M_pos
  have hLn_pos : (0 : ℝ) < L c.n := cast_pos.mpr c.L_pos
  have hσnorm_Ln_pos : 0 < σnorm (L c.n) := by
    rw [σnorm]; exact div_pos (cast_pos.mpr <| by rw [σ, sigma_pos_iff]; exact c.L_pos) hLn_pos
  have hprod_q_pos : (0 : ℝ) < (∏ i, c.q i) := cast_pos.mpr (prod_pos fun i _ ↦ (c.hq i).pos)
  have h1_sub_pos : (0 : ℝ) < 1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i) := by
    rw [sub_pos, div_lt_one hprod_q_pos]; exact_mod_cast c.prod_p_le_prod_q
  have h1_sub_lt : 1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i) < c.M / L c.n := by
    have hinv_lt := c.Ln_div_M_lt
    rw [lt_inv_comm₀ (div_pos hLn_pos hM_pos) h1_sub_pos, inv_div] at hinv_lt
    exact hinv_lt
  have hσM_gt : (σ c.M : ℝ) > σ (L c.n) := by
    have hσnorm_gt : σnorm c.M > σnorm (L c.n) * (L c.n / c.M) :=
      calc σnorm c.M ≥ σnorm (L c.n) / (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) := by
            rw [ge_iff_le, div_le_iff₀ h1_sub_pos]; exact h
        _ > σnorm (L c.n) / (c.M / L c.n) := by gcongr
        _ = σnorm (L c.n) * (L c.n / c.M) := by rw [div_div_eq_mul_div, mul_div_assoc]
    calc (σ c.M : ℝ) = σnorm c.M * c.M := by field_simp [σnorm]
      _ > σnorm (L c.n) * (L c.n / c.M) * c.M := by nlinarith
      _ = σ (L c.n) := by field_simp [σnorm, c.M_pos.ne']
  exact not_lt.mpr (cast_lt.mp hσM_gt).le (hHA c.M c.M_lt)


theorem Criterion.not_highlyAbundant_2 (c : Criterion)
    (h : σnorm c.M ≥ σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) *
    (1 + (3 : ℝ) / (8 * c.n))) : ¬HighlyAbundant (L c.n) := by
  refine c.not_highlyAbundant_1 ?_
  have hL'_pos : 0 < σnorm c.L' := by
    rw [σnorm]; exact div_pos (cast_pos.mpr <| by rw [σ, sigma_pos_iff]; exact c.L'_pos)
      (cast_pos.mpr c.L'_pos)
  have hR_pos : (0 : ℝ) < 1 - 4 * (∏ i, c.p i) / (∏ i, c.q i) := by
    rw [sub_pos, div_lt_one (cast_pos.mpr <| prod_pos fun i _ ↦ (c.hq i).pos)]
    exact_mod_cast c.prod_p_le_prod_q
  have hcrit : (∏ i, (1 + (1 : ℝ) / c.q i)) ≤ (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) *
      (1 + 3 / (8 * c.n)) * (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) := by
    convert c.h_crit using 3; simp only [prod_natCast]
  rw [c.σnorm_ln_eq]
  calc σnorm c.L' * ∏ i, (1 + (1 : ℝ) / c.q i)
    ≤ σnorm c.L' * ((∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) *
        (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i))) :=
          mul_le_mul_of_nonneg_left hcrit hL'_pos.le
  _ = σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) *
    (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) := by ring
  _ ≤ σnorm c.M * (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) :=
    mul_le_mul_of_nonneg_right h hR_pos.le


private lemma σnorm_ratio_ge_aux {k : ℕ} (n : ℕ) (hk : 2 ^ k ≤ n) :
    (∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i) / (∑ i ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ i) ≥
      1 + 3 / (8 * n) := by
    have h_sums : (∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i) = 2 - (1 / 2) ^ (k + 2) ∧
        (∑ i ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ i) = 2 - (1 / 2) ^ k := by
      norm_num [geom_sum_eq]; ring_nf; norm_num
    field_simp [h_sums]
    rw [h_sums.1,h_sums.2]; ring_nf; norm_num
    have h_inv : (n : ℝ)⁻¹ ≤ (1 / 2 : ℝ) ^ k := by
      simpa using inv_anti₀ (by positivity) (mod_cast hk)
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k, pow_le_pow_of_le_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (show k ≥ 0 by norm_num)]

theorem Criterion.σnorm_M_ge_σnorm_L'_mul (c : Criterion) :
    σnorm c.M ≥
      σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) := by
  have h_sigma_norm_M : (σnorm c.M) = (σnorm (c.L' : ℕ)) * (∏ p ∈ Nat.primeFactors c.M,
      ((∑ i ∈ Finset.range (Nat.factorization c.M p + 1), (1 / p : ℝ) ^ i) /
      (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) p + 1), (1 / p : ℝ) ^ i))) := by
    have h_sigma_norm_prod : ∀ {n : ℕ}, n ≠ 0 → (σnorm n : ℝ) = (∏ p ∈ Nat.primeFactors n,
        ((∑ i ∈ Finset.range (Nat.factorization n p + 1), (1 / p : ℝ) ^ i))) := by
      intro n hn_ne_zero
      have h_sigma_def : ((σ n) : ℝ) = (∏ p ∈ Nat.primeFactors n, (∑ i ∈ Finset.range
          (Nat.factorization n p + 1), (p ^ i : ℝ))) := by
        unfold σ
        have h_sigma_def : ∀ {n : ℕ}, n ≠ 0 → (Nat.divisors n).sum (fun d ↦ d) =
            ∏ p ∈ n.primeFactors, (∑ i ∈ Finset.range (Nat.factorization n p + 1), p ^ i) := by
          exact fun {n} a ↦ sum_divisors a
        convert congr_arg (( ↑ ) : ℕ → ℝ) (h_sigma_def hn_ne_zero) using 1 <;>
        norm_num [ArithmeticFunction.sigma]
      have h_sigma_def : (n : ℝ) = (∏ p ∈ Nat.primeFactors n, (p ^ (Nat.factorization n p) : ℝ)) :=
        mod_cast Eq.symm (Nat.prod_factorization_pow_eq_self hn_ne_zero)
      simp_all only [div_eq_mul_inv]
      rw [← div_eq_mul_inv, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp ↦ ?_
      field_simp
      rw [Finset.mul_sum _ _ _, ← Finset.sum_flip]
      exact Finset.sum_congr rfl fun i hi ↦ by
        rw [show ((1:ℝ) / ↑p) ^ i = 1 / ((↑p) ^ i) by simp]
        rw [mul_one_div, eq_div_iff (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <|
          Nat.pos_of_mem_primeFactors hp), ←pow_add, Nat.sub_add_cancel <|
          Finset.mem_range_succ_iff.mp hi]
    by_cases hM : c.M = 0 <;> by_cases hL' : c.L' = 0
    · simp_all
    · exact absurd hM (Nat.ne_of_gt (Criterion.M_pos c))
    · exact absurd hL' (Nat.ne_of_gt (Criterion.L'_pos c))
    · simp_all only [ne_eq, one_div, inv_pow, not_false_eq_true, prod_div_distrib]
      rw [mul_div, eq_div_iff]
      · rw [mul_comm, ← Finset.prod_subset (show c.L'.primeFactors ⊆ c.M.primeFactors from ?_)]
        · intro p hp hpn; rw [Nat.factorization_eq_zero_of_not_dvd] <;> aesop
        · intro p hp; simp_all only [mem_primeFactors, ne_eq, not_false_eq_true, and_true, true_and]
          exact dvd_trans hp.2 (by exact ⟨(4 * ∏ i, c.p i) * c.m, by rw [Criterion.M]; ring⟩)
      · exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ ne_of_gt <| Finset.sum_pos
          (fun _ _ ↦ inv_pos.mpr <| pow_pos (Nat.cast_pos.mpr <| Nat.pos_of_mem_primeFactors hp) _)
          <| by norm_num
  have h_ratio_terms (p : ℕ) (hp : p ∈ Nat.primeFactors c.M) : (∑ i ∈ Finset.range
      (Nat.factorization c.M p + 1), (1 / p : ℝ) ^ i) / (∑ i ∈ Finset.range
      (Nat.factorization (c.L' : ℕ) p + 1), (1 / p : ℝ) ^ i) ≥ if p ∈ Finset.image c.p Finset.univ
      then (1 + 1 / (p * (p + 1) : ℝ)) else if p = 2 then (1 + 3 / (8 * c.n : ℝ)) else 1 := by
    split_ifs
    · obtain ⟨i, hi⟩ : ∃ i : Fin 3, p = c.p i := by grind
      have h_ratio_p_i : (∑ i ∈ Finset.range (Nat.factorization c.M p + 1), (1 / p : ℝ) ^ i) /
          (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) p + 1), (1 / p : ℝ) ^ i) ≥
          (∑ i ∈ Finset.range 3, (1 / p : ℝ) ^ i) / (∑ i ∈ Finset.range 2, (1 / p : ℝ) ^ i) := by
        rw [show Nat.factorization (c.L' : ℕ) p = 1 from hi ▸ c.val_p_L' i]
        exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono
          (by grind [c.val_p_M_ge_two i])) fun _ _ _ ↦ by positivity)
          (Finset.sum_nonneg fun _ _ ↦ by positivity)
      convert h_ratio_p_i using 1; norm_num [Finset.sum_range_succ]; ring_nf; field_simp; grind
    · have h_geo_series : (∑ i ∈ Finset.range (Nat.factorization c.M 2 + 1), (1 / 2 : ℝ) ^ i)
          / (∑ i ∈ Finset.range (Nat.factorization c.L' 2 + 1), (1 / 2 : ℝ) ^ i) ≥
          (1 + 3 / (8 * c.n : ℝ)) := by
        have h_geo_series : (∑ i ∈ Finset.range (Nat.factorization c.M 2 + 1), (1 / 2 : ℝ) ^ i)
            / (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) 2 + 1), (1 / 2 : ℝ) ^ i) ≥
            (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) 2 + 3), (1 / 2 : ℝ) ^ i) /
            (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) 2 + 1), (1 / 2 : ℝ) ^ i) := by
          exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (by linarith [val_two_M_ge_L' c])) fun _ _ _ ↦ by positivity)
            (Finset.sum_nonneg fun _ _ ↦ by positivity)
        refine le_trans ?_ h_geo_series
        convert σnorm_ratio_ge_aux c.n _ using 1
        exact c.val_two_L'.symm ▸ Nat.pow_log_le_self 2 (by linarith [c.hn])
      aesop
    · rw [ge_iff_le, le_div_iff₀] <;> norm_num
      · refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ ?_))
          fun ?_ ?_ ?_ ↦ by positivity
        have h_div : c.L' ∣ c.M := by
          exact dvd_mul_left _ _
        exact (Nat.factorization_le_iff_dvd (by aesop) (by aesop)) |>.2 h_div p
      · exact Finset.sum_pos (fun _ _ ↦ inv_pos.mpr (pow_pos (Nat.cast_pos.mpr
          (Nat.pos_of_mem_primeFactors hp)) _)) (by norm_num)
  have h_prod_ratio_terms : (∏ p ∈ Nat.primeFactors c.M,
      ((∑ i ∈ Finset.range (Nat.factorization c.M p + 1), (1 / p : ℝ) ^ i) /
      (∑ i ∈ Finset.range (Nat.factorization (c.L' : ℕ) p + 1), (1 / p : ℝ) ^ i))) ≥
      (∏ p ∈ Finset.image c.p Finset.univ, (1 + 1/(p * (p + 1) : ℝ)))*(1 + 3 / (8 * c.n : ℝ)) := by
    refine le_trans ?_ (Finset.prod_le_prod ?_ h_ratio_terms)
    · rw [Finset.prod_ite]
      refine mul_le_mul ?_ ?_ (by positivity) (Finset.prod_nonneg fun _ _ ↦ by positivity)
      · rw [Finset.prod_subset]
        · simp only [mem_image, mem_univ, true_and, subset_iff, mem_filter, mem_primeFactors,
            forall_exists_index, forall_apply_eq_imp_iff, exists_apply_eq_apply, and_true]
          intro i; exact ⟨c.hp i, by
            exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
              (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) _) _) _, by
              exact Nat.ne_of_gt (Criterion.M_pos c)⟩
        · aesop
      · rw [Finset.prod_ite]
        by_cases h : 2 ∈ c.M.primeFactors <;> simp_all +decide only
          [mem_primeFactors, true_and, prod_const]
        · simp only [one_pow, mul_one]
          refine le_self_pow₀ (M₀ := ℝ) (by norm_num ; positivity) ?_
          · norm_num; exact ⟨2, Nat.prime_two, h.1, h.2, fun i ↦ by linarith [c.p_gt_two i], rfl⟩
        · contrapose! h
          refine ⟨dvd_mul_of_dvd_left ?_ _, Nat.ne_of_gt (Criterion.M_pos c)⟩
          · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by decide) _) _
    · intro p hp; split_ifs <;> positivity
  simp_all
  rw [Finset.prod_image] at h_prod_ratio_terms <;> norm_num [Finset.prod_range_succ] at *
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h_prod_ratio_terms <|
      show 0 ≤ σnorm c.L' by exact div_nonneg (Nat.cast_nonneg _) <| Nat.cast_nonneg _
  · simp [c.hp_mono.injective]




theorem Criterion.not_highlyAbundant (c : Criterion) : ¬HighlyAbundant (L c.n) :=
  c.not_highlyAbundant_2 c.σnorm_M_ge_σnorm_L'_mul



/-! ## The threshold, abstracted

`Lcm.v1` fixes `X₀ = 89693` and uses `11.4` as a lower bound for `log X₀`. Here both are
parameters: `X₀` is arbitrary, and `c` is any lower bound for `log X₀` with `5 ≤ c`.

`c` is used for exactly one thing -- bounding the relative gap `ε = 1/(log √n)³ ≤ 1/c³` -- so the
strategy is to convert `5 ≤ c` into the concrete bound `ε ≤ 1/125` once, and `5 ≤ log X₀` into
`148 < X₀` once, and then run the numerical endgame on those two rationals. That keeps the final
comparisons `nlinarith` problems over concrete numbers, exactly as in `v1`, rather than symbolic
ones. The margin is large: at `c = 5` the comparison closes with the `ε` coefficients `3.048` and
`3.232`, so the bound could be loosened considerably before anything breaks.

### A junk value, and where positivity really comes from

`c ≤ log X₀` does **not** give `0 < X₀`. `Real.log` of a negative number is `log |x|`, so
`log (-1000) ≈ 6.9` satisfies the hypothesis quite happily. The positivity the argument needs comes
instead from the prime-gap hypothesis: `logPower X₀ 3` applied at `x = 0` would demand a prime in
`(0, 0]`, so it is false for any `X₀ ≤ 0`. Deriving `0 < X₀` from `hd` rather than from `hcX` is
the difference between a proof and a proof of something vacuous.
-/

section Abstract

variable {c X₀ : ℝ}

/-- `0 < X₀`, from the prime-gap hypothesis rather than from `c ≤ log X₀` -- see the note above. -/
lemma X₀_pos (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) : 0 < X₀ := by
  by_contra h
  push_neg at h
  obtain ⟨p, hp, hp_lb, hp_ub⟩ := hd 0 h
  simp only [Real.log_zero, zero_div, add_zero] at hp_ub
  exact absurd (hp_lb.trans_le hp_ub) (lt_irrefl _)

lemma exp_five_le (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3)
    (hc : 5 ≤ c) (hcX : c ≤ Real.log X₀) : Real.exp 5 ≤ X₀ :=
  calc Real.exp 5 ≤ Real.exp (Real.log X₀) := Real.exp_le_exp.mpr (hc.trans hcX)
    _ = X₀ := Real.exp_log (X₀_pos hd)

/-- `X₀ > 148`, from `log X₀ ≥ 5` and `e > 2.7182818283`.  Every place `v1` used a property of the
literal `89693` -- that it exceeds 2, that `1/X₀` is small -- is served by this. -/
lemma X₀_gt (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3)
    (hc : 5 ≤ c) (hcX : c ≤ Real.log X₀) : (148 : ℝ) < X₀ := by
  refine lt_of_lt_of_le ?_ (exp_five_le hd hc hcX)
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, ← Real.exp_one_pow]
  grw [← Real.exp_one_gt_d9]
  norm_num

variable {n : ℕ}

lemma hsqrt_ge (hn : X₀ ^ 2 ≤ (n : ℝ)) : X₀ ≤ √(n : ℝ) :=
  Real.le_sqrt_of_sq_le hn

/-- `√n > 148`: the workhorse.  `v1` wrote `√n ≥ 89693` and used it for everything numerical. -/
lemma hsqrt_gt (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) (hc : 5 ≤ c)
    (hcX : c ≤ Real.log X₀) (hn : X₀ ^ 2 ≤ (n : ℝ)) : (148 : ℝ) < √(n : ℝ) :=
  lt_of_lt_of_le (X₀_gt hd hc hcX) (hsqrt_ge hn)

lemma hn_gt (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) (hc : 5 ≤ c)
    (hcX : c ≤ Real.log X₀) (hn : X₀ ^ 2 ≤ (n : ℝ)) : (148 : ℝ) ^ 2 < (n : ℝ) := by
  have h := hsqrt_gt hd hc hcX hn
  have hsq : √(n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg ((n : ℝ))]

lemma n_pos (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) (hc : 5 ≤ c)
    (hcX : c ≤ Real.log X₀) (hn : X₀ ^ 2 ≤ (n : ℝ)) : 0 < n := by
  have h := hn_gt hd hc hcX hn
  have : (0 : ℝ) < (n : ℝ) := by nlinarith
  exact_mod_cast this

/-- `log √n ≥ c`.  The one thing `c` is for. -/
lemma hlog (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) (hc : 5 ≤ c)
    (hcX : c ≤ Real.log X₀) (hn : X₀ ^ 2 ≤ (n : ℝ)) : c ≤ log √(n : ℝ) :=
  hcX.trans (log_le_log (X₀_pos hd) (hsqrt_ge hn))

lemma hlog_pos (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) (hc : 5 ≤ c)
    (hcX : c ≤ Real.log X₀) (hn : X₀ ^ 2 ≤ (n : ℝ)) : 0 < log √(n : ℝ) :=
  lt_of_lt_of_le (by linarith) (hlog hd hc hcX hn)

/-- The relative gap bound, converted to a concrete rational once and for all.

This is `v1`'s `inv_cube_log_sqrt_le`, which read `≤ 0.000675` because it was working from
`log √n ≥ 11.4`.  From `log √n ≥ 5` the same computation gives `≤ 1/125`. -/
lemma hgap (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) (hc : 5 ≤ c)
    (hcX : c ≤ Real.log X₀) (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    1 / (log √(n : ℝ)) ^ 3 ≤ 1 / 125 := by
  have h5 : (5 : ℝ) ≤ log √(n : ℝ) := le_trans hc (hlog hd hc hcX hn)
  have hcube : (125 : ℝ) ≤ (log √(n : ℝ)) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) h5 3
    norm_num at h
    linarith
  exact one_div_le_one_div_of_le (by norm_num) hcube

lemma hε_pos (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) (hc : 5 ≤ c)
    (hcX : c ≤ Real.log X₀) (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    0 < 1 + 1 / (log √(n : ℝ)) ^ 3 := by
  have := hlog_pos hd hc hcX hn
  positivity

section Gap

variable (hd : IEANTN.HasPrimeInInterval.logPower X₀ 3) (hc : 5 ≤ c) (hcX : c ≤ Real.log X₀)

include hd hc hcX in
theorem exists_p_primes (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i, p i ≤ √(n : ℝ) * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0 := by
  let x := √(n : ℝ)
  have hx_pos : 0 < x := (X₀_pos hd).trans_le (hsqrt_ge hn)
  have hlog_pos : 0 < log x := hlog_pos hd hc hcX hn
  set ε := 1 / (log x) ^ 3 with hε_def
  have upper {y : ℝ} (hy : 0 < y) (hlog_ge : log y ≥ log x) {p : ℕ}
      (hp : (p : ℝ) ≤ y + y / (log y) ^ (3 : ℝ)) : (p : ℝ) ≤ y * (1 + ε) := by
    have h : y / (log y) ^ (3 : ℝ) ≤ y / (log x) ^ (3 : ℝ) :=
      div_le_div_of_nonneg_left hy.le (rpow_pos_of_pos hlog_pos 3)
        (rpow_le_rpow hlog_pos.le hlog_ge (by grind))
    calc (p : ℝ) ≤ y + y / (log y) ^ (3 : ℝ) := hp
      _ ≤ y + y / (log x) ^ (3 : ℝ) := add_le_add_right h y
      _ = y * (1 + ε) := by simp only [hε_def, ← rpow_natCast]; grind
  have hε_pos : 0 < ε := by positivity
  have hx1_ge : x * (1 + ε) ≥ X₀ := (hsqrt_ge hn).trans (le_mul_of_one_le_right hx_pos.le
    (by grind))
  have hx2_ge : x * (1 + ε) ^ 2 ≥ X₀ := (hsqrt_ge hn).trans (le_mul_of_one_le_right hx_pos.le
    (by nlinarith [sq_nonneg ε]))
  obtain ⟨p₀, hp₀_prime, hp₀_lb, hp₀_ub⟩ := hd x (hsqrt_ge hn)
  obtain ⟨p₁, hp₁_prime, hp₁_lb, hp₁_ub⟩ := hd _ hx1_ge
  obtain ⟨p₂, hp₂_prime, hp₂_lb, hp₂_ub⟩ := hd _ hx2_ge
  have hp₀_ub' : (p₀ : ℝ) ≤ x * (1 + ε) := upper hx_pos le_rfl hp₀_ub
  have hp₁_ub' : (p₁ : ℝ) ≤ x * (1 + ε) ^ 2 := by
    linarith [sq (1 + ε), upper (by grind) (log_le_log hx_pos (by grind)) hp₁_ub]
  have hp₂_ub' : (p₂ : ℝ) ≤ x * (1 + ε) ^ 3 := by
    linarith [pow_succ (1 + ε) 2, upper (by grind) (log_le_log hx_pos (by grind)) hp₂_ub]
  refine ⟨![p₀, p₁, p₂], fun i ↦ by fin_cases i <;> assumption,
    Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
      fin_cases i
      · exact cast_lt.mp (hp₀_ub'.trans_lt hp₁_lb)
      · exact cast_lt.mp (hp₁_ub'.trans_lt hp₂_lb), fun i ↦ ?_, hp₀_lb⟩
  fin_cases i <;> norm_num
  · convert hp₀_ub' using 2
  · convert hp₁_ub' using 2
  · convert hp₂_ub' using 2

include hd hc hcX in
theorem exists_q_primes (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3, n * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (-((3 : ℝ) - (i : ℕ))) ≤ q i) ∧
      q 2 < n := by
  let x := √(n : ℝ)
  have hx_pos : 0 < x := (X₀_pos hd).trans_le (hsqrt_ge hn)
  have hlog_pos : 0 < log x := hlog_pos hd hc hcX hn
  set ε := 1 / (log x) ^ 3 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h1ε_pos : 0 < 1 + ε := by linarith
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast n_pos hd hc hcX hn
  have hn_eq_x2 : (n : ℝ) = x ^ 2 := (sq_sqrt hn_pos.le).symm
  have hX₀_gt : (148 : ℝ) < X₀ := X₀_gt hd hc hcX
  -- ε is small: this is where `5 ≤ c` enters, and the only place it does.
  have hε_small : ε ≤ 1 / 125 := hgap hd hc hcX hn
  have h1ε3_pos : 0 < (1 + ε) ^ 3 := by positivity
  have h1ε2_pos : 0 < (1 + ε) ^ 2 := by positivity
  have h1ε3_le_2 : (1 + ε) ^ 3 ≤ 2 := by nlinarith [hε_pos, hε_small]
  -- Define y_i = n / (1 + ε)^(3-i), and show y_i ≥ X₀
  have hy₀_ge : n / (1 + ε) ^ 3 ≥ X₀ := by
    calc n / (1 + ε) ^ 3 = x ^ 2 / (1 + ε) ^ 3 := by rw [hn_eq_x2]
      _ ≥ x ^ 2 / 2 := div_le_div_of_nonneg_left (sq_nonneg x) (by grind) h1ε3_le_2
      _ ≥ X₀ ^ 2 / 2 := by
        apply div_le_div_of_nonneg_right (by nlinarith [hsqrt_ge hn, X₀_pos hd])
        norm_num
      _ ≥ X₀ := by nlinarith [X₀_pos hd]
  have h1ε2_le_1ε3 : (1 + ε) ^ 2 ≤ (1 + ε) ^ 3 := by nlinarith [sq_nonneg ε]
  have h1ε_le_1ε2 : 1 + ε ≤ (1 + ε) ^ 2 := by nlinarith [sq_nonneg ε]
  have hy₁_ge : n / (1 + ε) ^ 2 ≥ X₀ := le_trans hy₀_ge
    (div_le_div_of_nonneg_left hn_pos.le h1ε2_pos h1ε2_le_1ε3)
  have hy₂_ge : n / (1 + ε) ≥ X₀ := le_trans hy₁_ge
    (div_le_div_of_nonneg_left hn_pos.le h1ε_pos h1ε_le_1ε2)
  obtain ⟨q₀, hq₀_prime, hq₀_lb, hq₀_ub⟩ := hd (n / (1 + ε) ^ 3) hy₀_ge
  obtain ⟨q₁, hq₁_prime, hq₁_lb, hq₁_ub⟩ := hd (n / (1 + ε) ^ 2) hy₁_ge
  obtain ⟨q₂, hq₂_prime, hq₂_lb, hq₂_ub⟩ := hd (n / (1 + ε)) hy₂_ge
  have hx_ge_2 : x ≥ 2 := by linarith [hsqrt_gt hd hc hcX hn]
  have hy₀_ge_x : n / (1 + ε) ^ 3 ≥ x := by
    calc n / (1 + ε) ^ 3 = x ^ 2 / (1 + ε) ^ 3 := by rw [hn_eq_x2]
      _ ≥ x ^ 2 / 2 := div_le_div_of_nonneg_left (sq_nonneg x) (by grind) h1ε3_le_2
      _ ≥ x := by rw [ge_iff_le, le_div_iff₀' (by norm_num : (0 : ℝ) < 2)]; nlinarith
  have hy₁_ge_x : n / (1 + ε) ^ 2 ≥ x := le_trans hy₀_ge_x
    (div_le_div_of_nonneg_left hn_pos.le h1ε2_pos h1ε2_le_1ε3)
  have hy₂_ge_x : n / (1 + ε) ≥ x := le_trans hy₁_ge_x
    (div_le_div_of_nonneg_left hn_pos.le h1ε_pos h1ε_le_1ε2)
  have upper {y : ℝ} (hy_pos : 0 < y) (hy_ge : y ≥ x) {q : ℕ}
      (hq : (q : ℝ) ≤ y + y / (log y) ^ (3 : ℝ)) : (q : ℝ) ≤ y * (1 + ε) := by
    have hlog_ge : log y ≥ log x := log_le_log hx_pos hy_ge
    have h : y / (log y) ^ (3 : ℝ) ≤ y / (log x) ^ (3 : ℝ) :=
      div_le_div_of_nonneg_left hy_pos.le (rpow_pos_of_pos hlog_pos 3)
        (rpow_le_rpow hlog_pos.le hlog_ge (by grind))
    calc (q : ℝ) ≤ y + y / (log y) ^ (3 : ℝ) := hq
      _ ≤ y + y / (log x) ^ (3 : ℝ) := add_le_add_right h y
      _ = y * (1 + ε) := by simp only [hε_def, ← rpow_natCast]; field_simp; ring_nf
  have hq₀_ub' : (q₀ : ℝ) ≤ n / (1 + ε) ^ 2 := by
    have := upper (by positivity) hy₀_ge_x hq₀_ub
    calc (q₀ : ℝ) ≤ (n / (1 + ε) ^ 3) * (1 + ε) := this
      _ = n / (1 + ε) ^ 2 := by field_simp
  have hq₁_ub' : (q₁ : ℝ) ≤ n / (1 + ε) := by
    have := upper (by positivity) hy₁_ge_x hq₁_ub
    calc (q₁ : ℝ) ≤ (n / (1 + ε) ^ 2) * (1 + ε) := this
      _ = n / (1 + ε) := by field_simp
  have hq₂_ub' : (q₂ : ℝ) ≤ n := by
    have := upper (by positivity) hy₂_ge_x hq₂_ub
    calc (q₂ : ℝ) ≤ (n / (1 + ε)) * (1 + ε) := this
      _ = n := by field_simp
  have hq₀_lt_q₁ : q₀ < q₁ := Nat.cast_lt.mp (hq₀_ub'.trans_lt hq₁_lb)
  have hq₁_lt_q₂ : q₁ < q₂ := Nat.cast_lt.mp (hq₁_ub'.trans_lt hq₂_lb)
  have hq₂_lt_n : q₂ < n := by
    have hy₂_pos : 0 < (n : ℝ) / (1 + ε) := by positivity
    have hy₂_lt_n : n / (1 + ε) < n := div_lt_self hn_pos (by linarith)
    have hlog_y₂_pos : 0 < log (n / (1 + ε)) := log_pos (by linarith : 1 < (n : ℝ) / (1 + ε))
    have hx_lt_y₂ : x < n / (1 + ε) := by
      have h1ε_lt_1ε3 : (1 + ε) < (1 + ε) ^ 3 := by nlinarith [sq_nonneg ε, sq_nonneg (1 + ε)]
      have h1 : n / (1 + ε) ^ 3 < n / (1 + ε) :=
        div_lt_div_of_pos_left hn_pos h1ε_pos h1ε_lt_1ε3
      calc x ≤ n / (1 + ε) ^ 3 := hy₀_ge_x
        _ < n / (1 + ε) := h1
    have hlog_y₂_gt : log (n / (1 + ε)) > log x := log_lt_log hx_pos hx_lt_y₂
    have hq₂_strict : (q₂ : ℝ) < n := by
      calc (q₂ : ℝ) ≤ n / (1 + ε) + (n / (1 + ε)) / (log (n / (1 + ε))) ^ 3 := hq₂_ub
        _ = (n / (1 + ε)) * (1 + 1 / (log (n / (1 + ε))) ^ 3) := by
            have hpos : (0 : ℝ) < log (n / (1 + ε)) := hlog_y₂_pos
            field_simp [hpos.ne']
            rw [mul_comm]
            norm_cast
        _ < (n / (1 + ε)) * (1 + 1 / (log x) ^ 3) := by
          apply mul_lt_mul_of_pos_left _ hy₂_pos
          gcongr
        _ = (n / (1 + ε)) * (1 + ε) := by simp only [hε_def]
        _ = n := by field_simp
    exact Nat.cast_lt.mp hq₂_strict
  refine ⟨![q₀, q₁, q₂], fun i ↦ by fin_cases i <;> assumption,
    Fin.strictMono_iff_lt_succ.mpr fun i ↦ by fin_cases i <;> assumption,
    fun i ↦ ?_, hq₂_lt_n⟩
  fin_cases i <;> simp only [hε_def]
  · simp only [CharP.cast_eq_zero, sub_zero]
    have heq : (n : ℝ) * (1 + 1 / (log x) ^ 3) ^ (-(3 : ℝ)) = n / (1 + ε) ^ 3 := by
      rw [rpow_neg h1ε_pos.le, div_eq_mul_inv]
      norm_cast
    rw [heq]
    exact hq₀_lb.le
  · simp only [Nat.cast_one]
    have heq : (n : ℝ) * (1 + 1 / (log x) ^ 3) ^ (-(3 - 1 : ℝ)) = n / (1 + ε) ^ 2 := by
      have h1 : -(3 - 1 : ℝ) = -2 := by ring
      rw [h1, rpow_neg h1ε_pos.le, div_eq_mul_inv]
      norm_cast
    rw [heq]
    exact hq₁_lb.le
  · simp only [Nat.cast_ofNat]
    have heq : (n : ℝ) * (1 + 1 / (log x) ^ 3) ^ (-(3 - 2 : ℝ)) = n / (1 + ε) := by
      have h1 : -(3 - 2 : ℝ) = -1 := by ring
      rw [h1, rpow_neg h1ε_pos.le, rpow_one, div_eq_mul_inv]
    rw [heq]
    exact hq₂_lb.le


theorem prod_q_ge (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    ∏ i, (1 + (1 : ℝ) / (exists_q_primes hd hc hcX hn).choose i) ≤
      ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((i : ℕ) + 1 : ℝ) / n) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast n_pos hd hc hcX hn
  rw [show ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((i : ℕ) + 1 : ℝ) / n) =
      ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n) by
    simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]; ring_nf]
  apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
  intro i _
  suffices h : (1 : ℝ) / (exists_q_primes hd hc hcX hn).choose i ≤
      (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n from (by linarith)
  have := (exists_q_primes hd hc hcX hn).choose_spec.2.2.1 i
  rw [show (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) / n =
      1 / (n / (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((3 : ℝ) - (i : ℕ)) ) by field_simp]
  have f0 : (0 : ℝ) < (log √(n : ℝ)) ^ 3 := by positivity [hlog_pos hd hc hcX hn]
  apply one_div_le_one_div_of_le
  · exact div_pos hnp (rpow_pos_of_pos (hε_pos hd hc hcX hn) _)
  · convert! this using 1
    field_simp
    rw [← rpow_add (hε_pos hd hc hcX hn)]
    simp

theorem prod_p_ge (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    ∏ i, (1 + (1 : ℝ) /
        ((exists_p_primes hd hc hcX hn).choose i *
          ((exists_p_primes hd hc hcX hn).choose i + 1))) ≥
      ∏ i : Fin 3,
        (1 + 1 / ((1 + 1 / (log √(n : ℝ)) ^ 3) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))) := by
  have hlp := hlog_pos hd hc hcX hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast n_pos hd hc hcX hn
  refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
  set p := (exists_p_primes hd hc hcX hn).choose
  have h₀ (i) : √n < p i := by
    have : p 0 ≤ p i := by
      apply (exists_p_primes hd hc hcX hn).choose_spec.2.1.monotone
      simp
    grw [← this]
    exact (exists_p_primes hd hc hcX hn).choose_spec.2.2.2
  gcongr 1 + 1 / ?_
  · have := ((exists_p_primes hd hc hcX hn).choose_spec.1 i).pos
    positivity
  have : p i ≤ √n * (1 + 1 / log √n ^ 3) ^ (i + 1 : ℝ) :=
    (exists_p_primes hd hc hcX hn).choose_spec.2.2.1 i
  have h₁ : p i ^ 2 ≤ n * (1 + 1 / log √n ^ 3) ^ (2 * i + 2 : ℝ) := by
    grw [this, mul_pow, sq_sqrt (by simp)]
    norm_cast
    rw [← pow_mul]
    grind
  have h₂ : p i + 1 ≤ p i * (1 / n * (n + √n)) := by
    field_simp [this, hnp.ne']
    linear_combination √n * h₀ i - sq_sqrt (cast_nonneg n)
  grw [h₂, ← mul_assoc, ← sq, h₁]
  field_simp [hnp.ne']
  all_goals norm_num

theorem pq_ratio_ge (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    1 - ((4 : ℝ) * ∏ i, ((exists_p_primes hd hc hcX hn).choose i : ℝ))
    / ∏ i, ((exists_q_primes hd hc hcX hn).choose i : ℝ) ≥
    1 - 4 * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ 12 / n ^ (3 / 2 : ℝ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast n_pos hd hc hcX hn
  have hep := hε_pos hd hc hcX hn
  have l1 : ((1 + 1 / Real.log √n ^ 3) ^ 12 / n ^ (3 / 2 : ℝ)) =
    (n ^ (3 / 2 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ 6) /
    (n ^ (3 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ (- 6 : ℝ)) := by
    rw [rpow_neg hep.le, ← div_eq_mul_inv, div_div_eq_mul_div, mul_assoc,
      mul_comm, ← rpow_natCast, ← rpow_natCast (n := 6), ← rpow_add hep,
      ← div_div_eq_mul_div]
    · congr
      · grind
      · rw [← rpow_sub (by positivity)]; grind
  have l2 : n ^ (3 / 2 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ 6 = ∏ i : Fin 3,
    √n * (1 + 1 / Real.log √n ^ 3) ^ ((i : ℝ) + 1) := by
    rw [← Finset.pow_card_mul_prod, Fin.prod_univ_three, ← rpow_add hep,
      ← rpow_add hep, rpow_div_two_eq_sqrt _ (by positivity)]
    norm_num
  have l3 : n ^ (3 : ℝ) * (1 + 1 / Real.log √n ^ 3) ^ (- 6 : ℝ) =
    ∏ i : Fin 3, n * (1 + 1 / Real.log √n ^ 3) ^ (-((3 : ℝ) - i.1))  := by
    rw [← Finset.pow_card_mul_prod, Fin.prod_univ_three, ← rpow_add hep,
      ← rpow_add hep]
    norm_num
  rw [← mul_div_assoc', ← mul_div_assoc', l1, l2, l3]
  gcongr
  all_goals first
    | exact (exists_p_primes hd hc hcX hn).choose_spec.2.2.1 _
    | exact (exists_q_primes hd hc hcX hn).choose_spec.2.2.1 _
    | exact Finset.prod_nonneg fun _ _ => by positivity
    | exact Finset.prod_pos fun _ _ => by positivity
    | (intro _ _; positivity)
    | positivity

/-! ### The numerical endgame

`v1` ran these with `0.000675` (from `log √n ≥ 11.4`) and `89693`.  Here they run with `1/125`
(from `log √n ≥ 5`) and `148` (from `log X₀ ≥ 5`), which are the worst cases the hypotheses allow.
The coefficients of `ε` come out at `3.048` and `3.232`, so the comparison closes with room. -/

include hd hc hcX in
theorem inv_n_pow_3_div_2_le (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    1 / ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (148 : ℝ)) * (1 / (n : ℝ)) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast n_pos hd hc hcX hn
  have hs := (hsqrt_gt hd hc hcX hn).le
  rw [one_div_mul_one_div, one_div_le_one_div (rpow_pos_of_pos hnp _)
    (mul_pos (by norm_num) hnp), show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      rpow_add hnp, rpow_one, mul_comm, ← sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left hs hnp.le

include hd hc hcX in
theorem inv_n_add_sqrt_ge (hn : X₀ ^ 2 ≤ (n : ℝ)) :
    1 / ((n : ℝ) + √(n : ℝ)) ≥ (1 / (1 + 1 / (148 : ℝ))) * (1 / (n : ℝ)) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast n_pos hd hc hcX hn
  have hs := (hsqrt_gt hd hc hcX hn).le
  have hsq : √(n : ℝ) ^ 2 = (n : ℝ) := sq_sqrt hnp.le
  have hsp : (0 : ℝ) < √(n : ℝ) := by positivity
  rw [ge_iff_le, one_div_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hs, hsq, hsp]

theorem prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (148 ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + (1.008 : ℝ) ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.05 * ε + 3.1 * ε ^ 2 + 1.05 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith [hε.1, hε.2]

theorem prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (148 ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / ((1.008 : ℝ) ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1 / 148)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * (1.008 : ℝ) ^ 12 / 148 * ε) ≥
      1 + 3.2 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]
  nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4, hε.1, hε.2]

theorem final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (148 ^ 2 : ℝ)) :
    1 + 3.05 * ε + 3.1 * ε ^ 2 + 1.05 * ε ^ 3 ≤ 1 + 3.2 * ε - 0.01 * ε ^ 2 := by
  nlinarith [hε.1, hε.2]

include hd hc hcX in
noncomputable def Criterion.mk' (hn : X₀ ^ 2 ≤ (n : ℝ)) : Criterion where
  n := n
  p := (exists_p_primes hd hc hcX hn).choose
  q := (exists_q_primes hd hc hcX hn).choose
  hn := n_pos hd hc hcX hn
  hp := (exists_p_primes hd hc hcX hn).choose_spec.1
  hp_mono := (exists_p_primes hd hc hcX hn).choose_spec.2.1
  hq := (exists_q_primes hd hc hcX hn).choose_spec.1
  hq_mono := (exists_q_primes hd hc hcX hn).choose_spec.2.1
  h_ord_1 := (exists_p_primes hd hc hcX hn).choose_spec.2.2.2
  h_ord_2 := by
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast n_pos hd hc hcX hn
    have hp' : ((exists_p_primes hd hc hcX hn).choose 2 : ℝ) ≤
        √n * (1 + 1 / (log √n) ^ 3) ^ 3 := by
      convert (exists_p_primes hd hc hcX hn).choose_spec.2.2.1 2 using 2; norm_cast
    have hq' : (n : ℝ) * (1 + 1 / (log √n) ^ 3) ^ (-3 : ℝ) ≤
        (exists_q_primes hd hc hcX hn).choose 0 := by
      convert (exists_q_primes hd hc hcX hn).choose_spec.2.2.1 0 using 2
      norm_num
    have hε_pos := hε_pos hd hc hcX hn
    have hgap := hgap hd hc hcX hn
    have hmid :
        √n * (1 + 1 / (log √n) ^ 3) ^ 3 < (n : ℝ) * (1 + 1 / (log √n) ^ 3) ^ (-3 : ℝ) := by
      norm_cast
      norm_num [rpow_neg_one] at *
      rw [← div_eq_mul_inv, lt_div_iff₀ <| pow_pos hε_pos 3]
      have h6 : (1 + ((log √n) ^ 3)⁻¹) ^ 6 < 2 := by
        have hle : (1 + ((log √(n : ℝ)) ^ 3)⁻¹) ≤ 1 + 1 / 125 := by
          have : ((log √(n : ℝ)) ^ 3)⁻¹ ≤ 1 / 125 := by simpa [one_div] using hgap
          linarith
        calc (1 + ((log √n) ^ 3)⁻¹) ^ 6 ≤ (1 + 1 / 125 : ℝ) ^ 6 := by gcongr
          _ < 2 := by norm_num
      nlinarith [mul_self_sqrt (Nat.cast_nonneg n), hsqrt_gt hd hc hcX hn]
    exact_mod_cast hp'.trans_lt <| hmid.trans_le hq'
  h_ord_3 := (exists_q_primes hd hc hcX hn).choose_spec.2.2.2
  h_crit := by
    have hnp : (0 : ℝ) < n := by exact_mod_cast n_pos hd hc hcX hn
    have hngt := hn_gt hd hc hcX hn
    have hn₀ : 0 ≤ Real.log √(n : ℝ) := (hlog_pos hd hc hcX hn).le
    have h₁ : 1 - (4 : ℝ) *
        (∏ i, (exists_p_primes hd hc hcX hn).choose i : ℝ) /
          ∏ i, ((exists_q_primes hd hc hcX hn).choose i : ℝ) ≥
        1 - 4 * (1 + 1 / 125 : ℝ) ^ 12 * ((1 / 148) * (1 / n)) := by
      grw [pq_ratio_ge hd hc hcX hn, hgap hd hc hcX hn,
        ← inv_n_pow_3_div_2_le hd hc hcX hn]
      simp [field]
    have hnn : 0 ≤ 1 - 4 * (1 + 1 / 125 : ℝ) ^ 12 * ((1 / 148) * (1 / n)) := by
      have : (1 : ℝ) / n ≤ 1 / 148 ^ 2 := by
        rw [div_le_div_iff₀ hnp (by norm_num)]; linarith
      nlinarith
    have := hnn.trans h₁
    have hn' : (0 : ℝ) ≤ 1 / (n : ℝ) ∧ (1 : ℝ) / (n : ℝ) ≤ 1 / 148 ^ 2 :=
      ⟨by positivity, by rw [div_le_div_iff₀ hnp (by norm_num)]; linarith⟩
    grw [prod_q_ge hd hc hcX hn, prod_p_ge hd hc hcX hn, h₁]
    simp_rw [div_eq_mul_one_div (_ ^ (_ : ℝ) : ℝ) (n : ℝ),
      show 3 / (8 * (n : ℝ)) = 3 / 8 * (1 / n) by field_simp, ← one_div_mul_one_div]
    grw [hgap hd hc hcX hn, inv_n_add_sqrt_ge hd hc hcX hn]
    set ε : ℝ := 1 / (n : ℝ)
    calc
      _ ≤ ∏ i : Fin 3, (1 + (1 + 1 / 125 : ℝ) ^ (i + 1 : ℝ) * ε) := by gcongr
      _ = ∏ i : Fin 3, (1 + (1.008 : ℝ) ^ (i + 1 : ℝ) * ε) := by norm_num
      _ ≤ _ := (prod_epsilon_le (ε := ε) hn')
      _ ≤ _ := final_comparison hn'
      _ ≤ _ := by
        grw [← prod_epsilon_ge hn']
        apply le_of_eq
        simp [field]
        ring_nf

include hd hc hcX in
/-- **The generalised result.**  `Lcm.v1` is the instance `c = 11.4`, `X₀ = 89693`. -/
theorem L_not_HA_of_ge (n : ℕ) (hn : X₀ ^ 2 ≤ (n : ℝ)) : ¬HighlyAbundant (L n) :=
  (Criterion.mk' hd hc hcX hn).not_highlyAbundant

end Gap

end Abstract


theorem L_eq_prod (n : ℕ) :
    L n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      p ^ ⌊Real.log n / Real.log p⌋₊ := Nat.lcmUpto_eq_prod_pow_floor n

theorem psi_eq_prod (n : ℕ) :
    Chebyshev.psi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      ⌊Real.log n / Real.log p⌋₊ * Real.log p := by
      convert! Chebyshev.psi_eq_sum_mul_log_prime n
      rw [←natFloor_logb_natCast, ←log_div_log]

theorem log_L_eq_psi (n : ℕ) : Real.log (L n) = Chebyshev.psi n := by
  rw [Chebyshev.psi_eq_log_lcmUpto n]
  rfl


end LcmDev
