import TernaryGoldbach.CircleMethod

/-!
# Ramanujan sums and Montgomery's inequality

* `ramanujan_coprime`: `∑_{a mod q, (a,q)=1} e(an/q) = μ(q)` for `(n, q) = 1`.
* `montgomery_ineq`: for squarefree `r` and `a(n)` supported on `n` coprime to `r`,
  `|S(α)|² ≤ φ(r) ∑_{b mod r, (b,r)=1} |S(α + b/r)|²`, where `S(β) = ∑ a(n) e(βn)`.
  This is Montgomery's inequality [Mon68], [IK04, Lemma 7.15] in the case `ω(p) = 1` used by
  [H, (5.40), (5.46)]; in this case it is just Cauchy–Schwarz plus the Ramanujan sum.
-/

open Finset Complex
open ArithmeticFunction (moebius)
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach

theorem e_eq_one_iff (t : ℝ) : e t = 1 ↔ ∃ n : ℤ, t = n := by
  rw [e, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    have : ((t : ℂ) - n) * (2 * Real.pi * I) = 0 := by rw [sub_mul, ← hn]; ring
    have := (mul_eq_zero.1 this).resolve_right hpi
    exact_mod_cast sub_eq_zero.1 this
  · rintro ⟨n, rfl⟩; exact ⟨n, by push_cast; ring⟩

theorem e_nat_mul' (b : ℕ) (t : ℝ) : e (b * t) = e t ^ b := by
  rw [e, e, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- `∑_{b < m} e(bn/m) = m` if `m ∣ n`, `0` otherwise. -/
theorem sum_e_range (m n : ℕ) (hm : 1 ≤ m) :
    ∑ b ∈ range m, e (b * n / m) = if m ∣ n then (m : ℂ) else 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hterm : ∀ b : ℕ, e (b * n / m) = e (n / m) ^ b := fun b => by
    rw [← e_nat_mul']; congr 1; ring
  simp_rw [hterm]
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have : e ((m : ℝ) * k / m) = 1 := (e_eq_one_iff _).2 ⟨k, by push_cast; field_simp⟩
    push_cast
    simp [this]
  · have hne : e (n / m) ≠ 1 := by
      intro h
      obtain ⟨k, hk⟩ := (e_eq_one_iff _).1 h
      apply hdvd
      have : (n : ℝ) = m * k := by field_simp at hk; linarith
      have hk0 : (0 : ℤ) ≤ k := by
        by_contra hneg; push Not at hneg
        have : (k : ℝ) < 0 := by exact_mod_cast hneg
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [show (0 : ℝ) < m by positivity]
      have hz : (n : ℤ) = m * k := by exact_mod_cast this
      refine ⟨k.toNat, ?_⟩
      have : ((n : ℕ) : ℤ) = ((m * k.toNat : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg hk0]; exact hz
      exact_mod_cast this
    rw [geom_sum_eq hne]
    have : e (n / m) ^ m = 1 := by
      rw [← e_nat_mul', (e_eq_one_iff _).2 ⟨n, by push_cast; field_simp⟩]
    rw [this]; simp

theorem sum_moebius_divisors (g : ℕ) (hg : 1 ≤ g) :
    ∑ d ∈ g.divisors, (μ d : ℂ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f g)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← h]
  simp [ArithmeticFunction.intCoe_apply]

/-- **Ramanujan sum at `n` coprime to `q`**: `∑_{a < q, (a,q)=1} e(an/q) = μ(q)`. -/
theorem ramanujan_coprime (q n : ℕ) (hq : 1 ≤ q) (hn : Nat.Coprime n q) :
    ∑ a ∈ (range q).filter q.Coprime, e (a * n / q) = μ q := by
  rw [sum_filter]
  -- Möbius inversion of the coprimality condition.
  have h1 : ∀ a ∈ range q, (if q.Coprime a then e (a * n / q) else 0) =
      ∑ d ∈ q.divisors, if d ∣ a then (μ d : ℂ) * e (a * n / q) else 0 := by
    intro a _
    have hg : 1 ≤ Nat.gcd q a := Nat.gcd_pos_of_pos_left _ (by omega)
    have := sum_moebius_divisors (Nat.gcd q a) hg
    rw [← sum_filter]
    have hfilt : q.divisors.filter (· ∣ a) = (Nat.gcd q a).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h1, h2⟩, by omega⟩
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h1, by omega⟩, h2⟩
    rw [hfilt, ← sum_mul, this]
    simp only [Nat.Coprime]
    split_ifs <;> simp
  rw [sum_congr rfl h1, sum_comm]
  -- The inner sums.
  have h2 : ∀ d ∈ q.divisors, (∑ a ∈ range q, if d ∣ a then (μ d : ℂ) * e (a * n / q) else 0) =
      if d = q then (μ q : ℂ) else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨m, hm⟩, _⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
    have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
    rw [← sum_filter, ← mul_sum]
    have himg : (range q).filter (d ∣ ·) = (range m).map ⟨(d * ·), mul_right_injective₀ hd0.ne'⟩ := by
      ext a
      simp only [mem_filter, mem_range, mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨ha, ⟨b, rfl⟩⟩
        exact ⟨b, by rw [hm] at ha; exact (Nat.mul_lt_mul_left hd0).1 ha, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨by rw [hm]; exact (Nat.mul_lt_mul_left hd0).2 hb, dvd_mul_right _ _⟩
    rw [himg, sum_map]
    have h3 : ∀ b ∈ range m, e (((d * b : ℕ) : ℝ) * n / q) = e (b * n / m) := by
      intro b _
      congr 1; rw [hm]; push_cast
      have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      field_simp
    simp only [Function.Embedding.coeFn_mk]
    rw [sum_congr rfl h3, sum_e_range m n hm1]
    by_cases hmn : m ∣ n
    · have hm1' : m = 1 := by
        have : m ∣ Nat.gcd n q := Nat.dvd_gcd hmn ⟨d, by rw [hm]; ring⟩
        rw [hn] at this; exact Nat.dvd_one.1 this
      have hdq : d = q := by rw [hm, hm1', mul_one]
      rw [if_pos hmn, if_pos hdq, hm1', hdq]; simp
    · rw [if_neg hmn, mul_zero, if_neg]
      rintro rfl
      apply hmn
      have : m = 1 := by
        have : d * m = d * 1 := by rw [← hm, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hd0 this
      rw [this]; exact one_dvd _
  rw [sum_congr rfl h2, sum_ite_eq']
  simp [Nat.mem_divisors, show q ≠ 0 by omega]

/-- **Montgomery's inequality** (case `ω(p) = 1`): for squarefree `r` and `a(n)` supported on
`n` coprime to `r`, `|S(α)|² ≤ φ(r) ∑_{b < r, (b,r)=1} |S(α + b/r)|²`. -/
theorem montgomery_ineq {r : ℕ} (hr : Squarefree r) (s : Finset ℕ) (a : ℕ → ℂ)
    (hs : ∀ n ∈ s, Nat.Coprime n r) (α : ℝ) :
    ‖∑ n ∈ s, a n * e (α * n)‖ ^ 2 ≤
      (Nat.totient r : ℝ) * ∑ b ∈ (range r).filter r.Coprime,
        ‖∑ n ∈ s, a n * e ((α + b / r) * n)‖ ^ 2 := by
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero (by rintro rfl; exact not_squarefree_zero hr)
  set T := (range r).filter r.Coprime
  have hsum : ∑ b ∈ T, ∑ n ∈ s, a n * e ((α + b / r) * n) =
      (μ r : ℂ) * ∑ n ∈ s, a n * e (α * n) := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have : ∀ b ∈ T, a n * e ((α + b / r) * n) = a n * e (α * n) * e (b * n / r) := by
      intro b _; rw [mul_assoc, ← e_add]; congr 2; ring
    rw [sum_congr rfl this, ← mul_sum, ramanujan_coprime r n hr1 (hs n hn)]
    ring
  have hμ : ‖(μ r : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hr
  have h1 : ‖∑ n ∈ s, a n * e (α * n)‖ ≤ ∑ b ∈ T, ‖∑ n ∈ s, a n * e ((α + b / r) * n)‖ := by
    have := norm_sum_le T (fun b => ∑ n ∈ s, a n * e ((α + b / r) * n))
    rw [hsum, norm_mul, hμ, one_mul] at this; exact this
  have h2 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun b => ‖∑ n ∈ s, a n * e ((α + b / r) * n)‖)
  have hcard : (#T : ℝ) = Nat.totient r := by rw [Nat.totient_eq_card_coprime]
  rw [hcard] at h2
  calc ‖∑ n ∈ s, a n * e (α * n)‖ ^ 2 ≤ (∑ b ∈ T, ‖∑ n ∈ s, a n * e ((α + b / r) * n)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end TernaryGoldbach
