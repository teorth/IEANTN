import TernaryGoldbach.MinorArcs.Montgomery

/-!
# Gauss sums of induced characters

For `f : ℕ → ℂ` periodic mod `N`, completely multiplicative, vanishing on `b` not coprime to `N`
(a Dirichlet character mod `N`, read on `ℕ`), and `r ≥ 1`:

`Σ_{b < Nr, (b, Nr) = 1} f(b) e(b/Nr) = μ(r) f(r) Σ_{c < N} f(c) e(c/N)`   (`gauss_induced`).

So the Gauss sum of the character mod `Nr` induced by `f` is `μ(r) f(r) τ(f)`; in particular it
vanishes unless `r` is squarefree and coprime to `N`.  (Montgomery–Vaughan, Thm. 9.10; no
primitivity is needed here.)  Used for [H, Prop. 12.1.1] via [Bom74, Thm. 7A].

Proved, with no `sorry`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace TernaryGoldbach

/-- `Σ_{c < Nt} g(c) = Σ_{c₀ < N} Σ_{j < t} g(c₀ + Nj)`. -/
theorem sum_range_mul_split {M : Type*} [AddCommMonoid M] (g : ℕ → M) (N t : ℕ) :
    ∑ c ∈ range (N * t), g c = ∑ c₀ ∈ range N, ∑ j ∈ range t, g (c₀ + N * j) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show N * (t + 1) = N * t + N by ring, sum_range_add, ih]
    simp only [sum_range_succ, sum_add_distrib]
    congr 1
    refine sum_congr rfl fun c _ => ?_
    rw [add_comm]

/-- The inner sum: `Σ_{c < Nt} f(c) e(c/Nt) = [t = 1] Σ_{c < N} f(c) e(c/N)` for `f` periodic
mod `N`. -/
theorem sum_periodic_e {N t : ℕ} (hN : 1 ≤ N) (ht : 1 ≤ t) (f : ℕ → ℂ)
    (hper : ∀ b, f (b + N) = f b) :
    ∑ c ∈ range (N * t), f c * e (c / (N * t)) =
      if t = 1 then ∑ c ∈ range N, f c * e (c / N) else 0 := by
  have hperk : ∀ b j, f (b + N * j) = f b := by
    intro b j
    induction j with
    | zero => simp
    | succ j ih => rw [show b + N * (j + 1) = (b + N * j) + N by ring, hper, ih]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (by omega : t ≠ 0)
  rw [sum_range_mul_split]
  have h1 : ∀ c₀ ∈ range N, ∑ j ∈ range t, f (c₀ + N * j) * e (((c₀ + N * j : ℕ) : ℝ) / (N * t)) =
      f c₀ * e (c₀ / (N * t)) * ∑ j ∈ range t, e (j * 1 / t) := by
    intro c₀ _
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [hperk, mul_assoc, ← e_add]
    congr 2
    push_cast
    field_simp
  rw [sum_congr rfl h1]
  have h2 := sum_e_range t 1 ht
  simp only [Nat.cast_one] at h2
  rw [← sum_mul, h2]
  by_cases ht1 : t = 1
  · subst ht1; simp
  · rw [ite_eq_right (by rwa [Nat.dvd_one]), ite_eq_right ht1, mul_zero]

/-- **Gauss sum of an induced character**: for `f` periodic mod `N`, completely multiplicative,
and zero off the residues coprime to `N`,
`Σ_{b < Nr, (b, Nr) = 1} f(b) e(b/Nr) = μ(r) f(r) Σ_{c < N} f(c) e(c/N)`. -/
theorem gauss_induced {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r) (f : ℕ → ℂ)
    (hper : ∀ b, f (b + N) = f b) (hmul : ∀ a b, f (a * b) = f a * f b)
    (hzero : ∀ b, ¬ Nat.Coprime b N → f b = 0) :
    ∑ b ∈ (range (N * r)).filter (fun b => Nat.Coprime b (N * r)), f b * e (b / (N * r)) =
      μ r * f r * ∑ c ∈ range N, f c * e (c / N) := by
  rw [sum_filter]
  -- `[b coprime to Nr] f(b) = Σ_{d ∣ r, d ∣ b} μ(d) f(b)`
  have h1 : ∀ b ∈ range (N * r), (if Nat.Coprime b (N * r) then f b * e (b / (N * r)) else 0) =
      ∑ d ∈ r.divisors, if d ∣ b then (μ d : ℂ) * (f b * e (b / (N * r))) else 0 := by
    intro b _
    have hg : 1 ≤ Nat.gcd r b := Nat.gcd_pos_of_pos_left _ (by omega)
    have hm := sum_moebius_divisors (Nat.gcd r b) hg
    rw [← sum_filter]
    have hfilt : r.divisors.filter (· ∣ b) = (Nat.gcd r b).divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h1, h2⟩, by omega⟩
      · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h1, by omega⟩, h2⟩
    rw [hfilt, ← sum_mul, hm]
    by_cases hbN : Nat.Coprime b N
    · by_cases hbr : Nat.gcd r b = 1
      · rw [ite_eq_left hbr, ite_eq_left (Nat.Coprime.mul_right hbN (Nat.coprime_comm.1 hbr)), one_mul]
      · rw [ite_eq_right hbr, zero_mul, ite_eq_right]
        intro h
        exact hbr (Nat.coprime_comm.1 (Nat.Coprime.coprime_mul_left_right h))
    · rw [hzero b hbN, zero_mul]; split_ifs <;> simp
  rw [sum_congr rfl h1, sum_comm]
  -- the inner sums
  have h2 : ∀ d ∈ r.divisors, (∑ b ∈ range (N * r),
      if d ∣ b then (μ d : ℂ) * (f b * e (b / (N * r))) else 0) =
      if d = r then (μ r : ℂ) * f r * ∑ c ∈ range N, f c * e (c / N) else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨t, ht⟩, _⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at ht; omega)
    have ht1 : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at ht; omega)
    rw [← sum_filter, ← mul_sum]
    have himg : (range (N * r)).filter (d ∣ ·) =
        (range (N * t)).map ⟨(d * ·), mul_right_injective₀ hd0.ne'⟩ := by
      ext b
      simp only [mem_filter, mem_range, mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hb, ⟨c, rfl⟩⟩
        refine ⟨c, ?_, rfl⟩
        rw [ht, show N * (d * t) = d * (N * t) by ring] at hb
        exact (Nat.mul_lt_mul_left hd0).1 hb
      · rintro ⟨c, hc, rfl⟩
        refine ⟨?_, dvd_mul_right _ _⟩
        rw [ht, show N * (d * t) = d * (N * t) by ring]
        exact (Nat.mul_lt_mul_left hd0).2 hc
    rw [himg, sum_map]
    simp only [Function.Embedding.coeFn_mk]
    have h3 : ∀ c ∈ range (N * t), f (d * c) * e (((d * c : ℕ) : ℝ) / (N * r)) =
        f d * (f c * e (c / (N * t))) := by
      intro c _
      rw [hmul, mul_assoc]
      congr 3
      rw [ht]; push_cast
      have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      field_simp
    rw [sum_congr rfl h3, ← mul_sum]
    have h4 := sum_periodic_e hN ht1 f hper
    rw [h4]
    by_cases htt : t = 1
    · have hdr : d = r := by rw [ht, htt, mul_one]
      subst hdr
      rw [ite_eq_left htt, ite_eq_left rfl]; ring
    · rw [ite_eq_right htt, mul_zero, mul_zero, ite_eq_right]
      intro hdr
      apply htt
      have : d * t = d * 1 := by rw [← ht, hdr, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hd0 this
  rw [sum_congr rfl h2, sum_ite_eq']
  simp [Nat.mem_divisors, show r ≠ 0 by omega]

/-! ## Primitive characters: `|τ(χ)|² = N` -/

/-- Sums over `ZMod N` as sums over `0 ≤ c < N`. -/
theorem sum_zmod_eq_sum_range {N : ℕ} [NeZero N] {M : Type*} [AddCommMonoid M] (F : ZMod N → M) :
    ∑ x : ZMod N, F x = ∑ c ∈ range N, F (c : ZMod N) := by
  refine Finset.sum_nbij' (fun x : ZMod N => x.val) (fun c : ℕ => (c : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro c _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro c hc; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hc)
  · intro x _; rw [ZMod.natCast_zmod_val]

/-- `stdAddChar (c mod N) = e(c/N)`. -/
theorem stdAddChar_natCast_eq_e {N : ℕ} [NeZero N] (c : ℕ) :
    (ZMod.stdAddChar (c : ZMod N) : ℂ) = e (c / N) := by
  have h := ZMod.stdAddChar_coe (N := N) (c : ℤ)
  simp only [Int.cast_natCast] at h
  rw [h, e]
  congr 1
  push_cast
  ring

/-- The Gauss sum `τ(χ) = Σ_{c < N} χ(c) e(c/N)` (Mathlib's `gaussSum` with `stdAddChar`). -/
theorem gaussSum_eq_sum_range {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    gaussSum χ ZMod.stdAddChar = ∑ c ∈ range N, χ (c : ZMod N) * e (c / N) := by
  rw [gaussSum, sum_zmod_eq_sum_range]
  refine sum_congr rfl fun c _ => ?_
  rw [stdAddChar_natCast_eq_e]

/-- **`|τ(χ)|² = N` for primitive `χ` mod `N`.** -/
theorem norm_sq_gaussSum_of_isPrimitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = N := by
  classical
  set ψ : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  set τ := gaussSum χ ψ
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar N
  have hconj : ∀ x : ZMod N, (starRingEnd ℂ) (ψ x) = ψ (-x) := by
    intro x
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (by simp [ψ, ZMod.stdAddChar_apply])]
  set K : ℝ := ∑ a : ZMod N, ‖χ a‖ ^ 2
  have hK : 0 < K := by
    have : ‖χ 1‖ ^ 2 ≤ K :=
      Finset.single_le_sum (f := fun a => ‖χ a‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ _)
    rw [map_one, norm_one] at this
    linarith
  -- first evaluation
  have hA1 : ∑ a : ZMod N, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 = K * ‖τ‖ ^ 2 := by
    simp_rw [gaussSum_mulShift_of_isPrimitive ψ hχ, norm_mul, mul_pow, ← Finset.sum_mul]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [← MulChar.star_apply', norm_star]
  -- second evaluation
  have hA2 : ∑ a : ZMod N, ‖gaussSum χ (ψ.mulShift a)‖ ^ 2 = N * K := by
    apply Complex.ofReal_injective
    push_cast
    simp_rw [← Complex.mul_conj', gaussSum, map_sum, map_mul, AddChar.mulShift_apply, hconj,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ b : ZMod N, ∑ a : ZMod N, ∑ b' : ZMod N,
        χ b * ψ (a * b) * ((starRingEnd ℂ) (χ b') * ψ (-(a * b'))) =
        (N : ℂ) * (χ b * (starRingEnd ℂ) (χ b)) := by
      intro b
      rw [Finset.sum_comm]
      have h2 : ∀ b' : ZMod N, ∑ a : ZMod N,
          χ b * ψ (a * b) * ((starRingEnd ℂ) (χ b') * ψ (-(a * b'))) =
          χ b * (starRingEnd ℂ) (χ b') * ∑ a : ZMod N, ψ (a * (b - b')) := by
        intro b'
        rw [Finset.mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [show a * (b - b') = a * b + -(a * b') by ring, AddChar.map_add_eq_mul]
        ring
      simp_rw [h2, AddChar.sum_mulShift _ hψ, sub_eq_zero, ZMod.card]
      simp [Finset.sum_ite_eq]
      ring
    rw [Finset.sum_congr rfl fun b _ => this b, ← Finset.mul_sum]
    congr 1
    simp only [K]
    push_cast
    exact Finset.sum_congr rfl fun (b : ZMod N) _ => Complex.mul_conj' _
  have := hA1.symm.trans hA2
  have hK' : K ≠ 0 := hK.ne'
  field_simp at this
  linarith

end TernaryGoldbach
