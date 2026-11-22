import RSBounds.Head1000Data
import RSBounds.ZetaZeroTable

/-!
# The first 649 zeros from the `Zeros0to1000` statement

`Certified` is the conjunction of the three theorems `located`, `unique` and
`count` of `challenge/Zeros0to1000.lean` (`Garald1/zeta-zero-locations`), with
the definitions vendored in `Zeros0to1000Statement.lean`. This file proves
nothing about the zeros by itself: every result below takes `Certified` as a
hypothesis. From it we build the project's `CertifiedTable 649 1000`, the
exact count `N(1000) = 649`, and the head bound
`Σ_{0 < γ ≤ 1000} 1/|ρ| ≤ 2.028658`, the last from the kernel computation on the
listed integers in `Head1000Data.lean`.
-/

open Complex

namespace TernaryGoldbach.RSBounds.Head1000
open BacklundCountIdentity ZetaZeroTable

/-- The statements of `Zeros0to1000.located`, `Zeros0to1000.unique` and
`Zeros0to1000.count`, verbatim, as one proposition. -/
def Certified : Prop :=
  (∀ s ∈ Zeros0to1000.zerosBetween 0 1000, s.re = 1 / 2 ∧ analyticOrderAt riemannZeta s = 1 ∧
      ∃ m ∈ Zeros0to1000.ordinates, |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    (∀ m ∈ Zeros0to1000.ordinates,
      ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (m : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20) ∧
    (Zeros0to1000.zerosBetween 0 1000).ncard = 649

/-! ## Generic facts about a certified table -/

section Generic

variable {n : ℕ} {H : ℝ}

theorem point_injective (t : CertifiedTable n H) :
    Function.Injective (fun i => (1 / 2 : ℂ) + t.ordinate i * I) := by
  intro i j hij
  apply t.strictMono.injective
  simpa using congrArg Complex.im hij

/-- A certified table enumerates exactly the positive zeros up to its height. -/
theorem image_eq_closedPositiveZeros (t : CertifiedTable n H) (hH : 0 < H) :
    Finset.univ.image (fun i => (1 / 2 : ℂ) + t.ordinate i * I) = closedPositiveZeros H := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_closedPositiveZeros_iff hH).mpr
      ⟨t.zero i, by simpa using t.positive i, by simpa using t.le_height i⟩
  · intro hz
    obtain ⟨hzeta, h0, h1⟩ := (mem_closedPositiveZeros_iff hH).mp hz
    obtain ⟨i, rfl⟩ := t.complete z hzeta h0 h1
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The multiplicity-weighted head sum is the table sum. -/
theorem weighted_head_eq (t : CertifiedTable n H) (hH : 0 < H) :
    (∑ ρ ∈ closedPositiveZeros H, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) =
      ∑ i : Fin n, 1 / ‖(1 / 2 : ℂ) + t.ordinate i * I‖ := by
  classical
  rw [← image_eq_closedPositiveZeros t hH,
    Finset.sum_image (fun i _ j _ hij => point_injective t hij)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [t.simple, ENat.toNat_one, Nat.cast_one]

/-- The inclusive multiplicity count at the table height. -/
theorem N_le_eq (t : CertifiedTable n H) (hH : 0 < H) : N_le H = n := by
  classical
  unfold N_le
  rw [← image_eq_closedPositiveZeros t hH,
    Finset.sum_image (fun i _ j _ hij => point_injective t hij)]
  have hone : ∀ i, (analyticOrderAt riemannZeta ((1 / 2 : ℂ) + t.ordinate i * I)).toNat = 1 := by
    intro i
    rw [t.simple i, ENat.toNat_one]
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem positiveZeroCount_eq (t : CertifiedTable n H) (hH : 0 < H) :
    Rosser1941.positiveZeroCount H = n := by
  rw [Rosser1941.positiveZeroCount_eq hH, N_le_eq t hH]

/-- The head sum is bounded by the reciprocal lower brackets. -/
theorem head_le_lower (t : CertifiedTable n H) (hlo : ∀ i, 0 < t.lower i) :
    (∑ i : Fin n, 1 / ‖(1 / 2 : ℂ) + t.ordinate i * I‖) ≤
      ∑ i : Fin n, 1 / (t.lower i : ℝ) := by
  apply Finset.sum_le_sum
  intro i _
  have hl : (0 : ℝ) < (t.lower i : ℝ) := by exact_mod_cast hlo i
  have hnorm : t.ordinate i ≤ ‖(1 / 2 : ℂ) + t.ordinate i * I‖ := by
    simpa using Complex.im_le_norm ((1 / 2 : ℂ) + t.ordinate i * I)
  exact one_div_le_one_div_of_le hl ((t.bracket i).1.le.trans hnorm)

end Generic

/-! ## The table, under `Certified` -/

section Table

variable (h : Certified)

include h in
theorem exists_unique_zero (i : Fin 649) :
    ∃! s : ℂ, riemannZeta s = 0 ∧ |s.im - (ord i : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 :=
  h.2.1 (ord i) (ord_mem i)

/-- The zero attached to the `i`-th listed integer by `unique`. -/
noncomputable def zero (i : Fin 649) : ℂ := (exists_unique_zero h i).exists.choose

theorem zero_spec (i : Fin 649) :
    riemannZeta (zero h i) = 0 ∧ |(zero h i).im - (ord i : ℝ) / 10 ^ 24| ≤ 1 / 10 ^ 20 :=
  (exists_unique_zero h i).exists.choose_spec

theorem ord_real_range (i : Fin 649) :
    (10 : ℝ) ^ 25 ≤ (ord i : ℝ) ∧ (ord i : ℝ) + 10001 ≤ 10 ^ 27 := by
  obtain ⟨h1, h2⟩ := ord_range i
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem im_bounds (i : Fin 649) :
    ((ord i : ℝ) - 10001) / 10 ^ 24 < (zero h i).im ∧
      (zero h i).im < ((ord i : ℝ) + 10001) / 10 ^ 24 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (zero_spec h i).2
  have e1 : ((ord i : ℝ) - 10001) / 10 ^ 24 = (ord i : ℝ) / 10 ^ 24 - 10001 / 10 ^ 24 := by ring
  have e2 : ((ord i : ℝ) + 10001) / 10 ^ 24 = (ord i : ℝ) / 10 ^ 24 + 10001 / 10 ^ 24 := by ring
  have hc : (1 : ℝ) / 10 ^ 20 < 10001 / 10 ^ 24 := by norm_num
  constructor <;> linarith

theorem zero_mem (i : Fin 649) : zero h i ∈ Zeros0to1000.zerosBetween 0 1000 := by
  obtain ⟨hlo, hhi⟩ := im_bounds h i
  obtain ⟨h1, h2⟩ := ord_real_range i
  have hpos : (0 : ℝ) < ((ord i : ℝ) - 10001) / 10 ^ 24 := by
    apply div_pos _ (by positivity)
    have : (10001 : ℝ) < 10 ^ 25 := by norm_num
    linarith
  have htop : ((ord i : ℝ) + 10001) / 10 ^ 24 ≤ 1000 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num at h2 ⊢
    linarith
  exact ⟨(zero_spec h i).1, by linarith, by linarith⟩

theorem zero_re (i : Fin 649) : (zero h i).re = 1 / 2 := (h.1 _ (zero_mem h i)).1

theorem zero_simple (i : Fin 649) : analyticOrderAt riemannZeta (zero h i) = 1 :=
  (h.1 _ (zero_mem h i)).2.1

theorem zero_eq (i : Fin 649) : zero h i = 1 / 2 + ((zero h i).im : ℂ) * I := by
  apply Complex.ext <;> simp [zero_re h i]

theorem ordinate_strictMono : StrictMono (fun i => (zero h i).im) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hg : (ord i.castSucc : ℝ) + 20002 ≤ (ord i.succ : ℝ) := by exact_mod_cast ord_gap i
  have h1 := (im_bounds h i.castSucc).2
  have h2 := (im_bounds h i.succ).1
  have hmid : ((ord i.castSucc : ℝ) + 10001) / 10 ^ 24 ≤ ((ord i.succ : ℝ) - 10001) / 10 ^ 24 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  show (zero h i.castSucc).im < (zero h i.succ).im
  linarith

theorem complete_aux (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.im) (h1 : ρ.im ≤ 1000) :
    ∃ i : Fin 649, ρ = 1 / 2 + ((zero h i).im : ℂ) * I := by
  have hmem : ρ ∈ Zeros0to1000.zerosBetween 0 1000 := ⟨hz, h0, h1⟩
  obtain ⟨-, -, m, hm, hwin⟩ := h.1 ρ hmem
  obtain ⟨k, hk, hkm⟩ := List.getElem_of_mem hm
  let i : Fin 649 := ⟨k, Nat.lt_of_lt_of_eq hk length_ordinates⟩
  have hord : ord i = m := hkm
  refine ⟨i, ?_⟩
  have hρ : ρ = zero h i := by
    apply (exists_unique_zero h i).unique _ (zero_spec h i)
    rw [hord]
    exact ⟨hz, hwin⟩
  rw [hρ]
  exact zero_eq h i

/-- The project's certified-table interface for the first 649 zeros. -/
noncomputable def table : CertifiedTable 649 1000 where
  lower i := ((ord i : ℚ) - 10001) / 10 ^ 24
  upper i := ((ord i : ℚ) + 10001) / 10 ^ 24
  ordinate i := (zero h i).im
  strictMono := ordinate_strictMono h
  bracket i := by
    push_cast
    exact im_bounds h i
  positive i := (zero_mem h i).2.1
  le_height i := (zero_mem h i).2.2
  zero i := by
    rw [← zero_eq h i]
    exact (zero_spec h i).1
  simple i := by
    rw [← zero_eq h i]
    exact zero_simple h i
  complete ρ hz h0 h1 := complete_aux h ρ hz h0 h1

include h in
theorem positiveZeroCount_thousand : Rosser1941.positiveZeroCount 1000 = 649 := by
  have := positiveZeroCount_eq (table h) (by norm_num)
  exact_mod_cast this

end Table

theorem reciprocal_lower_le (i : Fin 649) :
    1 / ((((ord i : ℚ) - 10001) / 10 ^ 24 : ℚ) : ℝ) ≤ (up (ord i) : ℝ) / 10 ^ 9 := by
  obtain ⟨h1, -⟩ := ord_range i
  have hm : 10001 < ord i := lt_of_lt_of_le (by norm_num) h1
  have hs := up_spec (ord i) hm
  have hcast : ((ord i - 10001 : ℕ) : ℝ) = (ord i : ℝ) - 10001 := by
    rw [Nat.cast_sub hm.le]
    norm_num
  have hd : (0 : ℝ) < (ord i : ℝ) - 10001 := by
    rw [← hcast]
    exact_mod_cast Nat.sub_pos_of_lt hm
  have hsR : (10 : ℝ) ^ 33 < (up (ord i) : ℝ) * ((ord i : ℝ) - 10001) := by
    rw [← hcast]
    exact_mod_cast hs
  push_cast
  rw [one_div_div, div_le_div_iff₀ hd (by positivity)]
  have e : (10 : ℝ) ^ 24 * 10 ^ 9 = 10 ^ 33 := by norm_num
  rw [e]
  exact hsR.le

/-- `Σ_{0 < γ ≤ 1000} 1/|ρ| ≤ 2.028658`, counted with multiplicity. -/
theorem weighted_head_le (h : Certified) :
    (∑ ρ ∈ closedPositiveZeros 1000,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) ≤ 2.028658 := by
  rw [weighted_head_eq (table h) (by norm_num)]
  have hlow : ∀ i, 0 < (table h).lower i := by
    intro i
    show (0 : ℚ) < ((ord i : ℚ) - 10001) / 10 ^ 24
    obtain ⟨h1, -⟩ := ord_range i
    have : (10 : ℚ) ^ 25 ≤ (ord i : ℚ) := by exact_mod_cast h1
    apply div_pos _ (by positivity)
    have : (10001 : ℚ) < 10 ^ 25 := by norm_num
    linarith
  apply (head_le_lower (table h) hlow).trans
  have hterm : ∀ i : Fin 649, 1 / ((table h).lower i : ℝ) ≤ (up (ord i) : ℝ) / 10 ^ 9 :=
    fun i => reciprocal_lower_le i
  apply (Finset.sum_le_sum (fun i _ => hterm i)).trans
  rw [← Finset.sum_div]
  have hsum : (∑ i : Fin 649, (up (ord i) : ℝ)) ≤ 2028658000 := by
    have := sum_up_le
    rw [← sum_up_eq] at this
    exact_mod_cast this
  rw [div_le_iff₀ (by positivity)]
  norm_num at hsum ⊢
  linarith

end TernaryGoldbach.RSBounds.Head1000
