import RSBounds.Zeros0to1000Statement
import Mathlib.Algebra.BigOperators.Fin

/-!
# Kernel-checked facts about the `Zeros0to1000` ordinate list

Facts about the 649 integers of `Zeros0to1000.ordinates` alone (no claim
about zeta): the length, the range, the gaps, and the rounded-up reciprocal
sum used for the head bound, each checked by `decide +kernel`. Kept apart
from `Head1000Table` so that these kernel checks run with a light import.
-/

namespace TernaryGoldbach.RSBounds.Head1000

theorem length_ordinates : Zeros0to1000.ordinates.length = 649 := by
  decide +kernel

/-- The `i`-th listed integer. -/
def ord (i : Fin 649) : ℕ :=
  Zeros0to1000.ordinates[i.1]'(Nat.lt_of_lt_of_eq i.2 length_ordinates.symm)

theorem ord_mem (i : Fin 649) : ord i ∈ Zeros0to1000.ordinates :=
  List.getElem_mem _

/-! Nat-only checkers on the list itself (a `decide` over `Fin 649` is far
more expensive in the kernel), with their soundness theorems. -/

/-- Every entry `m` satisfies `10^25 ≤ m` and `m + 10001 ≤ 10^27`. -/
def rangeCheck : List ℕ → Bool
  | [] => true
  | m :: l => (Nat.ble (Nat.pow 10 25) m && Nat.ble (Nat.add m 10001) (Nat.pow 10 27)) &&
      rangeCheck l

/-- Consecutive entries differ by at least `20002`. -/
def gapCheck : List ℕ → Bool
  | a :: b :: l => Nat.ble (Nat.add a 20002) b && gapCheck (b :: l)
  | _ => true

theorem rangeCheck_sound : ∀ l : List ℕ, rangeCheck l = true →
    ∀ m ∈ l, 10 ^ 25 ≤ m ∧ m + 10001 ≤ 10 ^ 27
  | [], _, m, hm => by simp at hm
  | a :: l, hc, m, hm => by
    simp only [rangeCheck, Bool.and_eq_true, Nat.ble_eq, Nat.pow_eq, Nat.add_eq] at hc
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hc.1
    · exact rangeCheck_sound l hc.2 m hm

theorem gapCheck_sound : ∀ l : List ℕ, gapCheck l = true →
    ∀ (i : ℕ) (h : i + 1 < l.length), l[i] + 20002 ≤ l[i + 1]
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | a :: b :: l, hc, i, h => by
    simp only [gapCheck, Bool.and_eq_true, Nat.ble_eq, Nat.add_eq] at hc
    cases i with
    | zero => simpa using hc.1
    | succ i =>
      have := gapCheck_sound (b :: l) hc.2 i (by simp only [List.length_cons] at h ⊢; omega)
      simpa using this

theorem range_checked : rangeCheck Zeros0to1000.ordinates = true := by
  decide +kernel

theorem gap_checked : gapCheck Zeros0to1000.ordinates = true := by
  decide +kernel

/-- Every listed integer lies in `[10^25, 10^27 - 10001]`. -/
theorem ord_range (i : Fin 649) : 10 ^ 25 ≤ ord i ∧ ord i + 10001 ≤ 10 ^ 27 :=
  rangeCheck_sound _ range_checked (ord i) (ord_mem i)

/-- Consecutive listed integers differ by at least `20002`. -/
theorem ord_gap (i : Fin 648) : ord i.castSucc + 20002 ≤ ord i.succ :=
  gapCheck_sound _ gap_checked i.1 (by rw [length_ordinates]; omega)

/-- A rounded-up numerator: `10^24 / (m - 10001) ≤ up m / 10^9`. -/
def up (m : ℕ) : ℕ := 10 ^ 33 / (m - 10001) + 1

theorem up_spec (m : ℕ) (hm : 10001 < m) : 10 ^ 33 < up m * (m - 10001) := by
  rw [Nat.mul_comm]
  exact Nat.lt_mul_div_succ (10 ^ 33) (Nat.sub_pos_of_lt hm)

theorem sum_up_le : (Zeros0to1000.ordinates.map up).sum ≤ 2028658000 := by
  decide +kernel

theorem sum_fin_getElem {l : List ℕ} {n : ℕ} (hl : l.length = n) (f : ℕ → ℕ) :
    (∑ i : Fin n, f (l[i.1]'(Nat.lt_of_lt_of_eq i.2 hl.symm))) = (l.map f).sum := by
  subst hl
  exact Fin.sum_univ_fun_getElem l f

theorem sum_up_eq : (∑ i : Fin 649, up (ord i)) = (Zeros0to1000.ordinates.map up).sum :=
  sum_fin_getElem length_ordinates up

end TernaryGoldbach.RSBounds.Head1000
