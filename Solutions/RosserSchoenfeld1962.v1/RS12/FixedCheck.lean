/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.Period

namespace RS12Factorial

private def positiveFixed (n : ℕ) : ℕ :=
  Nat.add (Nat.mul 1000000 (Nat.div n 1)) (Nat.add (Nat.mul 1000000 (Nat.div n 6)) (Nat.add (Nat.mul 1000000 (Nat.div n 10)) (Nat.add (Nat.mul 1000000 (Nat.div n 14)) (Nat.add (Nat.mul 1000000 (Nat.div n 15)) (Nat.add (Nat.mul 1000000 (Nat.div n 21)) (Nat.add (Nat.mul 1000000 (Nat.div n 22)) (Nat.add (Nat.mul 1000000 (Nat.div n 26)) (Nat.add (Nat.mul 1000000 (Nat.div n 35)) (Nat.add (Nat.mul 1000000 (Nat.div n 36)) (Nat.add (Nat.mul 205578 (Nat.div n 39)) (Nat.add (Nat.mul 794422 (Nat.div n 40)) (Nat.add (Nat.mul 1000000 (Nat.div n 55)) (Nat.add (Nat.mul 1000000 (Nat.div n 65)) (Nat.add (Nat.mul 483312 (Nat.div n 88)) (Nat.add (Nat.mul 1000000 (Nat.div n 90)) (Nat.add (Nat.mul 2000000 (Nat.div n 91)) (Nat.add (Nat.mul 1000000 (Nat.div n 99)) (Nat.add (Nat.mul 311110 (Nat.div n 117)) (Nat.add (Nat.mul 1091269 (Nat.div n 120)) (Nat.add (Nat.mul 3000000 (Nat.div n 126)) (Nat.add (Nat.mul 386522 (Nat.div n 140)) (Nat.add (Nat.mul 1613478 (Nat.div n 143)) (Nat.add (Nat.mul 1277734 (Nat.div n 168)) (Nat.add (Nat.mul 5205578 (Nat.div n 210)) (Nat.add (Nat.mul 3402378 (Nat.div n 220)) (Nat.add (Nat.mul 1000000 (Nat.div n 260)) (Nat.add (Nat.mul 516688 (Nat.div n 264)) (Nat.add (Nat.mul 193009 (Nat.div n 280)) (Nat.add (Nat.mul 219841 (Nat.div n 308)) (Nat.add (Nat.mul 1369003 (Nat.div n 312)) (Nat.add (Nat.mul 1205578 (Nat.div n 315)) (Nat.add (Nat.mul 2607957 (Nat.div n 330)) (Nat.add (Nat.mul 732601 (Nat.div n 390)) (Nat.add (Nat.mul 191622 (Nat.div n 396)) (Nat.add (Nat.mul 2588360 (Nat.div n 462)) (Nat.add (Nat.mul 1000000 (Nat.div n 468)) (Nat.add (Nat.mul 487053 (Nat.div n 504)) (Nat.add (Nat.mul 1000000 (Nat.div n 520)) (Nat.add (Nat.mul 4234004 (Nat.div n 546)) (Nat.add (Nat.mul 373953 (Nat.div n 572)) (Nat.add (Nat.mul 155368 (Nat.div n 585)) (Nat.add (Nat.mul 1000000 (Nat.div n 693)) (Nat.add (Nat.mul 1794422 (Nat.div n 728)) (Nat.add (Nat.mul 1066094 (Nat.div n 770)) (Nat.add (Nat.mul 1236301 (Nat.div n 780)) (Nat.add (Nat.mul 619635 (Nat.div n 792)) (Nat.add (Nat.mul 894468 (Nat.div n 819)) (Nat.add (Nat.mul 1101056 (Nat.div n 910)) (Nat.add (Nat.mul 264640 (Nat.div n 924)) (Nat.add (Nat.mul 633527 (Nat.div n 1155)) (Nat.add (Nat.mul 1502425 (Nat.div n 1260)) (Nat.add (Nat.mul 1063371 (Nat.div n 1287)) (Nat.add (Nat.mul 929259 (Nat.div n 1320)) (Nat.add (Nat.mul 1805477 (Nat.div n 1365)) (Nat.add (Nat.mul 45745 (Nat.div n 1386)) (Nat.add (Nat.mul 848487 (Nat.div n 1430)) (Nat.add (Nat.mul 73427 (Nat.div n 1980)) (Nat.add (Nat.mul 3207271 (Nat.div n 2002)) (Nat.add (Nat.mul 218627 (Nat.div n 2520)) (Nat.add (Nat.mul 91909 (Nat.div n 2574)) (Nat.add (Nat.mul 1167780 (Nat.div n 3080)) (Nat.add (Nat.mul 427269 (Nat.div n 3465)) (Nat.add (Nat.mul 177542 (Nat.div n 8008)) (Nat.mul 2466174 (Nat.div n 10920)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private def negativeFixed (n : ℕ) : ℕ :=
  Nat.add (Nat.mul 1000000 (Nat.div n 2)) (Nat.add (Nat.mul 1000000 (Nat.div n 3)) (Nat.add (Nat.mul 1000000 (Nat.div n 5)) (Nat.add (Nat.mul 1000000 (Nat.div n 7)) (Nat.add (Nat.mul 1000000 (Nat.div n 11)) (Nat.add (Nat.mul 1000000 (Nat.div n 13)) (Nat.add (Nat.mul 1000000 (Nat.div n 18)) (Nat.add (Nat.mul 1000000 (Nat.div n 20)) (Nat.add (Nat.mul 1000000 (Nat.div n 24)) (Nat.add (Nat.mul 2000000 (Nat.div n 30)) (Nat.add (Nat.mul 2000000 (Nat.div n 42)) (Nat.add (Nat.mul 1000000 (Nat.div n 44)) (Nat.add (Nat.mul 1000000 (Nat.div n 63)) (Nat.add (Nat.mul 2000000 (Nat.div n 70)) (Nat.add (Nat.mul 205578 (Nat.div n 78)) (Nat.add (Nat.mul 277734 (Nat.div n 84)) (Nat.add (Nat.mul 794422 (Nat.div n 104)) (Nat.add (Nat.mul 2205578 (Nat.div n 105)) (Nat.add (Nat.mul 2402378 (Nat.div n 110)) (Nat.add (Nat.mul 2000000 (Nat.div n 130)) (Nat.add (Nat.mul 219841 (Nat.div n 154)) (Nat.add (Nat.mul 574581 (Nat.div n 156)) (Nat.add (Nat.mul 1000000 (Nat.div n 165)) (Nat.add (Nat.mul 483312 (Nat.div n 180)) (Nat.add (Nat.mul 2000000 (Nat.div n 182)) (Nat.add (Nat.mul 394321 (Nat.div n 195)) (Nat.add (Nat.mul 1811257 (Nat.div n 198)) (Nat.add (Nat.mul 2000000 (Nat.div n 231)) (Nat.add (Nat.mul 196800 (Nat.div n 234)) (Nat.add (Nat.mul 2722266 (Nat.div n 252)) (Nat.add (Nat.mul 2205578 (Nat.div n 273)) (Nat.add (Nat.mul 987431 (Nat.div n 286)) (Nat.add (Nat.mul 1402378 (Nat.div n 360)) (Nat.add (Nat.mul 718645 (Nat.div n 385)) (Nat.add (Nat.mul 108788 (Nat.div n 420)) (Nat.add (Nat.mul 819056 (Nat.div n 429)) (Nat.add (Nat.mul 3277734 (Nat.div n 440)) (Nat.add (Nat.mul 2000000 (Nat.div n 455)) (Nat.add (Nat.mul 75412 (Nat.div n 495)) (Nat.add (Nat.mul 1466477 (Nat.div n 616)) (Nat.add (Nat.mul 4296847 (Nat.div n 630)) (Nat.add (Nat.mul 2519652 (Nat.div n 660)) (Nat.add (Nat.mul 2562012 (Nat.div n 840)) (Nat.add (Nat.mul 3172687 (Nat.div n 1001)) (Nat.add (Nat.mul 1939152 (Nat.div n 1092)) (Nat.add (Nat.mul 2707420 (Nat.div n 1540)) (Nat.add (Nat.mul 1955096 (Nat.div n 1560)) (Nat.add (Nat.mul 523470 (Nat.div n 1638)) (Nat.add (Nat.mul 701158 (Nat.div n 2145)) (Nat.add (Nat.mul 597013 (Nat.div n 2310)) (Nat.add (Nat.mul 3063059 (Nat.div n 2730)) (Nat.add (Nat.mul 43821 (Nat.div n 2772)) (Nat.add (Nat.mul 2616536 (Nat.div n 3640)) (Nat.add (Nat.mul 1589734 (Nat.div n 3960)) (Nat.add (Nat.mul 298593 (Nat.div n 4095)) (Nat.add (Nat.mul 1006349 (Nat.div n 4290)) (Nat.add (Nat.mul 1836980 (Nat.div n 6006)) (Nat.add (Nat.mul 234346 (Nat.div n 6435)) (Nat.add (Nat.mul 434282 (Nat.div n 6552)) (Nat.add (Nat.mul 428428 (Nat.div n 12870)) (Nat.add (Nat.mul 870478 (Nat.div n 18018)) (Nat.add (Nat.mul 587950 (Nat.div n 20020)) (Nat.add (Nat.mul 1220010 (Nat.div n 27720)) (Nat.add (Nat.mul 1327486 (Nat.div n 40040)) (Nat.add (Nat.mul 1373945 (Nat.div n 45045)) (Nat.add (Nat.mul 1595971 (Nat.div n 72072)) (Nat.add (Nat.mul 1522774 (Nat.div n 120120)) (Nat.add (Nat.mul 1088091 (Nat.div n 180180)) (Nat.mul 3387801 (Nat.div n 360360)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def checkFixedBlock (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 =>
    Nat.ble (Nat.add (negativeFixed start)
      (if 0 < start ∧ start < 60 then 1000000 else 0)) (positiveFixed start) &&
      checkFixedBlock (start + 1) count

set_option Elab.async false
set_option maxRecDepth 100000

private theorem cast_nat_add (a b : ℕ) : ((Nat.add a b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) := Nat.cast_add a b
private theorem cast_nat_mul (a b : ℕ) : ((Nat.mul a b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) := Nat.cast_mul a b

private def positiveParts : List (ℕ × ℤ) → ℕ → ℕ
  | [], _ => 0
  | (d, .ofNat b) :: cs, n => Nat.add (Nat.mul b (Nat.div n d)) (positiveParts cs n)
  | (_, .negSucc _) :: cs, n => positiveParts cs n

private def negativeParts : List (ℕ × ℤ) → ℕ → ℕ
  | [], _ => 0
  | (_, .ofNat _) :: cs, n => negativeParts cs n
  | (d, .negSucc b) :: cs, n => Nat.add (Nat.mul (b + 1) (Nat.div n d)) (negativeParts cs n)

private theorem parts_floor_eq (cs : List (ℕ × ℤ)) (n : ℕ) :
    floorNumerator cs n = (positiveParts cs n : ℤ) - (negativeParts cs n : ℤ) := by
  induction cs with
  | nil => simp [floorNumerator, positiveParts, negativeParts]
  | cons dw cs ih =>
    rcases dw with ⟨d, b⟩
    cases b with
    | ofNat b =>
      simp only [floorNumerator, List.map_cons, List.sum_cons,
        positiveParts, negativeParts, cast_nat_add, cast_nat_mul] at *
      rw [ih]
      change (b : ℤ) * (↑(n / d) : ℤ) + ((positiveParts cs n : ℤ) - (negativeParts cs n : ℤ)) =
        (b : ℤ) * (↑(n / d) : ℤ) + (positiveParts cs n : ℤ) - (negativeParts cs n : ℤ)
      ring
    | negSucc b =>
      simp only [floorNumerator, List.map_cons, List.sum_cons,
        positiveParts, negativeParts, cast_nat_add, cast_nat_mul] at *
      rw [ih]
      change (-(b + 1 : ℤ)) * (↑(n / d) : ℤ) + ((positiveParts cs n : ℤ) - (negativeParts cs n : ℤ)) =
        (positiveParts cs n : ℤ) - (((b + 1 : ℕ) : ℤ) * (↑(n / d) : ℤ) + (negativeParts cs n : ℤ))
      push_cast
      ring

/-- The expanded natural-number expression is exactly the signed floor sum. -/
private theorem fixed_floor_eq (n : ℕ) :
    floorNumerator factorialWeights n = (positiveFixed n : ℤ) - (negativeFixed n : ℤ) := by
  have hp : positiveParts factorialWeights n = positiveFixed n := by rfl
  have hn : negativeParts factorialWeights n = negativeFixed n := by rfl
  rw [← hp, ← hn]
  exact parts_floor_eq _ _

theorem checkFixedBlock_sound {start count : ℕ}
    (hc : checkFixedBlock start count = true) {n : ℕ}
    (hlo : start ≤ n) (hhi : n < start + count) :
    (if 0 < n ∧ n < 60 then (1000000 : ℤ) else 0) ≤ floorNumerator factorialWeights n := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    simp only [checkFixedBlock, Bool.and_eq_true, Nat.ble_eq] at hc
    by_cases hn : n = start
    · subst n
      rw [fixed_floor_eq]
      have h := hc.1
      split_ifs at h ⊢ <;>
        have hh := Int.ofNat_le.mpr h
        <;> norm_num only [cast_nat_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_zero] at hh
        <;> linarith
    · exact ih hc.2 (by omega) (by omega)

end RS12Factorial
