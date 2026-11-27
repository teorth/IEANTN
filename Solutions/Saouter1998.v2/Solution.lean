/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard
-/
import IEANTN.Nodes.Richstein2001.v1.Conclusions
import IEANTN.Nodes.Saouter1998.v1.Conclusions
import IEANTN.Nodes.Saouter1998.v2.Conclusions
import Mathlib

/-!
# Solution: `Saouter1998.v2`

`Saouter1998.v2.odd_up_to_1e20` is proved from its two imports, Saouter's ladder and the even
verification to `4·10¹⁴`. Below `4·10¹⁴ + 3` subtract `3`. Above it, take the highest rung
`p ≤ n − 4`; then `n − p` is even and lies in `[4, 4·10¹¹ + 4)`, inside the even range.

The ladder, `Saouter1998.v1.prime_ladder`, is the paper's computation, about `2.5·10⁸` certified
primes; it is a hypothesis here and stays `numerical` in `Saouter1998.v1`.
-/

namespace Saouter1998Sol

open IEANTN

/-- A rung at or below every point of a ladder's span, less than one step below it. -/
theorem ladder_cover (D : ℕ) (hD : 0 < D) :
    ∀ (l : List ℕ) (a : ℕ), (a :: l).IsChain (fun x y => x < y ∧ y - x < D) →
      ∀ m, a ≤ m → m ≤ (a :: l).getLast (List.cons_ne_nil a l) →
        ∃ p ∈ a :: l, p ≤ m ∧ m - p < D := by
  intro l
  induction l with
  | nil =>
    intro a _ m ham hmL
    simp only [List.getLast_singleton] at hmL
    exact ⟨a, List.mem_singleton_self a, ham, by omega⟩
  | cons b l ih =>
    intro a hc m ham hmL
    rw [List.isChain_cons_cons] at hc
    obtain ⟨⟨hab, hstep⟩, hc'⟩ := hc
    by_cases hmb : m < b
    · exact ⟨a, List.mem_cons_self, ham, by omega⟩
    · rw [List.getLast_cons (List.cons_ne_nil b l)] at hmL
      obtain ⟨p, hp, hpm, hmp⟩ := ih b hc' m (by omega) hmL
      exact ⟨p, List.mem_cons_of_mem a hp, hpm, hmp⟩

end Saouter1998Sol

open IEANTN in
theorem Saouter1998.v2.challenge_odd_up_to_1e20
    (saouter1998_v1_prime_ladder : Saouter1998.v1.prime_ladder)
    (richstein2001_v1_even_up_to_4e14 : Richstein2001.v1.even_up_to_4e14) :
    Saouter1998.v2.odd_up_to_1e20 := by
  obtain ⟨l, hprime, hhead, hlast, hchain⟩ := saouter1998_v1_prime_ladder
  have heven : GoldbachEvenUpTo (4 * 10 ^ 14) := richstein2001_v1_even_up_to_4e14
  intro n hn hodd
  rw [Finset.mem_Icc] at hn
  by_cases hsmall : n ≤ 4 * 10 ^ 14 + 3
  · obtain ⟨k, hk⟩ := hodd
    obtain ⟨p, q, hp, hq, hpq⟩ := heven (n - 3)
      (by rw [Finset.mem_Icc]; omega) ⟨k - 1, by omega⟩
    exact ⟨p, q, 3, hp, hq, Nat.prime_three, by omega⟩
  · -- the ladder covers `n - 4`
    cases l with
    | nil => simp at hhead
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      have hL : (138412033 :: t).getLast (List.cons_ne_nil _ _) = 100000000209366024193 := by
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)] at hlast
        exact Option.some.inj hlast
      obtain ⟨p, hpl, hpm, hmp⟩ := Saouter1998Sol.ladder_cover (4 * 10 ^ 11) (by norm_num)
        t 138412033 hchain (n - 4) (by omega) (by rw [hL]; omega)
      have hpp := hprime p hpl
      have hp2 : p ≠ 2 := by omega
      have hpo : Odd p := hpp.odd_of_ne_two hp2
      have hnp : Even (n - p) := Nat.Odd.sub_odd hodd hpo
      obtain ⟨q, r, hq, hr, hqr⟩ := heven (n - p) (by rw [Finset.mem_Icc]; omega) hnp
      exact ⟨p, q, r, hpp, hq, hr, by omega⟩
