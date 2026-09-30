/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.PsiRecurrence
import RS12.PsiFinite
import RS12.FiniteBridge

open Real Chebyshev
namespace RS12Factorial

/-- The complete finite range, obtained from the certified integer blocks. -/
private theorem psi_finite {x : ℝ} (hx : 0 < x) (hcut : x ≤ 500000) :
    ψ x < RS_prime.c₀ * x := by
  exact psi_finite_of_integer_bounds (B := 500000)
    (fun _ hlo hhi => RS12PsiInteger.psi_finite_integer hlo hhi) hx hcut

/-- The factorial recurrence propagates the finite certificate to every positive real. -/
theorem psi_upper_all {x : ℝ} (hx : 0 < x) : ψ x < RS_prime.c₀ * x := by
  have h : ∀ n : ℕ, ∀ y : ℝ, ⌊y⌋₊ = n → 0 < y → ψ y < RS_prime.c₀ * y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro y hyn hy
      by_cases hfin : y ≤ 500000
      · exact psi_finite hy hfin
      have hlarge : 500000 ≤ y := (lt_of_not_ge hfin).le
      have hless : ⌊y / 60⌋₊ < n := by
        rw [← hyn]
        exact floor_div_sixty_lt (by linarith)
      have hrec := psi_factorial_recurrence hlarge
      have hi := ih _ hless (y / 60) rfl (by positivity)
      dsimp [RS_prime.c₀] at hi ⊢
      nlinarith
  exact h ⌊x⌋₊ x rfl hx

end RS12Factorial

/-- The source theorem, retained as the interface to the ported development. -/
theorem RS_prime.theorem_12 {x : ℝ} (hx : 0 < x) : ψ x < RS_prime.c₀ * x :=
  RS12Factorial.psi_upper_all hx
