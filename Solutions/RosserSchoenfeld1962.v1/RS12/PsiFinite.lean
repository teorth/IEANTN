/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import RS12.PsiData19

namespace RS12PsiInteger
open Chebyshev

private theorem psi_range_600_50600 : ∀ m : ℕ, 600 < m → m ≤ 50600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_00.2 psi_certificate_01.2


private theorem psi_range_75600_125600 : ∀ m : ℕ, 75600 < m → m ≤ 125600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_03.2 psi_certificate_04.2


private theorem psi_range_50600_125600 : ∀ m : ℕ, 50600 < m → m ≤ 125600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_02.2 psi_range_75600_125600


private theorem psi_range_600_125600 : ∀ m : ℕ, 600 < m → m ≤ 125600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_range_600_50600 psi_range_50600_125600


private theorem psi_range_125600_175600 : ∀ m : ℕ, 125600 < m → m ≤ 175600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_05.2 psi_certificate_06.2


private theorem psi_range_200600_250600 : ∀ m : ℕ, 200600 < m → m ≤ 250600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_08.2 psi_certificate_09.2


private theorem psi_range_175600_250600 : ∀ m : ℕ, 175600 < m → m ≤ 250600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_07.2 psi_range_200600_250600


private theorem psi_range_125600_250600 : ∀ m : ℕ, 125600 < m → m ≤ 250600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_range_125600_175600 psi_range_175600_250600


private theorem psi_range_600_250600 : ∀ m : ℕ, 600 < m → m ≤ 250600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_range_600_125600 psi_range_125600_250600


private theorem psi_range_250600_300600 : ∀ m : ℕ, 250600 < m → m ≤ 300600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_10.2 psi_certificate_11.2


private theorem psi_range_325600_375600 : ∀ m : ℕ, 325600 < m → m ≤ 375600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_13.2 psi_certificate_14.2


private theorem psi_range_300600_375600 : ∀ m : ℕ, 300600 < m → m ≤ 375600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_12.2 psi_range_325600_375600


private theorem psi_range_250600_375600 : ∀ m : ℕ, 250600 < m → m ≤ 375600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_range_250600_300600 psi_range_300600_375600


private theorem psi_range_375600_425600 : ∀ m : ℕ, 375600 < m → m ≤ 425600 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_15.2 psi_certificate_16.2


private theorem psi_range_450600_500000 : ∀ m : ℕ, 450600 < m → m ≤ 500000 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_18.2 psi_certificate_19.2


private theorem psi_range_425600_500000 : ∀ m : ℕ, 425600 < m → m ≤ 500000 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_certificate_17.2 psi_range_450600_500000


private theorem psi_range_375600_500000 : ∀ m : ℕ, 375600 < m → m ≤ 500000 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_range_375600_425600 psi_range_425600_500000


private theorem psi_range_250600_500000 : ∀ m : ℕ, 250600 < m → m ≤ 500000 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_range_250600_375600 psi_range_375600_500000


private theorem psi_range_600_500000 : ∀ m : ℕ, 600 < m → m ≤ 500000 →
    ψ (m : ℕ) ≤ 1.038829 * m := psiRange_join psi_range_600_250600 psi_range_250600_500000


theorem psi_finite_integer {m : ℕ} (hlo : 600 < m) (hhi : m ≤ 500000) :
    ψ (m : ℕ) ≤ 1.038829 * m :=
  psi_range_600_500000 m hlo hhi
end RS12PsiInteger
