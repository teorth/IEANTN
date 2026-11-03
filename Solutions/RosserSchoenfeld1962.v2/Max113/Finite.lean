/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Max113.Data19

namespace RS12Max113
open Chebyshev

/-- The complete reused finite range with a five-unit absolute improvement. -/
theorem finite_integer {n : ℕ} (hlo : 600 < n) (hhi : n ≤ 500000) :
    ψ (n : ℕ) + 5 ≤ 1.038829 * n :=
  (shifted_join (shifted_join (shifted_join (shifted_join certificate_00.2 certificate_01.2) (shifted_join certificate_02.2 (shifted_join certificate_03.2 certificate_04.2))) (shifted_join (shifted_join certificate_05.2 certificate_06.2) (shifted_join certificate_07.2 (shifted_join certificate_08.2 certificate_09.2)))) (shifted_join (shifted_join (shifted_join certificate_10.2 certificate_11.2) (shifted_join certificate_12.2 (shifted_join certificate_13.2 certificate_14.2))) (shifted_join (shifted_join certificate_15.2 certificate_16.2) (shifted_join certificate_17.2 (shifted_join certificate_18.2 certificate_19.2))))) n hlo hhi

end RS12Max113
