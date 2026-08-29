/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions

/-!
# The two shift estimates

Both express `1/(log x − 1)^k` in terms of `1/(log x)^k`, and between them they are the whole
content of the erratum in Dudek–Platt's Lemma 2.1.

`shift_factorial_lower` handles the terms with positive coefficients `k!`, where a **lower** bound
on `1/(l−1)^{k+1}` is what is wanted, and the paper's own truncation argument is sound.

`shift_m_lower_of_nonpos` handles the term carrying `m`, where the paper applies the same lower
bound — valid only for `m ≥ 0`, and `m` is negative in every application. Bounding
`1/(l−1)^6` from **above** instead, by `(1 + 1/log xₐ)^6 / l^6`, is what makes the argument go
through for negative `m`, and the extra factor `(1 + 1/log xₐ)^6 > 1` is the difference between
`DudekPlatt.v3.εPos` and `DudekPlatt.v3.εNeg`.

Following `PrimeNumberTheoremAnd`'s `Ramanujan.shift_factorial_lower` and
`Ramanujan.shift_m_lower_of_nonpos`, which carry the same repair.
-/

open Real

namespace DudekPlattSol

/-- The positive-coefficient shift. Purely algebraic: the difference is a quotient whose numerator
is a polynomial in `l − 1` with non-negative coefficients. -/
lemma shift_factorial_lower (l : ℝ) (hl : 1 < l) :
    1 / l * (1 / (l - 1) + 1 / (l - 1) ^ 2 + 2 / (l - 1) ^ 3
        + 6 / (l - 1) ^ 4 + 24 / (l - 1) ^ 5)
      ≥ 1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 65 / l ^ 6
        + (206 + 364 / l + 381 / l ^ 2 + 238 / l ^ 3
            + 97 / l ^ 4 + 30 / l ^ 5 + 8 / l ^ 6) / l ^ 7 := by
  have hl0 : 0 < l := by linarith
  have hlm1 : 0 < l - 1 := by linarith
  have hdiff :
      1 / l *
          (1 / (l - 1) + 1 / (l - 1) ^ 2 + 2 / (l - 1) ^ 3 + 6 / (l - 1) ^ 4 + 24 / (l - 1) ^ 5)
        - (1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 65 / l ^ 6 +
            (206 + 364 / l + 381 / l ^ 2 + 238 / l ^ 3 + 97 / l ^ 4 + 30 / l ^ 5 + 8 / l ^ 6)
              / l ^ 7)
      = (153 * (l - 1) ^ 10 + 1484 * (l - 1) ^ 9 + 6249 * (l - 1) ^ 8 + 14886 * (l - 1) ^ 7 +
          22027 * (l - 1) ^ 6 + 21083 * (l - 1) ^ 5 + 13345 * (l - 1) ^ 4 + 5701 * (l - 1) ^ 3 +
          1658 * (l - 1) ^ 2 + 294 * (l - 1) + 24) / (l ^ 13 * (l - 1) ^ 5) := by
    field_simp [hl0.ne', hlm1.ne']
    ring
  have hnum_nonneg :
      0 ≤ 153 * (l - 1) ^ 10 + 1484 * (l - 1) ^ 9 + 6249 * (l - 1) ^ 8 + 14886 * (l - 1) ^ 7 +
          22027 * (l - 1) ^ 6 + 21083 * (l - 1) ^ 5 + 13345 * (l - 1) ^ 4 + 5701 * (l - 1) ^ 3 +
          1658 * (l - 1) ^ 2 + 294 * (l - 1) + 24 := by
    positivity
  have hden_pos : 0 < l ^ 13 * (l - 1) ^ 5 := by positivity
  have hdelta_nonneg :
      0 ≤ 1 / l *
            (1 / (l - 1) + 1 / (l - 1) ^ 2 + 2 / (l - 1) ^ 3 + 6 / (l - 1) ^ 4 + 24 / (l - 1) ^ 5)
          - (1 / l ^ 2 + 2 / l ^ 3 + 5 / l ^ 4 + 16 / l ^ 5 + 65 / l ^ 6 +
              (206 + 364 / l + 381 / l ^ 2 + 238 / l ^ 3 + 97 / l ^ 4 + 30 / l ^ 5 + 8 / l ^ 6)
                / l ^ 7) := by
    rw [hdiff]
    exact div_nonneg hnum_nonneg hden_pos.le
  linarith

/-- **The repair.** For `m ≤ 0`, the correct lower bound on `m / (l (l−1)^6)` uses `(1 + 1/log xₐ)^6`
rather than `1`.

The step is: `l/(l−1) ≤ 1 + 1/log xₐ` whenever `log xₐ + 1 ≤ l`, so raising to the sixth power and
multiplying by the *non-positive* `m / l^7` reverses the inequality — which is exactly the direction
a lower bound needs, and exactly what the paper's uniform use of the truncation misses. -/
lemma shift_m_lower_of_nonpos (m xₐ l : ℝ) (hm : m ≤ 0) (hxₐ : 0 < log xₐ)
    (hl : log xₐ + 1 ≤ l) :
    m / (l * (l - 1) ^ 6) ≥ ((1 + 1 / log xₐ) ^ 6 * m) / l ^ 7 := by
  have hlm1_pos : 0 < l - 1 := by linarith
  have hl_pos : 0 < l := by linarith
  have hbase : l / (l - 1) ≤ 1 + 1 / log xₐ := by
    have hlog_le : log xₐ ≤ l - 1 := by linarith
    have hsum : 1 + 1 / (l - 1) ≤ 1 + 1 / log xₐ := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (one_div_le_one_div_of_le hxₐ hlog_le) 1
    have hratio : l / (l - 1) = 1 + 1 / (l - 1) := by
      field_simp [hlm1_pos.ne']
      ring
    simpa [hratio] using hsum
  have hleft : m / (l * (l - 1) ^ 6) = (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    field_simp [hl_pos.ne', hlm1_pos.ne']
  have hright : ((1 + 1 / log xₐ) ^ 6 * m) / l ^ 7 = (m / l ^ 7) * (1 + 1 / log xₐ) ^ 6 := by
    ring
  rw [hleft, hright]
  exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ (by positivity) hbase 6)
    (div_nonpos_of_nonpos_of_nonneg hm (pow_nonneg hl_pos.le _))

/-- The positive-`m` counterpart, for completeness: when `0 ≤ m` the paper's own direction is
correct, and no `(1 + 1/log xₐ)^6` factor is needed. `εLower` selects between this branch and the
one above, which is the whole of the repair. -/
lemma shift_m_lower_of_nonneg (m l : ℝ) (hm : 0 ≤ m) (hl : 1 < l) :
    m / (l * (l - 1) ^ 6) ≥ m / l ^ 7 := by
  have hl0 : 0 < l := by linarith
  have hlm1 : 0 < l - 1 := by linarith
  have hratio_ge1 : 1 ≤ l / (l - 1) := (le_div_iff₀ hlm1).2 (by linarith)
  have hpow : 1 ≤ (l / (l - 1)) ^ 6 := one_le_pow₀ hratio_ge1
  have hmdiv_nonneg : 0 ≤ m / l ^ 7 := div_nonneg hm (pow_nonneg hl0.le _)
  have hmul : m / l ^ 7 ≤ (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_left hpow hmdiv_nonneg
  have hrepr : m / (l * (l - 1) ^ 6) = (m / l ^ 7) * (l / (l - 1)) ^ 6 := by
    field_simp [hl0.ne', hlm1.ne']
  rw [hrepr]
  exact hmul

end DudekPlattSol
