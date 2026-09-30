/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao, Taksh Kothari
-/
import IEANTN.Vocabulary.ErrorTerms

/-!
# Tables: `Buthe.v1`

Data from Büthe, *An analytic method for bounding ψ(x)*, Math. Comp. **87** (2018), 1991–2009.
Data only — what is claimed *about* it is in `Conclusions.lean`.

Table 1 matches the PNT+ transcription (`Buthe.table_1`) and the printed Table 1 of
arXiv:1511.02032v2: upper and lower bounds `M±_ψ(x)` for `(t − ψ(t)) / √t` on each dyadic
interval `[x, 2x]`.

Table 2 is the matching table for `(li(t) − π*(t)) · (log t) / √t`, read from the same preprint's
Table 2; PNT+ does not carry it.
-/

namespace Buthe.v1

/-- **Table 1**: rows `(x, M⁻_ψ(x), M⁺_ψ(x))`.

Equation (6.2) of the paper (and of the PNT+ transcription) reads: if `(x, M⁻, M⁺)` is a row,
then `M⁻ ≤ (t − ψ(t)) / √t ≤ M⁺` for all `t ∈ [x, 2x]`. The last three rows start at
`128 · 10¹⁶`, `256 · 10¹⁶` and `512 · 10¹⁶`; twice the last of those is past `10¹⁹`, which is
the range of Theorem 2, so a consumer that needs a uniform range should stop at a row whose
`2x` still sits inside that range.

Cross-checked against PNT+'s `table_1` (31 rows) and against the first/last printed blocks
(`10¹⁰`, `−0.77`, `0.85` and `512 · 10¹⁶`, `−0.83`, `0.94`). -/
def table_1 : List (ℝ × ℝ × ℝ) :=
  [
    (10 ^ 10, -0.77, 0.85),
    (2 * 10 ^ 10, -0.75, 0.64),
    (4 * 10 ^ 10, -0.73, 0.80),
    (8 * 10 ^ 10, -0.80, 0.86),
    (16 * 10 ^ 10, -0.88, 0.68),
    (32 * 10 ^ 10, -0.88, 0.78),
    (64 * 10 ^ 10, -0.66, 0.74),
    (10 ^ 12, -0.80, 0.81),
    (2 * 10 ^ 12, -0.79, 0.76),
    (4 * 10 ^ 12, -0.73, 0.73),
    (8 * 10 ^ 12, -0.80, 0.76),
    (16 * 10 ^ 12, -0.80, 0.68),
    (32 * 10 ^ 12, -0.67, 0.93),
    (64 * 10 ^ 12, -0.78, 0.77),
    (10 ^ 14, -0.79, 0.72),
    (2 * 10 ^ 14, -0.60, 0.76),
    (4 * 10 ^ 14, -0.65, 0.73),
    (8 * 10 ^ 14, -0.81, 0.88),
    (16 * 10 ^ 14, -0.66, 0.86),
    (32 * 10 ^ 14, -0.74, 0.86),
    (64 * 10 ^ 14, -0.73, 0.66),
    (10 ^ 16, -0.88, 0.74),
    (2 * 10 ^ 16, -0.87, 0.70),
    (4 * 10 ^ 16, -0.65, 0.73),
    (8 * 10 ^ 16, -0.82, 0.77),
    (16 * 10 ^ 16, -0.71, 0.92),
    (32 * 10 ^ 16, -0.78, 0.71),
    (64 * 10 ^ 16, -0.94, 0.82),
    (128 * 10 ^ 16, -0.94, 0.75),
    (256 * 10 ^ 16, -0.82, 0.86),
    (512 * 10 ^ 16, -0.83, 0.94)
  ]

/-- **Table 2**: rows `(x, M⁻_{π*}(x), M⁺_{π*}(x))`.

If `(x, M⁻, M⁺)` is a row, then `M⁻ ≤ (li(t) − π*(t)) · (log t) / √t ≤ M⁺` for all `t ∈ [x, 2x]`.
The paper reads Theorem 2's equation (1.8) for `x ≥ 10⁷` off these bounds together with its
Lemma 2; the last three rows again start past where `2x` sits inside `10¹⁹`.

Transcribed from arXiv:1511.02032v2 Table 2. Cross-checked at the first and last printed blocks
(`10¹⁰`, `−0.87`, `0.95` and `512 · 10¹⁶`, `−0.88`, `0.99`). -/
def table_2 : List (ℝ × ℝ × ℝ) :=
  [
    (10 ^ 10, -0.87, 0.95),
    (2 * 10 ^ 10, -0.84, 0.73),
    (4 * 10 ^ 10, -0.82, 0.89),
    (8 * 10 ^ 10, -0.89, 0.95),
    (16 * 10 ^ 10, -0.97, 0.76),
    (32 * 10 ^ 10, -0.96, 0.86),
    (64 * 10 ^ 10, -0.74, 0.82),
    (10 ^ 12, -0.88, 0.89),
    (2 * 10 ^ 12, -0.87, 0.84),
    (4 * 10 ^ 12, -0.81, 0.81),
    (8 * 10 ^ 12, -0.87, 0.84),
    (16 * 10 ^ 12, -0.87, 0.76),
    (32 * 10 ^ 12, -0.74, 1),
    (64 * 10 ^ 12, -0.85, 0.84),
    (10 ^ 14, -0.86, 0.79),
    (2 * 10 ^ 14, -0.67, 0.83),
    (4 * 10 ^ 14, -0.72, 0.80),
    (8 * 10 ^ 14, -0.87, 0.95),
    (16 * 10 ^ 14, -0.72, 0.93),
    (32 * 10 ^ 14, -0.80, 0.92),
    (64 * 10 ^ 14, -0.79, 0.72),
    (10 ^ 16, -0.94, 0.80),
    (2 * 10 ^ 16, -0.93, 0.76),
    (4 * 10 ^ 16, -0.71, 0.79),
    (8 * 10 ^ 16, -0.88, 0.83),
    (16 * 10 ^ 16, -0.77, 0.98),
    (32 * 10 ^ 16, -0.84, 0.77),
    (64 * 10 ^ 16, -1, 0.88),
    (128 * 10 ^ 16, -1, 0.80),
    (256 * 10 ^ 16, -0.87, 0.91),
    (512 * 10 ^ 16, -0.88, 0.99)
  ]

end Buthe.v1
