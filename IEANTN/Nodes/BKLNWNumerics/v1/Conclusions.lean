/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taksh Kothari
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Nodes.BKLNW.v1.Tables

/-!
# Node `BKLNWNumerics`

Table-driven claims from Broadbent–Kadiri–Lumley–Ng–Wilk, split off `BKLNW.v1` so the
paper node is not also a computation node.  Statements match `BKLNW.v1`; this node is
the importable numerical source.  Analytic Corollary 5.1 stays on the paper family.

**The data itself stays on `BKLNW.v1`.** This node imports `BKLNW.v1.Tables`, which the
architecture allows from any node, rather than carrying its own copy of Table 8: two
copies of 58 rows can diverge, and one of them would then be silently wrong. What is split
off here is the *claim about* the table, not the table.
-/

namespace BKLNWNumerics.v1

open IEANTN

/-- **Table 8**: for consecutive entries `(b, ε)` and `(b', ε')` of the table,
`|ψ(x) − x| ≤ ε · x` for all `e^b ≤ x ≤ e^b'`.

Same reading as `BKLNW.v1.table8_psi_bound` / Corollary 8.1, over the same rows —
`BKLNW.v1.table8` is the one copy of the data. `zip` with `tail` is consecutive entries
and says nothing about the last row. -/
def table8_psi_bound : Prop :=
  ∀ p ∈ BKLNW.v1.table8.zip BKLNW.v1.table8.tail, ∀ x : ℝ,
    Real.exp (p.1.1 : ℝ) ≤ x → x ≤ Real.exp (p.2.1 : ℝ) → |Chebyshev.psi x - x| ≤ p.1.2 * x

/-- **Tables 13 and 14**, as `FKS2` uses them: `Eθ(x) ≤ 1` for every `2 ≤ x ≤ e³⁰`.

Same as `BKLNW.v1.theta_error_le_one`. -/
def theta_error_le_one : Prop :=
  ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 30 → Eθ x ≤ 1

end BKLNWNumerics.v1
