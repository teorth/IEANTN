/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.ChebyshevNumerics.v1.Conclusions

/-!
# Examples: `ChebyshevNumerics.v1`

Consequences of the finite check, taken as a hypothesis. The endpoint `11723` is included
because the statement is `≤`, and `0` is included because the quantifier is every natural
number up to that bound. Neither example imports the sorried challenge.
-/

namespace ChebyshevNumerics.v1

example (h : psi_le_below_11723) : Chebyshev.psi 11723 ≤ 1.11 * 11723 :=
  h 11723 (by norm_num)

example (h : psi_le_below_11723) : Chebyshev.psi 0 ≤ 1.11 * 0 :=
  h 0 (by norm_num)

end ChebyshevNumerics.v1
