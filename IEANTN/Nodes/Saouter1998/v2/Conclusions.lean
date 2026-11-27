/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Hubbard
-/
import IEANTN.Vocabulary.Goldbach

/-!
# Node `Saouter1998.v2`

`Saouter1998.v1.odd_up_to_1e20`, split out so that it can be proved on its own. A node is verified
all at once, and the other conclusion of `Saouter1998.v1`, `prime_ladder`, is a computation of
about `2.5·10⁸` certified primes that stays numerical there, so a proof of this one could not be a
receipt on `Saouter1998.v1`.

The statement is copied unchanged, and so are its imports: Saouter's ladder,
`Saouter1998.v1.prime_ladder`, and the even verification `Richstein2001.v1.even_up_to_4e14`. The
challenge carries both as hypotheses, so what is proved here is the paper's implication from the
ladder and the even input to the odd range. `Saouter1998.v1`'s module docstring explains the
ladder, the even input, and the misprinted constant on page 865.
-/

namespace Saouter1998.v2

open IEANTN

/-- **The odd Goldbach conjecture up to `10²⁰`**, copied from `Saouter1998.v1.odd_up_to_1e20`.
Every odd `n` with `7 ≤ n ≤ 10²⁰` is a sum of three primes.

The paper's result, stated in its title and abstract, here imported against Saouter's ladder and
the even verification to `4·10¹⁴`. -/
def odd_up_to_1e20 : Prop :=
  GoldbachOddUpTo (10 ^ 20)

end Saouter1998.v2
