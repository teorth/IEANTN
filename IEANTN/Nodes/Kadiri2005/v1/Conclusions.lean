/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary

/-!
# Node `Kadiri2005.v1`

An explicit zero-free region of classical de la Vallee Poussin shape: zeta has no zeros in a
region defined by an explicit constant. The other analytic input, alongside a zero density
estimate, to explicit bounds on the Chebyshev functions.

Kadiri's value `R = 5.69693` is the one `MT` starts from: its Section 3 selects `R = 5.7` as the
already-established region before iterating, and `5.7` is `Kadiri`'s value rounded off in the safe
direction.

## The value, and which version of the paper it comes from

The published paper (Acta Arith. **117** (2005), 303-339) gives `5.69693`, which is the value the
whole subsequent literature cites and the one stated below. The arXiv preprint held in the local
library, `math/0401238`, gives `5.70176` in its abstract -- a slightly weaker value that the
published version improved. The published paper has not been obtained; `5.69693` is recorded here
at second hand from `MT`, which states it twice (its Table 1 and its Section 2, where it also
records the parameters Kadiri chose). See `docs/SOURCES.md`.
-/

namespace Kadiri2005.v1

open IEANTN

/-- **The zero-free region.** The classical zero-free region holds with `R = 5.69693`.

`ζ` has no zeroes with `Re s ≥ 1 - 1/(R log |Im s|)` and `Im s ≥ 3`. Kadiri obtained this by
an iterative procedure starting from Rosser and Schoenfeld's region and a height to which the
Riemann hypothesis had been verified; `MT` Section 2 records the parameters.

Note the shape. Kadiri states the region for `|Im s| ≥ 2`, and the vocabulary here requires
`Im s ≥ 3`, so this conclusion is weaker than the paper on `2 ≤ |Im s| < 3`. That is the common
denominator across the nodes that state a classical region, not a limitation of this paper. -/
def zero_free_region : Prop :=
  ClassicalZeroFreeRegion 5.69693

end Kadiri2005.v1
