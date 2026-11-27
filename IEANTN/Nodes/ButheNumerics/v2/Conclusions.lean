/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Teddy Tennant
-/
import Mathlib.NumberTheory.Chebyshev
import IEANTN.Vocabulary.PrimeCounting

/-!
# Node `ButheNumerics.v2`

`ButheNumerics.v1.lemma_3_constant_nonpos`, split out so that it can be proved on its own. A node
is verified all at once, and the other four conclusions of `ButheNumerics.v1` are computations on
ranges up to `5 · 10¹⁰`, so a proof of this one could not be a receipt there.

The statement is copied unchanged. `ButheNumerics.v1`'s module docstring explains where the
constant comes from and why (1.9) needs its sign.
-/

namespace ButheNumerics.v2

open IEANTN

/-- **The constant in Büthe's Lemma 3 at `a = 1500` is non-positive**, copied from
`ButheNumerics.v1.lemma_3_constant_nonpos`.

`A = π(1500) − li(1500) + (1500 − θ(1500)) / log 1500 ≤ 0`.

Numerically `A ≈ −3.64`: `π(1500) = 239`, `li(1500) ≈ 247.81` and `θ(1500) ≈ 1462.14`. -/
noncomputable def lemma_3_constant_nonpos : Prop :=
  primeCounting 1500 - li 1500 + (1500 - Chebyshev.theta 1500) / Real.log 1500 ≤ 0

end ButheNumerics.v2
