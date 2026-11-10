/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Helfgott
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `RosserYoheSchoenfeld.v1`

J. Barkley Rosser, J. M. Yohe and Lowell Schoenfeld, *Rigorous computation and the zeros of the
Riemann zeta-function*, Information Processing 68 (Proc. IFIP Congress 1968), pp. 70–76.

Up to 1977, the farthest-reaching verification of the Riemann hypothesis was that of Rosser, Yohe
and Schoenfeld, which checked that the first `3 500 000` zeros of `ζ(s)` lie on the critical line.
It was implemented with extreme care; see the paper. They actually went a little further: Rosser
and Schoenfeld (1975) say that this work, together with an observation by Rosser (1970), gives the
Riemann hypothesis for the first `3 502 500` zeros. That is the assumption used in the classic
"Sharper bounds" papers of the mid-1970s (Rosser–Schoenfeld 1975, Schoenfeld 1976, …), on which
much of the later literature rests.

## The height

Rosser and Schoenfeld (1975) use this assumption at the height `A = 1894438.51224…`, the solution
of `F(A) = 3 502 500` with `F(T) = (T/2π) log(T/2π) − T/2π + 7/8`, and they use `N(A) = F(A)`:
exactly `3 502 500` zeros of `ζ` in the critical strip have imaginary part in `(0, A]`. This node
states the Riemann hypothesis up to `1894438.5122`, which is `A` rounded down, so the historical
computation covers it.

It is deliberately not stated at the nearby integer `1894439`. The LMFDB lists the `3 502 500`th
zero at height `1894438.29779…` and the `3 502 501`st at `1894438.63746…` (the next one is above
`1894439`). So the Riemann hypothesis up to `1894439` is a claim about one zero more than Rosser,
Yohe and Schoenfeld verified.

The statement is meant to be verified in Lean directly as well; that is expected to be within reach
of a powerful desktop machine. On today's evidence it holds, since every modern verification reaches
far beyond this height; the bridge `IEANTN/Bridges/Platt/P2015ToRosserYoheSchoenfeld.lean` records
that in Lean, as a spare justification. The designated justification stays the historical one,
because this node exists to record what the 1970s papers relied on.
-/

namespace RosserYoheSchoenfeld.v1

open IEANTN

/-- **The Riemann hypothesis up to `1894438.5122`.**

This is the computation of Rosser, Yohe and Schoenfeld (the first `3 500 000` zeros), extended by
Rosser (1970) to the first `3 502 500` zeros, as stated by Rosser–Schoenfeld (1975) and assumed
there and in Schoenfeld (1976). The height is their `A = 1894438.51224…` rounded down; the zeros
with imaginary part in `(0, 1894438.5122]` are exactly the first `3 502 500`. -/
def rh_up_to : Prop :=
  RiemannHypothesisUpTo 1894438.5122

end RosserYoheSchoenfeld.v1
