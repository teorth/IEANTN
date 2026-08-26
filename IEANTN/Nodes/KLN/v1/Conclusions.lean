/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.Zeta

/-!
# Node `KLN.v1`

Kadiri, Lumley and Ng, *Explicit zero density for the Riemann zeta function*,
J. Math. Anal. Appl. **465** (2018), 22–46.

An explicit zero density estimate: a bound on the number of zeros of `ζ` in a rectangle to the
right of the critical line. Together with a zero-free region it is one of the two analytic inputs
the explicit Chebyshev bounds rest on.

## A corrected constant, and why the correction is small

The paper's Lemma 3.2 quotes an explicit van der Corput subconvexity bound on the critical line,

`|ζ(1/2 + it)| ≤ a₁ t^{1/6} log t` for `t ≥ 3`,

with `a₁ = 0.63`, attributed to Hiary. `FKS` (J. Math. Anal. Appl. **527** (2023) 127426) reports
that this value rests on an erroneous explicit version of the Cheng–Graham second derivative test,
that the corrected constant is `0.77`, and that the error "would render many results concerning the
prime number theorem unreliable" — `FKS` names four such papers. It then redoes its own work with
`0.77`. A later preprint of Hiary, Patel and Yang announces `0.618`, better than either.

**The conclusion below states `0.77`, not the printed `0.63`.** A node stating a value known to be
wrong has no legitimate consumer: nothing may soundly import it, and its presence works directly
against what the network is for. Keeping a faithful-to-print `v1` and a corrected `v2` would leave
`v1` with no valid use at all, so the correction is made in place and recorded here.

Note what the error does *not* touch. `a₁` enters this paper as an **input**, quoted from
elsewhere; the density method and the structure of Theorem 1.1 are unaffected. What changes is
which numerical values come out the other end.

## What is deliberately not stated

**Theorem 1.1 itself, and the numerical density tables.** The theorem's constants `C₁` and `C₂` are
defined by long expressions in §4 depending on seven parameters, and its published numerical
instances — `N(0.90, T) < 11.499 (log T)^{16/5} T^{4/15} + 3.186 (log T)²`, and the tables of §5 —
are computed *with* `a₁ = 0.63`. Nobody has published the recomputed values: `FKS` redid its own
estimates rather than reissuing this paper's tables.

So those numbers cannot be corrected here, only recomputed, which is work for someone with the
method in hand. Transcribing them as printed would reintroduce exactly the unreliability this node
exists to avoid.
-/

namespace KLN.v1

open IEANTN

/-- **Lemma 3.2, with the constant corrected.** `|ζ(1/2 + it)| ≤ 0.77 · t^{1/6} · log t` for every
`t ≥ 3`.

The paper prints `0.63`; see the module docstring for why `0.77` is stated instead. The bound
itself is Hiary's, quoted here in the form the density argument uses, and the correction is `FKS`'s.

`FKS` consumes exactly this: "in the present work we shall use the worse sub-convexity bound for
the Riemann zeta function, namely 0.77, and still recover, and actually improve on, these previous
results". -/
def subconvexity_bound : Prop :=
  ∀ t : ℝ, 3 ≤ t →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 0.77 * t ^ ((1 : ℝ) / 6) * Real.log t

end KLN.v1
