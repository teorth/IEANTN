/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeCounting

/-!
# Node `DudekPlatt.v3`

**Dudek and Platt's Lemma 2.1, repaired**: the criterion carrying a two-sided explicit estimate for
`π(x)` to Ramanujan's inequality `π(x)² < (e x / log x) · π(x/e)`, stated for arbitrary parameters.

A **variant** of `DudekPlatt.v1` and `.v2`, and the pipeline both of them are instances of. It
imports nothing — every input arrives as a hypothesis — so a Lean proof is its whole justification.

## Why "repaired"

Lemma 2.1 as printed does not prove what it claims, and the gap is in the treatment of the lower
bound. The paper writes (end of page 3 of arXiv:1407.1901, and the same step in the published
Exp. Math. version)

`(ex/log x) π(x/e) > (x²/log x) Σ_{k=0}^{4} k!/(log x − 1)^{k+1} + mₐ x/(log x − 1)⁶`

and then replaces each `1/(log x − 1)^{k+1}` by the **lower** bound obtained from truncating

`1/(log x − 1)^{k+1} = (1/log^{k+1} x)(1 + 1/log x + 1/log²x + ⋯)^{k+1}`
`  > (1/log^{k+1} x)(1 + 1/log x + ⋯ + 1/log^{5−k} x)^{k+1}`.

For the factorial terms, whose coefficients `k!` are positive, that is valid. **For the `mₐ` term it
is valid only when `mₐ ≥ 0`** — lower-bounding `1/(log x − 1)⁶` and multiplying by a negative `mₐ`
gives an *upper* bound on that term, which is the wrong direction for a lower bound on the whole.

And `mₐ` is negative in every application: the published paper uses `mₐ = −3103.33`. So the
argument as written never uses the branch in which it is valid. What is needed there is an **upper**
bound for `1/(log x − 1)^{k+1}`.

The repair is a case split, and it is the difference between `εPos` and `εNeg` below: the
coefficient on `mₐ` is `1` in the first and `(1 + 1/log xₐ)⁶` in the second. Since `mₐ < 0` and
`(1 + 1/log xₐ)⁶ > 1`, the corrected term is *more* negative — a weaker and valid lower bound. The
paper's `ε'` is `εPos`, applied where `εNeg` was required.

The effect is confined to seventh-order terms and the thresholds move only slightly, which is why
the paper's conclusions are believed to stand. But the argument does need this, and a Lean proof
cannot paper over it.

`PrimeNumberTheoremAnd` carries the repair, as `εlower` and `shift_m_lower_of_nonpos`; the
statement below follows its shape.

## What the criterion is not

It is not a claim that Ramanujan's inequality holds. It is the implication from an explicit
two-sided estimate for `π` to that inequality, above a threshold the hypotheses pin down. Supplying
the estimate is `DudekPlattNumerics.v1`'s job, and the instances are `DudekPlatt.v1` and `.v2`.
-/

namespace DudekPlatt.v3

open IEANTN

/-- The main term both halves of the estimate share, `x Σ_{k=0}^{4} k!/(log x)^{k+1}` — the fifth
partial sum of `li`'s asymptotic expansion.

Spelled the same way in `DudekPlattNumerics.v1`. Repeated rather than imported so that this node
depends on nothing, which is what lets it be verified on its own. -/
noncomputable def mainTerm (x : ℝ) : ℝ :=
  x * ∑ k ∈ Finset.range 5, (Nat.factorial k : ℝ) / Real.log x ^ (k + 1)

/-- The seventh-order term controlling the **upper** bound for `π(x)²`, from an upper estimate with
constant `M`. All of its coefficients are non-negative, so no sign condition is needed. -/
noncomputable def εUpper (M x : ℝ) : ℝ :=
  72 + 2 * M + (2 * M + 132) / Real.log x + (4 * M + 288) / Real.log x ^ (2 : ℕ)
    + (12 * M + 576) / Real.log x ^ (3 : ℕ) + 48 * M / Real.log x ^ (4 : ℕ)
    + M ^ (2 : ℕ) / Real.log x ^ (5 : ℕ)

/-- The seventh-order term controlling the **lower** bound, in the case `0 ≤ m` — this is the
paper's `ε'`, and in this case the paper's derivation of it is sound. -/
noncomputable def εPos (m x : ℝ) : ℝ :=
  206 + m + 364 / Real.log x + 381 / Real.log x ^ (2 : ℕ) + 238 / Real.log x ^ (3 : ℕ)
    + 97 / Real.log x ^ (4 : ℕ) + 30 / Real.log x ^ (5 : ℕ) + 8 / Real.log x ^ (6 : ℕ)

/-- The seventh-order term controlling the lower bound in the case `m < 0` — **the repair**.

Identical to `εPos` except that the coefficient on `m` is `(1 + 1/log xₐ)⁶` rather than `1`. With
`m < 0` that makes the term more negative, which is the direction a valid lower bound must move. It
is what comes out of bounding `1/(log x − 1)⁶` from **above** by `(1 + 1/log xₐ)⁶ / log⁶ x`, using
`log xₐ + 1 ≤ log x`. -/
noncomputable def εNeg (m xₐ x : ℝ) : ℝ :=
  206 + (1 + 1 / Real.log xₐ) ^ (6 : ℕ) * m + 364 / Real.log x + 381 / Real.log x ^ (2 : ℕ)
    + 238 / Real.log x ^ (3 : ℕ) + 97 / Real.log x ^ (4 : ℕ) + 30 / Real.log x ^ (5 : ℕ)
    + 8 / Real.log x ^ (6 : ℕ)

/-- The lower-bound seventh-order term, split on the sign of `m`.

**This case split is the whole content of the erratum.** The paper uses `εPos` unconditionally, and
uses it only ever with `m < 0`. -/
noncomputable def εLower (m xₐ x : ℝ) : ℝ :=
  if 0 ≤ m then εPos m x else εNeg m xₐ x

/-- **Lemma 2.1, repaired.** Let `1 < xₐ`, let `mₐ` and `Mₐ` bound `π` from below and above in the
shape

`mainTerm x + mₐ x/(log x)⁶ < π(x)` for `x > xₐ`, and
`π(x) < mainTerm x + Mₐ x/(log x)⁶` for `x > e·xₐ`,

let `x₀ ≥ e·xₐ`, and suppose the threshold condition

`εUpper Mₐ x − εLower mₐ xₐ x < log x`

holds for every `x > x₀`. Then Ramanujan's inequality `π(x)² < (e x / log x) · π(x/e)` holds for
every `x > x₀`.

Three things about the shape are worth not losing.

**The threshold condition is a comparison against `log x`, not against zero.** One might expect to
need the lower-bound term to dominate the upper-bound term; what is actually needed is that their
difference stay below `log x`. At the paper's parameters `Mₐ = 3343.48`, `mₐ = −3103.33` the
leading difference is `(72 + 2Mₐ) − (206 + mₐ) ≈ 9656`, and the paper's threshold is `exp(9657.8)`
— so the condition is satisfied with very little room, and reading it as a comparison against zero
makes the whole argument look false.

**The two estimates are needed on different ranges.** The lower bound is applied at `x/e` and so is
wanted from `xₐ`; the upper bound is applied at `x` and so is wanted only from `e·xₐ`. The
asymmetry is real and a solution that demands both on the same range is proving something stronger
than it needs.

**`εLower` is where the erratum lives.** A statement using `εPos` unconditionally in its place
would be the paper's flawed version, and would be false as an implication for negative `mₐ`. -/
noncomputable def criterion : Prop :=
  ∀ mₐ Mₐ xₐ x₀ : ℝ, 1 < xₐ →
    (∀ x > xₐ, mainTerm x + mₐ * x / Real.log x ^ (6 : ℕ) < primeCounting x) →
    (∀ x > Real.exp 1 * xₐ,
      primeCounting x < mainTerm x + Mₐ * x / Real.log x ^ (6 : ℕ)) →
    Real.exp 1 * xₐ ≤ x₀ →
    (∀ x > x₀, εUpper Mₐ x - εLower mₐ xₐ x < Real.log x) →
    ∀ x > x₀,
      primeCounting x ^ (2 : ℕ) < Real.exp 1 * x / Real.log x * primeCounting (x / Real.exp 1)

end DudekPlatt.v3
