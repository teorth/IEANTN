/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Node `CH2.v4`

The **contour-shifting half** of Chirre–Helfgott, arXiv:2512.15709 §5: the identity that moves an
integral off the line `Re s = 1` and onto a contour running out to `Re s = -∞`, picking up the
poles in between.

A **variant** of `CH2.v2` and `CH2.v3`, not a successor. `v2` is the Fourier-analytic core, `v3`
the approximants it consumes; this is the complex-analytic half, and `CH2.v5` — Theorem 1.1, not
yet stated — is where the three meet.

## The contour class, and why it is not the paper's

The paper's Lemma 5.1 and Proposition 5.2 are stated for an **admissible contour**: any continuous
path from `1` to `s = -∞` inside `(-∞, 1] + i[0, T]` meeting each unit-width strip in finitely many
smooth arcs of bounded total length. That is a tameness condition, not a shape constraint, and
formalizing it faithfully would drag a ladder-contour vocabulary into this repository.

It is also more freedom than the applications use. §8.2 says so outright — the contour may be
chosen "rather freely", it need only pass under the non-trivial zeros of `ζ` and over the trivial
ones — and Lemma 5.1's own proof already closes contours rectangularly. So this node fixes the
class to **L-shaped paths, parameterized by one complex number**: from `1` along `ℝ` to `Re w`, up
to `w`, then left along the horizontal ray to `-∞ + i·Im w`.

Everything is axis-parallel, so the regions that arise in a deformation are unions of rectangles
and `integral_boundary_rect_eq_zero_of_differentiableOn` applies directly. The paper's diagonal
(Figure 3) needs Cauchy on a triangle instead; the diagonal remains available as a later
generalization and nothing here forecloses it.

Two facts recorded because they are easy to get wrong. The paper's stated reason for the diagonal
is that "45° is the smallest angle for which a bound (Lemma 8.6) holds" — smallest, so the vertical
`90°` is inside the permitted range, not outside it. And on `Re s = -1`, the seam midway between the
poles of `cot(πs/2)` at `0` and `-2`, that bound becomes the identity
`|cot(πs/2)| = tanh(π|y|/2) ≤ 1`, where the paper's diagonal reaches `1.143` and passes within
`0.707` of the pole at `-2`.

## Only one definition, and three choices that keep it that way

**Poles arrive as a `Finset`, not as "the poles of `F` in a region".** The paper sums over
`ρ a pole of F` with `ρ` in a subregion; formalizing that needs discreteness, finiteness and a
bespoke sum. A consumer always has the list — for `ζ'/ζ` it is exactly the zeros below height `T`
that a verification node enumerates — so `P : Finset ℂ` together with holomorphy off `P` says the
same thing, finitely and checkably.

**Circle integrals stand in for residues.** Mathlib has no `residue`. It has `∮ z in C(c, r), f z`
and `circleIntegral_eq_of_differentiable_on_annulus_off_countable`, which is what makes the value
independent of `r`. Since `∮ = 2πi · Res`, writing the circle integrals directly also removes the
`2πi` from the statement.

**The upper half only.** The paper's region is `(-∞,1] + i[-T,T]` and Lemma 5.1 carries both `C`
and its conjugate. It also assumes `F(s̄) = conj (F s)`, which is exactly what lets a consumer
recover the lower half by conjugation, so stating one half is no loss and halves the geometry.

And `Φ` never appears: the shift is stated for an arbitrary `f`, and a consumer instantiates
`f s = Φ ((s-1)/(iT)) * F s * x ^ s`. The Beurling–Selberg family stays in `CH2.v3`.

## The hypotheses are the paper's, transposed

CH2 assumes `F s * x₀ ^ s` **bounded** on the region and concludes for `x > x₀`. The decay that the
argument actually uses comes from the leftover `(x/x₀) ^ s`, which tends to `0` as `Re s → -∞`
because `x / x₀ > 1`. So `DecaysLeft` below is that consequence, stated directly. A consumer
carrying the paper's hypotheses can supply it; see the node's limitations.
-/

namespace CH2.v4

open MeasureTheory intervalIntegral

/-- The closed upper region the shift takes place in: `Re s ≤ 1` and `0 ≤ Im s ≤ T`.

Node-local and deliberately a plain `Set ℂ`; nothing about it needs a structure. -/
def UpperRegion (T : ℝ) : Set ℂ := {s : ℂ | s.re ≤ 1 ∧ s.im ∈ Set.Icc 0 T}

/-- `DecaysLeft T f`: `f` tends to `0` uniformly in the strip as `Re s → -∞`.

This is what CH2's "`F s * x₀ ^ s` is bounded on the region, and `x > x₀`" delivers, and it is what
makes the far-left edge of the deformation vanish. -/
def DecaysLeft (T : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ ε > 0, ∃ M : ℝ, ∀ s : ℂ, s.re ≤ -M → s.im ∈ Set.Icc 0 T → ‖f s‖ ≤ ε

/-- `lContourIntegral w f`: the integral of `f` along the **L-shaped contour** from `1` to `-∞`
turning at `w` — along `ℝ` from `1` to `Re w`, up the vertical segment to `w`, then left along the
horizontal ray to `-∞ + i·Im w`.

This is the paper's admissible contour restricted to one complex parameter. The integral is defined
rather than the path: a `ℝ → ℂ` parameterization plus a limit at `-∞` is a great deal of machinery
for something used only under an integral sign.

**JUNK VALUE, AND IT MATTERS HERE.** Each piece is a Bochner integral, which is `0` for a
non-integrable integrand — so the ray piece is silently `0` whenever `f` fails to be integrable
along it. A conclusion quantified over `f` without an integrability hypothesis would therefore be
**vacuous rather than false**. Both conclusions below carry `IntegrableOn ... (Set.Iic w.re)`
explicitly, and any new one must too. -/
noncomputable def lContourIntegral (w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ t in (1 : ℝ)..w.re, f t)
    + Complex.I * (∫ t in (0 : ℝ)..w.im, f (w.re + t * Complex.I))
    - (∫ t in Set.Iic w.re, f (t + w.im * Complex.I))

/-- **The pole-free shift.** If `f` is holomorphic on the whole closed upper region and decays to
the left, the integral up the segment from `1` to `1 + iT` equals the L-contour integral plus the
integral along the top edge.

Pure Cauchy — no poles, no residues, no circle integrals. Stated separately from the general case
because it is the piece that exercises `lContourIntegral` against Mathlib's rectangle theorem, and
because a consumer whose integrand happens to be holomorphic should not have to supply an empty
`Finset` and an irrelevant radius.

The orientation is the counterclockwise boundary of the region between the contour and the top:
reversed L, up the right edge, left along the top, down at `-∞`. The last vanishes by `DecaysLeft`,
and the remaining three give the identity below.

Imports nothing: every input is universally quantified with its conditions as hypotheses. -/
def contour_shift_holomorphic : Prop :=
  ∀ (T : ℝ) (w : ℂ) (f : ℂ → ℂ),
    0 < T → w.re ≤ 1 → w.im ∈ Set.Ioo 0 T →
    DifferentiableOn ℂ f (UpperRegion T) →
    DecaysLeft T f →
    IntegrableOn (fun t : ℝ ↦ f (t + w.im * Complex.I)) (Set.Iic w.re) →
    IntegrableOn (fun t : ℝ ↦ f (t + T * Complex.I)) (Set.Iic 1) →
      Complex.I * (∫ t in (0 : ℝ)..T, f (1 + t * Complex.I))
        = lContourIntegral w f + (∫ t in Set.Iic (1 : ℝ), f (t + T * Complex.I))

/-- **The general shift.** The same with finitely many poles between the contour and the line, each
contributing its circle integral.

`P` is the pole set and `r` a radius small enough that the closed discs are pairwise disjoint, sit
strictly inside the region, and lie strictly **above** the horizontal ray. That last condition is
the paper's own configuration: the contour passes under the non-trivial zeros, which are the poles
being collected, and over the trivial ones, which are not.

`∮ z in C(ρ, r), f z` is `2πi` times the residue at `ρ`, which is why no `2πi` appears; its
independence of `r` is Mathlib's `circleIntegral_eq_of_differentiable_on_annulus_off_countable`.

Note that `f` is required holomorphic at `s = 1` — the corner of the region — so a consumer whose
Dirichlet series has its pole there must remove it first. That is no restriction in practice:
`CH2.v2.IsPoleFreePart` already works with `G s = A s - 1/(s-1)`.

Imports nothing. -/
def contour_shift : Prop :=
  ∀ (T r : ℝ) (w : ℂ) (P : Finset ℂ) (f : ℂ → ℂ),
    0 < T → 0 < r → w.re ≤ 1 → w.im ∈ Set.Ioo 0 T →
    (∀ ρ ∈ P, w.im + r < ρ.im ∧ ρ.im + r < T ∧ ρ.re + r < 1) →
    (∀ ρ ∈ P, ∀ σ ∈ P, ρ ≠ σ → 2 * r < dist ρ σ) →
    DifferentiableOn ℂ f (UpperRegion T \ ↑P) →
    DecaysLeft T f →
    IntegrableOn (fun t : ℝ ↦ f (t + w.im * Complex.I)) (Set.Iic w.re) →
    IntegrableOn (fun t : ℝ ↦ f (t + T * Complex.I)) (Set.Iic 1) →
      Complex.I * (∫ t in (0 : ℝ)..T, f (1 + t * Complex.I))
        = lContourIntegral w f + (∫ t in Set.Iic (1 : ℝ), f (t + T * Complex.I))
          + ∑ ρ ∈ P, (∮ z in C(ρ, r), f z)

end CH2.v4
