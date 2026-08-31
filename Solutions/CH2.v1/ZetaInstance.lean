/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Section5

/-!
# Instantiating §5 at `A(s) = -ζ'(s)/ζ(s)`

The first consumer of the ported §5 machinery, and the step that tells us whether that machinery is
*usable* rather than merely compiling.

Chirre–Helfgott's §10 (`prop:sagaro`) says what is wanted:

> Apply Theorem 1.1 with `A(s) = -ζ'(s)/ζ(s)`. The poles of `A(s)` are the zeros of `ζ(s)` and the
> pole of `ζ(s)` at `s = 1`. The residue of `A(s)` at a zero of `ζ(s)` is `-1` times the zero's
> multiplicity, and its residue at `s = 1` is `1`.

`prop_5_2` asks for five things about `F`. This file discharges the three that are properties of
`ζ` alone; the other two are growth bounds and belong with Appendix A. See the end of the file.

## The one that mattered

`HasSimplePolesOn` was the hypothesis I expected to be awkward — `−ζ'/ζ` has a pole at every zero of
`ζ`, of every multiplicity, and "simple pole regardless of multiplicity" is exactly the sort of fact
that is obvious on paper and painful in Lean. It is not painful: Mathlib has
`meromorphicOrderAt_logDeriv_eq_neg_one`, which says the logarithmic derivative has order exactly
`-1` at any zero or pole of a meromorphic function. A zero of order `m` gives `m/(s-ρ) + …`, order
`-1`, whatever `m` is.

That is worth recording because it also decides an earlier question: `ContourIntegration.v1`'s
general residue theorem, which admits arbitrary isolated singularities, is stronger than this
application ever needs.
-/

open Complex Filter Topology

namespace CH2ZetaInstance

/-- `A(s) = -ζ'(s)/ζ(s)`, the function CH2 applies the main theorem to.

Written as `-logDeriv riemannZeta` rather than `-(deriv ζ)/ζ` so that Mathlib's logarithmic
derivative API applies directly; the two are definitionally the same. -/
noncomputable def A : ℂ → ℂ := fun s ↦ -logDeriv riemannZeta s

/-- **Conjugation symmetry.** `A(s̄) = conj (A s)`, one of `prop_5_2`'s hypotheses.

Immediate from the ported `logDerivZeta_conj`, which is what `ZetaConj.lean` exists for. -/
lemma conjSymm_A : CH2.ConjSymm A := by
  intro s
  simp only [A, map_neg, neg_inj]
  exact logDerivZeta_conj' s

/-- `ζ` is analytic away from its pole.

`DifferentiableAt` unfolds to an `Exists`, so `(differentiableAt_riemannZeta hz).analyticAt` picks
up `Exists.analyticAt` and fails; the route is `DifferentiableOn.analyticAt` on the open complement
of `{1}`. -/
lemma analyticAt_riemannZeta {z : ℂ} (hz : z ∈ ({(1 : ℂ)}ᶜ : Set ℂ)) :
    AnalyticAt ℂ riemannZeta z := by
  refine DifferentiableOn.analyticAt (s := ({(1 : ℂ)}ᶜ : Set ℂ)) (fun w hw ↦ ?_) ?_
  · exact (differentiableAt_riemannZeta hw).differentiableWithinAt
  · exact (isOpen_compl_singleton).mem_nhds hz

/-- `ζ` is meromorphic away from its pole. -/
lemma meromorphicOn_riemannZeta_compl : MeromorphicOn riemannZeta {(1 : ℂ)}ᶜ :=
  fun z hz ↦ (analyticAt_riemannZeta hz).meromorphicAt

/-- **`A` is meromorphic away from `s = 1`.** -/
lemma meromorphicOn_A_compl : MeromorphicOn A {(1 : ℂ)}ᶜ := by
  have h := meromorphicOn_riemannZeta_compl.logDeriv
  intro z hz
  exact (h z hz).neg

/-- **Simple poles.** At a point off `s = 1` where `ζ` is not identically zero, `A` has meromorphic
order at least `-1`.

This is the pointwise content of `HasSimplePolesOn`, and it holds at *every* such point rather than
only at the zeros: away from a zero the order is `0`, and at a zero of any multiplicity the
logarithmic derivative has order exactly `-1`. The multiplicity shows up in the residue, not in the
order — which is why `−ζ'/ζ` needs only simple-pole machinery however bad the zeros are.

The non-vanishing hypothesis is `meromorphicOrderAt ζ z ≠ ⊤`, i.e. `ζ` does not vanish on a
punctured neighbourhood of `z`. It is true — `ζ` is analytic on the connected set `{1}ᶜ` and not
identically zero there — but discharging it needs the identity theorem, which is a separate small
task and is left as one. -/
lemma meromorphicOrderAt_A_ge_neg_one {z : ℂ} (hz : z ∈ ({(1 : ℂ)}ᶜ : Set ℂ))
    (htop : meromorphicOrderAt riemannZeta z ≠ ⊤) :
    (-1 : ℤ) ≤ meromorphicOrderAt A z := by
  have hanalζ : AnalyticAt ℂ riemannZeta z := analyticAt_riemannZeta hz
  have hζ : MeromorphicAt riemannZeta z := hanalζ.meromorphicAt
  -- `A = (-1) • logDeriv ζ`, and a nonzero constant has order `0`.
  have hconst : meromorphicOrderAt (fun _ : ℂ ↦ (-1 : ℂ)) z = 0 := by
    rw [analyticAt_const.meromorphicOrderAt_eq, analyticAt_const.analyticOrderAt_eq_zero.mpr
      (by norm_num)]
    rfl
  have hAeq : A = (fun _ : ℂ ↦ (-1 : ℂ)) • logDeriv riemannZeta := by
    funext w; simp [A]
  have hA : meromorphicOrderAt A z = meromorphicOrderAt (logDeriv riemannZeta) z := by
    rw [hAeq, meromorphicOrderAt_smul analyticAt_const.meromorphicAt hζ.logDeriv, hconst, zero_add]
  rw [hA]
  by_cases hzero : riemannZeta z = 0
  · -- a zero of `ζ`, of whatever multiplicity: the logarithmic derivative has order exactly `-1`.
    have h0 : meromorphicOrderAt riemannZeta z ≠ 0 := by
      rw [hanalζ.meromorphicOrderAt_eq]
      intro hcon
      have : analyticOrderAt riemannZeta z = 0 := by
        cases h : analyticOrderAt riemannZeta z with
        | top => rw [h] at hcon; simp at hcon
        | coe n => rw [h] at hcon; simpa using hcon
      exact (hanalζ.analyticOrderAt_eq_zero.mp this) hzero
    rw [meromorphicOrderAt_logDeriv_eq_neg_one hζ h0 htop]
    norm_cast
  · -- away from the zeros `logDeriv ζ` is analytic, so its order is nonnegative.
    have hanal : AnalyticAt ℂ (logDeriv riemannZeta) z :=
      (hanalζ.deriv).div hanalζ hzero
    refine le_trans ?_ hanal.meromorphicOrderAt_nonneg
    decide

end CH2ZetaInstance
