/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Doolan
-/
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.Chebyshev

/-!
# Node `TruncatedPerron.v1`

Perron's formula cut off at height `T`, with an explicit error. Textbook material (Titchmarsh,
*The Theory of the Riemann Zeta-Function*, §3.12; Montgomery–Vaughan, *Multiplicative Number
Theory I*, §5.1 and §12.1; Davenport, *Multiplicative Number Theory*, ch. 17) that Mathlib does
not have and that the papers in the network which need it (FKS Theorems 3.1/3.2, Platt–Trudgian
2021) cite rather than prove. PrimeNumberTheoremAnd has only the smoothed version.

Three conclusions, each a consumer of the one before:

* `perron_single_term` — the kernel bound for one term `y^s / s`;
* `perron_general` — the formula for a Dirichlet series `∑ aₙ n^{-s}` with an explicit error,
  obtained from the kernel bound term by term;
* `perron_psi` — the case `aₙ = Λ(n)`, `σ₀ = 1 + 1/log x`, in Davenport's form.

## Conventions

Every vertical integral is a *finite* interval integral over `t ∈ [-T, T]` on the line
`s = c + it`. Since `ds = i dt`, the factor `1/(2πi)` of the textbooks becomes `1/(2π)`:

  `(1/2πi) ∫_{c-iT}^{c+iT} g(s) ds = (1/2π) ∫_{-T}^{T} g(c + it) dt`.

No improper integral appears anywhere, so there is no conditional convergence to get wrong.

`y ^ s` for real `y > 0` is `Complex.cpow` of a positive real base, which is `exp (s log y)`
with the real logarithm: no branch cut is involved.
-/

namespace TruncatedPerron.v1

open Complex Real

/-- **The single-term truncated Perron bound**: the kernel estimate behind Titchmarsh §3.12,
Montgomery–Vaughan Theorem 5.2 and Davenport ch. 17.

For `c > 0`, `T > 0` and `y > 0` with `y ≠ 1`,

  `| (1/2πi) ∫_{c-iT}^{c+iT} y^s/s ds − 1_{y>1} | ≤ y^c · min(1, 1/(πT|log y|))`.

The `1/(πT|log y|)` half comes from shifting the contour to the left (`y > 1`, picking up the
residue `1` at `s = 0`) or to the right (`y < 1`), and the `1` half from shifting onto a circular
arc of radius `√(c² + T²)`.

`y = 1` is excluded, as in every source: there the integral is `(1/π) arctan(T/c)`, not `1/2`,
and `perron_general` handles that term separately.

The sources state `T ≥ 1` or leave `T` unrestricted; `T > 0` is what the proof uses. -/
def perron_single_term : Prop :=
  ∀ y c T : ℝ, 0 < y → y ≠ 1 → 0 < c → 0 < T →
    ‖(1 / (2 * π) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
        - (if 1 < y then 1 else 0)‖ ≤
      y ^ c * min 1 (1 / (π * T * |Real.log y|))

/-- **Truncated Perron formula for a Dirichlet series, with an explicit error**
(Titchmarsh §3.12; Montgomery–Vaughan Theorem 5.2, before its error is simplified).

Let `α(s) = ∑ aₙ n^{-s}` (Mathlib's `LSeries a`) converge absolutely at `σ₀ > 0`. Then for
`x > 0` and `T > 0`,

  `| ∑'_{n ≤ x} aₙ − (1/2πi) ∫_{σ₀-iT}^{σ₀+iT} α(s) x^s/s ds |
      ≤ ∑_{n ≥ 1} |aₙ| (x/n)^{σ₀} · K(x/n)`,

where `∑'` gives the term `n = x` (if `x` is an integer) weight `1/2`, and the kernel error is
`K(y) = min(1, 1/(πT|log y|))` for `y ≠ 1` and `K(1) = σ₀/(πT)`.

This is the term-by-term consequence of `perron_single_term`: the sum and the finite integral
commute because the series converges absolutely and uniformly on the segment. The `y = 1` term is
`|(1/π) arctan(T/σ₀) − 1/2| = (1/π) arctan(σ₀/T) ≤ σ₀/(πT)`.

Montgomery–Vaughan go on to bound the right-hand side by
`∑_{x/2<n<2x, n≠x} |aₙ| min(1, x/(T|x−n|)) + (4^{σ₀} + x^{σ₀})/T · ∑ |aₙ| n^{-σ₀}` (their
Corollary 5.3). That simplification is deliberately not stated here, so that no constant from it
is transcribed without being checked; it is a consequence of this conclusion.

**Junk-value notes.** The sum on the left is over `1 ≤ n ≤ ⌊x⌋`, matching `LSeries`, which ignores
`a 0`. On the right, the `n = 0` term is `‖a 0‖ · 0^{σ₀} · K = 0` because `σ₀ > 0`. The right-hand
`tsum` is summable (each term is at most `max(1, σ₀/(πT)) · x^{σ₀} · |aₙ| n^{-σ₀}`), so it is not
the junk value `0`. The hypothesis `abscissaOfAbsConv a < σ₀` is strict, so `LSeries a` is given
by a convergent series on the whole segment and is not junk there either. -/
def perron_general : Prop :=
  ∀ (a : ℕ → ℂ) (σ₀ x T : ℝ), 0 < σ₀ → LSeries.abscissaOfAbsConv a < (σ₀ : EReal) →
    0 < x → 0 < T →
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (if (n : ℝ) = x then (1 / 2 : ℂ) else 1) * a n)
        - (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
            LSeries a ((σ₀ : ℂ) + t * I) * (x : ℂ) ^ ((σ₀ : ℂ) + t * I) / ((σ₀ : ℂ) + t * I)‖ ≤
      ∑' n : ℕ, ‖a n‖ * (x / n) ^ σ₀ *
        (if (n : ℝ) = x then σ₀ / (π * T) else min 1 (1 / (π * T * |Real.log (x / n)|)))

/-- **Truncated Perron formula for `ψ`** (Montgomery–Vaughan, proof of Theorem 12.5: the bound
for `R₁`; also Davenport ch. 17).

With `c = 1 + 1/log x`, there is an absolute constant `C` such that for `x ≥ 2` and `T ≥ 1`,

  `| ψ₀(x) − (1/2πi) ∫_{c-iT}^{c+iT} (−ζ'/ζ)(s) x^s/s ds |
      ≤ C (x log²x / T + log x · min(1, x/(T⟨x⟩)))`,

where `ψ₀(x) = ψ(x) − Λ(x)/2` when `x` is an integer and `ψ(x)` otherwise, and `⟨x⟩` is the
distance from `x` to the nearest prime power other than `x` itself.

`−ζ'/ζ(s)` is written as `LSeries Λ s`, which equals it for `Re s > 1`
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`) and avoids the junk value of a quotient at a
zero of `ζ`; on the line `Re s = c > 1` the two agree.

**Junk-value notes.** The set defining `⟨x⟩` is nonempty and bounded below by `0`, and its infimum
is attained and positive (prime powers are discrete and `x` itself is excluded), so `x/(T⟨x⟩)` is
never a division by `0`. `c > 1` for `x ≥ 2`, so `LSeries Λ` is absolutely convergent on the
segment. -/
def perron_psi : Prop :=
  ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 1 ≤ T →
    ‖((Chebyshev.psi x - (if (⌊x⌋₊ : ℝ) = x then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2
          else 0) : ℝ) : ℂ)
        - (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
            LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
                (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) *
              (x : ℂ) ^ (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) /
              (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)‖ ≤
      C * (x * Real.log x ^ 2 / T + Real.log x * min 1 (x / (T *
        sInf {d : ℝ | ∃ q : ℕ, IsPrimePow q ∧ (q : ℝ) ≠ x ∧ d = |x - q|})))

end TruncatedPerron.v1
