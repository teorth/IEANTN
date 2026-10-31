/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Node `KadiriLumley.v1` — narrow intervals containing primes, above `exp 59`

Kadiri and Lumley's Theorem 1.1 gives, for each row of its Table 2, a threshold `x₀` and a
constant `Δ` such that every `x ≥ x₀` has a prime in `(x(1 − 1/Δ), x)`. The two rows below are the
ones the odd-Goldbach range consumes.

## Why two instances rather than the table

The network's habit with a paper's table is to carry it whole, as `Buthe.v1` and `BKLNW.v1` do.
Not here, and the reason is that **this paper is not in the library**. A twenty-row, seven-column
table transcribed from another formalization's transcription, checkable against nothing, is a
liability rather than an asset; what the two conclusions below transcribe is four numbers, and
each of them appears in the consequence rather than inside the method.

Stating the general theorem, with Table 2 in a `Tables.lean`, is the right shape once someone
holds the paper. `docs/SOURCES.md` records it as wanted.

## The interval is open on the right

Unlike `RamareSaouter2003.v1`, whose interval is `(x(1 − 1/Δ), x]`, this one is `(x(1 − 1/Δ), x)`.
PrimeNumberTheoremAnd transcribes it that way and its blueprint says so explicitly — "open on the
right; cf. the theorem display in the paper". The open form is the weaker claim, so nothing is
lost by stating it, and a consumer wanting `HasPrimeInInterval` gets it from `p < x` at once.
That is why these conclusions do not use the `HasPrimeInInterval` vocabulary: it would silently
strengthen them.
-/

namespace KadiriLumley.v1

open Real

/-- **A prime in `(x(1 − 1/1 946 282 821), x)` for every `x ≥ exp 59`.**

Table 2's row at `log x₀ = 59`. The row's other parameters — the zero-density and zero-free-region
constants `m`, `δ`, `T₁`, `σ₀`, `a` that produce `Δ` — are internal to the paper's method and do
not appear here. -/
def prime_in_interval_above_exp_59 : Prop :=
  ∀ x : ℝ, exp 59 ≤ x →
    ∃ p : ℕ, Nat.Prime p ∧ x * (1 - 1 / 1946282821) < p ∧ (p : ℝ) < x

/-- **A prime in `(x(1 − 1/1 966 196 911), x)` for every `x ≥ exp 60`.**

Table 2's row at `log x₀ = 60`, and the sharpest of the rows the network uses. Strictly stronger
than the `exp 59` row above `exp 60`, and strictly weaker below it, which is why both are
stated: the odd-Goldbach derivation climbs through the first to reach the second. -/
def prime_in_interval_above_exp_60 : Prop :=
  ∀ x : ℝ, exp 60 ≤ x →
    ∃ p : ℕ, Nat.Prime p ∧ x * (1 - 1 / 1966196911) < p ∧ (p : ℝ) < x

/-- One row of Table 2, as printed in arXiv:1407.7902 and in Integers A61.

The first row's threshold is `4 · 10^18`, whose logarithm is about `42.8328`. Every later row's
threshold is `exp n` for the integer in the `log x₀` column. `Δ` is the integer in the last
column. The columns `m`, `δ`, `T₁`, `σ₀` and `a` are the method that produces `Δ`. Theorem 1.1
does not quantify over them, so they are not part of the statement. -/
def Table2Row := ℕ × ℕ

/-- Table 2 of Kadiri–Lumley, `(n, Δ)` with threshold `exp n`, except the opening row. -/
def table2ExpRows : List Table2Row :=
  [(43, 38753947), (44, 61162616), (45, 95381241), (46, 148306019), (47, 227619375),
    (48, 346582570), (49, 518958776), (50, 753575355), (51, 1037917449), (52, 1313524036),
    (53, 1524171138), (54, 1670398039), (55, 1770251249), (56, 1838818070), (57, 1886389443),
    (58, 1920768795), (59, 1946282821), (60, 1966196911), (150, 2442159714)]

/-- **Theorem 1.1, for every row of Table 2.**

For the opening row, every `x ≥ 4 · 10^18` has a prime in `(x(1 − 1/36082898), x)`. For each
later row `(n, Δ)`, every `x ≥ exp n` has a prime in `(x(1 − 1/Δ), x)`. The interval is open on
the right, as in the two rows already stated. The table caption says `x ≥ x₀`. The theorem
display says `x > x₀`. The closed form is the one the caption prints, and it matches the two
conclusions above, which are the rows `n = 59` and `n = 60` of this list. -/
def table_2 : Prop :=
  (∀ x : ℝ, 4 * 10 ^ 18 ≤ x →
    ∃ p : ℕ, Nat.Prime p ∧ x * (1 - 1 / 36082898) < p ∧ (p : ℝ) < x) ∧
  ∀ n Δ, (n, Δ) ∈ table2ExpRows → ∀ x : ℝ, exp (n : ℝ) ≤ x →
    ∃ p : ℕ, Nat.Prime p ∧ x * (1 - 1 / (Δ : ℕ)) < p ∧ (p : ℝ) < x

end KadiriLumley.v1
