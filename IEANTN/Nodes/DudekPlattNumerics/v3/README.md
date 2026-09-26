# `DudekPlattNumerics.v3` — the derivation behind `pi_two_sided_footnote`

This file supersedes an earlier draft of this node's justification, which evaluated Dudek–Platt's
own eq. (8)–(9) at the footnote's `(a, R) = (3130, 6.315)` and asserted, without a supporting
calculus, that the resulting `π(x)` estimate holds for all `x > exp(9400)`. That assertion was
correct but under-justified in two ways an independent review of issue #63 (see the PR this README
ships with) found and this file repairs:

1. Eq. (8)–(9) apply a `θ(x)`-error bound valid only for `t > xₐ` inside a partial-summation
   integral that starts at `t = 2`; simply plugging numbers into the printed formula and calling
   the leftover terms "negligible" does not certify the missing `[2, xₐ]` range.
2. A displayed crossing function used to justify `xₐ = exp(9400)` was mis-normalized (it subtracted
   `log a` where the correct constant is `log(C/(aR^{1/4}))`, `C = √(8/17π)`) and, correctly
   evaluated, does not certify what it was used for.

Both are fixed below by working from Mossinghoff–Trudgian's Corollary 1 directly, controlling the
**entire** integration range (not just the tail), and avoiding root-finding altogether in favor of
an exact monotonicity argument. **The node's stated `Prop` is unchanged**: this is a stronger,
independently-checked derivation of the same `m = -3010.333`, `M = 3250.488` at `xₐ = exp(9400)`,
with room to spare, not a new claim.

[`certificate.py`](certificate.py) checks every numbered inequality below in exact
`fractions.Fraction` arithmetic — no floating point, no numerical root-finding, no sampled
tolerance. Run it with `python3 certificate.py`; it is self-contained (standard library only) and
its output is deterministic. It does not prove Mossinghoff–Trudgian's Corollary 1 itself, or
formalize the calculus below in Lean; both remain literature/written-mathematics authority, as
`imports_status: traced` on this node already records.

## 1. The literature input, exactly

Mossinghoff–Trudgian, *Nonnegative trigonometric polynomials and a zero-free region for the
Riemann zeta-function*, [arXiv:1410.3926](https://arxiv.org/pdf/1410.3926), §7, **Corollary 1**
(fetched and read directly, p. 15):

```
ε₀(x) = √(8/17π) · X^(1/2) · e^(−X),    X = √(log x / R),    R = 6.315

|θ(x) − x| ≤ x·ε₀(x)   for x ≥ 149
```

proved (their own words): *"Theorem 1 can be used, as in [Trudgian, arXiv:1401.2689, p. 2], to show
that there are no zeros of the Riemann zeta-function in the region σ ≥ 1 − 1/(6.315 log|t/17|),
t ≥ 24. The statement then follows from the arguments in [Trudgian]."* — i.e. Corollary 1 repeats
Trudgian's own R = 6.455 conversion recipe verbatim, substituting MT's own improved classical
constant `R₀ = 5.573412` (their **Theorem 1**) for Kadiri's raw `5.69693`, which is what changes the
output from `R = 6.455` to `R = 6.315`.

**"Unconditional" does not mean "no finite-height input."** MT's Theorem 1 itself — fetched and
read directly — states: *"We select `T₀ = 3.06 · 10¹⁰` as established in [10]"* (§3), and is proved
by combining Kadiri's classical region (`Kadiri2005.v1`) with that established, computationally
verified height. `MT.v1.zero_free_region`'s own `formalization.yaml` already records exactly this:
`imports: [Kadiri2005.v1.zero_free_region, Platt2015.v1.rh_up_to]` — the same
`RiemannHypothesisUpTo 3.06e10` this repository already holds as `Platt2015.v1.rh_up_to`. The
resulting Theorem 1 is unconditional (true for **every** `|t| ≥ 2`, not merely above `T₀`) precisely
*because* that height is an established computation, not an open conjecture — the same sense in
which `MT.v1.zero_free_region_sharpened` (§6.1, a **different**, larger, and at publication time
merely *announced* height `3 · 10¹¹`) is explicitly *not* what Corollary 1 rests on. Confirmed
independently by fetching Trudgian's own [arXiv:1401.2689](https://arxiv.org/pdf/1401.2689) p. 2,
which attributes the same established height to Platt: *"Let the Riemann hypothesis be true up to
height H: by Platt [15] we have H = 3.061 × 10¹⁰."*

`certificate.py` certifies (exact rationals) that Corollary 1's shifted region already sits inside
Theorem 1's classical region at that established height, so no larger or open height is smuggled
into this citation; the induction that extends Theorem 1's classical region down to `|t| ≥ 2` is
Mossinghoff–Trudgian's own published work and is not re-derived here.

## 2. `f_R`: a decreasing, exactly-bounded replacement for the withdrawn crossing function

Track `f_R(u) := C·(u/R)^(1/4)·e^(−√(u/R))·u⁵` for `u = log x`, chosen so that Corollary 1's
bound is equivalent to `|θ(x) − x| < a·x/(log x)⁵` exactly when `f_R(log x) < a`:

```
d/du log f_R(u) = 21/(4u) − 1/(2√(Ru))  <  0   whenever u > 441R/4 = 696.22875
```

so `f_R` is strictly decreasing on `[696.22875, ∞)` — an ordinary calculus fact about `√u`
eventually outgrowing any fixed multiple of `log u`. `certificate.py` certifies this cutoff and,
using rational brackets on `X = √(u/R)` and a positive-Taylor-series lower bound on `e^X` (so the
reciprocal gives a genuine upper bound, no floating point involved), that

```
f_R(9400) < 3110 < 3130 (the footnote's own a),      f_R(9306) < 3600.
```

`3110` is *derived*, not chosen independently: it is what the actual `R = 6.315` formula gives at
the actual threshold `u = 9400`, rounded up. Because it beats the footnote's own `a = 3130`, this
node's certification of `|θ(x) − x| < 3130·x/(log x)⁵` for `x ≥ exp(9400)` no longer needs the
footnote's bare assertion at all — only `R = 6.315` (§1) and monotonicity. This replaces the
withdrawn crossing-function argument entirely; no numerical root-finding is used anywhere in this
derivation.

## 3. The whole θ-error integral, not just the range above `xₐ`

Let `E(t) := θ(t) − t`. Partial summation needs `∫₂ˣ E(t)/(t log²t) dt`, and Corollary 1 only
controls the integrand for `t ≥ 149`, let alone the much larger range this node actually needs it
valid on. Write `b := 99/100` and split at `t = x^b` (so `log(x^b) = b·log x ≥ 9306` whenever
`log x ≥ 9400`, comfortably inside `f_R`'s decreasing range):

* **Below the split.** For `t ≥ 2`, at most `t` primes are each at most `t`, so `θ(t) ≤ t·log t`
  trivially, giving `|E(t)|/(t·log²t) < 1/log t + 1/log²t < 4` there (using `log 2 > 2/3`,
  certified from a positive series, not asserted).
* **Above the split.** Corollary 1 plus `f_R`'s monotonicity bounds the integrand by
  `f_R(bL)/(bL)⁷ ≤ f_R(9306)/(0.99·9400)⁷` for every `L := log x ≥ 9400`.

Multiplying the interval-length-`x` integral bound through by `L⁶/x` — the normalization
`(log x)⁶/x · |∫₂ˣ E(t)/(t log²t) dt|` this node's estimate actually needs — leaves an extra factor
of `L⁶` on **both** terms, not only the first:

```
D(L) := 4L⁶e^(−L/100) + L⁶·f_R(bL)/(bL)⁷ = 4L⁶e^(−L/100) + f_R(bL)/(b⁷L)
```

(the second equality cancels `L⁶` into `(bL)⁷ = b⁷L⁷`). Both terms of the simplified form are
decreasing on `L ≥ 9400` (the first has logarithmic derivative `6/L − 1/100 < 0` there; the second
is a product of positive decreasing factors), so `D(L) ≤ D(9400)` for every larger `L`.
`certificate.py` certifies `D(9400) < 0.4111 < 1/2` (using `e > 2` to replace the transcendental
tails by rational powers of `2` throughout — an intentionally crude but exact and fully rigorous
substitution). This bounds `(log x)⁶/x · |∫₂ˣ E(t)/(t log²t) dt|` for the **entire** unbounded range
`x ≥ exp(9400)`, which is the missing step §0 above identifies.

## 4. The main term, the finite correction, and the resulting `m`, `M`

Five integrations by parts of `∫₂ˣ θ(t)/(t log²t) dt` give the exact identity

```
π(x) = S₅(x) + 120·x/L⁶ + 720·I₇(x) − 2A + E(x)/L + ∫₂ˣ E(t)/(t log²t) dt

S₅(x) = x·Σₖ₌₀⁴ k!/L^(k+1),   I₇(x) = ∫₂ˣ dt/log⁷t,   A = Σₖ₌₁⁵ k!/log^(k+1)(2)
```

(this is Abel/partial summation on the real prime-counting function — matching the jump at each
prime rather than differentiating between primes — followed by five integrations by parts that
retain the lower endpoint at `x = 2`; `mainTerm` in `Conclusions.lean` is exactly this `S₅`). Using the elementary split `0 < I₇(x) < x/L⁷ +
7(√x/log⁸2 + 256x/L⁸)` (Dudek–Platt p. 6) and `e > 2` throughout, `certificate.py` certifies

```
0 < 720·L⁶/x · I₇(x) < 1/10,        A < 1600,        0 < 2A·L⁶e^(−L) < 1/1000        (L ≥ 9400).
```

Combining with §3's integral bound and §2's `a = 3110` for the `E(x)/L` term gives, for **every**
real `x ≥ exp(9400)`,

```
−2990.501  <  (log x)⁶/x · (π(x) − S₅(x))  <  3230.6
```

which `certificate.py` checks *implies* — with `2990.501 < 3010.333` and `3230.6 < 3250.488`, about
`20` coefficient units of slack in each direction — this node's stated, **unchanged**,
`m = −3010.333`, `M = 3250.488`. No statement edit, margin-factor change, or new-version migration
was needed: the stronger bound just proves the weaker, already-fingerprinted one.

## What this is, and is not

This is written mathematics with an exact-rational executable certificate, in the same spirit as
`Solutions/DudekPlatt.v2`'s own `threshold` lemma and this network's other `numerical`-justified
nodes (`DudekPlattNumerics.v1`, `.v2`). It is **not**:

- a Lean proof — nothing here is formalized, and `certificate.py` checks arithmetic inequalities,
  not the calculus steps (the partial-summation identity, the integration-by-parts split, the
  `θ(t) ≤ t log t` elementary fact) that connect them, which remain ordinary written mathematics;
- a proof of Mossinghoff–Trudgian's Corollary 1, Theorem 1, or Trudgian's own conversion recipe,
  all of which remain literature authority, independently fetched and read but not re-derived;
- a claim that `R = 6.315` is a drawable graph edge today via **this node's own historical route** —
  `MT.v1` states Theorem 1 and the §6.1 sharpened form, not Corollary 1, so `imports_status: traced`
  (not `identified`) is correct and unchanged by this repair; see the node's `formalization.yaml` and
  limitations. (Issue #63 has since added a separate, direct route to this node's same conclusion via
  `MT.v2.corollary_1` and `DudekPlattNumerics.v4`, registered as `bridge-from-v4` — an earned edge on
  its own terms, not a retroactive upgrade of `R = 6.315`'s provenance here.)
