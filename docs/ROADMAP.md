# Roadmap

What is deliberately not built yet, and the decisions already taken about it. Everything marked
*(planned)* in [ARCHITECTURE.md](ARCHITECTURE.md) and [../CONTRIBUTING.md](../CONTRIBUTING.md)
appears here.

> **Documentation debt.** The design has moved faster than the docs during the proof-of-concept
> phase, and parts of ARCHITECTURE.md and NODES.md describe an earlier iteration. **Once the
> proof of concept stabilises, do a full documentation pass** over `README.md`,
> `CONTRIBUTING.md`, `CLAUDE.md`, `docs/ARCHITECTURE.md`, `docs/NODES.md` and this file — and
> write a local Claude skill capturing the working conventions, so future sessions and other
> contributors' agents start from the settled design rather than reconstructing it.

## The remaining pieces

In rough dependency order.

**1. Statement hashing.** The `pp.all`-elaborated statement hash of every conclusion. Must run
inside Lean, since it needs elaboration — so this is a small Lake executable, not a Python script.
Everything below depends on it.

**2. Verification receipts.** `receipts/<node>.<conclusion>.json`, content-addressed
(ARCHITECTURE §4). **Writable only by the verification workflow's identity**, via a ruleset path
restriction: an author-written receipt is worthless. `check-graph` should then require every
`lean-comparator` justification to have a matching receipt file.

**3. The breaking-change detector.** Compute the graph at the PR base and at `HEAD`, then diff.
Hard-fails when a conclusion with downstream importers or a recorded receipt is edited in place,
with `new-version` as the suggested fix.

**4. The reviewer report.** Same machinery as (3): posts a PR comment naming the receipts that went
stale, new unjustified leaves, blast radius, and a recommended modification. Advisory, never
blocking.

**5. The `/verify` bot.** A maintainer-approved `workflow_dispatch` that runs Comparator on one
node's solution and, on success, commits the receipt and flips the justification.

**6. Staleness and the housekeeping queue's time-sensitive half.** Green / yellow / orange against
the Mathlib cache window (CONTRIBUTING §8).

**7. Visualisation.** A rendered graph over the receipts and metadata, computed rather than
re-running any verification.

## Deferred test case: `Lcm.v2` as a pipeline

The first real refactoring exercise, to run once the metaarchitecture above is in place. It
exercises pipeline abstraction, bridging, and parameter instantiation together.

**The idea.** `Lcm.v1` hardcodes Dusart's threshold. `Lcm.v2` should instead internalise the
Dusart-type hypothesis and its numerical side conditions, taking `X₀` as a variable — so `Lcm.v2`
has **no imports at all**:

```lean
def lcmUpto_not_highlyAbundant : Prop :=
  ∀ X₀ : ℝ, 11.4 < Real.log X₀ →
    IEANTN.HasPrimeInInterval.logPower X₀ 3 →
      ∀ n : ℕ, X₀ ^ 2 ≤ (n : ℝ) → ¬ HighlyAbundant (Nat.lcmUpto n)
```

**The bridge** then discharges `Lcm.v1`'s challenge from `Lcm.v2`'s conclusion by instantiating
`X₀ := 89693`, verifying the numerical side condition, and handling the ℕ→ℝ cast:

```lean
theorem Lcm.bridge_v2_to_v1
    (h : Lcm.v2.lcmUpto_not_highlyAbundant)
    (hd : Dusart2018.v1.proposition_5_4) :
    Lcm.v1.lcmUpto_not_highlyAbundant
```

Note this is a bridge, not an import edge: `Lcm.v1` keeps `Dusart2018.v1` as its declared import
and gains `justification: bridged`.

**The obstacle, already scouted.** The numerical step is `11.4 < Real.log 89693`, and it is tight —
the true value is `11.404148`, a margin of `0.0041`. Findings:

- Mathlib's `Analysis/Complex/ExponentialBounds.lean` has `log_two_gt_d9`, `log_three_gt_d9` and
  `log_five_gt_d9`, but **no `log 7`**.
- The natural witness is `89600 = 2⁹ · 5² · 7`, giving
  `log 89600 = 9 log 2 + 2 log 5 + log 7 = 11.403111 > 11.4` with margin `0.0031` — but it needs
  `log 7`.
- **There is no 5-smooth integer in `(e^11.4, 89693] = (89321.7, 89693]`**, so no witness avoids
  `log 7`.

Three ways out, to choose when the test is run: contribute `log_seven_gt_d9` upstream to Mathlib
(cheapest and most reusable); prove it locally from `Real.abs_log_sub_add_sum_range_le`; or make it
a small `computation` node justified by LeanCert.

That last option is worth noting for its own sake: it would be the first case where the
architecture's answer to "this step is awkward in Lean" is *make it a node* rather than *push
harder* — which is workflow 6 doing exactly what it is for.

**Also to reconcile:** the `11.4 < log X₀` side condition is reverse-engineered from the shape of
the existing PNT+ proof, not from a careful reading of it. The real set of numerical side
conditions must be confirmed against `PrimeNumberTheoremAnd/IEANTN/Lcm.lean` when the solution is
ported.
