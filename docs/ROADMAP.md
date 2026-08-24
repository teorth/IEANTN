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

**1. Statement fingerprints.** *Done* — `Tools/Hash.lean` plus `ieantn.py fingerprint`, with the
results committed to `fingerprints.json`. Structural, not pretty-printed, and Merkle-chained over
IEANTN's own definitions so a Vocabulary edit propagates. See the module docstring for the one
kind of change it deliberately cannot see.

**2. Verification receipts.** *Done* — `receipts/<conclusion>.json`, content-addressed, with
`ieantn.py record-receipt` (workflow-only) and `ieantn.py status` grading them green / yellow /
orange / BROKEN. `check-graph` refuses a `lean-comparator` justification with no matching receipt.

**Still to configure, once a receipt actually exists:** the ruleset path rule restricting
`receipts/` to the verification workflow's identity. Until that is set, the protection is review
convention rather than enforcement.

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

## A bridge must be trust-neutral

A principle the `Lcm.v2` design surfaced, and which applies to every restatement.

If `X.v1` takes its justification by a bridge from `X.v2`, then **`X.v1`'s transitive set of
unproved-in-Lean leaves must not grow**. A restatement is supposed to say the same thing better,
not to quietly acquire a new assumption. If the "refactor" leaves `X.v1` resting on more than it
did before, it is not a restatement at all — it is an amendment wearing a bridge.

This is mechanically checkable, and should be part of the breaking-change work (piece 3): compute
the leaf set before and after and require containment.

The concrete case that made it visible: an early sketch of `Lcm.v2` would have needed a numerical
side condition awkward enough to want its own `computation` node — but `Lcm.v1` needs no
computation of that kind. Introducing one would have made the bridged `Lcm.v1` depend on strictly
more than the original did. The abstraction has to be chosen so that it introduces **no new import
requirements, computational or otherwise.**

## Deferred test case: `Lcm.v2` as a pipeline

The first real refactoring exercise, to run once the metaarchitecture above is in place. It
exercises pipeline abstraction, bridging, and parameter instantiation together.

**Sequencing.** Do not design `Lcm.v2` first. The right order is:

1. **Port `Lcm.v1`'s solution from PNT+** (`PrimeNumberTheoremAnd/IEANTN/Lcm.lean`, commit
   `ae881f2e2b3acefc9b92f8d4dda7c2b8f6e8f5fe`, declaration `Lcm.L_not_HA_of_ge`) and verify it.
2. **Analyse what it actually uses** — in particular the real set of numerical side conditions,
   rather than the ones guessed from the shape of the statement.
3. **Then** design `Lcm.v2` as the abstraction that introduces no new import requirements.

Designing the abstraction before reading the proof is how you end up with side conditions that are
either wrong or that smuggle in new dependencies.

**The idea.** `Lcm.v1` hardcodes Dusart's threshold. `Lcm.v2` should instead internalise the
Dusart-type hypothesis and its numerical side conditions, taking `X₀` as a variable — so `Lcm.v2`
has **no imports at all**, roughly:

```lean
def lcmUpto_not_highlyAbundant : Prop :=
  ∀ X₀ : ℝ, <numerical side conditions on X₀> →
    IEANTN.HasPrimeInInterval.logPower X₀ 3 →
      ∀ n : ℕ, X₀ ^ 2 ≤ (n : ℝ) → ¬ HighlyAbundant (Nat.lcmUpto n)
```

The side conditions are deliberately left blank: step 2 above determines them.

**The bridge** then discharges `Lcm.v1`'s challenge from `Lcm.v2`'s conclusion by instantiating
`X₀ := 89693`, verifying the side conditions, and handling the ℕ→ℝ cast. Note this is a bridge,
not an import edge: `Lcm.v1` keeps `Dusart2018.v1` as its declared import and gains a `bridged`
justification.

**The numerical obstacle, already scouted.** If the side condition is the expected
`11.4 < Real.log X₀`, the bridge must discharge `11.4 < Real.log 89693` — true, but tight: the real
value is `11.404148`, a margin of `0.0041`. Findings:

- Mathlib's `Analysis/Complex/ExponentialBounds.lean` has `log_two_gt_d9`, `log_three_gt_d9` and
  `log_five_gt_d9`, but **no `log 7`**.
- The natural witness is `89600 = 2⁹ · 5² · 7`, giving `9 log 2 + 2 log 5 + log 7 = 11.403111`,
  margin `0.0031` — but it needs `log 7`.
- **There is no 5-smooth integer in `(e^11.4, 89693] = (89321.7, 89693]`**, so no witness avoids it.

**Decision: prove it locally**, from `Real.abs_log_sub_add_sum_range_le` (the log Taylor remainder
bound). Making it a `computation` node was considered and rejected: `Lcm.v1` requires no
computation of that kind, so a computation node would violate trust-neutrality above.

Longer term the right home is a **log-tables node**, which already exists de facto as
`PrimeNumberTheoremAnd/IEANTN/LogTables.lean` in PNT+ and which many nodes will want. Contributing
`log_seven_gt_d9` upstream to Mathlib is also worth doing on its own merits.
