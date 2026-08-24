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

**3. The breaking-change detector.** *Done* -- `ieantn.py diff --base <ref>`, run on every pull
request. Fails when a conclusion with downstream importers or a recorded receipt is edited in
place, or when one that is still imported is removed, with `new-version` as the suggested fix and
`changes/*.yaml` as the override.

Recovering the base state needs no Lean: `fingerprints.json` is committed, so the statements as
they were are readable with `git show`. That is most of why this is cheap enough to run per PR.

**4. The reviewer report.** *Partly done* -- `diff` writes its findings to the job summary, which
needs no token and no permissions. Still to do: posting it as a PR comment so it appears inline,
and adding the recommended-modification text for cases beyond the in-place edit.

**5. Verification.** *Mostly done* -- `scripts/verify-comparator.sh` with the four trusted tools
pinned, and `.github/workflows/verify.yml` splitting the run in two: `comparator` executes
contributor code with **no write access and no secrets**, and `receipt` holds write access but runs
no contributor code and recomputes the fingerprints itself from the core library.

**Untested end to end**, because no solution exists yet to verify. The pieces that could be tested
were: the scaffolder produces a project that builds, and `record-receipt` produces correct
receipts.

**Still to configure:** a `verification` GitHub Environment with required reviewers, so that
*requesting* a verification is open to any contributor while *approving* the run stays with
maintainers. Without it, `workflow_dispatch` silently restricts requests to people with write
access, which is an accident rather than a policy.

**6. Staleness and the housekeeping queue's time-sensitive half.** Green / yellow / orange against
the Mathlib cache window (CONTRIBUTING §8).

**7. Unit tests for the tooling.** There are none. `scripts/ieantn.py` is now around a thousand
lines carrying every invariant the network relies on, and it is exercised only by being run on a
two-node repository where most branches never execute. The tests that matter most are the ones a
manual check cannot give:

* a fixture repository with several nodes, versions, bridges and receipts, so `check-graph`,
  `diff`, `status` and `housekeeping` run against a graph with actual shape;
* **assertions that each substitution changed something** -- the silent-no-op class in the code
  audit below is the one unit tests would have caught outright;
* round-trip tests for `gen-challenges`, `new-version` and `deprecate`, including that comments
  survive;
* the fingerprint invariants, which were checked by hand once and should not have to be again:
  a binder rename does not move a fingerprint, an edited numeral does, and a Vocabulary edit
  propagates.

**8. Visualisation.** A rendered graph over the receipts and metadata, computed rather than
re-running any verification.

## Longer term: verification backends other than Comparator

Not a priority, and deliberately so. Recorded because the reasoning is worth having written down
before anyone attempts it.

Today `justification: numerical` means *asserted on the authority of a computation someone ran
elsewhere* — it is a citation, not a check. The natural expansion is a backend that actually runs
the computation: a sandboxed SymPy or interval-arithmetic job, verified the way a Comparator run is,
so that a numerical justification becomes evidence rather than an assurance.

Most of the machinery generalises. The statement of record is still the Lean conclusion, so
statement fingerprints are unchanged; a receipt would gain a `method` field, and its `environment`
would record a Python version and pinned wheel hashes instead of a Lean toolchain and Mathlib
revision. The privilege split in `verify.yml` already has the right shape.

### Two tiers, and only one of them is dangerous

**Tier A — the backend produces a certificate that Lean re-checks.** This is the LeanCert and
PrimeCert pattern, and the one to build first. Generate outside, verify inside: the external run
emits a Bernstein certificate, an interval enclosure, a factorisation witness, and a *Lean* solution
checks it. **The backend then leaves the trusted base entirely** — a bug in it causes a failed
build, not an unsound theorem — and the receipt stays a `lean-comparator` receipt, because that is
genuinely what it is. Almost no new trust, almost no new attack surface, and the justification kind
does not even need to change.

**Tier B — the computation's result is trusted directly.** An exhaustive search with no compact
witness; a floating-point computation whose certificate would be as expensive as the computation.
This is where the real cost sits, and it is two costs, not one:

*The trust semantics genuinely differ, and must not be flattened.* Comparator establishes
`imports → conclusion` under a bounded axiom set, checked by two kernels. A SymPy run establishes
"this numeric claim held, at this precision, in this arithmetic, on this machine." Those are not the
same thing, and a network whose whole promise is *read off how good the evidence is* must not render
them with the same green light. A tier-B receipt needs its own label and its own colour, or the
promise is quietly broken by making a floating-point run look like a kernel-checked proof.

*The attack surface is much worse than Comparator's.* Comparator at least runs a fixed export
format under Landlock. Arbitrary Python has no sandbox story of its own: it wants network access,
arbitrary imports, and unbounded resources. Minimum bar would be a container with no network, wheel
hashes pinned, a declared CPU and memory budget, and — as with Comparator today — a **small
structured artifact that the privileged job validates**, never a boolean the untrusted job asserts.

### The rule that follows

Build tier A, and treat every tier-B request as a question about whether a certificate is really
impossible or merely inconvenient. Most numerical claims in explicit analytic number theory are
certifiable: the interval-arithmetic and table-driven results in PNT+ are already of that shape.
Tier B should stay rare enough to be conspicuous.

## Code audit, still to do

The tooling has accumulated a real defect rate during the proof-of-concept phase, and the classes
below are the ones actually observed rather than a generic wish for review. They are recorded
because each predicts where the next one will be.

**Silent no-ops.** The worst class, because the tool reports success. A blanket `v1` to `v2`
rewrite in `new-version` silently repointed a node's *imports* at a version that did not exist. A
`re.sub` written for four-space indentation matched nothing after ruamel had normalised a file to
two, and the edit "succeeded". **Rule to enforce: every string or regex substitution in the tooling
must assert that it changed something.** The throwaway patch scripts used during development do
exactly this, and it is what caught most of these; the shipped tooling does not.

**Tests that do not test.** An `exit=$?` after a pipe reports the exit code of `head`. A `sed` that
matched nothing left a test asserting a property it had not established. This is the project's own
failure mode one level up: a check that passes vacuously is the junk-value problem applied to CI,
and it deserves the same suspicion the Vocabulary docstrings give to `tsum`.
**There are currently no unit tests for `scripts/ieantn.py` at all.**

**Destructive round-trips.** `yaml.safe_dump` silently discarded every comment in a node's
metadata, where the comments carry the provenance. Fixed by moving the mutating commands to
ruamel, but the general rule stands: a tool that rewrites a file it did not fully parse will lose
whatever it did not model.

**Heuristics where exact data was available.** The fingerprinter first decided "is this constant
ours?" by guessing at name prefixes; the environment records the defining module exactly.

**Environment-dependent checks.** The pyright step passed locally and failed in CI, because
`ruamel.yaml` is installed on the author's machine and CI installs only `pyyaml`. Any check whose
result depends on what happens to be installed is not really a check.

**Cross-platform hazards, all from authoring on Windows and running on Linux.** A file committed as
`scripts/Hash.lean` while the lakefile said `Scripts.Hash` built locally and would have failed CI.
An em dash in a report rendered as a replacement character on the Windows console, and would have
done so in the CI summary. Line endings are converted on every commit.

**Dead code and obfuscated expressions.** Two dead-code findings and one function written as an
index into a throwaway tuple, which also ignored the major version, so `v4.34` to `v5.2` came out
as thirty-two releases apart. Now caught by `pyrightconfig.json` in CI.

## Security audit, still to do

Worth being proactive about, given that contributors are increasingly agents and that some pull
requests will be too large for a human to review. Four vectors, with what exists today:

**Executable code in submitted Lean.** Elaboration can run arbitrary code, so any job that
compiles contributor Lean is running their program. Mitigated for verification by the privilege
split in `verify.yml` and by Comparator's Landlock sandbox. **Not** separately mitigated for the
*core* CI build, which compiles a PR's `Conclusions.lean`; it holds only `contents: read` and no
secrets, so the exposure is compute rather than credentials, but it has not been audited.

**Denial of service by triggering CI.** The verification workflow is hour-scale and should sit
behind the environment gate above. Core CI runs per push and is cheap, but nothing rate-limits it.

**Degradation of the informal layer -- the one that most deserves attention.** Statement
fingerprints cover the *Lean* statement and nothing else. A pull request can rewrite a conclusion's
docstring so it appears to say something it does not, change a `locator` from "Proposition 5.4" to
"Proposition 5.7", swap a `source` for a different paper, or flip a justification from `none-yet`
to `literature` with a fabricated citation -- **and no fingerprint moves, so nothing in CI
notices.** For `literature`, `asserted` and `numerical` nodes, which will be most of the network,
that informal layer *is* the evidence. The cheap first step is to fingerprint each conclusion's
justification and sources alongside its statement, so that such a change at least appears in the
impact report rather than passing silently.

**Trust in the tool pins.** Four revisions in `scripts/verify-comparator.sh` are the trusted base
of every receipt. Bumping them is a security change, not a chore.

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
