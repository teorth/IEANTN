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

**The intended `receipts/` path ruleset is impossible here, and provenance replaced it.** GitHub
refuses push rulesets on a public repository *and* on any repository not owned by an organisation,
and separately refuses to make the Actions app a bypass actor outside an organisation -- so a rule
restricting who may write `receipts/` cannot be created, and would block the verification workflow's
own push if it could.

`ieantn.py check-receipts` enforces the same intent more directly: every receipt must name a run
that really is a **successful run of `verify.yml` in this repository**. A path rule says who wrote
the file; this says the verification happened, which is what a forger would have to fake. A commit
author is trivially forged locally; a successful `verify.yml` run is not, because it needs a
maintainer to approve the `verification` environment. Verified to reject a receipt pointing at
another repository, at a real run of the *wrong* workflow, and at a real verification run that
*failed*.

If the repository ever moves to an organisation, the path rule becomes available and is worth
adding as defence in depth -- not as a replacement.

**3. The breaking-change detector.** *Done* -- `ieantn.py diff --base <ref>`, run on every pull
request. Fails when a conclusion with downstream importers or a recorded receipt is edited in
place, or when one that is still imported is removed, with `new-version` as the suggested fix and
`changes/*.yaml` as the override.

Recovering the base state needs no Lean: `fingerprints.json` is committed, so the statements as
they were are readable with `git show`. That is most of why this is cheap enough to run per PR.

**4. The reviewer report.** *Partly done* -- `diff` writes its findings to the job summary, which
needs no token and no permissions. Still to do: posting it as a PR comment so it appears inline,
and adding the recommended-modification text for cases beyond the in-place edit.

**5. Verification.** *Done, and exercised.* `scripts/verify-comparator.sh` with the four trusted
tools pinned, and `.github/workflows/verify.yml` splitting the run in two: `comparator` executes
contributor code with **no write access and no secrets**, and `receipt` holds write access but runs
no contributor code and recomputes the fingerprints itself from the core library.

Comparator accepts `Solutions/Lcm.v1` -- both the Lean kernel and NanoDa -- in about 50 seconds
locally. Getting there took four fixes, all recorded in the code audit below, and the most
instructive of them is that a solution must carry a `lean-toolchain` *equal* to the repository's:
Mathlib's `cache` reads it from the project directory, and the rule that briefly forbade the file
is what caused the 64-minute first run.

The `verification` GitHub Environment now exists with a required reviewer, so a dispatch pauses
until a maintainer approves. Note what that gate is and is not: it stops a *contributor* spending
hour-scale compute at will. It is no protection against a maintainer's own agent, which can approve
its own dispatch; there, the controls are cost visibility and keeping dispatch an explicit act.

**6. Staleness and the housekeeping queue's time-sensitive half.** Green / yellow / orange against
the Mathlib cache window (CONTRIBUTING §8).

**7. Unit tests for the tooling.** *Done* -- 73 tests in `tests/`, run against a fixture
repository the real functions are pointed at, and mutation-checked rather than merely passing.
Several are regression tests for defects that shipped.

Still absent: the substitutions inside `ieantn.py` do not assert that they changed anything, which
is the silent-no-op class in the code audit below and the one unit tests would catch outright.

**8. Visualisation.** A rendered graph over the receipts and metadata, computed rather than
re-running any verification.

## Considered and dropped: tiered verification levels

A two-level scheme was considered — an "express" run using only Lean's kernel, and a "full service"
run adding the independent NanoDa replay, on the reasoning that only a deliberate Lean-kernel
exploit merits the second. Comparator supports exactly this split: `enable_nanoda` registers NanoDa
in its `external_kernels` map, and its own trust assumptions state the difference precisely —
express requires you to trust that *"the Lean kernel is correct"*, full only that *"at least one of
the Lean kernel or the external kernels is correct"*.

**Dropped, because the measurement removed the reason for it.** The first CI run took 64 minutes
and suggested verification was expensive enough to want a cheap tier. It was not: 60 of those
minutes were Mathlib compiling from source because a cache fetch failed behind a `|| true`. With
that fixed, a full verification of `Lcm.v1` — both kernels — runs in **50 seconds**, of which NanoDa
is about one. There is no cost argument for skipping it.

The trust-legibility argument survives: two levels really do mean different things, and a network
whose promise is *read off how good the evidence is* should not paint them the same colour. But
that argument alone does not justify the machinery, and a level recorded in every receipt would
have to be maintained forever. Revisit only if CI proves expensive in a way local runs do not.

**If it is revisited**, the level belongs in two places and they must not be conflated: a
`required_level` in `formalization.yaml` is *policy* about a node, and a `level` in the receipt is
*fact* about a run. The gap between them — a node requiring `full` whose receipt says `express` —
is then a derived housekeeping task, exactly like staleness.

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

## Code audit

**First pass done.** What follows is in two parts: what the pass found and fixed, and the defect
*classes* observed during development, kept because each predicts where the next one will be.

### What the first pass found

Read end to end: `scripts/ieantn.py`, `Tools/Hash.lean`, `scripts/verify-comparator.sh`, and the
workflows. Nine defects, each now covered by a test that was checked to fail without its fix.

Two were soundness holes in the thing the repository exists to get right:

- **A receipt could cover a conclusion Comparator never saw.** Comparator runs once per node
  against `theorem_names` in the solution's `comparator.json`; receipts are written per conclusion;
  nothing connected the two. Adding a second conclusion to an already-verified node was enough to
  earn it a full `lean-comparator` justification for a statement no verifier had seen. No adversary
  required, and `status` would have shown it green. `record-receipt` now refuses unless every
  conclusion is listed.
- **Any successful verification validated any receipt.** `check-receipts` checked that the run
  existed, succeeded, and was `verify.yml` — not that it was *this node's*. Copying a real run URL
  into a fabricated receipt passed. The dispatched node now appears in `verify.yml`'s job names, so
  GitHub's record of the run decides what was verified; older runs fall back to one-run-one-node.

One was a live vulnerability:

- **Script injection in `verify.yml`.** Dispatch inputs were interpolated into `run:` bodies with
  `${{ }}`, which splices the value in before any shell exists to quote it. The worst case is the
  `receipt` job, which holds `contents: write` — precisely what the privilege split exists to
  protect. Inputs now reach the shell through `env:`.

Three were checks that did not check:

- **A trailing comment hid an import.** The import pattern was anchored at end of line, so
  `import Solutions.Whatever -- for now` matched nothing and every closure check silently passed.
- **`startswith` ignored module boundaries**, accepting `IEANTN.VocabularyScratch` as Vocabulary.
- **The receipt warning read the wrong justification** — the `kind` left over from a loop rather
  than the designated one — so recording any second ground made a verified node report unverified.
  Found by hitting it, not by reading: adding the `Lcm.v2` bridge triggered it immediately.

Three were hardening and hygiene:

- **Metadata is interpolated verbatim into generated Lean.** A conclusion `id`, and both halves of
  an import reference, become declaration names and binder types in `Challenge.lean`. Since CI only
  diffs that file against what the generator produces, crafted text would be regenerated faithfully
  and compiled into the core library. Ids must now be Lean identifiers.
- **`designate_verification` un-deprecated nodes** and left a stale run URL in the note on
  re-verification.
- **`deprecate` accepted a node superseding itself**, or a replacement already deprecated.

Documentation contradicted itself in three places about the `receipts/` ruleset — asserted as the
enforcement in `ARCHITECTURE.md` and `receipts/README.md`, correctly described as impossible in
`ROADMAP.md`. Provenance is the enforcement; the docs now say so uniformly.

### Defect classes to keep watching

The classes below are the ones actually observed rather than a generic wish for review.

**Silent no-ops.** The worst class, because the tool reports success. A blanket `v1` to `v2`
rewrite in `new-version` silently repointed a node's *imports* at a version that did not exist. A
`re.sub` written for four-space indentation matched nothing after ruamel had normalised a file to
two, and the edit "succeeded". **Rule to enforce: every string or regex substitution in the tooling
must assert that it changed something.** The throwaway patch scripts used during development do
exactly this, and it is what caught most of these; the shipped tooling does not.

**Tests that do not test.** An `exit=$?` after a pipe reports the exit code of `head`. A `sed` that
matched nothing left a test asserting a property it had not established. This is the project's own
failure mode one level up: a check that passes vacuously is the junk-value problem applied to CI,
and it deserves the same suspicion the Vocabulary docstrings give to `tsum`. Three of the nine
findings above are of exactly this class. The standing practice: **every new test is run once
against the unfixed code and must fail**, which is how the twelve added in the audit pass were
shown not to be decorative.

**Destructive round-trips.** `yaml.safe_dump` silently discarded every comment in a node's
metadata, where the comments carry the provenance. Fixed by moving the mutating commands to
ruamel, but the general rule stands: a tool that rewrites a file it did not fully parse will lose
whatever it did not model.

**Heuristics where exact data was available.** The fingerprinter first decided "is this constant
ours?" by guessing at name prefixes; the environment records the defining module exactly.

**Reasoning to a rule instead of testing it.** A solution must carry a `lean-toolchain` equal to
the repository's. The divergence argument -- a path dependency is built with the root's toolchain,
so a different pin cannot work -- is correct, and the conclusion drawn from it twice was not: first
that solutions pin freely, then that they carry none at all. Mathlib's `cache` reads the file from
the project directory, so absence meant compiling Mathlib from source. Both wrong answers were
written into the documentation before anything had been run.

**Guards that swallow the failure they guard.** `lake exe cache get || true` turned a failed cache
fetch into an hour of compiling. The `|| true` was defensive habit; what it defended against was
knowing.

**Copying a fix for a problem you do not have.** Restoring PalomarTemplate's landrun wrapper was
correct for the Comparator revision *it* pins and wrong for ours, which supplies the delimiter the
wrapper exists to add -- so the wrapper rejected it.

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

## Docs audit

**First pass done**, alongside the code audit. The docs had drifted in one direction throughout:
they described the design as it was *intended*, and the design moved. Nothing was wrong in a way a
reader would notice as wrong — every error read as confident and current.

Twelve corrections, in three classes.

**Claims the code contradicted.** Six. `NODES.md` opened with a banner saying receipts and
staleness tracking did not exist yet; both had existed for weeks. `ARCHITECTURE.md` said the
statement hash was of `pp.all` output, which `Tools/Hash.lean` explicitly rejects and explains at
length why. Two documents said the breaking-change detector was unimplemented while a third listed
it as an enforced invariant and CI ran it on every pull request. The housekeeping section was
headed *(planned)*. And `ARCHITECTURE.md` claimed CI attempts both bridges of a restatement and
reports which succeed — an appealing idea that nothing implements, stated as fact.

**Instructions that would have failed.** Three, and these are the ones that matter, because an
agent follows them literally. `NODES.md`'s `formalization.yaml` example omitted `node.family`,
`node.version` and `node.status` and gave the id as `Dusart2018` rather than `Dusart2018.v1` — as
written it fails `check-graph`. Three workflows in `CONTRIBUTING.md` showed a singular
`justification:` key; the schema has been a `justifications:` list with `designated:` since the
multiple-grounds design landed. And the Mathlib bump procedure said "update `lean-toolchain` and
`lake-manifest.json` — that is the whole PR", which fails `check-closure`: every solution's
toolchain must equal the repository's, so a bump sweeps them all, and a Lean release bump also
moves the `lean4export` pin.

That last one is the toolchain rule getting stated wrongly for the *third* time, in a document
whose neighbouring section explains at length that it was got wrong twice before. Which is the
lesson: a correction written in one place does not propagate, and this class is only findable by
re-deriving each claim from the code rather than reading for sense.

**Documentation ahead of the code.** One, fixed in the code instead. `ARCHITECTURE.md` said a
receipt records the repository commit and the four pinned tool revisions, and §2 leans on that —
"what pins a verification is the commit its receipt records". Receipts recorded neither. Rather
than weaken the doc, `record-receipt` now records both, at `"schema": 2`; without them a receipt
says a verification happened but not what tree it ran against or what checked it, so "re-run at the
recorded pin" had no referent.

Also swept: every relative link resolves, and every `ieantn.py` subcommand named in prose exists
while every subcommand that exists is documented. Both are now cheap to re-check and worth doing
after any tooling change.

A **local maintainer skill** now carries what is deliberately *not* in the repository: the
verification approval procedure and what to actually look at before approving, the alignment-
checking recipe that needs an LLM and so cannot be CI, cross-repository paths, PNT+ migration
state, and the accumulated traps in operational form.

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

**Alignment checking stays maintainer-side, deliberately.** The obvious answer to the gap below is
an LLM that reads a conclusions file against its informal description and its cited source. That is
**not** going into CI: it needs API keys, and it would put a paid, non-deterministic, prompt-
injectable step on the path of every pull request. Instead it belongs in **agent skills that
individual maintainers run**, against the bounded surface the architecture already guarantees — the
conclusions files and the metadata, not the solutions. So the design requirement on this repository
is only that the surface stay small and the metadata stay machine-readable, which it is.

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

## Done: `Lcm.v2` as a pipeline

The first real refactoring exercise, kept here for what the sequencing taught. `Lcm.v2` and
`IEANTN/Bridges/Lcm/V2ToV1.lean` now exist; the solution for `Lcm.v2` is issue #10.

**Sequencing.** Do not design `Lcm.v2` first. The order used was:

1. **Port `Lcm.v1`'s solution from PNT+** (`PrimeNumberTheoremAnd/IEANTN/Lcm.lean`, commit
   `ae881f2e2b3acefc9b92f8d4dda7c2b8f6e8f5fe`, declaration `Lcm.L_not_HA_of_ge`) and verify it.
2. **Analyse what it actually uses** — in particular the real set of numerical side conditions,
   rather than the ones guessed from the shape of the statement.
3. **Then** design `Lcm.v2` as the abstraction that introduces no new import requirements.

Designing the abstraction before reading the proof is how you end up with side conditions that are
either wrong or that smuggle in new dependencies.

**The idea.** `Lcm.v1` hardcodes Dusart's threshold. `Lcm.v2` internalises the Dusart-type
hypothesis and its numerical side condition, taking `X₀` as a variable — so `Lcm.v2` has **no
imports at all**:

```lean
def lcmUpto_not_highlyAbundant_of_primeGap : Prop :=
  ∀ X₀ : ℝ, 11.4 < Real.log X₀ → IEANTN.HasPrimeInInterval.logPower X₀ 3 →
    ∀ n : ℕ, X₀ ^ 2 ≤ (n : ℝ) → ¬ HighlyAbundant (Nat.lcmUpto n)
```

Step 2 determined the side condition: `log X₀ > 11.4`, and nothing else.

**The bridge** discharges `Lcm.v1`'s conclusion from `Lcm.v2`'s by instantiating `X₀ := 89693`,
verifying the side condition, and handling the ℕ→ℝ cast — three lines. It is a bridge, not an
import edge: `Lcm.v1` keeps `Dusart2018.v1` as its declared import and gains a **non-designated**
`bridged` justification, non-designated because `Lcm.v2` is itself unjustified and the direct
Comparator receipt depends on no other node.

Building it also forced the rule that bridges live inside the library and are compiled by the core
build. A bridge recorded only as a path would keep satisfying "the file named exists" after either
statement moved — and versions exist precisely so that statements can move.

**The numerical obstacle was imaginary.** Scouting this before the port suggested the bridge's
side condition `11.4 < Real.log 89693` would be hard: true by a margin of only `0.0041`, and
Mathlib carries `log 2`, `log 3` and `log 5` to nine digits but no `log 7`, with no 5-smooth
integer in `(e^11.4, 89693]` to route around it.

All of that was the wrong approach. The ported development already proves it, in five lines, by
raising to a power instead of factorising:

```lean
lemma log_X₀_gt : Real.log X₀ > 11.4 := by
  rw [gt_iff_lt, show (11.4 : ℝ) = 57 / (5 : ℕ) by norm_num, div_lt_iff₀ (by norm_num),
    mul_comm, ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num
```

`11.4 = 57/5`, so the claim is `X₀⁵ > exp 57 = (exp 1)⁵⁷`, bounded by `exp_one_lt_d9` and closed by
`norm_num` on the resulting rational. The scouting had dismissed exactly this route as too heavy;
`norm_num` does it without complaint.

The lesson is the same one the toolchain rule taught: **reasoning about whether something will
work, in advance and in the abstract, was worse than trying it.** The bridge's numerical step is
therefore already a proved lemma in `Solutions/Lcm.v1/LcmDev.lean`, and `Lcm.v2` is cheaper than
this section previously suggested.

Longer term the right home is a **log-tables node**, which already exists de facto as
`PrimeNumberTheoremAnd/IEANTN/LogTables.lean` in PNT+ and which many nodes will want. Contributing
`log_seven_gt_d9` upstream to Mathlib is also worth doing on its own merits.
