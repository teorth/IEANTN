# Security

## What is being protected

Not confidentiality — everything here is public and there are no secrets in the repository or in
any environment. What is worth attacking is the **integrity of the justification graph**, and one
claim in particular:

> A `lean-comparator` justification means Comparator actually accepted a solution against the
> generated challenge, in this repository, for that conclusion.

Everything below exists to make that sentence hard to falsify. A second, lesser goal is that CI
compute is not free for strangers.

Report a suspected problem by opening an issue, or privately to the maintainer if it would be
harmful to state publicly.

## Who can do what

| | |
|---|---|
| Anyone | Open a pull request. CI runs with a read-only token and no secrets. |
| Collaborator (write) | Push branches, dispatch `verify.yml`. Cannot merge to `main` without review. |
| Maintainer (admin) | Approve the `verification` environment, bypass the `main` ruleset. |

The `main` ruleset requires a pull request and code-owner review, and blocks deletion and
force-push. Administrators can bypass it; that is a deliberate current choice, not an oversight.
[CODEOWNERS](.github/CODEOWNERS) puts `IEANTN/Vocabulary/`, `.github/workflows/`,
`scripts/verify-comparator.sh` and `receipts/` behind maintainer review.

## Running untrusted code

Lean elaboration executes arbitrary code. Three places compile code this repository did not write,
and they are not equally exposed.

**Core CI (`ci.yml`, `build`).** Compiles a pull request's Vocabulary, Conclusions, Challenges and
bridges — including from a fork, unreviewed, on every push. It is not sandboxed. What bounds it:
the job holds only `contents: read` on a public repository, no secrets exist to read, and
`persist-credentials: false` means no token is left in `.git/config` for the compiled code to find.
So a hostile `Conclusions.lean` gets sixty minutes of throwaway runner and nothing else. That is an
accepted cost, not a mitigated risk: the alternative is not building pull requests.

**Verification (`verify.yml`).** Split across two jobs on privilege:

- `comparator` runs the contributor's *solution* — the large machine-generated artefact nobody
  reads — with `contents: read`, no secrets, `persist-credentials: false`, and Comparator's own
  Landlock sandbox around the export step. It cannot obtain a token.
- `receipt` holds `contents: write` and never builds the solution. It recomputes the statement
  fingerprints itself, so it need not believe anything the first job says about them; the only
  thing it takes from that job is a verdict artefact, whose node and verdict it re-checks.

Being exact about the second one, because the obvious reading is too generous: the receipt job does
run `lake build` on the branch, and the branch's *core* Lean is not trusted content either. What
protects it is not the split but the `verification` environment gate on the job before it — nothing
runs until a maintainer approves, and approving means having looked at the branch. **Approving a
verification vouches for the branch's `Conclusions.lean` and bridges, not merely its solution.**
Those are tens of lines; that is the point of the layer separation.

**Palomar metadata validation (`ci.yml`, `palomar-metadata`).** Imports and runs Python fetched
from `PalomarRegistry/PalomarSubmission` on every run. Pinning it would defeat the purpose — the
job exists to track a moving contract. So the exposure is bounded instead: the job declares
`permissions: {}` and holds no token at all, the fetch is an anonymous HTTPS `GET` rather than an
authenticated `gh api` call, and the resolved upstream commit is written to the job summary so
*which* validator ran is visible after the fact.

## The trusted base of a receipt

A receipt is worth exactly what these are worth:

- **Comparator, `lean4export`, NanoDa and Landrun**, each pinned to a commit in
  [`scripts/verify-comparator.sh`](scripts/verify-comparator.sh) and recorded in the receipt.
  `lean4export` must match the repository's toolchain; `check-pins` fails the build if a Mathlib
  bump leaves it behind.
- **The workflow file itself**, which is under CODEOWNERS.
- **A maintainer's approval** of the `verification` environment.
- **GitHub's record of the run**, which `check-receipts` queries rather than trusting the receipt.

Every GitHub Action is pinned to a full commit SHA. Two of the three third-party actions resolve
`@v1` to a *branch*, not a tag — a branch head moves on every push, and both were used in jobs
holding `contents: write`.

## What a forged receipt would take

The intended control was a ruleset restricting `receipts/` to the workflow's identity. GitHub
refuses push rulesets on public repositories and outside an organisation, so there is none, and
`check-receipts` enforces provenance instead — which is the better control anyway, since a path
rule says who wrote a file and provenance says the verification happened. It requires, for every
receipt:

1. a run URL in **this** repository — determined from `git remote get-url origin`, and the check
   refuses outright rather than asking the repository the receipt names if it cannot tell;
2. that the run exists, concluded `success`, and is `verify.yml` — which needed a maintainer to
   approve an environment;
3. that the run is **that node's**, since `verify.yml` puts the dispatched node in its job names,
   so GitHub's record decides what was verified rather than the receipt asserting it;
4. one run, one node, which covers runs predating (3).

Separately, `record-receipt` refuses to write a receipt for any conclusion absent from the
solution's `comparator.json`, so a receipt cannot cover a statement Comparator was never asked
about. That one needed no adversary: adding a second conclusion to a verified node was enough.

The receipt job also refuses to commit to the default branch. It is the only job in the repository
holding a write token, so it is the only thing that could put the most trusted file in the network
into `main` without review.

## Residual risks, stated plainly

- **Nothing checks that a conclusion says what its docstring claims.** Every mechanism here checks
  that statements are *stable*, never that they are *right*, and a node justified by a citation has
  no proof to fail. A mis-transcribed threshold or a flipped inequality survives indefinitely. This
  is the largest risk in the project and it is not a software problem; the mitigations are the
  bounded review surface, `Examples.lean`, and maintainer-side review against the source.
- **Mathlib redefining a name.** Fingerprints treat Mathlib constants as opaque names, so a change
  to what a definition *means* while keeping its name moves nothing. Detecting it would mean
  fingerprinting Mathlib's own bodies, which would turn every bump red. `Tools/Hash.lean` says so.
- **A job running untrusted code can lie about its own verdict.** It cannot obtain a token or forge
  a fingerprint, which is what the split buys; it can fail to report a rejection honestly. This is
  Palomar's residual too.
- **Denial of service.** Nothing rate-limits pull requests beyond GitHub's own limits. Every job
  has a timeout and core CI cancels superseded runs per ref. Verification, the expensive one, is
  behind the environment gate.
- **Administrator bypass of the `main` ruleset**, used deliberately today, means a mistaken direct
  push is possible. It has happened once.

## Configuration this depends on

These are repository settings, not files, so they are worth re-checking after any settings change:

- `main` ruleset: active, requires a pull request and code-owner review.
- `verification` environment: required reviewers, non-empty.
- Default workflow permissions: **read**.
- Allow GitHub Actions to approve pull requests: should be **off** — otherwise a workflow can
  satisfy a review requirement by approving its own pull request.
- Require approval for fork pull request workflows: at least "first-time contributors".
