# Receipts

One JSON file per Lean-verified conclusion, named `<Family>.<version>.<conclusion>.json`.

A receipt records what a verification actually depended on: the statement fingerprint of the
conclusion **and of every conclusion it imports**, the Lean toolchain and Mathlib revision, the
solution project, and the workflow run that produced it. Staleness is then *computed* by
re-fingerprinting and comparing — never by looking at a date. The timestamp is for display only.

## These files are written by the verification workflow, not by hand

A receipt an author can write is worth nothing: it is a claim of verification typed by the person
making the claim. A receipt arriving in a pull request from anyone but the verification workflow is
a review failure, not a formatting nit.

The intended enforcement — a ruleset restricting `receipts/` to the workflow's identity — is not
available here: GitHub refuses push rulesets on public repositories and on repositories outside an
organisation. `python scripts/ieantn.py check-receipts` enforces **provenance** instead, and it is
the better control anyway, because it checks that the verification happened rather than who typed
the file. For each receipt it requires:

- a recorded run URL pointing at this repository;
- that the run exists, concluded `success`, and is `verify.yml` — which needs a maintainer to have
  approved the `verification` environment;
- that the run is **this node's**. `verify.yml` puts the dispatched node in its job names, so
  GitHub's own record says what was verified. Without this, any successful verification validated
  any receipt: copying a real run URL into a fabricated receipt passed. Receipts predating the
  convention fall back to a uniqueness rule — one run, one node.

A receipt also may not cover more than Comparator was asked about. `record-receipt` cross-checks
the node's conclusions against `theorem_names` in the solution's `comparator.json` and refuses if
any conclusion is missing. This is not an anti-forgery measure: adding a second conclusion to an
already-verified node was enough to earn it a `lean-comparator` justification for a statement no
verifier had seen.

`python scripts/ieantn.py record-receipt` exists for the workflow to call. Do not run it yourself.

## Reading the result

`python scripts/ieantn.py status` grades every receipt on two axes that are deliberately not
collapsed:

| | Meaning |
|---|---|
| `green` | Verified against the current environment. |
| `yellow` | Statements unchanged, environment moved, still inside the Mathlib cache window. |
| `orange` | As above, but far enough behind that a refresh must build dependencies from source. |
| `BROKEN` | A statement moved. **Not staleness** — the verified implication no longer connects to what is now claimed. |

`BROKEN` is binary and fatal however small the edit, and it fires whether the statement that moved
was the conclusion's own or one it imports.
