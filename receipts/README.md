# Receipts

One JSON file per Lean-verified conclusion, named `<Family>.<version>.<conclusion>.json`.

A receipt records what a verification actually depended on: the statement fingerprint of the
conclusion **and of every conclusion it imports**, the Lean toolchain and Mathlib revision, the
solution project, and the workflow run that produced it. Staleness is then *computed* by
re-fingerprinting and comparing — never by looking at a date. The timestamp is for display only.

## These files are written by the verification workflow, not by hand

A receipt an author can write is worth nothing: it is a claim of verification typed by the person
making the claim. `receipts/` is therefore restricted to the verification workflow's identity by a
ruleset path rule, and a receipt arriving in a pull request from anyone else is a review failure,
not a formatting nit.

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
