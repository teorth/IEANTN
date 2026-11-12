# Source dossiers

A source dossier is an optional reading note for one node. It links a declaration key to a pinned
edition of a paper, a locator in that edition, the domain the statement assumes, the rounding
direction of each displayed numeral, and the divergences a reviewer has already recorded.

It is not a proof. The validator checks that the record is complete and that a displayed numeral
sits on the correct side of the exact rational named beside it. It does not open the paper, and
it does not decide that the Lean says what the citation claims. That gap is the one described in
[SECURITY.md](../SECURITY.md): nothing in this repository checks that a conclusion means what its
docstring says.

A node with no dossier is fine. A node with one keeps it next to `formalization.yaml`:

```
IEANTN/Nodes/<Family>/<version>/dossier.yaml
```

```yaml
schema: ieantn-source-dossier/1
node: RosserSchoenfeld1962.v1
declarations:
  - key: RosserSchoenfeld1962.v1.equation_3_35
    edition:
      pin: "Illinois Journal of Mathematics 6(1) (1962), 64-94"
      year: 1962
      pages: "64-94"
    locator: "Theorem 12, equation (3.35), p. 71; proof on pp. 77-80"
    domain: "every real x > 0, with both inequalities strict"
    rounding: exact
    quantities:
      - display: "1.03883"
        exact: "103883/100000"
    divergences:
      - "Theorem 12 also asserts a maximum at x = 113; that assertion is not represented."
```

`edition.pin` is the bibliographic pin already written down for that node, not a new citation.
It has to contain the parenthesized `year` and the `pages` range, so the three fields cannot
drift apart. `locator` is required and is the place in that edition; a theorem number that is
not already in the node's comments does not belong here. `domain` is the hypothesis the
statement actually quantifies over.

`rounding` is one of `exact`, `up`, `down`, `toward-zero`, `away-from-zero`, and it applies to
every entry of `quantities`:

| Direction | What the display must be |
|---|---|
| `exact` | Equal to the rational. This is the displayed decimal read as a rational, not a claim that the paper computed extra hidden digits. |
| `up` | Strictly greater than the exact rational. |
| `down` | Strictly less than the exact rational. |
| `toward-zero` | Strictly closer to zero, and not a sign change. |
| `away-from-zero` | Strictly farther from zero, same sign. |

`divergences` is required. An empty list means the reading recorded none. The validator checks
that the entries are strings. It cannot check that the reading happened.

Check the files that exist:

```bash
python3 scripts/check_dossiers.py
```

The two dossiers in the tree copy locators and edition pins from comments and metadata that were
already in those nodes. They were not filled in by guessing a theorem number.
