# Solutions, and planning a long one

A solution is a separate Lake project under `Solutions/<Family>.<version>/` that proves what a
node's `Challenge.lean` states. It may import anything, is not in the core build, and is verified
once by Comparator and then left alone. Readability is not a goal.

Most of what you need is in [CONTRIBUTING.md](../CONTRIBUTING.md) — workflows 1 and 2 cover
starting one and continuing one. This file is about the part that only matters when the port is
large: knowing its shape before you start.

## `progress.yaml` — a best practice, not a schema

A solution directory may carry a `progress.yaml`. **Nothing enforces it and nothing parses it.**
It is prose with structure, the way a good commit message is, and it exists because a port that
takes weeks needs somewhere to record what was decided before the deciding is forgotten.

The one number that *is* enforced lives elsewhere: `remaining_holes`, on the node's
`formalization.yaml`, derived from the build by `ieantn.py progress --write`. Do not duplicate it
here; a hand-copied count is a hand-copied count wherever it sits.

Suggested fields, all optional:

| field | what it is for |
|---|---|
| `solution`, `state` | which directory, and whether work is live, stalled or abandoned |
| `source` | the upstream being ported, pinned to a commit — so a later reader can diff |
| `targets` | one entry per compared theorem: its upstream analogue, whether that analogue is actually proved, and how closely the statements match |
| `trusted_numerics` | what the upstream leaves unproved, and what becomes of it here |
| `upstream_closure` | how much comes along transitively, and what should be pruned |
| `file_layout` | the decision about how to split, and why |
| `order` | what to do first, and what that de-risks |

`Solutions/FKS2.v1/progress.yaml` is the worked example.

## Two things worth deciding before writing any Lean

**What the upstream actually proves.** An upstream development that "does" a theorem may be
threading finite numerical data as deliberate `sorry`s — PNT+'s FKS2 does exactly that, and says
so. A wholesale copy then cannot pass Comparator, which permits only `propext`,
`Classical.choice` and `Quot.sound`, whatever else is finished.

That is not a setback. This network's conditional-theorem shape is the right home for such data:
what upstream must leave as a hole, a node states as an **import hypothesis**. The scaffolded
`Solution.lean` already takes the node's imports as hypotheses, so the port is largely a matter of
replacing holes with them — and any hole with no node behind it is a real dependency nobody had
written down. Finding those is worth as much as the proof.

**How much comes along.** Take the transitive import closure before copying anything. A monolithic
upstream will hand you far more than the argument needs: FKS2's closure in PNT+ is 76 modules and
63,000 lines, most of it analytic machinery reached through two wide imports that the explicit
argument never uses. Prune at the import, not afterwards.

## One file or many

**Many.** Not for readability — nobody reads a solution — but for build time. Lake elaborates
files in parallel and rebuilds only what changed; a single large file re-elaborates in full on
every edit and cannot parallelise. On a development that will be iterated on for weeks that
difference dominates.

Keep the compared theorems in `Solution.lean` and nothing else, with the development in sibling
files it imports. `Solutions/Lcm.v2` is the existing pattern: `LcmDev.lean` holds the argument,
`Solution.lean` holds the one theorem Comparator sees. Where the upstream has already split
sensibly — per-table-row files, say — keep its split rather than inventing another.

## Checking progress

```bash
python scripts/ieantn.py progress <node>            # report
python scripts/ieantn.py progress <node> --write    # report, and record the hole count
```

It builds the solution, re-elaborates it to locate every `sorry` by line, and runs `#print axioms`
on each compared theorem. **The axiom check is the one that matters**: a declaration can contain no
`sorry` and still not be proved, because something it depends on has one. It is also what
Comparator checks, so a clean report is a preview of the verdict — without the sandbox, the second
kernel, or a receipt.

A solution reporting every theorem proved is ready to verify. It still justifies nothing until it
is verified, and the justification must not be touched before then.
