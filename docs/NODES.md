# Authoring a node

Practical recipe. For *why* the structure is what it is, read [ARCHITECTURE.md](ARCHITECTURE.md)
first — especially §1, which explains why a node is a conditional theorem.

> **Status.** Challenge generation and the graph checks exist — see `scripts/ieantn.py`. Receipts
> and staleness tracking do not yet, so `receipt:` is always `null` for now.

## What a node is

A node is one folder recording:

- **conclusions** — what it claims, as named `Prop`s;
- **imports** — what each conclusion assumes, per conclusion;
- **justification** — the evidence for the step from assumptions to claim.

A node usually corresponds to a paper, but need not. Four kinds occur:

| Kind | Example |
|---|---|
| `paper` | Dusart 2018; FKS2. The default. |
| `pipeline` | An abstraction of several papers' shared argument, taking flexible inputs. |
| `folklore` | A fact used without proof in the literature, surfaced so it can be cited and eventually proved. |
| `computation` | A large numerical verification, split out so several papers can import it. |

## Layout

```
IEANTN/Nodes/<Family>/<version>/
  Conclusions.lean       hand-written — the human-readable face of the node
  Challenge.lean         generated — conditional theorems, sorried
  formalization.yaml     metadata: imports, justification, sources, receipts
  README.md              optional prose
Solutions/<Family>.<version>/    optional; separate Lake project, own toolchain pin
Bridges/<Family>/                short proofs that one version implies another
```

Nodes are **versioned**: `IEANTN/Nodes/Lcm/v1/` has id `Lcm.v1`, and a version id is stable
forever. Rather than editing a conclusion that anything depends on, make a new version:

```bash
python scripts/ieantn.py new-version Lcm            # scaffolds Lcm.v2 from the latest
python scripts/ieantn.py deprecate Lcm.v1 --for Lcm.v2
```

`deprecate` is **optional**, and does nothing mechanically. It signals the housekeeping tracker to
migrate dependants onto the newer version and then delete the old one;
`python scripts/ieantn.py housekeeping` lists what that implies.

Most families will never use it. Versions are *variants*, not a succession: a `paper` version
faithful to how a source states its result and a `pipeline` version stating a more general form
both earn their place permanently, and neither obsoletes the other. Deprecate only a version that
should genuinely disappear.

## Step 1: write `Conclusions.lean`

```lean
/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <you>
-/
import IEANTN.Vocabulary.PrimeGaps

/-!
# Dusart 2018

Explicit prime-counting and prime-gap estimates.
-/

namespace Dusart2018

/-- **Proposition 5.4.** For every `x ≥ 89693` there is a prime in `(x, x + x/(log x)³]`.

Dusart states this as the culmination of §5, combining an analytic bound above `4 × 10¹⁸` with a
prime-gap table below it. -/
def proposition_5_4 : Prop := IEANTN.HasPrimeInInterval.logPower 89693 3

end Dusart2018
```

Rules:

- **`def _ : Prop`, never `structure`.** A `def` unfolds to Mathlib; a structure cannot be unfolded
  away when generating a self-contained challenge.
- **Import only** Mathlib, `IEANTN.Vocabulary.*`, and other nodes' `Conclusions.lean`. Importing a
  solution, or PNT+, breaks the whole scheme silently. CI enforces this.
- **Prefer several small conclusions to one bundled one.** Downstream nodes then import only what
  they use, and a change to one conclusion does not invalidate the others.
- **Docstring every conclusion.** This is where the informal statement lives now — there is no
  blueprint. State the source's own numbering, its hypotheses, and anything a transcriber could get
  wrong.
- **Node-local definitions are fine.** `HighlyAbundant` belongs in the Lcm node until a second node
  needs it, at which point it moves to Vocabulary unchanged.

### Getting the statement right

The source is ground truth. The failure mode that matters is a statement that typechecks and is
quietly not the paper's claim:

- **Do not weaken a hypothesis to make a proof go through.** If the paper needs `x ≥ 10¹⁹` and the
  conclusion says `x ≥ 10¹⁸`, the node is claiming something else.
- **Watch endpoint conventions.** `x < p ≤ x + h` and `x ≤ p < x + h` are different claims.
- **Watch junk values.** `tsum` of a non-summable family is `0`; `Real.rpow` of a negative base is
  junk; `li` outside its domain of convergence is `Classical.choice`. A statement can be vacuous
  rather than false. The Vocabulary docstrings flag the specific traps.
- **Transcribe an unusual error term directly** rather than forcing it into a Vocabulary predicate
  of a different shape. If it does not fit, state it in the node.

## Step 2: write `formalization.yaml`

One per node. Deliberately a superset of Palomar's `formalization.yaml` so a node can be spun off
as a submission without restructuring, and validated in CI against Palomar's own contract.

```yaml
version: "v0.4"

node:
  id: Dusart2018
  kind: paper

project:
  name: "..."
  description: >-
    ...
  authors: ["..."]
  license: "Apache-2.0"
  responsible_maintainers: ["..."]

classification:
  arxiv: [math.NT]
  msc2020: ["11N05"]

conclusions:
  - id: proposition_5_4
    declaration: Dusart2018.v1.proposition_5_4
    challenge: Dusart2018.v1.challenge_proposition_5_4
    imports: []
    # Several justifications may be listed; exactly one is designated.
    justifications:
      - id: dusart-paper
        kind: literature
        source: Dusart2018
        locator: "Proposition 5.4"
        note: >-
          ...
    designated: dusart-paper

sources:
  - title: "..."
    authors: ["..."]
    type: "paper"
    id: "..."
    relationship: formalizes
```

Notes:

- `imports` is **per conclusion**, each entry naming another node's conclusion.
- `justifications` is a **list**, and `designated` names the id of the one that counts. A
  conclusion may legitimately have several — a paper, a Lean solution, a bridge — and recording
  the spares is useful, but only the designated one carries trust or appears in the dependency
  report. Re-designating is a one-line change and is often the cheapest fix when the designated
  justification goes stale.
- `kind` is one of `lean-comparator`, `numerical`, `literature`, `asserted`, `bridged`,
  `none-yet`. Use `literature` when the source proves the claim, `asserted` when it merely states
  it — the distinction is the point of recording it. `bridged` borrows another version's evidence
  and must name `from` and the `bridge` file; chains of *designated* `bridged` justifications must
  terminate at a primitive kind, which CI checks.
- Editing a node's metadata with `new-version` or `deprecate` requires `ruamel.yaml`
  (`pip install ruamel.yaml`), which preserves comments. The read-only checks need only PyYAML,
  so CI does not install it.
- `receipt` is `null` until a verification runs.
- Palomar's required-field list is a **moving target**. CI re-fetches the validator; do not vendor
  a copy and do not work from the list above as if it were closed.
- **Never claim novelty without a documented search.** "Unknown" is acceptable and safe; an
  unsupported novelty claim is a finding under Palomar review and a liability here too.
- **Check citations.** Authors, title, identifier, and which name is a given name.

## Step 3: generate `Challenge.lean`

```bash
python scripts/ieantn.py gen-challenges
```

One theorem per conclusion; hypotheses are exactly that conclusion's imports. Never hand-edit the
result — CI regenerates and diffs it.

```lean
import IEANTN.Nodes.Dusart2018.v1.Conclusions
import IEANTN.Nodes.Lcm.v1.Conclusions

theorem Lcm.v1.challenge_lcmUpto_not_highlyAbundant
    (dusart2018_v1_proposition_5_4 : Dusart2018.v1.proposition_5_4) :
    Lcm.v1.lcmUpto_not_highlyAbundant := by
  sorry
```

The `sorry` is deliberate and permanent: a challenge states, it does not prove. Do not add
hypotheses here that are absent from the yaml, and do not edit a generated challenge — the two are
diffed in CI.

## Step 4 (optional, last): a solution

Only when a conclusion is to carry `justification: lean-comparator`.

```bash
python scripts/ieantn.py new-solution Lcm.v1
```

`Solutions/<NodeId>/` is a **separate Lake project**, so its dependencies stay its own. It takes
the core as a path dependency to see the node's `Conclusions`, and must *not* import the
`Challenge`: Comparator compares two modules declaring the same names, so importing it collides.

Its environment is pinned by the receipt's commit, not by a separate `lean-toolchain`.

Namespace collision is the usual trap: if the development's own theorems live in `Lcm`, the
compared declarations cannot also be `Lcm.*`. Bridge in two lines.

Verification runs Comparator in CI (`workflow_dispatch`), not locally. Comparator needs Linux with
Landlock and `systemd-run`, so it does not run on Windows or macOS; WSL2 works for debugging
(Landlock ABI 3 and `systemd-run` are both present), but keep the clone inside the WSL filesystem —
Lake builds over `/mnt/c` are pathologically slow.

Before requesting verification, check the two guarantees locally:

Comparator checks that the challenge and solution declare the *same type* and that the solution
uses only the three permitted axioms. Both are checkable locally, from inside the solution project,
without Comparator itself. Substitute your own node and theorem names:

```bash
cd Solutions/Lcm.v1
NAME=Lcm.v1.challenge_lcmUpto_not_highlyAbundant

printf 'import IEANTN.Nodes.Lcm.v1.Challenge\nset_option pp.all true\n#check @%s\n' "$NAME" > /tmp/ch.lean
printf 'import Solution\nset_option pp.all true\n#check @%s\n#print axioms %s\n' "$NAME" "$NAME" > /tmp/so.lean

lake env lean /tmp/ch.lean > /tmp/ch.out
lake env lean /tmp/so.lean > /tmp/so.out
grep -v "depends on axioms" /tmp/so.out | diff /tmp/ch.out -    # must be identical
grep "depends on axioms" /tmp/so.out                            # must list only the three
```

`pp.all` matters: it prints implicit arguments, universes and instances, so a mismatch that default
printing hides will show up in the diff. The axiom line must name only `propext`,
`Classical.choice` and `Quot.sound` — anything else, `sorryAx` above all, means the solution is
incomplete.

## Invariants CI enforces

1. Vocabulary and every `Conclusions.lean` build clean.
2. No `Conclusions.lean` imports anything outside Mathlib, Vocabulary, and other Conclusions.
3. Every `Challenge.lean` matches what the generator would emit from Conclusions + yaml.
4. Every `formalization.yaml` passes Palomar's current validator.
5. The import graph is acyclic, and so is justification transport along *designated* bridges.
6. Every conclusion's statement fingerprint matches `fingerprints.json`.
7. No conclusion that other nodes depend on has been edited in place, and none still imported has
   been removed (`ieantn.py diff`).
8. Every `lean-comparator` justification has a matching file in `receipts/`.
9. The tooling type-checks (`pyright`, at `basic`).

On (6): after any deliberate change to a conclusion's meaning, run
`python scripts/ieantn.py fingerprint` and commit the result. Committing the fingerprints is what
makes a change of *meaning* visible as a diff line even when the Lean edit looks cosmetic — a
reviewer can see that a statement moved without elaborating anything. Purely cosmetic edits, such
as renaming a binder, leave the fingerprint alone and need no update.

Core CI does **not** run Comparator. That is deliberate: it would take hours per pull request and
would defeat the purpose of the split.

## Changing an existing conclusion

Read ARCHITECTURE §5 first. The short version: **you usually should not.**

CI will hard-fail if you edit a conclusion that has downstream importers or a recorded receipt
*(not yet implemented -- it needs a diff against the base commit)*. There
is no acknowledgement to write and no classification to declare — an author's declaration cannot be
trusted to say whether a change altered the mathematics, and a required one just becomes a box to
tick. The failure carries its own fix:

```bash
python scripts/ieantn.py new-version Lcm
```

Editing a conclusion that nothing imports and that has no receipt is silently fine.

### Making a new version

`new-version` copies the latest version, bumps the id, resets every justification to `none-yet`,
and adds the new version to the build. Then:

1. Edit `Conclusions.lean` in the new version — that is the point of it.
2. `python scripts/ieantn.py gen-challenges`
3. Justify it: write a solution, or a **bridge** from the old version.
4. When the old version should retire:
   `python scripts/ieantn.py deprecate Lcm.v1 --for Lcm.v2`

**Downstream nodes need no action at any point.** They still import the old version, which still
exists and is still verified. Migrating them, and deleting the old version once nothing imports it,
appears in `python scripts/ieantn.py housekeeping` and can wait for whenever there is compute.

### Bridges

A bridge is a short Lean file showing that one version's conclusions imply another's. It is *not* a
solution and *not* an import edge — registering it as an import would make a bidirectional pair of
bridges into an import cycle, and bidirectional is exactly what migration needs.

Two implications are in play, needed by different parties:

| Implication | Needed by | For |
|---|---|---|
| `C_old → C_new` | the new version | borrowing the old version's evidence (`justification: bridged`) |
| `C_new → C_old` | a downstream node | migrating its import onto the new version |

Both hold ⇒ genuine restatement; the old version can eventually be deleted. Only the first ⇒ the
new conclusion is weaker, so downstream cannot migrate and the old version legitimately stays.
Neither ⇒ the change is an amendment, and downstream nodes need human re-examination.

A `bridged` justification names `from` and `bridge`:

```yaml
justification:
  kind: bridged
  from: Lcm.v1.lcmUpto_not_highlyAbundant
  bridge: Bridges/Lcm/v1_to_v2.lean
```

Chains of `bridged` must terminate at a primitive justification. CI enforces this: without it two
versions could each borrow their evidence from the other while neither is justified by anything.
