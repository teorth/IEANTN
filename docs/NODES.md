# Authoring a node

Practical recipe. For *why* the structure is what it is, read [ARCHITECTURE.md](ARCHITECTURE.md)
first — especially §1, which explains why a node is a conditional theorem.

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
  Examples.lean          optional — consequences, to show what the node buys
  Tables.lean            optional — the paper's bulk data, and nothing else
Solutions/<Family>.<version>/    optional; separate Lake project, toolchain pinned equal
IEANTN/Bridges/<Family>/         short proofs that one version implies another
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
  id: Dusart2018.v1     # must equal the path-derived id; check-graph compares them
  family: Dusart2018
  version: v1
  kind: paper
  status: stub          # template | stub | awaiting-solution | awaiting-verification |
                        # active | deprecated.  `template` is a hard CI failure.

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
  # `id`, and both halves of every `imports` entry, must be Lean identifiers: they are written
  # verbatim into the generated challenge, as declaration names and as binder types. CI rejects
  # anything else.
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
- `imports_status` answers one question: *has anyone worked out what this rests on, and could all
  of it be drawn?*

  | value | meaning | border in `GRAPH.md` |
  |---|---|---|
  | `undetermined` | Nobody has looked. The default when the field is absent. | finely dotted |
  | `traced` | The inputs are written down in a justification note, and at least one is **not** an edge — either not a node yet, or something an arrow can never carry: an algorithm, a data set, a computation. | dashed |
  | `identified` | Every input is drawn as an edge. The arrows tell the whole story. | solid |
  | `none` | There are no inputs — a conditional whose hypotheses a consumer supplies, for instance. | solid |

  The pattern tracks how much of the story the arrows tell: solid says all of it, a clear dash
  says most, fine dots say none.

  An empty `imports` list on its own is ambiguous — it means either "rests on nothing" or "nobody
  looked" — and those are very different things to show a reader, so the honest one is what you get
  for free.

  `traced` exists because `undetermined` was doing two jobs. "Nobody has looked at this
  verification" and "it rests on Trudgian's Theorem 4.2, Whittaker–Shannon sampling, a subconvexity
  bound, and its own FFT, of which only the third could currently be an edge" are not the same
  state. It also lets `identified` mean exactly what it says, rather than "identified apart from
  the bits that cannot be drawn".

  `housekeeping` lists `undetermined` conclusions. It deliberately does **not** list `traced` ones:
  some of their missing edges await a node that could exist and some await one that never can, and
  nothing can tell those apart mechanically — a queue of unactionable items is worse than none.
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
- There is no `receipt` field. Receipts live in `receipts/`, one JSON file per verified
  conclusion, written by the verification workflow. See [../receipts/README.md](../receipts/README.md).
- Palomar's required-field list is a **moving target**. CI re-fetches the validator; do not vendor
  a copy and do not work from the list above as if it were closed.
- **Never claim novelty without a documented search.** "Unknown" is acceptable and safe; an
  unsupported novelty claim is a finding under Palomar review and a liability here too.
- **Check citations.** Authors, title, identifier, and which name is a given name.

## `Tables.lean`, for a paper that carries data

Some explicit results are stated against a paper's numeric tables — rows of constants, parameter
sets, thresholds. Those go in an optional `Tables.lean` beside the conclusions, **not inside them**.

The reason is the one thing `Conclusions.lean` is for: it is the file a human audits, and its
shortness is a feature. A reviewer checking three claims should not have to scroll past two hundred
rows of data to reach them. Anything that would make them scroll belongs next door. A definition or
two the conclusions need — `Lcm.v2`'s `HighlyAbundant`, say — is not data in this sense and stays
where it is; the test is bulk, not kind.

**Data only.** A `Tables.lean` may not declare a `theorem` or a `lemma`, and CI enforces it:

- a *statement* about a table is a **conclusion**, where it becomes a claim of record with a
  fingerprint and a justification;
- a *proof* about one — the numerical verification that a table's rows satisfy what the paper says
  they do — belongs in a **solution**, unless it is somehow needed in order to state an exportable
  result at all. That should be rare, and is worth resisting when it is not.

**Any node's conclusions may import any node's tables**, not only its own. A table is data, and the
node that computed it is often not the node that states a claim about it — FKS2's conversion
pipelines are stated in terms of quantities BKLNW tabulates. Forcing a copy would create a second
source of truth, which is the thing this repository exists to avoid.

**Keep the import list very short.** A table file may import only Mathlib, Vocabulary and other
table files; CI enforces that much, which rules out the case that matters — a table that needs a
*conclusion* in order to be stated is not data. Beyond that it is guidance rather than a rule: a
table wanting a long list of imports is usually a computation wearing a table's clothes, and
probably wants to be its own node.

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

Only when a conclusion is to carry a `lean-comparator` justification.

```bash
python scripts/ieantn.py new-solution Lcm.v1
```

`Solutions/<NodeId>/` is a **separate Lake project**, so its dependencies stay its own. It takes
the core as a path dependency to see the node's `Conclusions`, and must *not* import the
`Challenge`: Comparator compares two modules declaring the same names, so importing it collides.

It carries a `lean-toolchain` identical to the repository's; CI enforces the match. What pins a
verification is the commit its receipt records, not that file.

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
2. No `Conclusions.lean` imports anything outside Mathlib, Vocabulary, and other Conclusions; no
   `Examples.lean` or bridge does either, and neither contains `sorry`. Vocabulary holds no
   theorems.
3. Every `Challenge.lean` matches what the generator would emit from Conclusions + yaml, and so do
   `IEANTN/Nodes.lean` and `IEANTN/Bridges.lean`.
4. Every `formalization.yaml` passes Palomar's current validator.
5. The import graph is acyclic, and so is justification transport along *designated* bridges.
6. Every conclusion's statement fingerprint matches `fingerprints.json`, and `STATE.md` is current.
7. No conclusion that other nodes depend on has been edited in place, and none still imported has
   been removed (`ieantn.py diff`, in the `Network impact` job).
8. Every `lean-comparator` justification has a matching file in `receipts/`, every receipt names a
   successful run of `verify.yml` **for that node**, and no receipt covers a conclusion absent from
   its solution's `comparator.json`.
9. Every conclusion `id`, and both halves of every import reference, is a Lean identifier — they are
   written verbatim into the generated challenge.
10. Every solution's `lean-toolchain` equals the repository's, and `verify-comparator.sh` pins
    `lean4export` for that same toolchain.
11. The tooling type-checks (`pyright`, at `basic`) and its unit tests pass.

On (6): after any deliberate change to a conclusion's meaning, run
`python scripts/ieantn.py fingerprint` and commit the result. Committing the fingerprints is what
makes a change of *meaning* visible as a diff line even when the Lean edit looks cosmetic — a
reviewer can see that a statement moved without elaborating anything. Purely cosmetic edits, such
as renaming a binder, leave the fingerprint alone and need no update.

Core CI does **not** run Comparator. That is deliberate: it would take hours per pull request and
would defeat the purpose of the split.

## Changing an existing conclusion

Read ARCHITECTURE §5 first. The short version: **you usually should not.**

CI will hard-fail if you edit a conclusion that has downstream importers or a recorded receipt.
This is the `Network impact` job, which runs `ieantn.py diff` against the pull request's base
commit. There is no acknowledgement to write and no classification to declare — an author's declaration cannot be
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
justifications:
  - id: bridge-from-v2
    kind: bridged
    from: Lcm.v2.lcmUpto_not_highlyAbundant_of_primeGap
    bridge: IEANTN/Bridges/Lcm/V2ToV1.lean
```

Chains of `bridged` must terminate at a primitive justification. CI enforces this: without it two
versions could each borrow their evidence from the other while neither is justified by anything.

**A bridge file lives under `IEANTN/Bridges/`, and CI rejects one that does not.** That directory
is inside the library, so the core build compiles it. A bridge somewhere else would still satisfy
"the file named exists" for as long as anyone cared to look, while having stopped being a proof the
moment either statement it relates moved — which is exactly the situation versioning creates. The
generated `IEANTN/Bridges.lean` imports every one of them.

Consequently a bridge is held to the same closure rule as a Conclusions file — Mathlib, Vocabulary,
other Conclusions, other bridges — and may not contain `sorry`, and may not import a `Challenge`. A
bridge resting on the very `sorry` it exists to discharge would elaborate, would be recorded, and
would prove nothing.

Its hypotheses are the conclusions named in `from`, plus whatever the *target* node already
imports. `IEANTN/Bridges/Lcm/V2ToV1.lean` is the worked example: it takes `Lcm.v2`'s conclusion and
Dusart's Proposition 5.4 — which `Lcm.v1` imports anyway — and produces `Lcm.v1`'s conclusion.

Unlike a solution, a bridge is not sandboxed and not Comparator-checked. It does not need to be:
there is no untrusted development here, only a short implication between two statements that are
already pinned by their fingerprints, and `lake build` checks it on every push.
