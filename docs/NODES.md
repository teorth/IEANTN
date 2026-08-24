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
IEANTN/Nodes/<NodeId>/
  Conclusions.lean       hand-written — the human-readable face of the node
  Challenge.lean         generated — conditional theorems, sorried
  formalization.yaml     metadata: imports, justification, sources, receipts
  README.md              optional prose
Solutions/<NodeId>/      optional; separate Lake project, own toolchain pin
```

`<NodeId>` is stable forever. It survives refactoring — see ARCHITECTURE §5.

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
    declaration: Dusart2018.proposition_5_4
    imports: []
    justification:
      kind: literature
      source: Dusart2018
      note: >-
        ...
    receipt: null

sources:
  - title: "..."
    authors: ["..."]
    type: "paper"
    id: "..."
    relationship: formalizes
```

Notes:

- `imports` is **per conclusion**, each entry naming another node's conclusion.
- `justification.kind` is one of `lean-comparator`, `numerical`, `literature`, `asserted`,
  `none-yet`. Use `literature` when the source proves the claim, `asserted` when it merely states
  it — the distinction is the point of recording it.
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
import IEANTN.Nodes.Lcm.Conclusions
import IEANTN.Nodes.Dusart2018.Conclusions

theorem Lcm.challenge_not_highly_abundant
    (h : Dusart2018.proposition_5_4) : Lcm.lcm_not_highly_abundant := by
  sorry
```

The `sorry` is deliberate and permanent: a challenge states, it does not prove. Do not add
hypotheses here that are absent from the yaml, and do not edit a generated challenge — the two are
diffed in CI.

## Step 4 (optional, last): a solution

Only when a conclusion is to carry `justification: lean-comparator`.

`Solutions/<NodeId>/` is a **separate Lake project with its own `lean-toolchain`**. It may import
anything. It declares the same theorem names as the challenge, and proves them.

Namespace collision is the usual trap: if the development's own theorems live in `Lcm`, the
compared declarations cannot also be `Lcm.*`. Bridge in two lines.

Verification runs Comparator in CI (`workflow_dispatch`), not locally. Comparator needs Linux with
Landlock and `systemd-run`, so it does not run on Windows or macOS; WSL2 works for debugging
(Landlock ABI 3 and `systemd-run` are both present), but keep the clone inside the WSL filesystem —
Lake builds over `/mnt/c` are pathologically slow.

Before requesting verification, check the two guarantees locally:

```bash
printf 'import Challenge\nset_option pp.all true\n#check @Lcm.challenge_not_highly_abundant\n' > /tmp/ch.lean
printf 'import Solution\nset_option pp.all true\n#check @Lcm.challenge_not_highly_abundant\n#print axioms Lcm.challenge_not_highly_abundant\n' > /tmp/so.lean
lake env lean /tmp/ch.lean > /tmp/ch.out; lake env lean /tmp/so.lean > /tmp/so.out
grep -v "depends on axioms" /tmp/so.out | diff /tmp/ch.out -    # must be identical
```

The axiom line must show only `propext`, `Classical.choice`, `Quot.sound`.

## Invariants CI enforces

1. Vocabulary and every `Conclusions.lean` build clean.
2. No `Conclusions.lean` imports anything outside Mathlib, Vocabulary, and other Conclusions.
3. Every `Challenge.lean` matches what the generator would emit from Conclusions + yaml.
4. Every `formalization.yaml` passes Palomar's current validator.
5. The import graph is acyclic.
6. Every conclusion's elaborated-statement hash matches its recorded receipts, or the affected
   nodes are marked stale.

Core CI does **not** run Comparator. That is deliberate: it would take hours per pull request and
would defeat the purpose of the split.

## Changing an existing conclusion

Read ARCHITECTURE §5 first. A pull request that changes any conclusion's statement must carry a
**change note**, one entry per changed conclusion:

```yaml
change:
  - conclusion: Lcm.lcm_not_highly_abundant
    classification: restatement        # restatement | amendment | unclassified
    rationale: >-
      Quantifier moved outside the definition; the bound and threshold are unchanged.
    equivalence: Migrations/Lcm/2026-08-24.lean    # required iff restatement
```

- **`restatement`** — `equivalence` names a Lean file bridging old and new. CI attempts both
  directions and reports which hold; see below.
- **`amendment`** — no proof needed, but downstream receipts are void and every downstream node is
  flagged for human re-examination.
- **`unclassified`** — the default if the note is missing or fails to check. Treated as an
  amendment.

You may let an agent draft the classification. It does not need to be right: CI *derives* the true
answer by attempting the bridges, so a wrong guess costs a red check, not a corrupted graph.

### What actually happens on a restatement

You do not patch downstream nodes. The previous version of the node is archived automatically as
`<NodeId>@<hash>`, frozen with `status: superseded` and **its existing receipt intact**; your new
solution becomes a small *bridge* deriving the new conclusions from the archived ones. Downstream
nodes keep importing the archived node and need no action at all — no large solution is re-run.
Migrating them to the new node, and deleting the archive once nothing imports it, is later
housekeeping.

Two implications are in play, and they are needed by different parties:

| Implication | Needed by | For |
|---|---|---|
| `C_old → C_new` | this node | the bridge |
| `C_new → C_old` | a downstream node | migrating off the archived node |

Both hold ⇒ genuine restatement, and the archived node can eventually be retired. Only the first ⇒
the new conclusion is weaker; fine for this node, but downstream cannot migrate and the archived
node stays. Neither ⇒ it is an amendment, whatever the note said.

If you are only reformatting, renaming binders, or refactoring Vocabulary in a way that unfolds
identically, the elaborated-statement hash will not change and no note is required.
