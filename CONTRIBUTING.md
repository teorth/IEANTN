# Contributing to IEANTN

Contributions go through ordinary GitHub pull requests. What is unusual here is that the
repository holds a *graph of claims with evidence attached*, so a change can degrade something far
from the file you edited. The workflows below are designed so that the cheap path is also the safe
one.

Read [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) once before your first contribution.
[docs/NODES.md](docs/NODES.md) is the reference for node file formats.

> **Status.** Marked *(planned)* below: the breaking-change detector, the `/verify` bot, and the
> reviewer report. Everything else works today.

## Two principles

**Versioning is the escape hatch, not a ceremony.** If a change would break something, the answer
is almost always to create a new version of the node rather than to edit the existing one. New
versions never break anything, so CI stays green and nobody downstream has to act.

**Acknowledging breakage is rare, and that is the point.** You do not write an acknowledgement in
the normal course of work; there is no box to tick. It exists only for the case where a change is
genuinely breaking and has to land anyway. Because it is rare, it shows up in the diff and a
reviewer notices — which is exactly what a routine, always-required acknowledgement would destroy.

---

## 1. Start a solution for a node that has none

You want to begin proving an existing challenge.

**Do:** create `Solutions/<Family>.<version>/` as its own Lake project with its own
`lean-toolchain`. Declare the same theorem names as `Challenge.lean` and prove what you can.

**Metadata:** the justification does **not** change. Add a progress marker instead:

```yaml
    justification:
      kind: none-yet
    progress:
      solution: Solutions/Lcm.v1/
      state: in-progress
      remaining_holes: 7
```

**CI:** nothing runs. Solutions are outside the core build.

> **An incomplete solution is never a justification.** `justification` records what a claim *rests
> on*; `progress` records what someone is *doing*. They are orthogonal, and a partial proof with
> seven `sorry`s supports nothing. Conflating them would corrupt the one report the repository
> exists to produce.
>
> But a partial solution is not nothing either: it establishes *imports + remaining holes →
> conclusion*. It is a **justification-in-waiting whose missing pieces have not been named yet** —
> which is what workflow 6 is about.

## 2. Continue an incomplete solution

You closed some holes but not all.

**Do:** push the changes. **Metadata:** update `remaining_holes`; nothing else. **CI:** core checks
only.

This is the cheapest kind of PR in the repository and deliberately so — most work is of this shape.

If you want the solution typechecked, add the `build-solution` label and a dispatchable workflow
builds just that project *(planned)*. It is not in core CI because a solution can take an hour.

## 3. Complete a solution

All holes closed and you believe Comparator will accept it.

**Do:** push, then comment `/verify <Family>.<version>` on the PR *(planned)*.

A maintainer approves the run; Comparator executes against the generated challenge; on success the
bot commits the receipt and flips the justification to `lean-comparator`.

**Do not write the receipt yourself, and do not set `kind: lean-comparator` by hand.**

> **Receipts must be written by the verifier, never by the author** — otherwise anyone can claim
> verification by typing it, and every downstream trust computation is decorative. Receipts
> therefore live under `receipts/`, not in `formalization.yaml`, and that path is writable only by
> the verification workflow's identity (a ruleset path restriction). `check-graph` requires a
> `lean-comparator` justification to have a corresponding receipt file. *(planned: `receipts/`
> currently does not exist and receipts are a `null` field in the yaml.)*

## 4. Modify a conclusion

The statement is wrong, imprecise, or should be generalised.

**Do:**

```bash
python scripts/ieantn.py new-version Lcm
```

Then edit the new version's `Conclusions.lean`, run `gen-challenges`, and pick whichever of these
is least work:

| Option | When |
|---|---|
| No solution yet | The old solution will not port and you are not ready to redo it. |
| Port the solution | The proof survives the restatement with small edits. |
| Bridge from the old version | The old conclusion implies the new one. Usually the cheapest. |

**CI:** editing a depended-on conclusion in place is a hard failure *(planned)*; making a new
version is always green. **Downstream nodes need no action** — they still import the old version.

Deprecate the old version when you want it retired:

```bash
python scripts/ieantn.py deprecate Lcm.v1 --for Lcm.v2
```

## 5. Modify Vocabulary

The riskiest change in the repository: Vocabulary is shared, so a semantic change can alter what
every node that mentions it is claiming.

Three cases, and only the third is expensive:

- **Additive** — a new definition. Free; breaks nothing.
- **Cosmetic** — renamed binders, reformatting, a refactor that unfolds to the same term. **Also
  free**: statement hashes are taken of the *elaborated* statement, so nothing goes stale.
- **Semantic** — the definition now means something different. Every node whose conclusions mention
  it is now claiming something else.

For the third case, **do not version the Vocabulary file.** Version the *definition*: add the new
one alongside the old, mark the old `@[deprecated]`, migrate node versions onto it one at a time,
and delete the old definition when nothing uses it.

> File-versioning (`PrimeCounting.v1` / `.v2`) fragments the module structure for everyone in order
> to solve a problem local to one definition, and it leaves no compiler-visible signal. Lean's
> `@[deprecated]` attribute gives you a warning at every remaining use site for free, so the
> migration list maintains itself. This is the node-versioning pattern at definition granularity.

## 6. Extract intermediate nodes from a solution

A solution is stuck because the paper leans on a result it does not prove, or a numerical
computation, or a piece of folklore.

**Do:** promote each remaining hole to its own node — `kind: folklore` or `computation`, with
`justification: asserted` or `none-yet` — add it to the stuck node's imports, and the solution
becomes complete relative to those new imports.

This is the main way the network grows, and it is why workflow 1 tracks `remaining_holes`: **the
holes in a stuck solution are a ready-made list of candidate nodes.** If the extracted fact serves
several papers, every one of them benefits at once.

Do the extraction with a new version of the stuck node (its imports are changing, so its challenge
changes) and CI stays green throughout.

## 7. Housekeeping

Simplifying the graph: collapsing versions, migrating dependants off deprecated nodes, refreshing
stale verifications, deleting what nothing imports.

```bash
python scripts/ieantn.py housekeeping
```

Usually done by maintainers or experienced contributors, often in large PRs touching many nodes.
Anything goes provided CI passes and a human reviewer confirms that the surviving nodes'
`Conclusions.lean` files still say the right things — that last check is not mechanisable today.

Housekeeping PRs are where the reviewer degradation report matters most, since they are the ones
that touch enough nodes for the consequences to be hard to hold in your head.

## 8. Bump Mathlib

This gently degrades everything at once, and it is the case the two-axis trust model
(ARCHITECTURE §4) exists for: a bump changes the **environment**, not the **statements**. Every
receipt was made under an older Mathlib; no edge has broken. That is a yellow light, not a red one.

**Do:** update `lean-toolchain` and `lake-manifest.json`. That is the whole PR.

**Metadata:** *nothing changes, in any node.* Staleness is **derived**, not stored — it is computed
by comparing each receipt's recorded environment against the current one. So a bump that degrades
two hundred nodes still touches exactly two files.

**CI:** two things must hold, and one is red if it fails:

- The core must build — Vocabulary, Conclusions and Challenges all compile under the new Mathlib.
- **Every conclusion's elaborated-statement hash must be unchanged.** Normally it is. If a hash
  *did* move, Mathlib has silently changed what one of your statements means, and that is a genuine
  semantic change to be handled as workflow 5 — red, not yellow. This is the case that earns the
  hash mechanism its keep: it is otherwise invisible.

If both hold, every affected node simply moves one release further from its verification, and the
PR is green with warnings.

### How stale is too stale

Three levels, with the third defined by something real rather than a made-up number:

| | Meaning |
|---|---|
| **green** | Verified against the current Mathlib. |
| **yellow** | Stale, but within the Mathlib cache window — a refresh costs about one node-sized run. |
| **orange** | Past the cache window. Dependencies must now build from source, so a refresh costs many times the per-node budget. |

Solutions keep their own toolchain pins, so a core bump does not break them: they still build at
the Mathlib they were verified against, and re-running at that pin stays cheap. What has aged is
the *claim that the result holds under current Mathlib*, not the proof.

**Do not chase bumps.** Let staleness accumulate, and run refresh sweeps ordered by fan-in when
compute is available (`python scripts/ieantn.py housekeeping`). The one thing worth avoiding is
letting a node slide from yellow to orange, because that is where the cost jumps discontinuously.

---

## The acknowledgement escape hatch

If CI reports that your change breaks something and you need it to land anyway, add
`changes/<slug>.yaml`:

```yaml
acknowledge:
  - conclusion: Lcm.v1.lcmUpto_not_highlyAbundant
    effect: receipt-voided
    reason: >-
      The threshold was wrong; the recorded statement was not Dusart's. Landing the correction
      matters more than preserving the receipt, which was verifying the wrong claim anyway.
```

CI cross-checks this against its own computation, so it cannot be written without reading what
actually broke. It is an override, not a routine step: if you find yourself writing one often, you
are editing where you should be versioning.

## Disclose AI assistance

Say so in the PR body — one line is enough (`Made with Claude Code`, or the tool's own
`Co-Authored-By:` footer). Much of this repository is expected to be AI-assisted; the disclosure
lets reviewers calibrate, not disqualify.

Please understand the diff you submit. "The agent wrote it" is not an answer to a reviewer's
question about why a conclusion says what it says.
