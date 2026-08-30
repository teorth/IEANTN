# Contributing to IEANTN

Contributions go through ordinary GitHub pull requests. What is unusual here is that the
repository holds a *graph of claims with evidence attached*, so a change can degrade something far
from the file you edited. The workflows below are designed so that the cheap path is also the safe
one.

Read [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) once before your first contribution.
[docs/NODES.md](docs/NODES.md) is the reference for node file formats, and
[SECURITY.md](SECURITY.md) states what the repository trusts and why.

> **Status.** Everything below works today except where marked *(planned)*: the `/verify` comment
> trigger (workflow 3 gives what to do meanwhile), the `build-solution` label (workflow 2), and
> posting the reviewer report as a pull request comment rather than to the job summary. See
> [docs/ROADMAP.md](docs/ROADMAP.md).

## Two principles

**Versioning is the escape hatch, not a ceremony.** If a change would break something, the answer
is almost always to create a new version of the node rather than to edit the existing one. New
versions never break anything, so CI stays green and nobody downstream has to act.

**Acknowledging breakage is rare, and that is the point.** You do not write an acknowledgement in
the normal course of work; there is no box to tick. It exists only for the case where a change is
genuinely breaking and has to land anyway. Because it is rare, it shows up in the diff and a
reviewer notices — which is exactly what a routine, always-required acknowledgement would destroy.

## Where to start, by how much of the network you can see

**If you are looking for something to do**, the [project
board](https://github.com/users/teorth/projects/3) lists it. Anything marked `Unclaimed` is free to
take: comment `claim` on the issue and a bot assigns it to you and moves the card to `Claimed`.
`disclaim` releases it, and `propose PR #123` links your pull request. Claims do not expire, so
release one you have put down rather than leaving it to block someone else.

Claiming is a courtesy, not a lock — nothing in CI enforces it. Its purpose is to stop two people
independently formalizing the same node, which in a repository where a single node can be a
six-thousand-line solution is a costly collision.

The three layers carry very different blast radii, and that is the natural order to work through
them in.

| | Blast radius | Start here if |
|---|---|---|
| **Solutions** | one node | You are new. A solution is contained: get it wrong and the verification fails, and nothing else in the network notices. |
| **Conclusions** | the node and its dependants | You know the source literature. A wrong statement is not caught by any check — see below. |
| **Vocabulary** | every node | You have the whole project in your head. Mathlib treats changes to its core files the same way, for the same reason. |

**Nothing checks that a conclusion says what its docstring claims.** Every mechanism here checks
that statements are *stable*, never that they are *right* — and a node justified by a citation has
no proof to fail, so a mis-transcribed threshold or a flipped inequality can sit in the network
indefinitely. That is why conclusions want someone who knows the paper, and why review of a
conclusions file is a different activity from review of code.

The compensating strength: **the surface a human must read is bounded.** Nobody has to read a
solution. For a pull request adding two hundred thousand lines of machine-generated proof, the
mandatory review is the `Conclusions.lean` files and the `formalization.yaml` — tens of lines. If
you are reviewing, read those against the source and let the rest be.

## Large tasks

Tasks are now the size of *"formalize FKS2"* or *"extract BKLNW's table computations into their own
node"*, not *"fill in the sorry in Lemma 5.2"*. Four things follow.

**Land conclusions early, justify later.** Do not hold one enormous pull request open for a month.
A node whose conclusions are stated and whose justification is `none-yet` is *immediately useful*:
it makes the claim citable, gives downstream nodes something to import, and turns the remaining
work into a well-posed task. Land the conclusions in the first week; the solution can follow.

**One person per node solution** — or a group in constant contact. A solution is a single Lean
development and does not merge well across independent efforts.

**To parallelise, split the node.** If two groups genuinely need to work on separate parts of one
node, split it into smaller nodes, open an issue for each, and sew them back together afterwards
with a bridge:

```yaml
justifications:
  - id: reassembled
    kind: bridged
    from:
      - Dusart_part1.v1.main
      - Dusart_part2.v1.main
    bridge: IEANTN/Bridges/Dusart/PartsToV3.lean
```

A bridge takes *several* conclusions to one, so this is expressible directly. Merging the parts
back into a single node afterwards is housekeeping, and can wait.

Bridges live under `IEANTN/Bridges/`, inside the library, so the core build compiles them. They
may not contain `sorry` and may not import a `Challenge`. See [docs/NODES.md](docs/NODES.md).

**Claim per node, not per conclusion.** Two people working on different conclusions of the same
node collide on its `formalization.yaml` and its generated challenge. Record the issue number on
the conclusion, so `python scripts/ieantn.py housekeeping` shows what is claimed and what is not.

## Generated files

`Challenge.lean`, `IEANTN/Nodes.lean`, `IEANTN/Bridges.lean`, `fingerprints.json`, `STATE.md`,
`GRAPH.md` and everything under `docs/nodes/` are generated *and* committed, and CI checks they are
current.

**If you hit a merge conflict in any of them, do not resolve it by hand.** Take either side, then
regenerate:

```bash
python scripts/ieantn.py gen-challenges
python scripts/ieantn.py fingerprint
python scripts/ieantn.py state
python scripts/ieantn.py graph
```

They are committed rather than gitignored on purpose: a change of *meaning* then shows up as a diff
line even when the Lean edit looks cosmetic, and the `STATE.md` diff says what your change did to
the network.

---

## 1. Start a solution for a node that has none

You want to begin proving an existing challenge.

**Do:**

```bash
python scripts/ieantn.py new-solution Lcm.v1
```

That scaffolds `Solutions/Lcm.v1/` as its own Lake project, with a `Solution.lean` declaring
exactly what the challenge states and a `comparator.json` naming those theorems. Prove what you
can.

**Metadata:** the justification does **not** change. Add a progress marker instead:

```yaml
    justifications:
      - id: unjustified
        kind: none-yet
    designated: unjustified
    progress:
      solution: Solutions/Lcm.v1/
      state: in-progress
      remaining_holes: 7
```

**Do not count the holes by hand.** Derive them:

```bash
python scripts/ieantn.py progress Lcm.v1           # report
python scripts/ieantn.py progress Lcm.v1 --write   # report and record
```

It builds the solution, re-elaborates it to find every `sorry` with a line number, and then runs
`#print axioms` on each compared theorem. That last step is the one that matters, and it is why
this does not simply search for the word: a declaration can contain no `sorry` and still not be
proved, because something it depends on has one. It is also what Comparator checks, so this is a
cheap preview of the verdict — without the sandbox, the second kernel, or a receipt, none of which
it substitutes for. A solution that reports every theorem proved is ready to verify and still
justifies nothing until it is.

(`justifications` is a list and `designated` names the one that counts — see
[docs/NODES.md](docs/NODES.md). A conclusion may carry several grounds; exactly one carries trust.)

**CI:** nothing runs. Solutions are outside the core build.

> **An incomplete solution is never a justification.** `justification` records what a claim *rests
> on*; `progress` records what someone is *doing*. They are orthogonal, and a partial proof with
> seven `sorry`s supports nothing. Conflating them would corrupt the one report the repository
> exists to produce.
>
> But a partial solution is not nothing either: it establishes *imports + remaining holes →
> conclusion*. It is a **justification-in-waiting whose missing pieces have not been named yet** —
> which is what workflow 6 is about.

For a port long enough to need planning, write a `progress.yaml` in the solution directory first
— what the upstream actually proves, how much comes along transitively, and how to split the
files. It is a best practice rather than a schema; see [docs/SOLUTIONS.md](docs/SOLUTIONS.md), with
`Solutions/FKS2.v1/progress.yaml` as the worked example.

## 2. Continue an incomplete solution

You closed some holes but not all.

**Do:** push the changes. **Metadata:** update `remaining_holes`; nothing else. **CI:** core checks
only.

This is the cheapest kind of PR in the repository and deliberately so — most work is of this shape.

If you want the solution typechecked, add the `build-solution` label and a dispatchable workflow
builds just that project *(planned)*. It is not in core CI because a solution can take an hour.

## 3. Complete a solution

All holes closed and you believe Comparator will accept it.

### The order, and why it is this order

1. **Push the branch and open the pull request.** Core CI triggers on `pull_request` and on pushes
   to `main` only — so until the PR exists, nothing runs on your branch at all.
2. **A maintainer dispatches the verification** for that branch:

   ```bash
   python scripts/ieantn.py verify Lcm.v1 --branch <your-branch>
   ```

   Prefer this over `gh workflow run verify.yml` directly, for three reasons. A run waiting at the
   approval gate looks exactly like one that is building — a spinner and a job name — and
   `ieantn.py verify` is the only thing that says so out loud. It also refuses to dispatch when
   `origin` has no such branch, suggesting near misses, because a dropped path prefix costs an
   approval and dies at checkout. And it refuses when the node's solution still has holes, since
   Comparator would reject it after an hour of compute. It cannot approve anything, and must not be
   able to.

   Both refusals are pre-flight only, and the second is skipped with `--skip-precheck` or when your
   local `HEAD` is not the tip of the branch being verified — in that case the local tree is not the
   code that will be checked, and the command says so rather than checking the wrong thing.
3. **Approve the `verification` environment.** The gate is on the *run*, not the request:
   verification is hour-scale compute, so it is not self-serve, but neither should asking for one
   require write access. Approving means vouching for the branch's *core* Lean, not its solution —
   the receipt job runs `lake build` on it while holding a write token.
4. **Wait.** Comparator, then the receipt job.
5. **Pull.** The receipt lands on *your branch* — see below — so your local copy is now behind.
6. **Merge**, once the CI run triggered by the receipt commit is green.

**Verify last.** A receipt records the statement fingerprint of its conclusion *and of every
conclusion it imports*. Move any of them afterwards, however slightly, and `ieantn.py status`
grades the receipt `BROKEN`: the verified implication no longer connects to what is now claimed.
Editing metadata, notes or the solution is fine; editing a *statement* throws the verification away.
So make the branch's statements final before step 2.

**Expect a commit you did not write.** The receipt job commits `receipts/`, `IEANTN/Nodes/`,
`STATE.md`, `GRAPH.md` and `docs/nodes/` as `ieantn-verifier[bot]`. It regenerates all three derived
files because designating a `lean-comparator` justification changes the node's evidence kind, and a
receipt whose own pull request failed CI would be self-defeating. Push without pulling first and you
will be rejected.

**A receipt never goes straight to `main`.** The job refuses if the branch being verified is the
default branch: the one file the network trusts most goes through review like anything else.

**A node is verified all at once, or not at all.** `record-receipt` refuses unless the solution's
`comparator.json` lists a challenge for *every* conclusion of the node — the guard that stops a
conclusion added to an already-verified node from inheriting its receipt. So a node with one open
hole cannot be verified at all, and trimming `comparator.json` to the finished ones does not help.
If part of a node is provable now and part waits on inputs that may be a long time coming, that is a
reason to split it across two versions, not to wait. See `docs/NODES.md` on versions as variants.

Comparator executes against the generated challenge; on success the workflow commits the receipt to
your branch and designates the `lean-comparator` justification.

**Before requesting one**, check locally what Comparator will check — that the challenge and
solution declare the same type and that only the three permitted axioms are used. Both are
checkable from inside the solution project without Comparator itself; [docs/NODES.md](docs/NODES.md)
step 4 gives the commands. A rejected run costs a maintainer's approval and an hour of compute.

**Do not write the receipt yourself, and do not set `kind: lean-comparator` by hand.**

> **Receipts must be written by the verifier, never by the author** — otherwise anyone can claim
> verification by typing it, and every downstream trust computation is decorative. Receipts
> therefore live under `receipts/`, not in `formalization.yaml`. `check-graph` refuses a
> `lean-comparator` justification with no matching receipt, warns when a receipt exists that nothing
> designates, and `check-receipts` requires every receipt to name a **successful run of the
> verification workflow in this repository** -- which is what anyone forging one would have to fake.
> *(planned: the `/verify` comment trigger.)*

On success the workflow also designates the verification, because a Lean-verified justification
rests on no citation, no external computation and no other version, and so is almost always what a
conclusion should point at. You can re-designate afterwards; that is an ordinary reviewed edit.

Check the result with `python scripts/ieantn.py status`, which grades each receipt `green`,
`yellow`, `orange` or `BROKEN`. `BROKEN` means a statement moved — the conclusion's own, or one it
imports — so the verified implication no longer connects to what is now claimed. That is not
staleness and it does not age gracefully; re-verify, or make a new version.

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

**CI:** editing a depended-on conclusion in place is a hard failure; making a new version is
always green. **Downstream nodes need no action** — they still import the old version.

Deprecate the old version when you want it retired:

```bash
python scripts/ieantn.py deprecate Lcm.v1 --for Lcm.v2
```

### Writing the bridge

Usually the cheapest of the three, and often only a few lines. Put it at
`IEANTN/Bridges/<Family>/<Name>.lean` — inside the library, so the core build compiles it — and
prove the target's conclusion from the source's:

```lean
theorem bridge_v2_to_v1
    (general : Lcm.v2.lcmUpto_not_highlyAbundant_of_primeGap)
    (dusart : Dusart2018.v1.proposition_5_4) :
    Lcm.v1.lcmUpto_not_highlyAbundant :=
  fun n hn =>
    general 11.4 89693 (by norm_num) lt_log_89693.le dusart n (by exact_mod_cast hn)
```

Its hypotheses are the conclusions you name in `from`, plus whatever the *target* node already
imports. Then record it, run `gen-challenges` so the generated `IEANTN/Bridges.lean` picks it up,
and `lake build` — a bridge is checked by the ordinary build, not by Comparator, because there is
no untrusted development in it.

```yaml
  - id: bridge-from-v2
    kind: bridged
    from: Lcm.v2.lcmUpto_not_highlyAbundant_of_primeGap
    bridge: IEANTN/Bridges/Lcm/V2ToV1.lean
```

`IEANTN/Bridges/Lcm/V2ToV1.lean` is the worked example. Rules: no `sorry`, no importing a
`Challenge`, and the same import closure as a Conclusions file — all checked by `check-closure`.

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

**Do:** promote each remaining hole to its own node — `node.kind: folklore` or `computation`, with
a designated justification of kind `asserted` or `none-yet` — add it to the stuck node's imports,
and the solution becomes complete relative to those new imports.

This is the main way the network grows, and it is why workflow 1 tracks `remaining_holes`: **the
holes in a stuck solution are a ready-made list of candidate nodes.** If the extracted fact serves
several papers, every one of them benefits at once.

Do the extraction with a new version of the stuck node (its imports are changing, so its challenge
changes) and CI stays green throughout.

## 7. Add examples to a node

Optional, cheap, and the best defence available against a conclusion that typechecks but claims
less than its docstring says.

**Do:** add `Examples.lean` to the node directory, deriving consequences *from* its conclusions:

```lean
example (h : Lcm.v1.lcmUpto_not_highlyAbundant) : ¬ HighlyAbundant (Nat.lcmUpto (10 ^ 10)) :=
  h (10 ^ 10) (by norm_num)
```

Take the conclusion as a **hypothesis**. That exhibits the statement's force without assuming it is
true, and it is exactly where a transcription error shows up: if the threshold had been stated over
`ℝ`, or the inequality the wrong way round, this would not elaborate.

**Two rules, both checked by `check-closure`:**

- an examples file may not import the node's `Challenge`, which is sorried — an example resting on
  that `sorry` proves anything while looking exactly like one that proves something;
- it may not contain `sorry` itself.

**CI:** examples are built by the core build, and the umbrella imports them automatically. They
make no claims of record, so they are not fingerprinted and never affect a receipt.

## 8. Add a new node

A paper the network does not cover yet, a pipeline abstracted from several, a piece of folklore, or
a large computation.

**Do:**

```bash
python scripts/ieantn.py new-node FKS2 --kind paper
```

That scaffolds `IEANTN/Nodes/FKS2/v1/` with a placeholder conclusion, a `formalization.yaml`
skeleton, a generated challenge, and the umbrella import. Then:

1. Write the real conclusions in `Conclusions.lean`, replacing `replace_me`.
2. Fill in `formalization.yaml` — sources, classification, justification — and change
   `node.status` away from `template`.
3. `python scripts/ieantn.py gen-challenges`
4. `python scripts/ieantn.py check`

**CI:** a node still marked `status: template` is a **hard failure**. The scaffold is deliberately
built so that `lake build` stays green — you can iterate locally — while `check-graph` refuses it,
so a half-finished node cannot be merged by accident.

`--kind` is one of `paper` (default), `pipeline`, `folklore`, `computation`.

Most new nodes start with a designated justification of kind `none-yet` or `literature`, and no
solution at all. That is
the normal, expected state: a node that merely *records* a result and its dependencies is already
useful to the network, and workflows 1–3 exist to justify it later.

## 9. Bump Mathlib

This gently degrades everything at once, and it is the case the two-axis trust model
(ARCHITECTURE §4) exists for: a bump changes the **environment**, not the **statements**. Every
receipt was made under an older Mathlib; no edge has broken. That is a yellow light, not a red one.

**Do:** update `lean-toolchain` and `lake-manifest.json` — and the same two files in **every**
`Solutions/<node>/`, because a solution's toolchain must equal the repository's and `check-closure`
fails otherwise. If the Lean *release* changed, also move `lean4export_commit` and
`lean4export_toolchain` in `scripts/verify-comparator.sh` to the matching tag; `check-pins` fails
the bump otherwise, deliberately, so that the pin is fixed while the reason is obvious rather than
weeks later when a verification breaks for no visible cause.

No node metadata changes.

**Metadata:** *nothing changes, in any node.* Staleness is **derived**, not stored — it is computed
by comparing each receipt's recorded environment against the current one. So a bump that degrades
two hundred nodes still touches exactly two files.

**CI:** two things must hold, and one is red if it fails:

- The core must build — Vocabulary, Conclusions and Challenges all compile under the new Mathlib.
- **Every statement fingerprint must be unchanged**, and normally it is — by construction, in
  fact. Fingerprints treat Mathlib constants as opaque names (see `Tools/Hash.lean`), so a bump
  that reorganises proofs or restates a lemma equivalently cannot move one. What *can* move one is
  a Mathlib rename that changes which constant a statement refers to; a rename that removes the old
  name is a build error instead.

  So this check is less a detector of Mathlib misbehaviour than a guard against the bump PR
  quietly carrying an unrelated edit. The case it cannot see is Mathlib changing what a definition
  *means* while keeping its name — that is stated plainly in `Tools/Hash.lean` and is not
  detectable at this price.

If both hold, every affected node simply moves one release further from its verification, and the
PR is green with warnings.

### How stale is too stale

Three levels, with the third defined by something real rather than a made-up number:

| | Meaning |
|---|---|
| **green** | Verified against the current Mathlib. |
| **yellow** | Stale, but within the Mathlib cache window — a refresh costs about one node-sized run. |
| **orange** | Past the cache window. Dependencies must now build from source, so a refresh costs many times the per-node budget. |

A solution's toolchain pin must **equal** the repository's, so a bump moves the solutions with it
— that is why the bump PR touches their `lean-toolchain` and `lake-manifest.json` too. What stays
cheap is re-running a verification *at the commit its receipt records*, where the core and the
solution agree by construction. What has aged is the *claim that the result holds under current
Mathlib*, not the proof.

(An earlier version of this file said solutions pin independently and so are unaffected. They do
not, and this is the rule the project has got wrong twice; the reasoning is in
[docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) §2.)

**Do not chase bumps.** Let staleness accumulate, and run refresh sweeps ordered by fan-in when
compute is available (`python scripts/ieantn.py housekeeping`). The one thing worth avoiding is
letting a node slide from yellow to orange, because that is where the cost jumps discontinuously.

## 10. Housekeeping

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

---

## The acknowledgement escape hatch

If `Network impact` fails and you need the change to land anyway, add `changes/<slug>.yaml`:

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
