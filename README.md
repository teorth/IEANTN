# IEANTN

The **Integrated Explicit Analytic Number Theory Network**: a graph of claims about explicit
analytic number theory, together with a record of how well each one is justified.

Explicit analytic number theory is a field of long dependency chains. A bound on `π(x)` rests on a
bound on `ψ(x)`, which rests on a zero-free region, which rests on a numerical verification of the
Riemann hypothesis to some height — and in the published literature those dependencies are recorded
only in prose, if at all. Some links are fully rigorous, some rest on very large computations, and
some rest on claims a paper states without proof.

This repository records that structure explicitly. Each **node** makes a mathematical claim,
declares what it assumes, and carries evidence for the step from its assumptions to its claim. The
evidence may be a Lean proof checked by [Comparator](https://github.com/leanprover/comparator), a
numerical computation, or a citation. The goal is not that everything is certain — it is that **for
any result you can read off exactly what it rests on and how good that evidence is.**

## The central idea

Every node's challenge is a **conditional theorem**: *if* the results it imports hold, *then* its
own conclusions hold. Whether the node itself is justified is **metadata, not Lean**.

So a node backed by a one-line citation and a node backed by a 200,000-line machine-generated proof
have the same shape, and nodes import each other's *statements*, never each other's *proofs*. The
Lean layer certifies only the **edges** of the graph; the standing of the graph as a whole is a
separate, auditable question.

## Layout

```
IEANTN/Vocabulary/               the shared language — definitions only, Mathlib-only
IEANTN/Nodes/<Family>/<version>/ Conclusions.lean, Challenge.lean, formalization.yaml
IEANTN/Bridges/<Family>/         proofs that one version's conclusions imply another's
Solutions/<Family>.<version>/    proofs — separate Lake projects, not in the core build
receipts/                        one JSON file per Lean-verified conclusion
fingerprints.json, STATE.md      generated and committed, so a change of meaning is a diff line
docs/                            ARCHITECTURE.md, NODES.md, ROADMAP.md
```

The core build is Vocabulary and Nodes only, and is deliberately fast. Solution verification is a
separate, dispatchable workflow: running Comparator on every pull request would take hours and
defeat the purpose of the split.

## Reading order

0. [GRAPH.md](GRAPH.md) — **the network itself**: what it contains, what each result rests
   on, and what is taken on trust. Generated, and the place to start if you only want to
   see the thing.
1. [CONTRIBUTING.md](CONTRIBUTING.md) — the ten things people actually do, and how.
2. [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) — the design and why it is what it is.
3. [docs/NODES.md](docs/NODES.md) — node file formats, in detail.
4. [CLAUDE.md](CLAUDE.md) — the short version, for coding agents.
5. [docs/ROADMAP.md](docs/ROADMAP.md) — what is deliberately not built yet, and why.
6. [SECURITY.md](SECURITY.md) — the trust model, and what a forged receipt would take.

## Status

Early, but the machinery is in place and exercised. Vocabulary, three proof-of-concept node
versions and the bridge between two of them, challenge generation, statement fingerprints,
verification receipts, the breaking-change detector, the network checks and the housekeeping queue
all exist and run in CI.

**The Comparator path works end to end**: `Lcm.v1` carries a receipt written by the verification
workflow, and `ieantn.py status` grades it against the current environment.

Outstanding: visualisation, the `/verify` comment trigger, and the composing half of the
Palomar spin-off generator. [docs/ROADMAP.md](docs/ROADMAP.md) tracks what is deliberately not built
and why; [SECURITY.md](SECURITY.md) states the trust model.

This work grows out of the IEANTN subproject of
[PNT+](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), whose blueprint-based structure
it is intended to replace; discussion is on the
[`#PrimeNumberTheorem+`](https://leanprover.zulipchat.com/#narrow/channel/423402-PrimeNumberTheorem.2B)
Zulip channel.

## Building

```bash
lake exe cache get
lake build
```

One `declaration uses 'sorry'` warning per node conclusion is expected. A challenge states; it does
not prove.
