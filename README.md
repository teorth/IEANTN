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
IEANTN/Vocabulary/          the shared language — definitions only, Mathlib-only
IEANTN/Nodes/<Id>/          Conclusions.lean, Challenge.lean, formalization.yaml
Solutions/<Id>/             proofs — separate Lake projects, not in the core build
docs/                       ARCHITECTURE.md, NODES.md
```

The core build is Vocabulary and Nodes only, and is deliberately fast. Solution verification is a
separate, dispatchable workflow: running Comparator on every pull request would take hours and
defeat the purpose of the split.

## Reading order

1. [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) — the design and why it is what it is.
2. [docs/NODES.md](docs/NODES.md) — how to author a node.
3. [CLAUDE.md](CLAUDE.md) — the short version, for coding agents.

## Status

Early. Vocabulary and two proof-of-concept nodes exist; challenge generation, verification
receipts, the graph tooling and the visualisation are not built yet. Sections marked *(planned)* in
the documentation are not implemented.

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

Two `declaration uses 'sorry'` warnings are expected — one per node conclusion. A challenge states;
it does not prove.
