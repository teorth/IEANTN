# IEANTN — orientation for coding agents

This repository is a **graph of claims about explicit analytic number theory, together with a
record of how well each one is justified.** It is not a single formalization project with one
build.

**Read [CONTRIBUTING.md](CONTRIBUTING.md) first — it covers the nine common kinds of change and
which one you are making. Then [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) before changing
anything structural, and [docs/NODES.md](docs/NODES.md) for node file formats.** They are short. Most mistakes in
this repository come from treating it as an ordinary Lean project.

## The one idea to hold on to

Every node's challenge is a **conditional theorem**: *if* the results it imports hold, *then* its
own conclusions hold. Whether the node itself is justified — by a Lean proof, a numerical
computation, or a citation — is **metadata, not Lean**.

So a node backed by a citation and a node backed by a 200,000-line solution have the same shape.
Nodes import each other's *statements*, never each other's *proofs*.

## Layers, and what may import what

| Layer | May import |
|---|---|
| `IEANTN/Vocabulary/` | Mathlib only. **Definitions only — no theorems, no `sorry`.** |
| `IEANTN/Nodes/<Family>/<version>/Conclusions.lean` | Mathlib, Vocabulary, other nodes' `Conclusions.lean` |
| `IEANTN/Nodes/<Family>/<version>/Challenge.lean` | its own and imported `Conclusions.lean` — **generated, do not hand-edit** |
| `Solutions/<Family>.<version>/` | anything. Separate Lake project, own toolchain pin. **Not in the core build.** |

The Mathlib-only closure of Vocabulary and Conclusions is load-bearing, not stylistic: it is what
lets any node be spun off as a standalone Palomar submission. An import that reaches outside it
breaks the architecture silently and CI will reject it.

## Hard rules

- **Conclusions are `def _ : Prop`, never `structure`.** Data-carrying structures go in Vocabulary.
- **A `sorry` in a `Challenge.lean` is correct and permanent.** A challenge states; it does not
  prove. Never "fix" one.
- **Never weaken a statement to make a proof work.** The source paper is ground truth. If the
  stated bound is wrong, say so — do not quietly adjust it.
- **Watch junk values.** `tsum` of a non-summable family is `0`; `Real.rpow` of a negative base is
  junk; `li` outside its domain is `Classical.choice`. A statement can typecheck and be *vacuous*
  rather than false. Vocabulary docstrings flag the specific traps — read them.
- **Do not add a theorem to Vocabulary.** Every claim belongs to a node.
- **Never edit a conclusion that anything depends on.** Make a new version instead:
  `python scripts/ieantn.py new-version <Family>`. See NODES.md.

## Build

```bash
lake build                              # Vocabulary + Conclusions + Challenges. Fast. Keep it so.
lake build IEANTN.Vocabulary.PrimeGaps  # a single module while iterating
python scripts/ieantn.py check          # every network invariant
python scripts/ieantn.py report         # what each conclusion rests on
python scripts/ieantn.py status         # green / yellow / orange / BROKEN per conclusion
python scripts/ieantn.py diff           # what your branch degrades, and for whom
python scripts/ieantn.py housekeeping   # the derived task queue
```

`Challenge.lean` files are generated: after editing a `Conclusions.lean` or a
`formalization.yaml`, run `python scripts/ieantn.py gen-challenges`.

Core CI does **not** run Comparator — that is deliberate. Solution verification is a separate
dispatchable workflow. Comparator does not run on Windows or macOS; WSL2 works (Landlock ABI 3 and
`systemd-run` are present) but the clone must live inside the WSL filesystem, not under `/mnt/c`.

## Style

Mathlib conventions apply to Vocabulary and Conclusions — these are the files humans read, and the
`mathlibStandardSet` linter is on. Solutions are exempt: they are machine-generated, verified once,
and never read.

Every file needs the four-line copyright header, including an `Authors:` line, or the header linter
fails the build.
