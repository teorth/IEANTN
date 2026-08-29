/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN.Vocabulary.PrimeCounting
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.Numerics
import IEANTN.Vocabulary.PrimeGaps
import IEANTN.Vocabulary.Zeta

/-!
# IEANTN Vocabulary

The shared language in which every node states its conclusions.

Vocabulary contains **definitions only** — no theorems, no `sorry`, and nothing that depends on
anything outside Lean core and Mathlib.  Those three restrictions are what the rest of the
architecture rests on:

* **Definitions only.**  A theorem in Vocabulary would be an unattributed mathematical claim with
  no node to own it.  Every claim belongs to a node.
* **Mathlib-only closure.**  A node's `Challenge.lean` transitively imports Vocabulary, so if
  Vocabulary reached outside Mathlib no node could ever be spun off as a standalone Palomar
  submission.  Enforced by `scripts/check_closure.sh`.
* **Shared.**  Node `X` importing a conclusion of node `Y` refers to it *by name*.  For that
  reference to mean anything, both nodes must state their claims about the same `Eψ`, the same
  `π`, the same `ζ`.  Vocabulary is where that agreement lives.

The rule for what belongs here: **anything appearing in more than one node's conclusions.**
Something used by a single node starts in that node's own `Conclusions.lean` and is promoted here
when a second node needs it — promotion is a file move plus an import, and it changes no
statement.
-/
