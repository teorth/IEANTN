/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andres Helfgott
-/
import IEANTN.Nodes.ContourIntegration.v1.Conclusions
import ResidueRectangle

/-!
# Solution: `ContourIntegration.v1`

Proves the same declarations `Challenge.lean` states. Do **not** import the challenge module --
Comparator compares two modules declaring the same names, so importing it would collide.

This file may import anything. It is not part of the core build, and it is verified once and then
left alone; readability is not a goal here.

Replace each `sorry` below. While any remain, record progress in the node's `formalization.yaml`
under `progress`, and leave the justification alone -- an incomplete solution justifies nothing.
-/

theorem ContourIntegration.v1.challenge_residue_theorem_rectangle :
    ContourIntegration.v1.residue_theorem_rectangle :=
  ResidueRectangle.residue_theorem_rectangle
