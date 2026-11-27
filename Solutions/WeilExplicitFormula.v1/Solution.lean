/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andres Helfgott
-/
import IEANTN.Nodes.ContourIntegration.v1.Conclusions
import IEANTN.Nodes.WeilExplicitFormula.v1.Conclusions
import IEANTN.Nodes.ZetaGoodHeights.v1.Conclusions
import WeilExplicitFormula.NumberTheory.WeilExplicitFormula.ExplicitFormula

/-!
# Solution: `WeilExplicitFormula.v1`

Proves the same declarations `Challenge.lean` states. Do **not** import the challenge module --
Comparator compares two modules declaring the same names, so importing it would collide.

This file may import anything. It is not part of the core build, and it is verified once and then
left alone; readability is not a goal here.

Replace each `sorry` below. While any remain, record progress in the node's `formalization.yaml`
under `progress`, and leave the justification alone -- an incomplete solution justifies nothing.
-/

theorem WeilExplicitFormula.v1.challenge_theorem_12_13
    (contourintegration_v1_residue_theorem_rectangle : ContourIntegration.v1.residue_theorem_rectangle)
    (zetagoodheights_v1_theorem_10_13 : ZetaGoodHeights.v1.theorem_10_13)
    (zetagoodheights_v1_lemma_12_2 : ZetaGoodHeights.v1.lemma_12_2) :
    WeilExplicitFormula.v1.theorem_12_13 :=
  -- The library states the conclusion and the three imports verbatim.
  WeilExplicitFormula.theorem_12_13_of zetagoodheights_v1_theorem_10_13
    zetagoodheights_v1_lemma_12_2 contourintegration_v1_residue_theorem_rectangle
