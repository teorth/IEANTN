/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akula, PNT+ contributors
-/
import IEANTN.Nodes.RosserSchoenfeld1962.v1.Conclusions
import RS12.Proof

/-! The Comparator-facing adapter to the proof ported from PNT+ at 81eca5a. -/

theorem RosserSchoenfeld1962.v1.challenge_equation_3_35 : RosserSchoenfeld1962.v1.equation_3_35 :=
  fun _ hx => RS_prime.theorem_12 hx
