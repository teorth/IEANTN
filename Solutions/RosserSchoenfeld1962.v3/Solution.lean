/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Interval.Tail
import Interval.Finite
import Interval.Dyadic
import IEANTN.Nodes.RosserSchoenfeld1962.v3.Conclusions

/-- Rosser–Schoenfeld 1962, Corollary 3, equation (3.8), p. 69. -/
theorem RosserSchoenfeld1962.v3.challenge_equation_3_8 :
    RosserSchoenfeld1962.v3.equation_3_8 := by
  intro x hx
  by_cases h : x < 4096
  · exact RSInterval.finite x hx h
  · exact RSInterval.tail x (le_of_not_gt h)
