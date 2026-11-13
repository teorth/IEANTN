/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions

/-!
# Examples: `FKS2Numerics.v1`

Each example instantiates a closed endpoint the docstring names, so a missing or reversed
interval would fail to elaborate. The mid-range statements are not exercised at `e^20000`:
that endpoint is transcendental and is not decided here.
-/

namespace FKS2Numerics.v1

open IEANTN

example (h : table6_row2_floor) :
    Eπ (Real.exp 1) ≤ margin 0 * admissibleBound 0.826 0.25 1 5.5666305 (Real.exp 1) :=
  h (Real.exp 1) ⟨le_rfl, (Real.exp_strictMono (by norm_num : (1 : ℝ) < 6)).le⟩

example (h : theta_asymp_ge_one_below_e30) :
    1 ≤ margin 0 * admissibleBound 121.0961 (3 / 2) 2 5.5666305 2 :=
  h 2 ⟨le_rfl, le_trans (by norm_num : (2 : ℝ) ≤ 1 + 30) (Real.add_one_le_exp 30)⟩

example (h : nu_asymp_e30_le) : nuAsympE30 ≤ margin 0 * 6.3376e-7 :=
  h

end FKS2Numerics.v1
