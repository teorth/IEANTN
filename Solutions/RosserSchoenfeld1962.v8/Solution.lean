/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Wright
-/
import IEANTN.Nodes.RosserSchoenfeld1962.v8.Conclusions
import RSPrimeRecip

/-! The Comparator-facing adapter to the elementary proof in `RSPrimeRecip.lean`. -/

theorem RosserSchoenfeld1962.v8.challenge_equation_3_19 : RosserSchoenfeld1962.v8.equation_3_19 :=
  fun x hx => RSPrimeRecip.sum_inv_prime_gt_loglog x hx
