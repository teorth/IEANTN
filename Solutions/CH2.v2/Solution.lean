/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Core

/-!
# Solution: `CH2.v2`

Chirre–Helfgott's Proposition 2.4, both halves.

The mathematics is `PrimeNumberTheoremAnd`'s, ported in `Core.lean` — its `CH2_part1.lean` up to
the "Extremal approximants" section, which is Propositions 2.3 and 2.4 with the machinery they rest
on. What remains here is a bridge: the node states the hypotheses grouped into three named
predicates and uses its own names for the two definitions, where the port carries them as a long
list of separate hypotheses over `S` and `I'`.

Both conclusions **import nothing** — every input arrives as a hypothesis — so this proof is their
whole justification, and the node can be verified without waiting on any numerical input.
-/

open Real MeasureTheory FourierTransform Complex

namespace CH2V2Sol

/-- The node's `partialSum` is the port's `S`. -/
lemma partialSum_eq (a : ℕ → ℝ) (σ x : ℝ) : CH2.v2.partialSum a σ x = CH2Sol.S a σ x := rfl

/-- The node's `truncExp` is the port's `I'`. -/
lemma truncExp_eq (lambda u : ℝ) : CH2.v2.truncExp lambda u = CH2Sol.I' lambda u := rfl

end CH2V2Sol

theorem CH2.v2.challenge_proposition_2_4_upper : CH2.v2.proposition_2_4_upper := by
  intro a T β σ G φ x hcoef hT hβ hσ hpole hband hmaj hx
  obtain ⟨ha_pos, ha_sum⟩ := hcoef
  obtain ⟨hG, hG'⟩ := hpole
  obtain ⟨hmes, hint, hcont, hsupp, hfour⟩ := hband
  exact CH2Sol.prop_2_4_plus ha_pos hT hβ hσ ha_sum hG hG' hmes hint hcont hsupp hfour hmaj x hx

theorem CH2.v2.challenge_proposition_2_4_lower : CH2.v2.proposition_2_4_lower := by
  intro a T β σ G φ x hcoef hT hβ hσ hpole hband hmin hx
  obtain ⟨ha_pos, ha_sum⟩ := hcoef
  obtain ⟨hG, hG'⟩ := hpole
  obtain ⟨hmes, hint, hcont, hsupp, hfour⟩ := hband
  exact CH2Sol.prop_2_4_minus ha_pos hT hβ hσ ha_sum hG hG' hmes hint hcont hsupp hfour hmin hx
