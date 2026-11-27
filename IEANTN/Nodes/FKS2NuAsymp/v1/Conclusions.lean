/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Vecchi
-/
import IEANTN.Nodes.FKS2Numerics.v1.Conclusions

/-!
# Node `FKS2NuAsymp.v1`

Corrected bound and formal refutation for `FKS2Numerics.v1.nu_asymp_e30_le`, split out so a
Comparator receipt for this closed-form evaluation cannot certify the remaining conclusions of
`FKS2Numerics.v1`.

In Fiori, Kadiri and Swidinsky (*Sharper bounds for the error term in the prime number theorem*,
Res. Number Theory **9** (2023), Paper No. 63; arXiv:2206.12557), the proof of Corollary 14
applies Proposition 13 at `x₀ = e³⁰` with `Aψ = 121.096`, `B = 3/2`, `C = 2`, `R = 5.5666305`,
and BKLNW's `a₁ = 1 + 1.93378·10⁻⁸` and `a₂(30)`, and displays `ν_asymp(e³⁰) ≤ 6.3376·10⁻⁷`.

Evaluating the exact expression `FKS2Numerics.v1.nuAsympE30` gives
`6.3380932222…·10⁻⁷ > 6.3376·10⁻⁷`, so the printed inequality is false as stated. In the arXiv
LaTeX source (`New_Bounds_on_Pi-Revised-RNTB-May2023.tex`, commented-out earlier draft at lines
222–227 vs. final proof at lines 813–818), `6.3376·10⁻⁷` came from an earlier draft with
`Aψ = 121.1070` (where `ν_asymp(e³⁰) = 6.33751754…·10⁻⁷ ≤ 6.3376·10⁻⁷`) and was not recomputed
when `Aψ` was lowered to `121.096`.

Corollary 14 itself (`Aθ = 121.0961`) is unaffected:
`121.096 · (1 + 6.3381·10⁻⁷) = 121.09607675… < 121.0961`.
-/

namespace FKS2NuAsymp.v1

open IEANTN

/-- **Corrected multiplier bound behind FKS2's Corollary 14**:
`ν_asymp(e³⁰) ≤ 6.3381·10⁻⁷`.

The exact value is `6.3380932222…·10⁻⁷`, so `6.3381·10⁻⁷` is the tight 5-significant-digit
ceiling matching the precision of the paper's printed `6.3376·10⁻⁷`. It suffices for Corollary 14,
since `121.096 · (1 + 6.3381·10⁻⁷) < 121.0961`.

Imports nothing: `FKS2Numerics.v1.nuAsympE30` is a closed-form real definition. -/
def nu_asymp_e30_le : Prop :=
  FKS2Numerics.v1.nuAsympE30 ≤ margin 0 * 6.3381e-7

/-- **Refutation of the printed multiplier bound `FKS2Numerics.v1.nu_asymp_e30_le`**:
`¬ (nuAsympE30 ≤ margin 0 * 6.3376e-7)`, i.e., `nuAsympE30 > 6.3376·10⁻⁷`.

Formalizes the counterexample showing that the bound displayed in the proof of Corollary 14 of
FKS2 (`6.3376·10⁻⁷`) is strictly smaller than `FKS2Numerics.v1.nuAsympE30 = 6.3380932222…·10⁻⁷`.

Imports nothing: this is a direct lower-bound evaluation of a closed-form real definition. -/
def nu_asymp_e30_gt : Prop :=
  ¬ FKS2Numerics.v1.nu_asymp_e30_le

end FKS2NuAsymp.v1
