/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Doolan
-/
import IEANTN.Nodes.TruncatedPerron.v1.Conclusions
import PerronDev
import PerronGeneral
import PerronPsi

/-!
# Solution: `TruncatedPerron.v1`

Proves the same declarations `Challenge.lean` states. The challenge module is deliberately not
imported: Comparator compares two modules declaring the same names, so importing it would collide.

`perron_single_term` is proved, from `TruncPerron.perron_single` in `PerronDev.lean`. The bridge
only unfolds `perronT y c T = (1/(2πi)) · i · ∫_{-T}^{T} y^(c+it)/(c+it) dt` and cancels the `i`.

`perron_general` is proved term by term from `perron_single_term`, in `PerronGeneral.lean`
(`TruncPerronGeneral.perron_general_of_single`).

`perron_psi` is proved from `perron_general` with `aₙ = Λ(n)`, `σ₀ = 1 + 1/log x` and `C = 400`,
in `PerronPsi.lean` (`TruncPerronPsi.perron_psi_of_general`).
-/

open Complex Real

theorem TruncatedPerron.v1.challenge_perron_single_term :
    TruncatedPerron.v1.perron_single_term := by
  intro y c T hy0 hy1 hc hT
  have h := TruncPerron.perron_single hy0 hy1 hc hT
  have e : TruncPerron.perronT y c T =
      (1 / (2 * π) : ℂ) * (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
    simp only [TruncPerron.perronT, TruncPerron.VIntegral, TruncPerron.F]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
    field_simp
  rwa [e] at h

theorem TruncatedPerron.v1.challenge_perron_general : TruncatedPerron.v1.perron_general :=
  TruncPerronGeneral.perron_general_of_single TruncatedPerron.v1.challenge_perron_single_term

theorem TruncatedPerron.v1.challenge_perron_psi : TruncatedPerron.v1.perron_psi :=
  TruncPerronPsi.perron_psi_of_general TruncatedPerron.v1.challenge_perron_general
