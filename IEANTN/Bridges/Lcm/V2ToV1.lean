/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import IEANTN.Nodes.Lcm.v1.Conclusions
import IEANTN.Nodes.Lcm.v2.Conclusions
import IEANTN.Nodes.Dusart2018.v1.Conclusions

/-!
# Bridge: `Lcm.v2` implies `Lcm.v1`

`Lcm.v2` states the argument with its threshold abstracted; `Lcm.v1` states the instance the source
paper does. This file proves that the second follows from the first, given the Dusart hypothesis
`v1` imports.

## Why this is a bridge and not an import

If `Lcm.v1` *imported* `Lcm.v2`, the two would be joined in the trust graph and neither could bridge
back — bidirectional bridges between versions would be import cycles, and migrating dependants from
one version to another needs exactly that. So a bridge is a relation *about* statements, recorded
as a justification, and deliberately outside the import graph. What keeps that sound is a separate
condition: chains of `bridged` justifications must terminate at a primitive one, which
`check-graph` enforces.

## Why it lives in the core build

A bridge carries trust, so it should not be a file that merely exists at a recorded path. This one
imports only Mathlib and conclusions files, contains no `sorry`, and is compiled by the ordinary
core build — so if it ever stops being a proof, `lake build` says so.

It is not Comparator-checked, and does not need to be: it proves an implication between two
statements of record, both of which are already fixed by their fingerprints. There is no untrusted
solution here to sandbox.
-/

namespace Lcm

open Real

/-- `11.4 < log 89693`, the side condition `Lcm.v2` imposes on its threshold.

True by a margin of about `0.004`, so it needs an argument rather than `norm_num`. The trick, taken
from the ported development, is to clear the decimal by raising to a power rather than to factorise
`89693`: since `11.4 = 57/5`, the claim is `89693⁵ > exp 57 = (exp 1)⁵⁷`, which `exp_one_lt_d9`
bounds and `norm_num` closes.

An earlier attempt to decompose `89693` into small primes stalled, because Mathlib carries `log 2`,
`log 3` and `log 5` to nine digits but not `log 7`, and no 5-smooth integer lies in the necessary
range. That route was unnecessary. -/
theorem lt_log_89693 : (11.4 : ℝ) < Real.log 89693 := by
  rw [show (11.4 : ℝ) = 57 / (5 : ℕ) by norm_num, div_lt_iff₀ (by norm_num), mul_comm,
    ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num

/-- **The bridge.**  `Lcm.v2`'s abstract form, together with the Dusart hypothesis that `Lcm.v1`
imports, gives `Lcm.v1`'s conclusion.

The whole content is instantiating `c := 11.4` and `X₀ := 89693`, discharging the side conditions,
and moving the threshold hypothesis from `ℕ` to `ℝ`. That it is this short is the point: `v1` is an
instance of `v2`, and the bridge exhibits the instantiation.

`11.4` is passed for `c` because that is the value `Lcm.v1`'s development uses, and `lt_log_89693`
is exactly the side condition it needs. `Lcm.v2` requires only `5 ≤ c`, so any value in `[5, 11.4]`
would do here; keeping `11.4` makes the bridge a faithful record of what the ported proof actually
establishes. -/
theorem bridge_v2_to_v1
    (general : Lcm.v2.lcmUpto_not_highlyAbundant_of_primeGap)
    (dusart : Dusart2018.v1.proposition_5_4) :
    Lcm.v1.lcmUpto_not_highlyAbundant :=
  fun n hn =>
    general 11.4 89693 (by norm_num) lt_log_89693.le dusart n (by exact_mod_cast hn)

end Lcm
