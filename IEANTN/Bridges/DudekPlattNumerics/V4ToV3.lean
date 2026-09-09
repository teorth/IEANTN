/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors (AI-assisted)
-/
import IEANTN.Nodes.DudekPlattNumerics.v3.Conclusions
import IEANTN.Nodes.DudekPlattNumerics.v4.Conclusions

/-!
# Bridge: `DudekPlattNumerics.v4` to `.v3`

`.v4` restates `.v3`'s `pi_two_sided_footnote` verbatim (same `mainTerm`, same threshold `exp 9400`,
same constants `3010.333`/`3250.488`) under its own id so it can carry its own conditional Lean
solution rather than editing `.v3` in place — see `.v4`'s module docstring. Since the two statements
are the same formula spelled twice, the implication is immediate once both `mainTerm`s are unfolded.

This is the `C_new → C_old` direction: it lets a downstream node that currently imports
`DudekPlattNumerics.v3.pi_two_sided_footnote` (namely `DudekPlatt.v4`'s solution) discharge that
hypothesis from `.v4`'s conclusion instead, i.e. ultimately from the explicit literature premise
`MT.v2.corollary_1` rather than from a Python-checked certificate:

`DudekPlatt.v4.challenge_ramanujan_inequality_9401 crit
  (pi_two_sided_footnote_of_v4 (DudekPlattNumerics.v4.challenge_pi_two_sided_footnote mt))`

is a term of `DudekPlatt.v4.ramanujan_inequality_9401` given only `crit : DudekPlatt.v3.criterion`
and `mt : MT.v2.corollary_1` — no numerical certificate needed anywhere in that chain. This bridge
IS registered, as the non-designated alternate justification `bridge-from-v4` on
`DudekPlattNumerics.v3`'s own node: `.v3` keeps its certificate-based `numerical` justification as
the designated ground of record, and this bridge's entry there records that an independent,
literature-grounded route to the same statement is now also machine-checked — see `.v3`'s own
`formalization.yaml` for the exact registration.
-/

theorem DudekPlattNumerics.v4.pi_two_sided_footnote_of_v4
    (h : DudekPlattNumerics.v4.pi_two_sided_footnote) :
    DudekPlattNumerics.v3.pi_two_sided_footnote :=
  fun x hx => h x hx
