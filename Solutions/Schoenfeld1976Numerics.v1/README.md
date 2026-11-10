# Schoenfeld 1976: the conditional psi bound at exp(23)

This solution proves

```lean
theorem Schoenfeld1976Numerics.v1.challenge_psi_error_b23
    (zetazerolocations_v1_located_0_1000 : ZetaZeroLocations.v1.located_0_1000)
    (zetazerolocations_v1_unique_0_1000 : ZetaZeroLocations.v1.unique_0_1000)
    (zetazerolocations_v1_count_0_1000 : ZetaZeroLocations.v1.count_0_1000) :
    Schoenfeld1976Numerics.v1.psi_error_b23
```

that is: if the zeros of zeta up to height 1000 are where `ZetaZeroLocations.v1` says, then
RH up to 1894438.5122 implies |psi(x) - x| < 0.00020171 x for x >= exp(23). This is the row
b = 23 of the table Schoenfeld recalculated in 1976 (Math. Comp. 30, table on p. 358).

## Method

The proof is the quartic-smoothing proof of the 1975 row in `Solutions/RosserSchoenfeld.v2`
(pull request #208), with one change: the explicit zeros are taken up to height 1000 (649 zeros)
instead of 100 (29 zeros). delta = 0.0000211, the eight cancellation subbands, the 0.931 factor
and the high-zero term are unchanged. The scalar budget, checked by the kernel in
`Proof/RSBounds/QuarticHead1000BudgetNumerics.lean`, is at most 0.00020152574343131 < 0.00020171.

## Files

* `Proof/`, `RSBoundsCompat/`, `RSBoundsCompat.lean`, `licenses/`, `upstream/`: copied unchanged
  from `Solutions/RosserSchoenfeld.v2` at commit 98c7b280283326ac12474b49970dabaa60b2ccb3 (pull
  request #208). Their origin, hashes and the 29 compatibility edits for this toolchain are
  recorded in that directory's `source-provenance.json` and `adaptations/`. Check the copy with
  `diff -r` against that commit: for `Proof/`, it reports only the six new files below.
* Six new files in `Proof/RSBounds/`, from the standalone RSBounds project (Lean 4.35.0, Mathlib
  56a00585), unchanged:
  * `Zeros0to1000Statement.lean`: the definitions of `challenge/Zeros0to1000.lean` in
    `Garald1/zeta-zero-locations` (theorems omitted);
  * `Head1000Data.lean`: kernel-checked facts about the 649 listed integers;
  * `Head1000Table.lean`: from the three `Zeros0to1000` statements, the certified table of the
    first 649 zeros, N(1000) = 649, and the head bound sum 1/|rho| <= 2.028658;
  * `QuarticHead1000BudgetNumerics.lean` (generated) and `QuarticHead1000Budget.lean`: the budget;
  * `PsiTable1976.lean`: the assembly, `psi_error_of_zeros0to1000`.
* `Solution/FiniteRH.lean`: copied from `Solutions/RosserSchoenfeld.v2`, only the namespace
  changed: IEANTN's `RiemannHypothesisUpTo` gives the RSBounds finite-RH predicate.
* `Solution/Zeros.lean`: the three `ZetaZeroLocations.v1` statements give those of
  `Zeros0to1000` (the two ordinate lists are equal by `rfl`; `zetaOrder s = 1` gives
  `analyticOrderAt riemannZeta s = 1` at s != 1).
* `Solution.lean`: the compared theorem.

The proof code is a copy rather than a dependency on `Solutions/RosserSchoenfeld.v2` because both
projects have a root module `Solution`, which a path dependency would make ambiguous.

## Checks made

On the core's Lean v4.34.0-rc2 and Mathlib 71a80585: `lake build` of this project completes;
the `pp.all` types of the compared theorem in the challenge and in the solution are identical; and
`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. The same six files built
unchanged on top of pull request #208's tree before they were copied here.

On Lean 4.35.0 (the RSBounds project), the same theorem, stated with the `Zeros0to1000`
definitions, passed an independent Comparator run with the bwrap sandbox on. That run is not an
IEANTN receipt.
