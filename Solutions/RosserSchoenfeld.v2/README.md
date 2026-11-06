# RS75: the conditional psi bound at exp(23)

This solution integrates the theorem

```lean
IEANTN.RiemannHypothesisUpTo 1894439 →
  ∀ x : ℝ, Real.exp 23 ≤ x → |Chebyshev.psi x - x| < 0.00020211 * x
```

Finite RH is an explicit hypothesis, including the upper height endpoint. This
does not establish RH through 1894439, an unconditional psi bound, or the 1976
coefficient 0.00020171. The existing `RosserSchoenfeld.v1` zero-free statements
are unchanged.

`Solution.lean` converts the network's right-half/nonnegative-height RH predicate
to the full-strip/absolute-height predicate of RSBounds, using conjugation and
reflection of xi. It then applies `RosserSchoenfeld1975.psi_error_b23`.

## Source and method

The mathematical source is Rosser–Schoenfeld, *Sharper bounds for the Chebyshev
functions theta(x) and psi(x)*, Math. Comp. 29 (1975), 243–269, Lemmas 7–9 and
Theorem 4, [DOI](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
The fourfold smoothing proof retains delta = 0.0000211, height 1894439,
threshold exp(23), and the final 1975 constant. Its numerical organization uses
29 certified zeros and eight cancellation subbands, rather than reproducing
the paper's 57-zero head computation. No quantitative zero-free region,
Büthe theorem, Ramaré estimate, or PNT bound is an additional premise.

The implementation is pinned to
[Garald1/PrimeNumberTheoremAnd, 087f4418](https://github.com/Garald1/PrimeNumberTheoremAnd/tree/087f4418a84516a34cddaa8883062abfd0fc7e4e/Projects/RSBounds),
with the 35 imported TernaryGoldbach modules pinned to
[calr3/ternary-goldbach, ce82a5b2](https://github.com/calr3/ternary-goldbach/tree/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0).
Only the 254-module source dependency closure of the psi theorem is included.
It contains 120 RSBounds modules, 35 TernaryGoldbach modules, and the 99-module
height-100 zero-certificate development. Proof code is isolated from the core
build under `Proof/`.

`source-provenance.json` records the source repository, exact commit, path,
Git-blob hash, SHA-256, and any integration changes for every module. All
RSBounds and certificate source blobs were matched against the pinned public
commit before copying. Original notices and the MIT/Apache licenses are retained
in `licenses/`; inherited zero-certificate provenance and seven earlier
adaptations are retained under `upstream/rh100/`. The original zero-certificate
manifest's historical verification status is preserved unchanged. Run
`python3 check_source_provenance.py` here to check the exact source inventory
and hashes; that check is separate from Lean proof verification.

## Verification boundary

The original Lean 4.35.0 / Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` theorem passed independent Comparator
statement/definition matching, an allowed-axiom check, and full replay with
Lean's default kernel. Only `propext`, `Classical.choice`, and `Quot.sound` were
permitted. The final replay took 3143.89 seconds. Evidence is in the pinned
[psi-resume-run.json](https://github.com/Garald1/PrimeNumberTheoremAnd/blob/087f4418a84516a34cddaa8883062abfd0fc7e4e/Projects/RSBounds/verification/psi-resume-run.json)
and
[psi-comparator-resume.log](https://github.com/Garald1/PrimeNumberTheoremAnd/blob/087f4418a84516a34cddaa8883062abfd0fc7e4e/Projects/RSBounds/verification/psi-comparator-resume.log).
Process sandboxing was disabled for the recorded bwrap limitation; this was
not a sandboxed attestation.

**That original replay is not an IEANTN receipt.** This integration targets the
core's Lean 4.34.0-rc2 and Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. The metadata deliberately remains
`none-yet` while compatibility and official verification are unfinished.
`validation.md` records the checks actually completed, separately from the
upstream proof's status. No author-written verification receipt is supplied.

The first source compatibility change is an import rename:
`Integrability.Log` becomes `Integrability.LogMeromorphic` at the core Mathlib
pin. Its patch and hashes are recorded. No mathematical statement is weakened.

## Reproduction and upstream verification

From the repository root:

```sh
lake exe cache get
lake build
python3 scripts/ieantn.py fingerprint
python3 scripts/ieantn.py check
python3 -m unittest discover -s tests
```

From this directory, resolve dependencies using the core's manifest, then run
`lake build`. Its toolchain and shared package revisions must equal the core.
The 99 numerical certificate modules may require a substantial fresh replay.

After opening the PR and completing the compatibility build, a maintainer runs

```sh
python3 scripts/ieantn.py verify RosserSchoenfeld.v2 --pr PR_NUMBER
```

and approves the verification environment. That workflow, rather than the
author, writes the official Comparator receipt. Ordinary core CI does not
perform this verification.
