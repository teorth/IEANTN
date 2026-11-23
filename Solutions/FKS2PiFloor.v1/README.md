# FKS2 small-range π-error floor

A proof of the existing `FKS2Numerics.v1.table6_row2_floor`, isolated as
`FKS2PiFloor.v1` so verification of this floor cannot certify the numerical
node's other four conclusions. The original closed interval, constants,
normalization, and `margin 0` are unchanged.

## Argument

`Li x` means the offset integral `∫ t in 2..x, 1 / log t`, not principal-value
`li x`. The proof handles both signs of `π(x) - Li(x)`.

1. `IntegralBounds.lean` proves integrability, the derivative of Li, and
   endpoint-slope enclosures using the decreasing integrand `1 / log t`.
2. `Quadrature.lean` bounds Li at the integers through 29 by summing 27
   kernel-checked unit-integral certificates, each using 64 dyadic partitions.
   In particular, `11.6677 ≤ Li 29 ≤ 11.6963`.
3. `Envelopes.lean` compares derivatives of
   `P_k(x) = x / log x + k*x / (log x)^2` with `1 / log x`.
   `Anchors.lean` yields, for every `x ≥ 29`,
   `P_1(x) ≤ Li(x) ≤ P_(5/2)(x) - 3.3`.
4. `CertifiedCells.lean` proves 160 continuous signed-error inequalities.
   Below 29 they use the integral enclosures and endpoint slopes; above 29
   they use the analytic envelopes. They are whole-interval certificates,
   not samples or unchecked endpoint maxima.
5. `Counting.lean` uses kernel-computed exact prime counts on half-open
   arithmetic cells. `Floor.lean` exhausts 80 cells covering `[2.7, 404)`;
   every prime right endpoint belongs to the next cell. Certified bounds
   `2.7 ≤ exp 1` and `exp 6 < 404` include both requested endpoints.
6. `RowBound.lean` proves the exact normalization and quarter-power identities.
   `Solution.lean` exports the single compared theorem.

`CertificateKernel.lean` proves the finite subdivision combiner from LeanCert's
soundness theorems. `CoreExpressions.lean` clears positive denominators and
proves evaluator equality. Its scaled square roots are exact identities;
scaling avoids the pinned evaluator's coarse upper bound of 1 for small roots.

The external LeanCert sources are unchanged and pinned at
`9c4bde501499fb50ec22d08d072cb47019f9dbe5`. The solution uses the core's
`v4.34.0-rc2` toolchain and the committed manifest's core-identical Mathlib pin.
No dependency update is needed to build.

## Validation

From the repository root:

```sh
lake -d Solutions/FKS2PiFloor.v1 build
python3 scripts/ieantn.py progress FKS2PiFloor.v1
```

The default build includes `Audit.lean`: both endpoints, the prime jump at 11,
rejection of false quadrature bounds, rejection of an insufficient subdivision,
and an exact axiom guard permitting only `propext`, `Classical.choice`, and
`Quot.sound`. Every retained computation uses kernel verification; numerical
searches only proposed candidates. Neither `native_decide` nor an asserted
numerical conclusion is evidence for the theorem.

Comparator/NanoDa verification requires the maintainer-approved Linux workflow
and has not run locally. The node's designated justification remains `none-yet`;
the bridge back is deliberately undesignated and no receipt is supplied.
