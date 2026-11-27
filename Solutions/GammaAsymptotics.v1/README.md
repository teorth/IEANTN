# Uniform digamma estimate

This solution proves the unchanged `GammaAsymptotics.v1.digamma_sub_log_isBigO`:

```lean
∃ C : ℝ, ∀ w : ℂ, 1 ≤ w.re →
  ‖Complex.digamma w - Complex.log w‖ ≤ C / ‖w‖
```

`Uniform.lean` proves the explicit bound with `C = 4`. This is a formalization of a classical
estimate, not a claim of new mathematics. It includes the boundary `Re w = 1` at arbitrary height.

## Argument

Write `E(w) = digamma w - log w`.

1. On the horizontal segment from `w` to `w + 1`, the derivative of
   `log(w + t) - t/w` is `1/(w + t) - 1/w`. Its norm is at most `1/‖w‖²`, since moving right in
   the right half-plane cannot decrease the norm. The mean-value inequality therefore gives
   `‖log(w + 1) - log w - 1/w‖ ≤ 1/‖w‖²`, without any logarithmic branch-product identity.
2. The digamma recurrence identifies this increment with `E(w) - E(w + 1)`.
3. If `r = ‖w‖ ≥ 1`, then `‖w + n‖² ≥ (r + n)²/2`, so the increment is bounded by
   `4/((n + r)(n + r + 1))`. This positive series telescopes to `4/r`.
4. For each fixed `w`, the existing strip estimate gives `E(w + n) → 0`. Its height-dependent
   constant disappears in this limit. Telescoping the increments now bounds `‖E(w)‖` by `4/r`.

## Reuse and dependencies

The strip estimate, Gauss-series development, and reciprocal comparison series are Terence Tao's
existing proof in `Solutions/GammaAsymptotics.v2`. The `GammaStrip` Lake library compiles those
sources directly from the sibling directory; they are neither copied nor modified. Its roots
exclude v2's `Solution` module, avoiding a module-name collision with this solution.

No challenge is imported. No v2 conclusion is assumed as a hypothesis: the existing proof sources
are checked as part of this solution. There are no new external dependencies; all git revisions
match the core manifest, and the Lean toolchain is identical to the core's.

## Local checks

From the repository root:

```sh
lake -d Solutions/GammaAsymptotics.v1 exe cache get
lake -d Solutions/GammaAsymptotics.v1 build
python3 scripts/ieantn.py progress GammaAsymptotics.v1
python3 scripts/ieantn.py check
python3 scripts/ieantn.py gen-challenges --check
```

The default solution build includes `Audit.lean`: an arbitrary-height boundary example and a
`#guard_msgs` axiom check requiring exactly `propext`, `Classical.choice`, and `Quot.sound` on the
compared theorem. The axiom regression was also checked to reject a temporary incomplete proof
in `Uniform.lean`, with the completed proof restored afterwards.

A successful local build is **not** a verification receipt. Comparator, including NanoDa, still
requires the repository's Linux verification workflow and maintainer approval. The node remains
designated `none-yet` until that workflow records a receipt.
