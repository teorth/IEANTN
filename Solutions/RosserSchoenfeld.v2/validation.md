# Integration checks

Target core commit: `466b41b28ecc224398cf53a99c5fe9618131398b`.

Completed on 2026-11-06:

- Generated the psi-only challenge with `ieantn.py gen-challenges`.
- The complete `ieantn.py check` command passed (the pending solution manifest,
  absent issue number, and derived views produce advisory warnings).
- `ieantn.py check-graph` passed. It warns that the new pending conclusion has
  no issue number yet; no issue or verification receipt has been fabricated.
- `ieantn.py check-closure` passed, initially with the expected warning that a
  newly scaffolded solution had no resolved manifest.
- Matched all copied RSBounds/certificate Git blobs against the pinned public
  source commit and recorded source hashes for all 254 modules.
- All 352 Python unit tests passed with the declared Python dependencies installed.
- Generated-challenge freshness and authored-file whitespace checks passed.
  The exact vendored sources retain two upstream terminal blank lines; the
  historical patch files retain blank context lines. A full staged
  `git diff --check` reports those preserved upstream formatting details.
- Installed the core's Lean 4.34.0-rc2 and fetched all 3707 Mathlib modules
  needed by the core's 24 direct Mathlib imports.
- The actual IEANTN Zeta vocabulary and the exact new conclusion compiled
  in the source Lean 4.35.0 environment. This is an auxiliary compatibility
  check, not a core-toolchain build or an official receipt.
- Inspected all direct Mathlib imports. One renamed module was identified and
  adapted: `Integrability.Log` to `Integrability.LogMeromorphic`.

Still pending at this checkpoint:

- Core compilation and generated statement fingerprints.
- Compilation of the RH vocabulary adapter.
- Full solution compilation on the core's pinned toolchain and Mathlib.
- IEANTN's official Comparator workflow and its receipt.

The successful upstream Lean 4.35.0 psi replay is documented in README.md and
does not discharge these integration checks.
