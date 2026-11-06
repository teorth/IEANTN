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
  source commit and recorded original/adapted hashes for all 254 modules.
  The three additional Mathlib compatibility modules have separate provenance
  and source hashes, also checked by `check_source_provenance.py`.
- All 352 Python unit tests passed with the declared Python dependencies installed.
- Generated-challenge freshness and authored-file whitespace checks passed.
  The exact vendored sources retain two upstream terminal blank lines; patch
  files retain the blank context lines of unified-diff syntax. A full staged
  `git diff --check` reports those preserved upstream formatting details.
- Installed the core's Lean 4.34.0-rc2 and fetched all 3707 Mathlib modules
  needed by the core's 24 direct Mathlib imports.
- The actual IEANTN Zeta vocabulary and the exact new conclusion compiled
  in the source Lean 4.35.0 environment. This is an auxiliary compatibility
  check, not a core-toolchain build or an official receipt.
- The current exact `Solution.lean` and `Solution/FiniteRH.lean` compiled on
  Lean 4.35.0 against the original proof objects and the actual copied IEANTN
  vocabulary/conclusion. Both transitive-axiom audits list only `propext`,
  `Classical.choice`, and `Quot.sound`. This checks the updated wrapper in
  the original environment, not the full ported dependency closure.
- The new core psi conclusion and generated challenge built successfully with
  the core's pinned Lean 4.34.0-rc2 and Mathlib. This checks the statement and
  challenge, not the separate solution; the challenge's `sorry` is intentional.
- The actual `Solution/FiniteRH.lean` and all three `RSBoundsCompat` modules
  compiled on Lean 4.34.0-rc2. All six exported helper/RH-bridge theorems passed
  transitive-axiom audits with exactly the same three standard axioms.
- Inspected direct Mathlib imports and scanned used declaration names against
  both pinned source trees. Added small conjugation, arctan, and Gamma helpers,
  two direct replacements by existing APIs, and the earlier import rename.
  This scan does not establish complete compatibility: signatures, tactics,
  visibility, and elaboration still require the full solution build.

A local core-toolchain `lake build ieantn_hash` attempt reached its 1800-second
runtime limit while compiling pre-existing IEANTN nodes. It reported no Lean
error before the timeout. The core build, fingerprint generation, and solution
manifest resolution were not completed by this attempt.

Still pending at this checkpoint:

- The full core build and generated statement fingerprints.
- Resolution and commitment of the solution's matching Lake manifest.
- Full solution compilation on the core's pinned toolchain and Mathlib.
- IEANTN's official Comparator workflow and its receipt.

The successful upstream Lean 4.35.0 psi replay is documented in README.md and
does not discharge these integration checks.
