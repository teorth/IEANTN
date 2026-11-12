# Step 1 dependency audit

Audit input: the edited #187 worktree, before this extraction.
`dependency-audit-before.json` records the exact import edges and 46 v1 modules.

| Category | Previous paths and references | Local replacement |
| --- | --- | --- |
| Global (3.35) | Already absent: no `RS12.Proof` or `RS_prime.theorem_12`. Both `Solution` declarations → `ratio_*` → `psi_*maximum` → `tail_strict hψ`. | Preserve the generated hypothesis; `hψ (x/60)` is the only global bound used. |
| Witnesses | `Finite → Data19 → … → Data00 → RS12.PsiData00..19`; 1,998 `rs12_private% … psi_check_*` references. | Pinned integer hints and endpoints; local `check_* := by decide +kernel` declarations in the existing adapters. |
| Checker soundness | `Shifted/SmallChecker → PsiWitness → PsiInteger → KernelLogs`; private `hintUnits` and `vonMangoldt_le_factorUnits`. | `Witness` extracts these as local declarations; `Shifted` retains its stronger invariant. |
| Recurrence | `Proof → PsiRecurrence → FactorialData → FactorialData00..11 → FixedCheck → Period → Weights/Factorial → Chebyshev`; also `FactorialUpper → Constants → FactorialBound/KernelLogs`. | Required support under `Max113.Recurrence`, with local floor certificate checks and six local logarithm bounds. |
| Numerical logs | `Lower → KernelLogs → LeanCert.Core.IntervalRat.Taylor`; `mem_logPointComputable` and `logPointComputable`. | Mathlib exponential Taylor bounds and `log_two_gt_d9`; no LeanCert imports. |
| Incidental | `PsiData00 → PsiFiniteBase`; unused `checkPsiBlock`, unshifted witness soundness/join, `T_small_error`, list floor checker; private-name elaborator. | Omitted. The existing small checker supplies its own seed. |

The retained recurrence is a separate certificate calculation, not a consequence of
(3.35). It checks the entire period 360360 and proves kernel weight ≥1 on [1,60)
and ≥0 elsewhere. This yields ψ(x) ≤ 1.021x + ψ(x/60) for x≥500000.
The finite handoff, strict separator 1.03882, and floor-x=113 case are unchanged.

## Validation results (2026-11-12)

PASS in `/tmp/pr187-isolated-d8h9p8eh`. The source snapshot contains only the v2
solution, with fresh core and solution output directories. No sibling v1 solution
or old solution artifacts were copied. Only Mathlib and its package caches were
shared. All 51 supplied Lean source files match the edited worktree byte for byte.

* All 1,998 witness checks (twenty shards), the twelve floor shards covering period
  360360, and the small-range certificate compiled with local kernel proofs.
* `lake build` completed successfully (3542 jobs, including cached Mathlib jobs).
* Both compared `pp.all` types exactly match their regenerated challenges.
* Both axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`.
* The actual loaded module closure contains zero `RS12.*` and zero `LeanCert.*`
  modules. The v1 core Conclusions module remains, as required.
* The isolated `LEAN_PATH` contains only nine cached Mathlib packages, the fresh
  temporary core/solution outputs, and Lean's standard library. A direct import of
  `RS12.PsiWitness` fails with unknown module prefix `RS12`.
* The generated challenge check passes. Recomputing the two v2 fingerprints with
  the unchanged structural algorithm from `Tools/Hash.lean`, restricted to v2
  imports, matches both recorded hashes. Conclusions and fingerprints also remain
  byte-identical to the branch HEAD.
* Local provenance, generated-adapter and dependency checks pass.

The retained temporary environment contains the fresh compiled artifacts. Logs and
all type/axiom/import outputs are also preserved under the working solution's
`.lake/step1-isolated-validation/`. These are local build logs, not Comparator
receipts. No certificate computation or dependency-removal blocker remains.

Fingerprint values:

* maximum: `ee95631b0283fe17bca77f8f7d14132efb0f03f108f5f4d30a1bc5e0feb3fa9f`
* uniqueness: `4d4cb4ce3f98ba42e13f47a5113a04839afd6480aaea6280bac55a1ad6e117ac`
