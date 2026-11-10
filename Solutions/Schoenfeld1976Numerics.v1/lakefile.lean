import Lake
open Lake DSL

package solution_Schoenfeld1976Numerics_v1

require IEANTN from "../.."

@[default_target] lean_lib Solution where
  globs := #[.andSubmodules `Solution]

lean_lib RSBoundsCompat where
  globs := #[.submodules `RSBoundsCompat]

-- Proof/ and RSBoundsCompat/ are copied from Solutions/RosserSchoenfeld.v2 (pull request #208,
-- commit 98c7b280), plus six new files under Proof/RSBounds/; see README.md. The libraries are
-- outside the default core build and use the core Mathlib pin.
lean_lib RSBounds where
  srcDir := "Proof"
  globs := #[.submodules `RSBounds]

lean_lib TernaryGoldbach where
  srcDir := "Proof"
  globs := #[.submodules `TernaryGoldbach]
  leanOptions := #[⟨`linter.unusedSectionVars, false⟩]

lean_lib Zeta23 where
  srcDir := "Proof"
  globs := #[.submodules `Zeta23]
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`pp.unicode.fun, true⟩]

lean_lib ZetaLean where
  srcDir := "Proof"
  globs := #[.submodules `ZetaLean]

lean_lib RHHeight where
  srcDir := "Proof"
  globs := #[.submodules `RHHeight]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib RHHeight100 where
  srcDir := "Proof"
  globs := #[.submodules `RHHeight100]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

lean_lib HardyFirstZero where
  srcDir := "Proof"
  globs := #[.submodules `HardyFirstZero]

lean_lib HardyTenZeros where
  srcDir := "Proof"
  globs := #[.submodules `HardyTenZeros]
