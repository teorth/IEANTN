/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo, PNT+ contributors
-/
import Lake
open Lake DSL

package solution_RosserSchoenfeld1962_v2 where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require IEANTN from "../.."

@[default_target]
lean_lib Solution where
  roots := #[`Solution]

lean_lib Max113 where
  globs := #[.submodules `Max113]
