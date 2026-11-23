/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Lake
open Lake DSL

package solution_RosserSchoenfeld1962_v3 where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Local logarithm certificates need LeanCert; retain the validated pin.
require leancert from git "https://github.com/alerad/leancert.git" @
  "6b11513512c9d27183fb4725bfc291ab38b4a6d7"
require IEANTN from "../.."

@[default_target]
lean_lib Solution where
  roots := #[`Solution]

lean_lib Interval where
  globs := #[.submodules `Interval]
