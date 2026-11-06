/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Lake
open Lake DSL

package solution_RosserSchoenfeld1962_v4 where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Only the solution depends on LeanCert; use the validated v1 pin.
require leancert from git "https://github.com/alerad/leancert.git" @
  "6b11513512c9d27183fb4725bfc291ab38b4a6d7"
require IEANTN from "../.."

@[default_target]
lean_lib Solution where
  roots := #[`Solution]

lean_lib Port where
  globs := #[.submodules `Port]

-- Reuse only the unchanged RS12 library, avoiding v1's conflicting Solution module.
-- Deriving the absolute sibling directory also preserves v1's source locations in caches.
lean_lib RS12 where
  srcDir := (__dir__).parent.get! / "RosserSchoenfeld1962.v1"
  roots := #[`RS12.Proof]
  globs := #[.submodules `RS12]
