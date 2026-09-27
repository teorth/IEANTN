import Lake
open Lake DSL

package solution_RosserSchoenfeld1962_v2 where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Only the solution depends on LeanCert; use the validated v1 pin.
require leancert from git "https://github.com/alerad/leancert.git" @
  "6b11513512c9d27183fb4725bfc291ab38b4a6d7"
require IEANTN from "../.."

@[default_target]
lean_lib Solution where
  roots := #[`Solution]

lean_lib Max113 where
  globs := #[.submodules `Max113]

-- Reuse only the unchanged RS12 library, avoiding v1's conflicting Solution module.
-- Deriving the absolute sibling directory also preserves v1's source locations in caches.
lean_lib RS12 where
  srcDir := (__dir__).parent.get! / "RosserSchoenfeld1962.v1"
  roots := #[`RS12.Proof]
  globs := #[.submodules `RS12]
