/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Håkon Xue-Lønmo
-/
import Lean

/-! Resolve a private declaration from the pinned v1 proof port without copying its certificate
or modifying its module. This elaborator only returns a constant reference: the kernel still checks
its type and proof. The generator's provenance check pins every reused source file. -/
open Lean Elab Term in
elab "rs12_private% " mod:ident decl:ident : term => do
  let name := mkPrivateNameCore mod.getId decl.getId
  unless (← getEnv).contains name do
    throwError "Missing pinned RS12 declaration {name}"
  return mkConst name
