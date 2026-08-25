/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN
import Lean

/-!
# Spin-off support: locating the definitions a conclusion rests on

Emits, for one or more named conclusions, every IEANTN-local constant they transitively mention, in
dependency order, with the exact source range of each. `scripts/ieantn.py spinoff` slices those
ranges out of the source files and assembles a self-contained Challenge.

## Why this exists

A Palomar Challenge's transitive import closure must be Lean core and Mathlib only -- it may not
import the submitter's own library. IEANTN's conclusions do import one: `IEANTN.Vocabulary`, and
sometimes another node's `Conclusions`. Spinning a node off therefore means **inlining** those
definitions into the Challenge, which is the operation `docs/ARCHITECTURE.md` section 7 calls
generating a self-contained challenge "by substitution", and the reason Vocabulary is held to a
Mathlib-only closure in the first place.

## Why source ranges rather than pretty-printing

Pretty-printing the elaborated definitions is the obvious approach and was tried first. It produces
correct but unreadable output -- `LE.le 5 c` for `5 ≤ c`, `Exists fun p ↦ …` for `∃ p, …` -- because
a standalone executable's environment has none of the notation delaborators registered, and the
usual remedies (`pp.notation`, `enableInitializersExecution`) do not bring them back. The output is
*correct* either way, which is exactly what makes that failure easy to ship by accident.

The Challenge is the small file a mathematical reader audits. A Challenge nobody can read has
failed at its job even if Comparator accepts it. So the text comes from the source files, which
were written to be read, docstrings and all.

## The namespace problem, and how the selection range solves it

Sliced source cannot simply be concatenated: a definition's body refers to its neighbours by
whatever short name was in scope where it was written -- `HighlyAbundant`, not
`Lcm.v2.HighlyAbundant` -- and those names stop resolving once the surrounding `namespace` is gone.

Rather than reconstruct namespaces by parsing Lean, ask Lean. `findDeclarationRanges?` gives two
spans: `range` covers the whole declaration *including its docstring*, and `selectionRange` covers
just the declared name as written. Slicing the second gives the source-level name, and the
namespace is the full name with that suffix removed. The generator re-emits each declaration inside
its own `namespace`, so every short name resolves exactly as it did originally.

## What is not assumed

That the slicing is faithful. `ieantn.py spinoff` compiles the Challenge it assembles, so a
mis-sliced declaration fails there rather than silently producing a Challenge that states something
other than the node does.
-/

open Lean

namespace IEANTN.Spinoff

/-- Is this constant defined by this project rather than by Lean core or Mathlib?

Decided by module provenance, as in `Tools/Hash.lean`. Unknown provenance counts as local for the
same reason it does there: over-including a definition costs a few lines in the Challenge, while
under-including one produces a Challenge that does not compile. -/
def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => (`IEANTN).isPrefixOf m
  | none => true

/-- Elaboration artifacts, which must not be inlined: they are proofs, not statements. -/
def isArtifact (n : Name) : Bool :=
  n.hasMacroScopes ||
    match n.components.getLast? with
    | some c => c.toString.startsWith "_proof_" || c.toString.startsWith "_example"
    | none => false

/-- Every constant a term mentions. -/
partial def constantsIn (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => if isArtifact n then acc else acc.insert n
  | .app f a => constantsIn a (constantsIn f acc)
  | .lam _ t b _ => constantsIn b (constantsIn t acc)
  | .forallE _ t b _ => constantsIn b (constantsIn t acc)
  | .letE _ t v b _ => constantsIn b (constantsIn v (constantsIn t acc))
  | .mdata _ e => constantsIn e acc
  | .proj _ _ e => constantsIn e acc
  | _ => acc

/-- The local constants `n` rests on, in dependency order, `n` itself last.

A post-order walk, so a definition always appears after everything it mentions. Names are visited
in sorted order at each step, which is what keeps the output stable between runs -- a generator
whose output reshuffles cannot be reviewed by diffing. -/
partial def collect (env : Environment) (n : Name) (seen : NameSet) (out : Array Name) :
    NameSet × Array Name :=
  if seen.contains n then (seen, out)
  else
    let seen := seen.insert n
    match env.find? n with
    | none => (seen, out)
    | some info =>
      let deps := match info with
        | .defnInfo d => constantsIn d.value (constantsIn d.type)
        | other => constantsIn other.type
      let locals := deps.toList.filter (fun d => isLocal env d && d != n)
      let sorted := (locals.map Name.toString).toArray.qsort (· < ·) |>.toList
      let (seen, out) := sorted.foldl
        (fun (acc : NameSet × Array Name) s => collect env s.toName acc.1 acc.2) (seen, out)
      (seen, out.push n)

/-- Where one local constant is written, and what kind of declaration it is. -/
def locate (n : Name) : CoreM (Option Json) := do
  let env ← getEnv
  let some info := env.find? n | return none
  let some ranges ← findDeclarationRanges? n | return none
  let full : DeclarationRange := Lean.DeclarationRanges.range ranges
  let sel : DeclarationRange := Lean.DeclarationRanges.selectionRange ranges
  let kind := match info with
    | .defnInfo _ => "def"
    | .axiomInfo _ => "axiom"
    | .thmInfo _ => "theorem"
    | _ => "other"
  return some <| Json.mkObj [
    ("name", Json.str n.toString),
    ("module", Json.str ((env.getModuleFor? n).map Name.toString |>.getD "")),
    ("kind", Json.str kind),
    ("startLine", Json.num full.pos.line), ("startCol", Json.num full.pos.column),
    ("endLine", Json.num full.endPos.line), ("endCol", Json.num full.endPos.column),
    ("nameStartLine", Json.num sel.pos.line), ("nameStartCol", Json.num sel.pos.column),
    ("nameEndLine", Json.num sel.endPos.line), ("nameEndCol", Json.num sel.endPos.column)]

end IEANTN.Spinoff

open IEANTN.Spinoff in
/-- Emit the inlining plan for the declarations named on the command line. -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: ieantn_spinoff <declaration>..."
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `IEANTN }] {}
  let mut order : Array Name := #[]
  let mut seen : NameSet := {}
  let mut failed := false
  for a in args do
    let n := a.toName
    if env.find? n |>.isNone then
      IO.eprintln s!"error: unknown declaration `{a}`"
      failed := true
    else
      let (s, o) := collect env n seen order
      seen := s
      order := o
  if failed then return 1
  let act : CoreM (Array Json) := do
    let mut acc : Array Json := #[]
    for n in order do
      match ← locate n with
      | some j => acc := acc.push j
      | none => throwError "no source range for `{n}`; it cannot be inlined"
    return acc
  let (located, _) ← (act.toIO { fileName := "<spinoff>", fileMap := default } { env := env })
  IO.println (Json.mkObj [("declarations", Json.arr located)]).compress
  return 0
