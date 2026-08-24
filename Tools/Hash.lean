/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import IEANTN
import Lean

/-!
# Statement fingerprints

Emits a canonical fingerprint of each named conclusion, for the receipt and staleness machinery.
Everything downstream — receipts, the breaking-change detector, the reviewer report — is a
comparison of these fingerprints, so what exactly gets fingerprinted is a load-bearing decision.

## What is fingerprinted, and why

A conclusion is a `def _ : Prop`, so its *type* is just `Prop`; the mathematics is in its **value**.
That value is what we fingerprint.

The value is serialised **structurally**, not pretty-printed, and with three deliberate erasures:

* **binder names are dropped**, so renaming `∀ x` to `∀ n` is not a change;
* **`mdata` is dropped**, so elaborator annotations do not leak in;
* **`Level` and `BinderInfo` are kept**, since universe and implicitness differences are real.

Pretty-printed output (`pp.all`) was rejected: it is a *presentation*, and Lean is free to change
it between versions. Fingerprinting it would turn every toolchain bump red for reasons having
nothing to do with the mathematics.

## Constants, and the one thing this does not detect

The value refers to other constants by name — `IEANTN.HasPrimeInInterval.logPower`, `Real.log`,
`Nat.lcmUpto`. Those are handled asymmetrically, and the asymmetry is the point:

* **IEANTN's own constants are followed.** Their values are fingerprinted too and folded in, so
  the result is a Merkle hash over IEANTN's local definition graph. A semantic change to a
  Vocabulary definition therefore moves the fingerprint of every conclusion that mentions it —
  which is exactly what makes a Vocabulary edit detectable.
* **Mathlib and core constants are opaque**, identified by name alone. So a Mathlib bump that
  reorganises proofs, renames binders, or restates a lemma equivalently leaves every fingerprint
  untouched, and the bump stays yellow rather than red.

**The residual risk, stated plainly:** if Mathlib changes what a definition *means* while keeping
its name, no fingerprint moves and this machinery will not notice. That case is not detectable at
this price — detecting it would mean fingerprinting Mathlib's own bodies, which would make every
bump red and destroy the property above. It is mitigated only by Mathlib's own conventions
(renaming or deprecating rather than silently redefining) and by the core build still having to
compile.

The fingerprint text is emitted as JSON; the caller hashes it. Keeping the hash outside Lean avoids
needing a cryptographic primitive here and keeps the digest algorithm easy to change.
-/

open Lean

namespace IEANTN.Fingerprint

/-- Is this constant defined by this project, rather than by Lean core or Mathlib?

Decided by **module provenance**, not by guessing at name prefixes: the environment records which
module every constant came from, and ours are exactly those under `IEANTN`. A constant with no
recorded module was defined in the module currently being elaborated, which is also ours. -/
def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => (`IEANTN).isPrefixOf m
  | none => true

/-- Auto-generated proof constants (`foo._proof_3`, and anything carrying macro scopes) are
elaboration artifacts. Their *numbering* shifts for reasons unrelated to the mathematics -- adding
an unrelated numeral earlier in the file is enough -- so including their names would make
fingerprints move spuriously.

Canonicalising them is safe in the sound direction: by proof irrelevance the identity of a proof
cannot affect what a statement says, so collapsing them can never hide a change of meaning. It can
only ever avoid a false alarm.

(The exact-but-costlier version is to run in `MetaM` and erase every subterm with `Meta.isProof`.
Worth doing if this heuristic is ever seen to matter.) -/
def isProofArtifact (n : Name) : Bool :=
  n.hasMacroScopes ||
    match n.components.getLast? with
    | some c => c.toString.startsWith "_proof_" || c.toString.startsWith "_example"
    | none => false

/-- A binder's information, as a stable tag. -/
def binderTag : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Structural serialisation of an expression, with binder names and `mdata` erased. -/
partial def skeleton : Expr → String
  | .bvar i => s!"b{i}"
  | .fvar id => s!"F{id.name}"
  | .mvar id => s!"M{id.name}"
  | .sort u => s!"S[{u}]"
  | .const n us => if isProofArtifact n then "C[<proof>]" else s!"C[{n}|{us.map toString}]"
  | .app f a => s!"({skeleton f} {skeleton a})"
  | .lam _ t b bi => s!"L{binderTag bi}[{skeleton t}][{skeleton b}]"
  | .forallE _ t b bi => s!"P{binderTag bi}[{skeleton t}][{skeleton b}]"
  | .letE _ t v b _ => s!"E[{skeleton t}][{skeleton v}][{skeleton b}]"
  | .lit l => s!"N[{repr l}]"
  | .mdata _ e => skeleton e
  | .proj n i e => s!"J[{n}|{i}|{skeleton e}]"

/-- Every constant a term mentions. -/
partial def constantsIn (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => if isProofArtifact n then acc else acc.insert n
  | .app f a => constantsIn a (constantsIn f acc)
  | .lam _ t b _ => constantsIn b (constantsIn t acc)
  | .forallE _ t b _ => constantsIn b (constantsIn t acc)
  | .letE _ t v b _ => constantsIn b (constantsIn v (constantsIn t acc))
  | .mdata _ e => constantsIn e acc
  | .proj _ _ e => constantsIn e acc
  | _ => acc

/-- The body of a definition, or its type if it has no body. -/
def bodyOf (env : Environment) (n : Name) : Option Expr := do
  let info ← env.find? n
  match info with
  | .defnInfo d => some d.value
  | .thmInfo d => some d.type
  | other => some other.type

/-- The Merkle fingerprint of `n`: its own skeleton, plus the fingerprints of every project-local
constant it transitively mentions, in a deterministic order. -/
partial def fingerprint (env : Environment) (n : Name) (visiting : NameSet := {}) : String :=
  if visiting.contains n then s!"<cycle {n}>"
  else match bodyOf env n with
    | none => s!"<missing {n}>"
    | some e =>
      let own := skeleton e
      let localDeps := (constantsIn e).toList.filter fun d => isLocal env d && d != n
      let deps := (localDeps.map Name.toString).toArray.qsort (· < ·) |>.toList
      let visiting := visiting.insert n
      let rendered := deps.map fun d =>
        s!"{d}={fingerprint env d.toName visiting}"
      s!"{own}||{String.intercalate ";" rendered}"

end IEANTN.Fingerprint

open IEANTN.Fingerprint in
/-- Emit `{"<decl>": "<fingerprint text>"}` for each declaration named on the command line. -/
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: ieantn_hash <declaration>..."
    return 1
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `IEANTN }] {}
  let mut out : Array (String × Json) := #[]
  let mut failed := false
  for name in args do
    let n := name.toName
    if env.find? n |>.isNone then
      IO.eprintln s!"error: unknown declaration `{name}`"
      failed := true
    else
      out := out.push (name, Json.str (fingerprint env n))
  IO.println (Json.mkObj out.toList).compress
  return if failed then 1 else 0
