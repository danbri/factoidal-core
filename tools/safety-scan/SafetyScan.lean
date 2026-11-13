/-
SafetyScan: which modules of the browser engine can reach an effect.

Issue: https://github.com/danbri/factoidal-core/issues/427
Record: docs/designissues/2026-11-13-foafnaut-safety-map.md

Run (the driver `tools/safety-scan/safety-scan.py` sets LEAN_PATH and the roots):

    lean --run tools/safety-scan/SafetyScan.lean OUT.json ROOT_MODULE...

WHAT IT CLAIMS. A Lean definition whose type has no `IO`, `EIO`, `BaseIO` and no
`IO.RealWorld` cannot do I/O, unless the code it runs reaches an ESCAPE HATCH:

  * a constant of this project with `@[extern]` (C code, any effect),
  * a constant of this project with `@[implemented_by]` other than the copy that
    `partial def` compiles to (the code that runs is not the code that was checked),
  * an `unsafe` constant of this project written in source,
  * an `initialize` / `builtin_initialize` declaration (runs at module load),
  * a core constant in `effectRunners` below (`dbgTrace` prints from pure code).

Lean refuses a safe definition that names an `unsafe` constant, so pure code reaches
`unsafeBaseIO`, `unsafeIO` or `unsafeCast` only through one of the first three
hatches. Core constants of `Init`, `Std` and `Lean` are trusted otherwise: their
`@[extern]` bodies (Nat arithmetic, `ByteArray`) are part of the Lean runtime, which
is in the trusted base (the record lists it).

HOW. Edges are the constants named in the VALUE of each definition and opaque of
this project (theorem values are erased at run time and are not followed), plus the
`@[implemented_by]` target. A reverse walk from every hatch marks each constant that
reaches it. A module is

  * `effect-typed`: some constant written in it has an effect in its type
    (test runners, `main`, the host bridge);
  * `io-free`: no effect in any type and no hatch reached;
  * `reaches-hatch`: no effect in any type, but its code reaches a hatch (listed).

WHAT IT DOES NOT CLAIM. `io-free` is a fact about the compiled code of the module
as the kernel stores it. It says nothing about whether the code is correct, or
about what a host does with the values the engine returns. Build-time execution
(`#eval`, `run_cmd`, custom elaborators) is counted by the driver from the source,
not here.
-/
import Lean
open Lean

namespace SafetyScan

/-- Core constants that are safe to name from pure code and still have an effect,
plus the unsafe runners (listed so that a change in Lean's rules shows up here). -/
def effectRunners : List Name :=
  [``dbgTrace, ``dbgTraceIfShared, ``dbgSleep, ``dbgStackTrace,
   ``unsafeBaseIO, ``unsafeEIO, ``unsafeIO, ``unsafeCast, ``ptrAddrUnsafe,
   ``Lean.ofReduceBool, ``Lean.ofReduceNat]

/-- Type constants that mean "this does I/O". -/
def effectTypeConsts : List Name := [``IO, ``EIO, ``BaseIO, ``IO.RealWorld, ``IO.Ref]

def compilerMade (n : Name) : Bool :=
  let n := (privateToUserName? n).getD n
  n.isInternal || (Compiler.isUnsafeRecName? n).isSome

def inProject (prefixes : List Name) (m : Name) : Bool :=
  prefixes.contains m.getRoot || (m.getPrefix.isAnonymous &&
    !([`Init, `Std, `Lean, `Lake, `SafetyScan].contains m.getRoot))

def hasEffectType (t : Expr) : Bool :=
  (t.find? fun e => match e with
    | .const n _ => effectTypeConsts.contains n
    | _ => false).isSome

def jstr (s : String) : String := (Json.str s).compress

def jarr (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

def main (args : List String) : IO UInt32 := do
  let out :: roots := args | do
    IO.eprintln "usage: lean --run SafetyScan.lean OUT.json ROOT_MODULE..."; return 2
  if roots.isEmpty then IO.eprintln "no root modules"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules (roots.toArray.map fun r => { module := r.toName }) {} (loadExts := false)
  -- Project = the top namespace of each root, plus one-component modules that are not
  -- Lean's own (the lab modules of labs/demos/foafnaut have one-component names).
  let prefixes : List Name := (roots.map (·.toName.getRoot)).eraseDups
  let names := env.header.moduleNames
  -- 1. Which module each constant was written in, for project modules only.
  let mut owner : Std.HashMap Name Nat := {}
  let mut projMods : Array Nat := #[]
  for i in [0:env.header.moduleData.size] do
    if inProject prefixes names[i]! then
      projMods := projMods.push i
      for c in env.header.moduleData[i]!.constants do
        owner := owner.insert c.name i
  -- 2. Hatch kinds per constant, and reverse edges.
  let mut hatchKind : Std.HashMap Name String := {}
  let mut rev : Std.HashMap Name (Array Name) := {}
  for r in effectRunners do
    if env.contains r then hatchKind := hatchKind.insert r "core-effect"
  for i in projMods do
    for c in env.header.moduleData[i]!.constants do
      let n := c.name
      if isExtern env n then hatchKind := hatchKind.insert n "extern"
      else if (getInitFnNameFor? env n).isSome || isIOUnitInitFn env n then
        hatchKind := hatchKind.insert n "initialize"
      else if c.isUnsafe && !compilerMade n then hatchKind := hatchKind.insert n "unsafe"
      let mut targets : Array Name := #[]
      match Compiler.implementedByAttr.getParam? env n with
      | some impl =>
        targets := targets.push impl
        if (Compiler.isUnsafeRecName? impl).isNone && !hatchKind.contains n then
          hatchKind := hatchKind.insert n "implemented_by"
      | none => pure ()
      match c with
      | .defnInfo d => targets := targets ++ d.value.getUsedConstants
      | .opaqueInfo o => targets := targets ++ o.value.getUsedConstants
      | _ => pure ()
      for t in targets do
        if owner.contains t || hatchKind.contains t || effectRunners.contains t then
          rev := rev.insert t ((rev.getD t #[]).push n)
  -- 3. Reverse walk from every hatch.
  let mut reach : Std.HashMap Name (Array Name) := {}
  for (h, _) in hatchKind.toList do
    let mut seen : Std.HashSet Name := {}
    let mut stack : Array Name := #[h]
    while !stack.isEmpty do
      let x := stack.back!
      stack := stack.pop
      if seen.contains x then continue
      seen := seen.insert x
      reach := reach.insert x ((reach.getD x #[]).push h)
      for y in rev.getD x #[] do
        if !seen.contains y then stack := stack.push y
  -- 4. One record per project module.
  let mut recs : Array String := #[]
  for i in projMods do
    let mut effectDecls : Array Name := #[]
    let mut decls := 0
    let mut theorems := 0
    let mut partials := 0
    let mut hatches : Std.HashSet Name := {}
    let mut own : Array String := #[]
    for c in env.header.moduleData[i]!.constants do
      let n := c.name
      if compilerMade n then continue
      decls := decls + 1
      if c matches .thmInfo _ then theorems := theorems + 1
      if c matches .opaqueInfo _ && env.contains (Compiler.mkUnsafeRecName n) then
        partials := partials + 1
      if !(c matches .thmInfo _) && hasEffectType c.type then effectDecls := effectDecls.push n
      if let some k := hatchKind.get? n then own := own.push (jarr [jstr n.toString, jstr k])
      if !(c matches .thmInfo _) then
        for h in reach.getD n #[] do hatches := hatches.insert h
    let cls :=
      if !effectDecls.isEmpty then "effect-typed"
      else if hatches.isEmpty then "io-free" else "reaches-hatch"
    let hs := hatches.toList.map fun h =>
      let m := (env.getModuleIdxFor? h).map (names[·.toNat]!.toString) |>.getD "?"
      jarr [jstr h.toString, jstr (hatchKind.getD h "?"), jstr m]
    recs := recs.push <| "{" ++ ",".intercalate [
      s!"\"module\":{jstr names[i]!.toString}",
      s!"\"class\":{jstr cls}",
      s!"\"decls\":{decls}", s!"\"theorems\":{theorems}", s!"\"partial_defs\":{partials}",
      s!"\"effect_typed_decls\":{effectDecls.size}",
      s!"\"effect_typed_sample\":{jarr ((effectDecls.toList.take 5).map (jstr ·.toString))}",
      s!"\"own_hatches\":{jarr own.toList}",
      s!"\"hatches_reached\":{jarr hs}"] ++ "}"
  IO.FS.writeFile out ("{\"roots\":" ++ jarr (roots.map jstr) ++ ",\"modules\":[\n" ++
    ",\n".intercalate recs.toList ++ "\n]}\n")
  IO.println s!"safety-scan: {recs.size} project modules, {hatchKind.size} hatches → {out}"
  return (if recs.isEmpty then 1 else 0)

end SafetyScan

def main (args : List String) : IO UInt32 := SafetyScan.main args
