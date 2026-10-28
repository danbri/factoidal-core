/-
Harness/Xsd11Run — the W3C XML Schema Test Suite (`w3c/xsdtests`, vendored
at `third_party/testing/xsd`) run against `L4Factoidal.XSD11` (XML Schema
1.1 Part 1 Structures with Part 2 Datatypes).

The suite's own manifests decide the denominator: `suite.xml` names the
test sets, each test set holds `testGroup`s, and a group has at most one
`schemaTest` (one or more schema documents and the expected validity of
the schema) and any number of `instanceTest`s (an instance document and
its expected validity). Every test is scored, schema tests and instance
tests apart.

A test is one of:
  * pass / fail — the outcome was decided and agrees / disagrees with the
    `<expected>` that applies to XSD 1.1;
  * unsupported — a document is not readable by the project's XML parser
    (the suite has some UTF-16 and Latin-1 documents), or the schema or
    the assessment needed something this engine does not decide
    (`Schema.unsupported`, `Assessment.unsupported`, an XPath test with
    no hook). Unsupported is never counted as a pass;
  * not applicable — the group or test applies only to XSD 1.0, to
    restricted XPath in type alternatives, or to Unicode 4.0.0; or the
    expected validity is `indeterminate`. Counted, not scored.

Usage (from `formal/lean4/`):
  lake build l4xsd11 && .lake/build/bin/l4xsd11 [suite-dir] [--set NAME]
      [--verbose] [--group NAME]
-/
import L4Factoidal.XSD11.XPathHooks

open L4Factoidal.XML
open L4Factoidal.XSD11
open L4Factoidal.XSD (localOf attrOf tagOf elementChildren)

structure Tally where
  sPass : Nat := 0
  sFail : Nat := 0
  sUnsup : Nat := 0
  iPass : Nat := 0
  iFail : Nat := 0
  iUnsup : Nat := 0
  na : Nat := 0
deriving Inhabited

def Tally.add (a b : Tally) : Tally :=
  { sPass := a.sPass + b.sPass, sFail := a.sFail + b.sFail, sUnsup := a.sUnsup + b.sUnsup,
    iPass := a.iPass + b.iPass, iFail := a.iFail + b.iFail, iUnsup := a.iUnsup + b.iUnsup,
    na := a.na + b.na }

def Tally.show (t : Tally) : String :=
  s!"schema {t.sPass} pass, {t.sFail} fail, {t.sUnsup} unsupported; instance {t.iPass} pass, {t.iFail} fail, {t.iUnsup} unsupported; total {t.sPass + t.iPass} pass, {t.sFail + t.iFail} fail, {t.sUnsup + t.iUnsup} unsupported (out of {t.sPass + t.iPass + t.sFail + t.iFail + t.sUnsup + t.iUnsup}); {t.na} not applicable"

def hrefOf (n : Node) : Option String :=
  (attrOf "xlink:href" n).orElse (fun _ => attrOf "href" n)

/-- Is a `version` token list applicable to this processor (XSD 1.1,
full XPath 2.0 in type alternatives, Unicode 6 or later)? -/
def versionApplies (v : String) : Bool :=
  let ws := L4Factoidal.XSD.qnameList v
  ws.isEmpty || ws.any (fun w => w == "1.1" || w == "full-xpath-in-CTA" || w == "Unicode_6.0.0" ||
    w == "XSD_1.1")

/-- The `<expected>` that applies to XSD 1.1. -/
def expectedOf (test : Node) : Option String :=
  let exps := (elementChildren test).filter (fun c => localOf (tagOf c) == "expected")
  let pick := exps.find? (fun e => match attrOf "version" e with
    | none => false
    | some v => versionApplies v)
  let pick := pick.orElse (fun _ => exps.find? (fun e => (attrOf "version" e).isNone))
  pick.bind (attrOf "validity")

def readDoc (path : String) : IO (Option Document) := do
  if !(← System.FilePath.pathExists path) then return none
  if ← System.FilePath.isDir path then return none
  let bytes ← try IO.FS.readBinFile path catch _ => return none
  match String.fromUTF8? bytes with
  | none => return none
  | some src =>
    match parseXML src with
    | .ok d => return some d
    | .error _ => return none

/-- Load the schema documents named by `roots` and everything they reach. -/
def loadClosure (roots : List String) : IO (List LoadedDoc × Bool) := do
  let mut loaded : List LoadedDoc := []
  let mut todo := roots
  let mut seen : List String := []
  let mut allRead := true
  for _ in [0:500] do
    match todo with
    | [] => break
    | l :: rest =>
      todo := rest
      if seen.contains l then continue
      seen := l :: seen
      if (l.splitOn "://").length > 1 then continue
      match ← readDoc l with
      | some d =>
        loaded := { loc := l, doc := d } :: loaded
        todo := todo ++ refsOf l d
      | none =>
        if ← System.FilePath.pathExists l then allRead := false
  return (loaded.reverse, allRead)

def outcome (valid : Bool) : String := if valid then "valid" else "invalid"

def runGroup (s4s : Option Schema) (base : String) (group : Node) (verbose : Bool) : IO Tally := do
  let kids := elementChildren group
  let gname := (attrOf "name" group).getD "?"
  let schemaTests := kids.filter (fun c => localOf (tagOf c) == "schemaTest")
  let instTests := kids.filter (fun c => localOf (tagOf c) == "instanceTest")
  let ntests := schemaTests.length + instTests.length
  if !(versionApplies ((attrOf "version" group).getD "")) then
    return { na := ntests }
  let mut t : Tally := {}
  let schemaLocs := schemaTests.flatMap (fun st =>
    ((elementChildren st).filter (fun c => localOf (tagOf c) == "schemaDocument")).filterMap
      (fun d => (hrefOf d).map (fun h => pathNormalize (base ++ h))))
  let (docs, allRead) ← loadClosure schemaLocs
  let rootsRead := schemaLocs.all (fun l => docs.any (fun d => d.loc == l))
  let sch := buildSchema s4s xpathHooks docs schemaLocs
  let schemaUnsup := !allRead || !rootsRead || !sch.unsupported.isEmpty
  for st in schemaTests do
    if !(versionApplies ((attrOf "version" st).getD "")) then t := { t with na := t.na + 1 }; continue
    match expectedOf st with
    | some exp =>
      if exp != "valid" && exp != "invalid" then t := { t with na := t.na + 1 }
      else if schemaUnsup then
        t := { t with sUnsup := t.sUnsup + 1 }
        if verbose then IO.println s!"  UNSUP schema {gname}: {sch.unsupported.take 3} read={allRead && rootsRead}"
      else
        let got := outcome sch.errors.isEmpty
        if got == exp then t := { t with sPass := t.sPass + 1 }
        else
          t := { t with sFail := t.sFail + 1 }
          if verbose then IO.println s!"  FAIL schema {gname}: expected {exp}, errors {sch.errors.take 3}"
    | none => t := { t with na := t.na + 1 }
  for it in instTests do
    if !(versionApplies ((attrOf "version" it).getD "")) then t := { t with na := t.na + 1 }; continue
    let tn := (attrOf "name" it).getD "?"
    match expectedOf it with
    | none => t := { t with na := t.na + 1 }
    | some exp =>
      if exp != "valid" && exp != "invalid" then t := { t with na := t.na + 1 }; continue
      let ih := ((elementChildren it).find? (fun c => localOf (tagOf c) == "instanceDocument")).bind hrefOf
      match ih with
      | none => t := { t with na := t.na + 1 }
      | some ih =>
        let ipath := pathNormalize (base ++ ih)
        match ← readDoc ipath with
        | none =>
          t := { t with iUnsup := t.iUnsup + 1 }
          if verbose then IO.println s!"  UNSUP instance {gname}/{tn}: unreadable"
        | some idoc =>
          -- With no schema test, the instance's schema location hints
          -- name the schema (§4.3.2).
          -- With no schema test, or when the group's schema does not
          -- declare the document element, the instance's schema location
          -- hints name the schema (§4.3.2).
          let rootName := match idoc.root with
            | .element tag attrs _ => some (elemXName (instBindings [] attrs) tag)
            | _ => none
          let declared := match rootName with
            | some n => (sch.elemIdx? n).isSome
            | none => true
          let (sch, unsup) ← if schemaTests.isEmpty || !declared then do
              let hints := schemaHints idoc.root
              let locs := (schemaLocs ++ hints.map (fun h => resolveLoc ipath h)).eraseDups
              let (docs, ok) ← loadClosure locs
              let s := buildSchema none xpathHooks docs locs
              pure (s, !ok || !s.unsupported.isEmpty)
            else pure (sch, schemaUnsup)
          if unsup then
            t := { t with iUnsup := t.iUnsup + 1 }
            if verbose then IO.println s!"  UNSUP instance {gname}/{tn}: schema {sch.unsupported.take 3}"
          else
            let a := assessDoc sch xpathHooks idoc
            if !a.unsupported.isEmpty then
              t := { t with iUnsup := t.iUnsup + 1 }
              if verbose then IO.println s!"  UNSUP instance {gname}/{tn}: {a.unsupported.take 2}"
            else
              let got := outcome a.valid
              if got == exp then t := { t with iPass := t.iPass + 1 }
              else
                t := { t with iFail := t.iFail + 1 }
                if verbose then IO.println s!"  FAIL instance {gname}/{tn}: expected {exp}, errors {a.errors.take 3}"
  return t

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let rec optVal : List String → String → Option String
    | k :: v :: rest, key => if k == key then some v else optVal (v :: rest) key
    | _, _ => none
  let setFilter := optVal args "--set"
  let groupFilter := optVal args "--group"
  let positional := args.filter (fun a => !a.startsWith "--") |>.filter (fun a =>
    some a != setFilter && some a != groupFilter)
  let suiteDir := positional.head?.getD "../../third_party/testing/xsd"
  let cwd ← IO.currentDir
  let suiteDir := if suiteDir.startsWith "/" then suiteDir
    else pathNormalize (cwd.toString ++ "/" ++ suiteDir)
  match ← readDoc (suiteDir ++ "/suite.xml") with
  | none =>
    IO.println s!"l4xsd11: cannot read {suiteDir}/suite.xml (run tools/ensure-test-env.sh)"
    return 1
  | some suite =>
    let refs := (elementChildren suite.root).filterMap (fun c =>
      if localOf (tagOf c) == "testSetRef" then hrefOf c else none)
    let refs := match setFilter with
      | none => refs
      | some f => refs.filter (fun r => (r.splitOn f).length > 1)
    -- the schema for schema documents (§3.17.6.1)
    let s4sLoc := suiteDir ++ "/saxonData/Override/XMLSchema.xsd"
    let (s4sDocs, _) ← loadClosure [s4sLoc]
    let s4s := buildSchema none xpathHooks s4sDocs [s4sLoc]
    if !s4s.errors.isEmpty then
      IO.println s!"schema for schema documents: {s4s.errors.length} errors, first {s4s.errors.take 5}"
    -- (the 2009 copy restricts a type whose local `group` element has an
    -- anonymous type; that one finding does not stop it being used)
    let s4s := if !args.contains "--no-s4s" then some s4s else none
    let mut total : Tally := {}
    for rel in refs do
      let path := pathNormalize (suiteDir ++ "/" ++ rel)
      match ← readDoc path with
      | none => IO.println s!"{rel}: test set unreadable"
      | some ts =>
        let base := pathDir path
        let groups := (elementChildren ts.root).filter (fun c => localOf (tagOf c) == "testGroup")
        let groups := match groupFilter with
          | none => groups
          | some g => groups.filter (fun x => attrOf "name" x == some g)
        let mut t : Tally := {}
        for g in groups do
          if args.contains "--trace" then
            IO.eprintln s!"  group {(attrOf "name" g).getD "?"}"
          t := t.add (← runGroup s4s base g verbose)
        IO.println s!"{rel}: {t.show}"
        total := total.add t
    IO.println ""
    IO.println s!"XSD 1.1 (w3c/xsdtests): {total.show}"
    return 0
