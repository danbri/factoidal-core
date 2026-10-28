/-
L4Factoidal.XSD11.Load — the file side of schema processing, for the
harnesses and hosts: read schema documents and everything they reach,
build a schema, validate a document into an XDM 4.0 document with type
annotations, and give XPath 4.0 the in-scope schema definitions
(`XPath4.SchemaHook`).

The schema reading and validation themselves are pure
(`XSD11.Reader`, `XSD11.Validate`); this module only reads files.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.XPathHooks

namespace L4Factoidal.XSD11

open L4Factoidal.XML

/-- Read and parse an XML file; `none` when it is missing, a directory,
not UTF-8, or not well-formed. -/
def readDocFile (path : String) : IO (Option Document) := do
  if !(← System.FilePath.pathExists path) then return none
  if ← System.FilePath.isDir path then return none
  let bytes ← try IO.FS.readBinFile path catch _ => return none
  match String.fromUTF8? bytes with
  | none => return none
  | some src =>
    match parseXML src with
    | .ok d => return some d
    | .error _ => return none

/-- Load the schema documents named by `roots` and everything they reach
by `include`, `import`, `redefine` and `override`. The second component
is false when a document that exists could not be read. -/
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
      match ← readDocFile l with
      | some d =>
        loaded := { loc := l, doc := d } :: loaded
        todo := todo ++ refsOf l d
      | none =>
        if ← System.FilePath.pathExists l then allRead := false
  return (loaded.reverse, allRead)

/-- A schema from schema document files (component constraints checked). -/
def loadSchema (files : List String) : IO Schema := do
  let files := files.map pathNormalize
  let (docs, _) ← loadClosure files
  return buildSchema none xpathHooks docs files

/-- Schemas already read in this process, by their document files. -/
initialize schemaCache : IO.Ref (List (List String × Schema)) ← IO.mkRef []

/-- `loadSchema`, reading each set of files once per process. -/
def loadSchemaCached (files : List String) : IO Schema := do
  match (← schemaCache.get).lookup files with
  | some s => return s
  | none =>
    let s ← loadSchema files
    schemaCache.modify (fun c => (files, s) :: c)
    return s

def qnXName (q : XPath4.QN) : XName := ⟨q.uri, q.loc⟩

/-- The type index of a type annotation name (`Schema.typeQN`). -/
def Schema.typeOfQN? (s : Schema) (q : XPath4.QN) : Option Nat :=
  if q.uri == "" && q.loc.startsWith "#anonymous-" then (q.loc.drop 11).toString.toNat?
  else s.typeIdx? (qnXName q)

/-- Validate a document element for `xsd-validation` (F&O 4.0 `fn:parse-xml`):
`strict` needs a global declaration (or `xsi:type`) and validity; `lax`
validates what has declarations; `type Q{uri}local` validates against
that type. -/
def validateFor (s : Schema) (mode : String) (root : Node) (uri : String) : Except XPath4.Err XPath4.Doc :=
  let how? : Option How :=
    if mode == "strict" then rootHow s root []
    else if mode == "lax" then some (.wild .lax)
    else if mode.startsWith "type Q{" then
      let rest := (mode.drop 7).toString
      match rest.splitOn "}" with
      | [u, l] => (s.typeIdx? ⟨u, l⟩).map How.typ
      | _ => none
    else none
  match how? with
  | none => .error { code := "FODC0007", msg := s!"xsd-validation {mode}: no declaration or type to validate against" }
  | some how =>
    let r := validateElement s xpathHooks 10000 [] how root {}
    let idcErrs := checkIdcs s r.1
    let v := (r.1.info?.map (·.validity)).getD .notKnown
    if (mode != "lax" && v != .valid) || v == .invalid || !idcErrs.isEmpty then
      .error { code := "FODC0007", msg := s!"the document is not valid: {(r.2.errors ++ idcErrs).take 2}" }
    else .ok (psviDoc s r.1 uri)

/-- The in-scope schema definitions of `s` for XPath 4.0. -/
def schemaHookOf (s : Schema) : XPath4.SchemaHook :=
  { derives := fun t u =>
      match s.typeOfQN? t, s.typeOfQN? u with
      | some ti, some ui => s.derivesFrom ti ui
      | _, _ => XPath4.builtinTypeDerives t u,
    elemDecl := fun q => (s.elemIdx? (qnXName q)).map (fun d =>
      (s.typeQN (s.elem d).typ, (s.elem d).nillable)),
    attrDecl := fun q => (s.attrIdx? (qnXName q)).map (fun d => s.typeQN (s.attr d).typ),
    substitutes := fun n h =>
      match s.elemIdx? (qnXName n), s.elemIdx? (qnXName h) with
      | some ni, some hi => s.substOk hi ni
      | _, _ => false,
    validate := some (validateFor s) }

/-- Validate a document (§5.2, strict) and give its XDM 4.0 document with
the PSVI type annotations. -/
def validatedDoc (s : Schema) (d : Document) (uri : String := "") : XPath4.Doc × Assessment :=
  let a := assessDoc s xpathHooks d
  (psviDoc s a.root uri, a)

end L4Factoidal.XSD11
