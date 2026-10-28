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
  | none => .error { code := if mode == "strict" then "XQDY0084" else "FODC0007",
                     msg := s!"xsd-validation {mode}: no declaration or type to validate against" }
  | some how =>
    let r := validateElement s xpathHooks 10000 [] how root {}
    let idcErrs := checkIdcs s r.1
    let v := (r.1.info?.map (·.validity)).getD .notKnown
    if (mode != "lax" && v != .valid) || v == .invalid || !idcErrs.isEmpty then
      .error { code := "FODC0007", msg := s!"the document is not valid: {(r.2.errors ++ idcErrs).take 2}" }
    else .ok (psviDoc s r.1 uri)

/-- The XML tree of a node of an XDM document (element names with their
prefixes, and the in-scope namespaces declared on every element, so the
tree can be validated on its own). -/
def nodeTree (d : XPath4.Doc) : Nat → Nat → Node
  | 0, _ => .text ""
  | f + 1, i =>
    let r := d.get i
    match r.kind with
    | .element =>
      let qn (q : XPath4.QN) := if q.pfx == "" then q.loc else q.pfx ++ ":" ++ q.loc
      let nsAttrs := (r.inscope.filter (fun b => b.1 != "xml")).eraseDups.reverse.map (fun (p, u) =>
        ({ name := if p == "" then "xmlns" else "xmlns:" ++ p, value := u } : Attribute))
      let nsAttrs := nsAttrs.foldl (fun acc a => if acc.any (·.name == a.name) then acc else acc ++ [a]) []
      let ats := r.attrs.toList.map (fun j => let a := d.get j; ({ name := qn a.name, value := a.value } : Attribute))
      .element (qn r.name) (nsAttrs ++ ats) (r.children.toList.map (nodeTree d f))
    | .text => .text r.value
    | .comment => .comment r.value
    | .pi => .pi r.name.loc r.value
    | _ => .text ""

/-- `validateFor` on a node of an XDM document: an element, or the document
element of a document node. -/
def validateNodeIn (s : Schema) (mode : String) (d : XPath4.Doc) (i : Nat) (uri : String) : Except XPath4.Err XPath4.Doc :=
  let r := d.get i
  let elemIdx := if r.kind == .document then
      r.children.toList.find? (fun j => (d.get j).kind == .element)
    else some i
  match elemIdx with
  | none => .error { code := "XQDY0061", msg := "the document node has no element child" }
  | some j => validateFor s mode (nodeTree d 100000 j) uri

/-- `fn:xsd-validator`: validate a node of an XDM document; with schema
documents from the options, against the schema they make. -/
def validateWithFor (s : Schema) (mode : String) (extra : List (XPath4.Doc × Nat))
    (d : XPath4.Doc) (i : Nat) (uri : String) : Except XPath4.Err (Option XPath4.Doc × List String) :=
  let s := if extra.isEmpty then s else
    let docs : List LoadedDoc := extra.zipIdx.filterMap (fun ((xd, j), k) =>
      let r := xd.get j
      let el := if r.kind == .document then r.children.toList.find? (fun c => (xd.get c).kind == .element) else some j
      el.map (fun e => { loc := s!"#xsd-validator-schema-{k}",
                         doc := { decl := none, doctype := none, prolog := [], root := nodeTree xd 100000 e, epilog := [] } }))
    buildSchema none xpathHooks docs (docs.map (·.loc))
  if !s.errors.isEmpty then .error { code := "FODC0007", msg := s!"the schema is not valid: {s.errors.take 2}" } else
  match validateNodeIn s mode d i uri with
  | .ok nd => .ok (some nd, [])
  | .error x => if x.code == "FODC0007" || x.code == "XQDY0061" || x.code == "XQDY0084" then .ok (none, [x.msg]) else .error x

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
    targetNamespaces := ((s.gTypes.map (·.1.ns)) ++ (s.gElems.map (·.1.ns)) ++ (s.gAttrs.map (·.1.ns))).filter
      (fun u => u != xsNS && u != xsiNS) |>.eraseDups,
    validate := some (validateFor s),
    validateIn := some (validateNodeIn s),
    validateWith := some (validateWithFor s) }

/-- Validate a document (§5.2, strict) and give its XDM 4.0 document with
the PSVI type annotations. -/
def validatedDoc (s : Schema) (d : Document) (uri : String := "") : XPath4.Doc × Assessment :=
  let a := assessDoc s xpathHooks d
  (psviDoc s a.root uri, a)

end L4Factoidal.XSD11
