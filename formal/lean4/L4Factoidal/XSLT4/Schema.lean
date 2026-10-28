/-
L4Factoidal.XSLT4.Schema — the schema side of a schema-aware XSLT 4.0
processor: the in-scope schema of a stylesheet (`xsl:import-schema`,
§3.15) and the validation of constructed nodes (§25).

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28), §3.15 "Importing Schema Components", §25 "Validation".
The schema reading and the validation are those of `L4Factoidal.XSD11`.

The schema documents are texts that the caller reads before compilation
(by file URI, as for stylesheet modules): this module does no I/O.

No `sorry`, no `axiom`, no `partial`.
-/
import L4Factoidal.XSD11.Load

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4
open L4Factoidal.XSD11 (Schema LoadedDoc)

/-- The file path of a `file:` URI (other URIs are kept). -/
def schemaPathOf (u : String) : String :=
  if u.startsWith "file://" then (u.drop 7).toString else u

/-- An `xsl:import-schema` declaration: the `namespace` attribute, the
    `schema-location` resolved against the module (a URI), the contained
    `xs:schema` element, and the module URI. -/
structure SchemaImport where
  ns : Option String := none
  loc : Option String := none
  inline : Option L4Factoidal.XML.Node := none
  base : String := ""
deriving Inhabited

/-- The `targetNamespace` of a schema document element (`""`: none). -/
def schemaTns (root : L4Factoidal.XML.Node) : String :=
  (L4Factoidal.XML.findAttr "targetNamespace" root.elementAttrs).getD ""

/-- The schema documents `roots` (file paths) reach by `include`,
    `import`, `redefine` and `override`, from `texts` (keyed by file URI),
    after the given documents. A document with no text is left out. -/
def schemaDocsFrom (texts : List (String × String)) (given : List LoadedDoc) (roots : List String) :
    List LoadedDoc := Id.run do
  let mut out := given
  let mut todo := roots ++ given.flatMap (fun d => XSD11.refsOf d.loc d.doc)
  let mut seen := given.map (·.loc)
  for _ in [0:500] do
    match todo with
    | [] => break
    | l :: rest =>
      todo := rest
      if seen.contains l then continue
      seen := l :: seen
      match texts.lookup ("file://" ++ l) with
      | none => continue
      | some t =>
        match L4Factoidal.XML.parseXML t with
        | .ok d =>
          out := out ++ [{ loc := l, doc := d }]
          todo := todo ++ XSD11.refsOf l d
        | .error _ => continue
  return out

/-- The schema of a stylesheet: the built-in components and the
    components of the `xsl:import-schema` declarations (§3.15). An import
    with only a namespace takes the schema documents of `texts` with that
    target namespace. XTSE0215: a contained `xs:schema` with a
    `schema-location`, or a `namespace` that differs from its target
    namespace; XTSE0220: the schema is not valid. -/
def stylesheetSchema (texts : List (String × String)) (imps : List SchemaImport) : Except Err Schema := do
  if imps.isEmpty then return Schema.builtins
  let mut given : List LoadedDoc := []
  let mut roots : List String := []
  for (im, k) in imps.zipIdx do
    match im.inline with
    | some root =>
      if im.loc.isSome then
        throw { code := "XTSE0215", msg := "xsl:import-schema has both a schema-location and an xs:schema child" }
      let tns := schemaTns root
      if let some n := im.ns then
        if n != tns then
          throw { code := "XTSE0215", msg := s!"xsl:import-schema namespace '{n}' differs from the target namespace '{tns}'" }
      let loc := schemaPathOf im.base ++ "#xsl-import-schema-" ++ toString k
      given := given ++ [{ loc, doc := { decl := none, doctype := none, prolog := [], root, epilog := [] } }]
      roots := roots ++ [loc]
    | none =>
      let byLoc := im.loc.bind (fun u =>
        let p := XSD11.pathNormalize (schemaPathOf u)
        if (texts.lookup ("file://" ++ p)).isSome then some p else none)
      match byLoc with
      | some p => roots := roots ++ [p]
      | none =>
        -- a namespace only: the schema documents for it that the caller gave
        let want := im.ns.getD ""
        for (u, t) in texts do
          if !(u.endsWith ".xsd") then continue
          match L4Factoidal.XML.parseXML t with
          | .ok d => if schemaTns d.root == want then roots := roots ++ [schemaPathOf u]
          | .error _ => pure ()
  let docs := schemaDocsFrom texts given roots
  let s := XSD11.buildSchema none XSD11.xpathHooks docs roots
  if !s.errors.isEmpty then
    throw { code := "XTSE0220", msg := s!"the imported schema is not valid: {s.errors.take 2}" }
  return s

/-- Is `q` the name of a type definition of the schema (built-in or
    imported)? -/
def schemaHasType (s : Schema) (q : QN) : Bool := (s.typeIdx? ⟨q.uri, q.loc⟩).isSome

/-- Is `q` the name of a complex type definition of the schema? -/
def schemaComplexType (s : Schema) (q : QN) : Bool :=
  match s.typeIdx? ⟨q.uri, q.loc⟩ with
  | some t => !(s.type t).isSimple
  | none => false

/-- The XSLT error code for a failed validation (§25.1.1, §25.1.2):
    `how` is `strict`, `lax` or `type Q{uri}local`. -/
def validationCode (how : String) (e : Err) : String :=
  if how == "strict" then (if e.code == "XQDY0084" then "XTTE1512" else "XTTE1510")
  else if how == "lax" then "XTTE1515" else "XTTE1540"

/-- Validate node `i` of the tree `d` (an element, or a document node
    whose element child is validated): the typed document, record 1 the
    element. -/
def validateTree (s : Schema) (how : String) (d : Doc) (i : Nat) : Except Err Doc :=
  match XSD11.validateNodeIn s how d i d.uri with
  | .ok d' => .ok d'
  | .error e => .error { code := validationCode how e, msg := e.msg }

/-- Validate an attribute value (§25.1.1, §25.1.2): `how` is `strict`,
    `lax` or `type Q{uri}local`; `scope` resolves prefixes in the value.
    The type annotation and the typed value, or `none` when lax
    validation finds no declaration. An `xml:id` attribute is an
    `xs:ID` (§25.3). -/
def validateAttrValue (s : Schema) (how : String) (q : QN) (v : String) (scope : List (String × String)) :
    Except Err (Option (QN × Option (List Atomic))) := do
  let t? : Option Nat ←
    if how.startsWith "type Q{" then
      match (how.drop 7).toString.splitOn "}" with
      | [u, l] => match s.typeIdx? ⟨u, l⟩ with
        | some t => pure (some t)
        | none => throw { code := "XTSE1520", msg := s!"no type definition {how}" }
      | _ => throw { code := "XTSE1520", msg := s!"invalid type name {how}" }
    else if q.uri == nsXML && q.loc == "id" then pure (some (XSD11.builtinIdx .id))
    else match s.attrIdx? ⟨q.uri, q.loc⟩ with
      | some d => pure (some (s.attr d).typ)
      | none => if how == "strict" then throw { code := "XTTE1512", msg := s!"no attribute declaration for {q.show}" }
                else pure none
  match t? with
  | none => return none
  | some t =>
    if !(s.type t).isSimple then
      throw { code := "XTTE1540", msg := "an attribute is validated against a complex type" }
    -- QName and NOTATION values need the namespace context of an element (XTTE1545)
    let qnLike := (s.derivesFrom t (XSD11.builtinIdx .qname)) || (s.derivesFrom t (XSD11.builtinIdx .notation))
    if qnLike then throw { code := "XTTE1545", msg := "an attribute is validated against a type derived from xs:QName or xs:NOTATION" }
    match (XSD11.validateSimple s XSD11.xpathHooks scope t v []).1 with
    | .ok (norm, _) => return some (s.typeQN t, XSD11.atomsOf s (fun p => scope.lookup p) t norm)
    | .error m =>
      let code := if how == "strict" then "XTTE1510" else if how == "lax" then "XTTE1515" else "XTTE1540"
      throw { code, msg := m }

end L4Factoidal.XSLT4
