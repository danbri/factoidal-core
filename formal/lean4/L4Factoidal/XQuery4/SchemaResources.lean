/- Schema location hints resolved from host-supplied resources, without I/O.
   The XSD reader, transitive document references and schema checker are shared
   with the file loader. Source documents are retained so later hints rebuild
   one schema with all component references checked together. -/
import L4Factoidal.XSD11.Load

namespace L4Factoidal.XQuery4

open L4Factoidal.XPath4
open L4Factoidal.XSD11

/-- Find the actual resource key, first as written and then against the
static base URI. Relative schema references use that key as their base. -/
def schemaResource (env : Env) (loc : String) : Option (String × String) :=
  match env.resources.lookup loc with
  | some txt => some (loc, txt)
  | none =>
    let absolute := resolveUri env.baseUri loc
    (env.resources.lookup absolute).map (absolute, ·)

/-- Read a closed set of supplied schema resources. A missing resource is a
static import error; no network or filesystem access is attempted. -/
def schemaResourceClosure (env : Env) : Nat → List String → List LoadedDoc → M (List LoadedDoc)
  | _, [], docs => pure docs
  | 0, _ :: _, _ => err "XQST0059" "schema resource references nested too deeply"
  | fuel + 1, loc :: todo, docs => do
    if docs.any (·.loc == loc) then schemaResourceClosure env fuel todo docs else
    let some (key, txt) := schemaResource env loc
      | err "XQST0059" ("schema location is not available: " ++ loc)
    if docs.any (·.loc == key) then schemaResourceClosure env fuel todo docs else
    let doc ← match XML.parseXML txt with
      | .ok d => pure d
      | .error _ => err "XQST0059" ("schema location is not well-formed XML: " ++ key)
    let refs := refsOf key doc
    schemaResourceClosure env fuel (todo ++ refs) (docs ++ [{ loc := key, doc }])

/-- Extend the in-scope schema with the locations of explicit schema
imports. Every supplied root must have the requested target namespace.
Opaque host hooks cannot be combined with new documents: the source
components are required to check cross-schema references. -/
def withSchemaLocations (env : Env) (imports : List (String × List String)) : M Env := do
  if !env.features.schemaLocationHints then return env
  let hints := imports.flatMap (fun (u, ls) => ls.map (u, ·))
  if hints.isEmpty then return env
  if !env.schema.targetNamespaces.isEmpty && env.schema.sourceDocuments.isEmpty then
    err "XQST0059" "schema location hints need the source documents of the existing schema"
  let mut roots := env.schema.sourceRoots
  for (u, loc) in hints do
    let some (key, txt) := schemaResource env loc
      | err "XQST0059" ("schema location is not available: " ++ loc)
    let d ← match XML.parseXML txt with
      | .ok d => pure d
      | .error _ => err "XQST0059" ("schema location is not well-formed XML: " ++ key)
    if (XSD.attrOf "targetNamespace" d.root).getD "" != u then
      err "XQST0059" ("schema location has a different target namespace: " ++ key)
    if !roots.contains key then roots := roots ++ [key]
  let previous : List LoadedDoc := env.schema.sourceDocuments.map (fun (loc, doc) => { loc, doc })
  let docs ← schemaResourceClosure env 500 roots previous
  let schema := buildSchema none xpathHooks docs roots env.features.xsdVersion
  if !schema.errors.isEmpty then
    err "XQST0059" ("schema location hints do not form a valid schema: " ++ toString (schema.errors.take 2))
  if !schema.unsupported.isEmpty then
    err "XQST0059" ("schema location hints use unsupported schema constructs: " ++ toString (schema.unsupported.take 2))
  return { env with schema := schemaHookOf schema }

@[simp] theorem withSchemaLocations_nil (env : Env) :
    withSchemaLocations env [] = .ok env := by
  cases h : env.features.schemaLocationHints <;> simp [withSchemaLocations, h] <;> rfl

theorem withSchemaLocations_disabled (env : Env) (imports : List (String × List String))
    (h : env.features.schemaLocationHints = false) :
    withSchemaLocations env imports = .ok env := by
  simp [withSchemaLocations, h]
  rfl

-- The host supplies text resources; the loader checks namespace agreement
-- and follows schema-relative imports with the same XSD reader as file I/O.
#guard match withSchemaLocations
    { features := { schemaLocationHints := true }, resources := [
      ("schemas/root.xsd", "<xs:schema xmlns:xs='http://www.w3.org/2001/XMLSchema' targetNamespace='urn:root'><xs:import namespace='urn:item' schemaLocation='item.xsd'/><xs:element name='root' type='xs:string'/></xs:schema>"),
      ("schemas/item.xsd", "<xs:schema xmlns:xs='http://www.w3.org/2001/XMLSchema' targetNamespace='urn:item'><xs:element name='item' type='xs:integer'/></xs:schema>")] }
    [("urn:root", ["schemas/root.xsd"])] with
  | .ok e => e.schema.targetNamespaces.contains "urn:root" && e.schema.targetNamespaces.contains "urn:item"
  | .error _ => false

#guard match withSchemaLocations
    { features := { schemaLocationHints := true }, resources := [
      ("schema.xsd", "<xs:schema xmlns:xs='http://www.w3.org/2001/XMLSchema' targetNamespace='urn:actual'/>")] }
    [("urn:requested", ["schema.xsd"])] with
  | .error e => e.code == "XQST0059"
  | .ok _ => false

#print axioms withSchemaLocations_disabled

end L4Factoidal.XQuery4
