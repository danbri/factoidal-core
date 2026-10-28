/-
L4Factoidal.XSD11.SchemaForSchemas — the Schema Representation
Constraint that every schema document is valid against the schema for
schema documents (XML Schema 1.1 Part 1 §3.17.6.1, "Schema Document",
and Appendix A).

The schema for schema documents is itself a schema document; it is read
by `XSD11.Reader` and applied by `XSD11.Validate`, so the representation
constraints it expresses (allowed children, attribute names and values,
`id` uniqueness, the identity constraints on names) are checked by the
same code that validates instances. The harness reads the copy that the
W3C suite ships (`saxonData/Override/XMLSchema.xsd`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.Constraints

namespace L4Factoidal.XSD11

/-- The schema documents of `docs` that are not valid against the schema
for schema documents `s4s`, with the first errors of each. -/
def s4sErrors (s4s : Schema) (h : Hooks) (docs : List LoadedDoc) : List String :=
  docs.flatMap (fun d =>
    if d.loc == xmlNsSchemaLoc then [] else
    let root := XSD.conditionalInclusion d.doc.root
    let a := assessRoot s4s h root
    let errs := checkIdcs s4s a.root
    if a.valid && errs.isEmpty then []
    else [s!"{d.loc}: not valid against the schema for schema documents: {(errs ++ a.errors).take 2}"])

/-- A schema from its documents, with the component constraints and (when
a schema for schema documents is given) the representation constraint. -/
def buildSchema (s4s : Option Schema) (h : Hooks) (docs : List LoadedDoc) (roots : List String) : Schema :=
  let s := checkSchema (readSchemaDocs docs roots)
  match s4s with
  | some s4 => { s with errors := s.errors ++ s4sErrors s4 h docs }
  | none => s

end L4Factoidal.XSD11
