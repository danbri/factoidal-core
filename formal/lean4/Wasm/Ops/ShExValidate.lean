/-
Wasm.Ops.ShExValidate — the ShEx validation operation of the npm entry
(https://github.com/danbri/factoidal/issues/713 stage 3).

  shexValidate(dataNquads, schemaText, focus, shape)
    -> {"ok":true,"verdict":true|false}

The envelope follows the F* npm entry (`bin/npm-entry/entry_extras.ml`,
`shex_validate_json`) member for member. This op was in
`Wasm/Ops/Validate.lean` until 2026-10-10; it has its own module so that the
core dispatch (`Wasm/CoreDispatch.lean`, issue 713 stage 4) serves SHACL
without linking the ShEx validator. Only the full dispatch imports it.

`shexValidate` reads the DEFAULT graph of `dataNquads`. The schema text is
ShExJ when its first non-whitespace character is `{` and ShExC otherwise —
the rule the F* entry states, and no ShExC document starts with `{`. The
focus and the shape are an IRI or `_:label`; an empty shape selects the
schema's START shape expression (`ShEx.validateStart`), any other shape is a
shape label (`ShEx.validateNode`). An `IMPORT` is not followed (no file or
network access through this entry). The F* function answered `null` outside
its decidable fragment; the Lean validator decides every schema it reads,
so `verdict` is always a boolean.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.ShEx.FromJson
import L4Factoidal.ShEx.Compact
import L4Factoidal.ShEx.Satisfies

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- A focus node or shape label given as an IRI or `_:label`. -/
private def nodeOfText (s : String) : Option Term :=
  if s.startsWith "_:" then
    if s.length > 2 then some (.bnode (String.ofList (s.toList.drop 2))) else none
  else if h : isIri s then some (.iri ⟨s, h⟩) else none

/-- The schema text, read as ShExJ or ShExC by its first non-whitespace
character. -/
private def schemaOfText (text : String) : Except String L4Factoidal.ShEx.Schema :=
  if (text.toList.dropWhile Char.isWhitespace).head? == some '{' then
    match parseJson? text with
    | none => .error "the ShExJ schema is not a JSON document"
    | some j =>
      match L4Factoidal.ShEx.schemaOf j with
      | some sch => .ok sch
      | none => .error "the JSON document is not a ShExJ schema this validator reads"
  else
    L4Factoidal.ShEx.Compact.parseShExC text

/-- `shexValidate(dataNquads, schemaText, focus, shape)`. -/
def shexValidate (dataNq schemaText focus shape : String) : String :=
  match parseNQuadsFast dataNq .rdf12 with
  | .error e => errJson s!"shexValidate(data): {fmtParseError e}"
  | .ok ds =>
  match schemaOfText schemaText with
  | .error e => errJson s!"shexValidate(schema): {e}"
  | .ok sch =>
  match nodeOfText focus with
  | none => errJson s!"shexValidate: the focus '{focus}' is not an IRI or _:label"
  | some n =>
    let verdict :=
      if shape.isEmpty then L4Factoidal.ShEx.validateStart sch ds.default n
      else L4Factoidal.ShEx.validateNode sch ds.default shape n
    okWith [("verdict", .bool verdict)]

/-! ## Build-time checks (positive and negative) -/

private def sxData : String :=
  "<http://e/alice> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Person> .\n" ++
  "<http://e/alice> <http://e/name> \"Alice\" .\n" ++
  "<http://e/dave> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/Person> .\n"

private def vShExC : String :=
  "PREFIX e: <http://e/>\ne:S { e:name LITERAL }\n"

private def vShExJ : String :=
  "{\"type\":\"Schema\",\"shapes\":[{\"type\":\"ShapeDecl\",\"id\":\"http://e/S\"," ++
  "\"shapeExpr\":{\"type\":\"Shape\",\"expression\":{\"type\":\"TripleConstraint\"," ++
  "\"predicate\":\"http://e/name\",\"valueExpr\":{\"type\":\"NodeConstraint\"," ++
  "\"nodeKind\":\"literal\"}}}}]}"

-- ShEx: alice has a literal name, dave has none; both schema syntaxes agree.
#guard shexValidate sxData vShExJ "http://e/alice" "http://e/S" == "{\"ok\":true,\"verdict\":true}"
#guard shexValidate sxData vShExJ "http://e/dave" "http://e/S" == "{\"ok\":true,\"verdict\":false}"
#guard shexValidate sxData vShExC "http://e/alice" "http://e/S" == "{\"ok\":true,\"verdict\":true}"
#guard shexValidate sxData vShExC "http://e/dave" "http://e/S" == "{\"ok\":true,\"verdict\":false}"
#guard (shexValidate sxData vShExC "not an iri" "http://e/S").startsWith "{\"ok\":false"
#guard (shexValidate sxData "{ not json" "http://e/alice" "http://e/S").startsWith "{\"ok\":false"

end L4Wasm.Ops
