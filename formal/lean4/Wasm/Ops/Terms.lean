/-
Wasm.Ops.Terms — ops over RDF terms, IRIs and syntax names that a host API
over the engine needs (the Jena-, RDFLib- and RDF4J-style APIs of
https://github.com/danbri/echochamber). Each op is a thin envelope around a
pure function of the `L4Factoidal` library; the decisions are there.

  sameValue(termJsonA, termJsonB)
    -> {"ok":true,"sameValue":"true"|"false"|"incomparable"}
       `L4Factoidal.SPARQL.sameValue`: SPARQL 1.1 `=` on two terms
       (https://github.com/danbri/factoidal/issues/1052)
  syntaxFor(name, mediaType)
    -> {"ok":true,"syntax":"turtle"|...|null}
       `L4Factoidal.RDF.syntaxOfNames`: the registered media type, else the
       registered extension of the file name or IRI path
       (https://github.com/danbri/factoidal/issues/1053)

All are stateless: the core and the full engines serve them through `call`.
-/
import Wasm.Ops.Support
import L4Factoidal.RDF.TermJson
import L4Factoidal.SPARQL.SameValue
import L4Factoidal.RDF.MediaType

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF

/-- A term argument (`TermJson`), or the `term.invalid` refusal that names it. -/
private def termArg (who what text : String) : Except String Term :=
  match parseJson? text >>= TermJson.decodeTerm with
  | some t => .ok t
  | none => .error (errCoded "term.invalid" s!"{who}: {what} is not a term: {text}")

/-- `sameValue(termJsonA, termJsonB)` — SPARQL 1.1 `=` on two RDF terms,
three-valued (`L4Factoidal.SPARQL.sameValue`). -/
def sameValueOp (a b : String) : String :=
  match termArg "sameValue" "the first argument" a, termArg "sameValue" "the second argument" b with
  | .error e, _ => e
  | _, .error e => e
  | .ok x, .ok y =>
      okWith [("sameValue", .string (L4Factoidal.SPARQL.sameValueWord (L4Factoidal.SPARQL.sameValue x y)))]

/-- `syntaxFor(name, mediaType)` — the syntax label (`formatLabel`, a name of
`datasetFormats`) of a document by its media type or its file name; `null`
when neither names a registered syntax. Either argument may be empty. -/
def syntaxForOp (name mediaType : String) : String :=
  okWith [("syntax", match syntaxOfNames mediaType name with
    | some f => .string (formatLabel f)
    | none => .null)]

/-- The op names of this module. -/
def termsOpNames : List String :=
  ["sameValue", "syntaxFor"]

private def arityErr (op : String) (n : Nat) (args : List String) : String :=
  errJson s!"{op} expects {n} argument{if n == 1 then "" else "s"}, got {args.length}"

/-- Serve an op of this module; `none` for any other op. -/
def callTerms (op : String) (args : List String) : Option String :=
  match op, args with
  | "sameValue", [a, b] => some (sameValueOp a b)
  | "syntaxFor", [a, b] => some (syntaxForOp a b)
  | "syntaxFor", [a] => some (syntaxForOp a "")
  | "sameValue", _ => some (arityErr op 2 args)
  | "syntaxFor", _ => some (errJson s!"syntaxFor expects 1 or 2 arguments, got {args.length}")
  | _, _ => none

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def intLit (lex : String) : String :=
  s!"\{\"type\":\"literal\",\"value\":\"{lex}\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\"}"
private def decLit (lex : String) : String :=
  s!"\{\"type\":\"literal\",\"value\":\"{lex}\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#decimal\"}"

#guard sameValueOp (intLit "01") (decLit "1.0") == "{\"ok\":true,\"sameValue\":\"true\"}"
#guard sameValueOp (intLit "1") (intLit "2") == "{\"ok\":true,\"sameValue\":\"false\"}"
#guard sameValueOp (intLit "x") (intLit "2") == "{\"ok\":true,\"sameValue\":\"incomparable\"}"
#guard has (sameValueOp "{}" (intLit "2")) "\"code\":\"term.invalid\""
#guard syntaxForOp "http://e/a.ttl?x" "" == "{\"ok\":true,\"syntax\":\"turtle\"}"
#guard syntaxForOp "a.ttl" "application/n-quads" == "{\"ok\":true,\"syntax\":\"nquads\"}"
#guard syntaxForOp "a.unknown" "" == "{\"ok\":true,\"syntax\":null}"
#guard termsOpNames.all fun op => (callTerms op ["x", "y", "z", "w"]).isSome

end L4Wasm.Ops
