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
  splitIri(iri)
    -> {"ok":true,"namespace":"...","localName":"..."}
       `L4Factoidal.RDF.splitIriXml`: the longest NCName suffix
       (https://github.com/danbri/factoidal/issues/1051 item 4)
  isNCName(text)
    -> {"ok":true,"ncName":true|false}   (`L4Factoidal.XML.isValidNCName`)
  vocabularies()
    -> {"ok":true,"vocabularies":[{"prefix","namespace","terms":[...]}]}
       `L4Factoidal.RDF.vocabularyTable` (issue 1051 item 5)
  memberIri(n)        -> {"ok":true,"iri":"...#_n"}       (n >= 1)
  memberOrdinal(iri)  -> {"ok":true,"ordinal":n|null}
       `L4Factoidal.RDF.memberIri`, `memberOrdinal?` (issue 1051 items 5, 6)

All are stateless: the core and the full engines serve them through `call`.
-/
import Wasm.Ops.Support
import L4Factoidal.RDF.TermJson
import L4Factoidal.SPARQL.SameValue
import L4Factoidal.RDF.MediaType
import L4Factoidal.RDF.IriSplit
import L4Factoidal.RDF.VocabularyTable

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

/-- `splitIri(iri)` — namespace and local name (`splitIriXml`). -/
def splitIriOp (iri : String) : String :=
  let (ns, l) := splitIriXml iri
  okWith [("namespace", .string ns), ("localName", .string l)]

/-- `isNCName(text)` — an XML NCName (Namespaces in XML 1.0, `[4] NCName`). -/
def isNCNameOp (text : String) : String :=
  okWith [("ncName", .bool (L4Factoidal.XML.isValidNCName text))]

/-- `vocabularies()` — `vocabularyTable` as JSON. -/
def vocabulariesOp : String :=
  okWith [("vocabularies", .array (vocabularyTable.map fun r =>
    Json.object [("prefix", .string r.prefixLabel), ("namespace", .string r.namespaceIri),
                 ("terms", .array (r.terms.map Json.string))]))]

/-- `memberIri(n)` — `rdf:_n` for a decimal `n ≥ 1`. -/
def memberIriOp (n : String) : String :=
  match n.trimAscii.toString.toNat? with
  | some k => if k ≥ 1 then okWith [("iri", .string (memberIri k))]
              else errCoded "call.arguments" s!"memberIri: n must be 1 or more (got {n})"
  | none => errCoded "call.arguments" s!"memberIri: n must be a decimal integer (got {n})"

/-- `memberOrdinal(iri)` — the `n` of `rdf:_n`, `null` for any other IRI. -/
def memberOrdinalOp (iri : String) : String :=
  okWith [("ordinal", match memberOrdinal? iri with
    | some k => .number (toString k)
    | none => .null)]

/-- The op names of this module. -/
def termsOpNames : List String :=
  ["sameValue", "syntaxFor", "splitIri", "isNCName", "vocabularies", "memberIri", "memberOrdinal"]

private def arityErr (op : String) (n : Nat) (args : List String) : String :=
  errJson s!"{op} expects {n} argument{if n == 1 then "" else "s"}, got {args.length}"

/-- Serve an op of this module; `none` for any other op. -/
def callTerms (op : String) (args : List String) : Option String :=
  match op, args with
  | "sameValue", [a, b] => some (sameValueOp a b)
  | "syntaxFor", [a, b] => some (syntaxForOp a b)
  | "syntaxFor", [a] => some (syntaxForOp a "")
  | "splitIri", [a] => some (splitIriOp a)
  | "isNCName", [a] => some (isNCNameOp a)
  | "vocabularies", [] => some vocabulariesOp
  | "memberIri", [a] => some (memberIriOp a)
  | "memberOrdinal", [a] => some (memberOrdinalOp a)
  | "sameValue", _ => some (arityErr op 2 args)
  | "syntaxFor", _ => some (errJson s!"syntaxFor expects 1 or 2 arguments, got {args.length}")
  | "splitIri", _ | "isNCName", _ | "memberIri", _ | "memberOrdinal", _ => some (arityErr op 1 args)
  | "vocabularies", _ => some (arityErr op 0 args)
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
#guard splitIriOp "http://e/ns#a1" == "{\"ok\":true,\"namespace\":\"http://e/ns#\",\"localName\":\"a1\"}"
#guard isNCNameOp "1a" == "{\"ok\":true,\"ncName\":false}"
#guard memberIriOp "2" == "{\"ok\":true,\"iri\":\"http://www.w3.org/1999/02/22-rdf-syntax-ns#_2\"}"
#guard has (memberIriOp "0") "call.arguments"
#guard memberOrdinalOp "http://www.w3.org/1999/02/22-rdf-syntax-ns#_7" == "{\"ok\":true,\"ordinal\":7}"
#guard memberOrdinalOp "http://e/x" == "{\"ok\":true,\"ordinal\":null}"
#guard has vocabulariesOp "\"prefix\":\"owl\""
#guard termsOpNames.all fun op => (callTerms op ["x", "y", "z", "w"]).isSome

end L4Wasm.Ops
