/-
Wasm.Ops.ExtFns — caller-registered SPARQL 1.1 §17.6 extension
functions for the Lean engine.

  extRegister(iri)    -> {"ok":true,"count":N}
  extUnregister(iri)  -> {"ok":true,"count":N}
  extClear()          -> {"ok":true,"count":0}
  extList()           -> {"ok":true,"iris":[…]}

These ops are served by `callIO` only: the registry is an `IO.Ref` the
pure `L4Wasm.call` entry cannot reach, so that entry keeps answering
with the `geof:` table alone.

WHAT REGISTERING AN IRI DOES, AND DOES NOT DO
It adds the IRI to the set the evaluator is allowed to ask the host
about. It never displaces anything:

* SPARQL built-ins (`fn:`, `xsd:` casts, STRUUID, BNODE, …) are
  matched by `SPARQL/Expr.lean` BEFORE `env.ext` is consulted at all,
  so a registration cannot override one. That holds by construction.
* `L4Factoidal.Geo.extFns` is consulted before the host, so `geof:`
  keeps answering exactly as it did.
* An IRI that is not registered never crosses the boundary; it is the
  §17.6 error, which drops the row in FILTER position and leaves the
  variable unbound in BIND / SELECT-expression position.

THE WIRE
Arguments are SRJ binding-value objects (`jsonOfTerm`), the same
encoding the F* engine's bridge uses, so one JavaScript function serves
both engines. The answer is one SRJ binding-value object, or the empty
string for the §17.6 error.

DETERMINISM
The engine may evaluate one expression a different number of times than
the reference evaluator (the physical-plan runners are free to). The
host bridge therefore memoises on `iri + " " + argsJson` for the
duration of one top-level query, so a call with the same arguments
answers once. That memo table is also what makes the async
re-evaluation loop safe. See the design document.

Design: `docs/designissues/2026-09-04-lean-extension-functions.md`.
-/
import Wasm.ExtHost
import Wasm.Ops.Support
import L4Factoidal.SPARQL.Expr
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.Geo.Functions
import L4Factoidal.XSD.JsValue
import L4Factoidal.RDF.TermJson

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.JSON

/-- The IRIs the caller has registered, in registration order. The
wasm entry layer is the one place permitted to hold mutable state
(`Wasm/Ops/Handles.lean`); the evaluator still takes its extension
table as an ordinary argument. -/
initialize extRegistry : IO.Ref (List String) ← IO.mkRef []

/-- Encode the evaluated arguments as a JSON array of SRJ
binding-value objects. An argument with no term form (a §17.6 error
propagating in) makes the whole call an error without crossing the
boundary. -/
def extArgsJson (args : List EvalResult) : Option String :=
  (args.mapM EvalResult.toTerm?).map fun ts =>
    (Json.array (ts.map jsonOfTerm)).toString

/-- The literal of a JavaScript value the host tagged with its JavaScript type,
`{"js":"number"|"bigint"|"boolean"|"string","v":…}`: the datatype and the
lexical form are `XSD.JsValue.jsLiteral`'s choice
(https://github.com/danbri/factoidal/issues/894 item 3). -/
def jsValueTerm (j : Json) : Option Term := do
  let tag ← j.getString? "js"
  let v ← match j.field? "v" with
    | some (.string x) => some x
    | some (.bool b) => some (if b then "true" else "false")
    | _ => none
  let (dt, lex) ← L4Factoidal.XSD.JsValue.jsLiteral tag v
  mkResultLiteral lex ("http://www.w3.org/2001/XMLSchema#" ++ dt) none

/-- Decode one parsed answer: a tagged JavaScript value (`jsValueTerm`, the
engine chooses datatype and lexical form), or a term the application built
(`TermJson.decodeCheckedTerm`: the lexical form and the datatype IRI are kept
exactly as given, RDF 1.1 Concepts §3.3, and only what RDF requires is
checked). A term RDF does not admit is the §17.6 error for this call. -/
def extAnswerJson (j : Json) : Option EvalResult :=
  if (j.field? "js").isSome then (jsValueTerm j).map EvalResult.term
  else (TermJson.decodeCheckedTerm j).map EvalResult.term

/-- Decode the host's answer text. The empty string, an unparsable document,
and a document `extAnswerJson` rejects are all the same §17.6 error. -/
def extAnswer (s : String) : Option EvalResult :=
  if s.isEmpty then none
  else match parseJson s with
    | .error _ => none
    | .ok j => extAnswerJson j

/-- An application-supplied term that RDF admits is the answer, unchanged
(https://github.com/danbri/factoidal/issues/894: the application, not the
engine, chose its datatype and lexical form). -/
theorem extAnswerJson_encodeTerm (t : Term) (h : TermJson.termChecked t = true) :
    extAnswerJson (TermJson.encodeTerm t) = some (.term t) := by
  have hjs : (TermJson.encodeTerm t).field? "js" = none := by
    cases t with
    | literal l =>
        obtain ⟨⟨lex, dt, lang, dir⟩, _⟩ := l
        cases lang <;> cases dir <;>
          simp [TermJson.encodeTerm, TermJson.literalJson, Json.field?]
    | _ => simp [TermJson.encodeTerm, TermJson.iriJson, TermJson.bnodeJson, Json.field?]
  simp [extAnswerJson, hjs, TermJson.decodeCheckedTerm_encodeTerm t h]

#print axioms extAnswerJson_encodeTerm

/-- The extension table a query runs with: the built-in `geof:` family
first, then the host for a registered IRI, then the §17.6 error.

`registered` is a snapshot taken once per query by the IO dispatch
entry, so this stays an ordinary function of its arguments — the
mutable registry is read at the edge, never inside evaluation. -/
def extFnsWith (registered : List String)
    (iri : String) (args : List EvalResult) : Option EvalResult :=
  match L4Factoidal.Geo.extFns iri args with
  | some v => some v
  | none =>
      if registered.contains iri then
        match extArgsJson args with
        | none => none
        | some a => extAnswer (L4Wasm.extCallHost iri a)
      else none

/-- The snapshot every IO query path passes to `queryParsedDatasetWith`. -/
def extSnapshot : IO (List String) := extRegistry.get

private def registryEnvelope (iris : List String) : String :=
  okWith [("count", .number (toString iris.length)),
          ("iris", .array (iris.map Json.string))]

/-- `extRegister(iri)` — allow the host to answer this IRI. Registering
an IRI twice is not an error and does not duplicate it. -/
def extRegister (iri : String) : IO String := do
  if iri.isEmpty then
    pure (errJson "extRegister: the IRI must not be empty")
  else do
    let iris ← extRegistry.modifyGet fun iris =>
      let iris' := if iris.contains iri then iris else iris ++ [iri]
      (iris', iris')
    pure (registryEnvelope iris)

/-- `extUnregister(iri)` — stop allowing the host to answer this IRI.
Unregistering an IRI that was never registered is not an error. -/
def extUnregister (iri : String) : IO String := do
  let iris ← extRegistry.modifyGet fun iris =>
    let iris' := iris.filter (· != iri)
    (iris', iris')
  pure (registryEnvelope iris)

/-- `extClear()` — return the engine to the `geof:`-only table. A
long-lived server calls this between callers. -/
def extClear : IO String := do
  extRegistry.set []
  pure (registryEnvelope [])

/-- `extList()` — the registered IRIs, in registration order. -/
def extList : IO String := do
  pure (registryEnvelope (← extRegistry.get))

#guard (extAnswer "{\"js\":\"number\",\"v\":\"1e+21\"}").isSome
#guard match extAnswer "{\"js\":\"number\",\"v\":\"1e+21\"}" with
  | some (.term (.literal l)) => l.val.lexicalForm == "1.0E21" &&
      l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#double"
  | _ => false
#guard match extAnswer "{\"js\":\"number\",\"v\":\"7\"}" with
  | some (.term (.literal l)) => l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#integer"
  | _ => false
#guard match extAnswer "{\"js\":\"boolean\",\"v\":true}" with
  | some (.term (.literal l)) => l.val.lexicalForm == "true"
  | _ => false
#guard (extAnswer "{\"js\":\"number\",\"v\":\"x\"}").isNone
#guard (extAnswer "{\"js\":\"symbol\",\"v\":\"x\"}").isNone
-- an application-supplied term keeps its lexical form and datatype IRI
#guard match extAnswer "{\"type\":\"literal\",\"value\":\"007\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\"}" with
  | some (.term (.literal l)) => l.val.lexicalForm == "007"
  | _ => false
#guard match extAnswer "{\"type\":\"literal\",\"value\":\"1e21\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#double\"}" with
  | some (.term (.literal l)) => l.val.lexicalForm == "1e21"
  | _ => false
#guard match extAnswer "{\"type\":\"nt\",\"value\":\"_:b1\"}" with
  | some (.term (.bnode b)) => b == "b1"
  | _ => false
#guard (extAnswer "{\"type\":\"literal\",\"value\":\"x\",\"datatype\":\"rel\"}").isNone
#guard (extAnswer "{\"type\":\"literal\",\"value\":\"x\",\"xml:lang\":\"not a tag\"}").isNone
-- a plain JavaScript string that looks like a blank node is a string literal
#guard match extAnswer "{\"js\":\"string\",\"v\":\"_:x\"}" with
  | some (.term (.literal l)) => l.val.lexicalForm == "_:x"
  | _ => false

end L4Wasm.Ops
