/- Public CSVW producer controls: unsupported conversion cannot become a
complete dataset; successful raw envelopes retain warnings and invalid-cell
information. These are finite producer tests, not CSVW conformance proofs. -/
import Wasm.Ops.Formats

namespace L4Wasm.FormatsBoundaryTests
open L4Factoidal.JSON
open L4Wasm.Ops

private def metadata (pattern : String) : String :=
  (Json.object [("url", .string "data.csv"), ("tableSchema", .object
    [("columns", .array [.object [("name", .string "value"),
      ("datatype", .object [("base", .string "string"),
        ("format", .string pattern)])]])])]).toString

private def response (pattern : String) : Json :=
  (parseJson? (csvwToRdf "value\na\n" (metadata pattern) "{}")).getD .null

private def kinds (pattern : String) : List String :=
  match (response pattern).field? "diagnostics" with
  | some (.array issues) => issues.filterMap (fun issue => issue.getString? "kind")
  | _ => []

#guard (csvwDataset "value\na\n" (metadata "^a$") "{}").isOk
#guard (response "^a$").getBool? "ok" == some true
#guard (response "^a$").getString? "nquads" |>.isSome
#guard kinds "^a$" == []
#guard (csvwDataset "value\na\n" (metadata "[") "{}").isOk
#guard kinds "[" == ["warning"]
#guard (response "[").getBool? "ok" == some true
#guard (csvwDataset "value\na\n" (metadata "^b$") "{}").isOk
#guard kinds "^b$" == ["invalidValue"]
#guard (response "^b$").getBool? "ok" == some true
#guard !(csvwDataset "value\na\n" (metadata "(?=a)a") "{}").isOk
#guard kinds "(?=a)a" == ["unsupported"]
#guard (response "(?=a)a").getBool? "ok" == some false
#guard ((response "(?=a)a").field? "nquads").isNone
#guard ((response "(?=a)a").getString? "error").any (·.startsWith "unsupported-syntax:")

-- The public pure RIF producer cannot certify an unresolved import or
-- expose a blocked partial graph as completed saturation.
private def rifDocument (body : String := "") (directives : String := "") : String :=
  "<Document xmlns='http://www.w3.org/2007/rif#'>" ++ directives ++
  "<payload><Group>" ++ body ++ "</Group></payload></Document>"

private def blockedRule : String :=
  "<sentence><Implies><if><External><content><Atom><op>" ++
  "<Const type='http://www.w3.org/2007/rif#iri'>urn:unsupported-predicate</Const>" ++
  "</op><args ordered='yes'/></Atom></content></External></if><then>" ++
  "<Atom><op><Const type='http://www.w3.org/2007/rif#iri'>urn:result</Const>" ++
  "</op><args ordered='yes'/></Atom></then></Implies></sentence>"

#guard (rifSaturate (rifDocument) { default := [], named := [] }).isOk
#guard !(rifSaturate "<bad" { default := [], named := [] }).isOk
#guard !(rifSaturate (rifDocument blockedRule) { default := [], named := [] }).isOk
#guard match rifSaturate (rifDocument blockedRule) { default := [], named := [] } with
  | .error reason => reason.startsWith "incomplete-search:"
  | _ => false
#guard !(rifSaturate (rifDocument ""
  "<directive><Import><location>https://example.test/missing</location></Import></directive>") { default := [], named := [] }).isOk

end L4Wasm.FormatsBoundaryTests
