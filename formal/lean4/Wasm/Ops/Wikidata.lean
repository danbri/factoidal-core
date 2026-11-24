import L4Factoidal.Wikidata.Rewrite

namespace L4Wasm.Ops

/-- A pure rewrite. Rule refusals and diagnostics are part of the result. -/
def wikidataRewrite (query language : String) (preserveComments : Bool := false) : String :=
  (Lean.Json.mkObj [("ok", Lean.toJson true), ("result",
    Lean.toJson (L4Factoidal.Wikidata.rewriteQuery query language preserveComments))]).compress

end L4Wasm.Ops
