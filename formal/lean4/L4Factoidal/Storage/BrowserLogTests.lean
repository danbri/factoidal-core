/-
L4Factoidal.Storage.BrowserLogTests — the browser update log against the
served store and against SPARQL 1.1 Update.

* `applyEntry_eq_store`: the replay step of the browser log is the replay
  step of `SPARQL.StoreEndpoint` (`applyDeltaEntry`). `BrowserLog` keeps a
  copy so that the core wasm does not link the HTTP server; this theorem
  keeps the copy equal.
* Build-time checks: for each update form the log admits, the merge of the
  log of the update over a base equals the reference SPARQL 1.1 Update
  semantics (`SPARQL.applyUpdate`) over the same base, as datasets compared
  as sets (`StoreEndpoint.datasetSetEq`); and a form the log does not admit
  has no batch.
-/
import L4Factoidal.Storage.BrowserLogTheorems
import L4Factoidal.SPARQL.StoreEndpoint
import L4Factoidal.SPARQL.UpdateDelta
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.Syntax.NQuadsFast

namespace L4Factoidal.Storage.BrowserLog

open L4Factoidal.RDF
open L4Factoidal.Storage

theorem applyEntry_eq_store : applyEntry = L4Factoidal.SPARQL.StoreEndpoint.applyDeltaEntry := rfl

theorem applyBatch_eq_store (ds : Dataset) (b : DeltaBatch) :
    applyBatch ds b = L4Factoidal.SPARQL.StoreEndpoint.applyDeltaEntries ds b.ops := rfl

/-- The merge of the log of one update request over `base`, against the
reference update semantics over the same base. -/
private def agreesWithUpdate (baseNQ update : String) : Bool :=
  match L4Factoidal.Syntax.parseNQuadsFast baseNQ .rdf12,
        L4Factoidal.SPARQL.parseSparqlUpdate update none with
  | .ok base, .ok u =>
    match L4Factoidal.SPARQL.deltaBatchForUpdate? 0 0 id u,
          L4Factoidal.SPARQL.applyUpdate base u with
    | some b, .ok expected =>
      match encodeLog? [b] with
      | some bytes =>
        L4Factoidal.SPARQL.StoreEndpoint.datasetSetEq (merge base bytes) expected
      | none => false
    | _, _ => false
  | _, _ => false

private def baseNQ : String :=
  "<http://e/a> <http://e/p> \"1\" .\n" ++
  "<http://e/b> <http://e/p> \"2\" <http://e/g> .\n" ++
  "<http://e/c> <http://e/p> \"3\" <http://e/h> .\n"

#guard agreesWithUpdate baseNQ "INSERT DATA { <http://e/d> <http://e/p> \"4\" }"
#guard agreesWithUpdate baseNQ "INSERT DATA { GRAPH <http://e/k> { <http://e/d> <http://e/p> \"4\" } }"
#guard agreesWithUpdate baseNQ "DELETE DATA { <http://e/a> <http://e/p> \"1\" }"
#guard agreesWithUpdate baseNQ "DELETE DATA { GRAPH <http://e/g> { <http://e/b> <http://e/p> \"2\" } }"
#guard agreesWithUpdate baseNQ "CLEAR DEFAULT"
#guard agreesWithUpdate baseNQ "CLEAR GRAPH <http://e/g>"
#guard agreesWithUpdate baseNQ "DROP GRAPH <http://e/h>"
#guard agreesWithUpdate baseNQ "CREATE GRAPH <http://e/new>"
#guard agreesWithUpdate baseNQ
  "INSERT DATA { <http://e/x> <http://e/p> \"5\" } ; DELETE DATA { <http://e/x> <http://e/p> \"5\" }"
-- A form whose effect needs its WHERE clause evaluated has no batch.
#guard !agreesWithUpdate baseNQ "DELETE WHERE { ?s ?p ?o }"
-- The check can fail: a merge of a different log is not the update's result.
#guard match L4Factoidal.Syntax.parseNQuadsFast baseNQ .rdf12,
        L4Factoidal.SPARQL.parseSparqlUpdate "CLEAR DEFAULT" none with
  | .ok base, .ok u =>
    match L4Factoidal.SPARQL.applyUpdate base u with
    | .ok expected => !L4Factoidal.SPARQL.StoreEndpoint.datasetSetEq (merge base []) expected
    | .error _ => false
  | _, _ => false

end L4Factoidal.Storage.BrowserLog
