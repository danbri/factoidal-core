import L4Factoidal.Crypto.SHA2
import L4Factoidal.Wikidata.Rewrite

open Lean

-- Wikimedia's JSONL v1 process boundary:
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/SparqlRewriteServer.java

private def envelope (requestId queryId : Option String) (status : String) : List (String × Json) :=
  [("protocol_version", toJson (1 : Nat)), ("status", toJson status)] ++
    requestId.toList.map (fun id => ("request_id", toJson id)) ++
    queryId.toList.map (fun id => ("query_id", toJson id))

private def protocolError (requestId queryId : Option String) (code message : String)
    (status : String := "protocol_error") : Json :=
  Json.mkObj (envelope requestId queryId status ++
    [("diagnostic", Json.mkObj [("code", toJson code), ("message", toJson message)])])

private def requiredString (request : Json) (field : String) : Option String :=
  ((request.getObjVal? field).bind Json.getStr?).toOption

private def handle (line : String) (language : String) : Json := Id.run do
  let .ok request := Json.parse line |
    return protocolError none none "rewrite_engine_failure" "Unexpected rewrite-engine failure." "engine_error"
  let some requestId := requiredString request "request_id" |
    return protocolError none none "invalid_request" "Missing or non-string field: request_id"
  let some queryId := requiredString request "query_id" |
    return protocolError (some requestId) none "invalid_request" "Missing or non-string field: query_id"
  let fail := protocolError (some requestId) (some queryId)
  let .ok version := (request.getObjVal? "protocol_version").bind Json.getNum? |
    return fail "invalid_request" "Missing or non-numeric field: protocol_version"
  if version != (1 : JsonNumber) then
    return fail "unsupported_protocol_version" "Only protocol version 1 is supported."
  let some query := requiredString request "query" |
    return fail "invalid_request" "Missing or non-string field: query"
  let result := toJson (L4Factoidal.Wikidata.rewriteQuery query language)
  let result := (result.setObjVal! "contract_version" (toJson (1 : Nat))).setObjVal! "query_id" (toJson queryId)
  return Json.mkObj (envelope (some requestId) (some queryId) "ok" ++
    [("query_sha256", toJson (L4Factoidal.Crypto.sha256Hex query)), ("result", result)])

def main (args : List String) : IO UInt32 := do
  let some language := (match args with
    | [] => some ""
    | ["--language", language] => some language
    | _ => none) |
    IO.eprintln "usage: l4wikidata-rewriter [--language TAG]"
    return 1
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    unless line.trimAscii.isEmpty do
      output.putStrLn (handle line language).compress
      output.flush
  return 0
