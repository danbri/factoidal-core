/-
Wasm.Ops.Cid — Controlled Identifiers v1.0 over the dispatch ABI
(https://github.com/danbri/factoidal/issues/1100, items 7 and 9). Every
decision is in `L4Factoidal.CID` (`Validate.lean`, `Fetch.lean`); this module
reads and writes JSON.

  cidValidate(text)
    text: the controlled identifier document, as JSON text.
    -> {"ok":true,"valid":B,"errors":[{"code","message","path"}]}
       (`CID.checkText`: `valid` is `parseDocument`'s answer; each error is a
       failed MUST of §2 with its RFC 6901 JSON Pointer.)

  cidRetrieve(requestJson)
    requestJson: {"vm":URL,"relationship":NAME,"now":SECONDS?,
      "allowHttp":B?,"allowPrivateFetch":B?,"resolver":B? (default true),
      "resolved":[{"host":H,"addresses":[TEXT…]}]?,
      "fetched":[{"url":U,"status":N,"contentType":T,"body":TEXT}]?}
    -> one step of `CID.Fetch.step`:
       {"ok":true,"step":"resolve","host":H}
       {"ok":true,"step":"fetch","url":U,"accept":A,"address":TEXT|null}
       {"ok":true,"step":"method","verificationMethod":{…},"controllerDocument":U}
       {"ok":true,"step":"error","code":NAME,"problem":{"type","title","detail"}}
    A request that is not JSON, or names no `vm` or an unknown
    relationship, is an error envelope.

Both ops are pure and in the full table only.
-/
import Wasm.Ops.Support
import L4Factoidal.CID.Validate
import L4Factoidal.CID.Fetch

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.CID

/-- `cidValidate(text)`. -/
def cidValidate (text : String) : String :=
  let r := checkText text
  okWith [("valid", .bool r.valid),
          ("errors", .array (r.issues.map fun i => .object
            [("code", .string i.error.code), ("message", .string i.error.describe), ("path", .string i.path)]))]

private def cidNat? (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number s) => s.toNat?
  | _ => none

private def cidInt? (j : Json) (k : String) : Option Int :=
  match j.field? k with
  | some (.number s) => s.toInt?
  | _ => none

/-- Read the request of `cidRetrieve`. -/
def cidRequestOf (j : Json) : Except String Fetch.Request :=
  match j.getString? "vm", j.getString? "relationship" with
  | none, _ => .error "cidRetrieve: member \"vm\" (a string) is required"
  | _, none => .error "cidRetrieve: member \"relationship\" (a string) is required"
  | some vm, some rn =>
      match Relationship.ofName? rn with
      | none => .error s!"cidRetrieve: '{rn}' is not a verification relationship of CID 1.0 §2.3"
      | some rel =>
          let resolved := ((j.getArray? "resolved").getD []).filterMap fun e =>
            (e.getString? "host").map fun h => (h, ((e.getArray? "addresses").getD []).filterMap Json.asString?)
          let fetched := ((j.getArray? "fetched").getD []).filterMap fun e =>
            (e.getString? "url").map fun u =>
              { url := u, status := (cidNat? e "status").getD 0,
                contentType := (e.getString? "contentType").getD "",
                body := (e.getString? "body").getD "" : Fetch.Fetched }
          .ok { vm, rel, now := cidInt? j "now",
                allowHttp := (j.getBool? "allowHttp").getD false,
                allowPrivateFetch := (j.getBool? "allowPrivateFetch").getD false,
                resolver := (j.getBool? "resolver").getD true,
                resolved, fetched }

/-- `cidRetrieve(requestJson)`. -/
def cidRetrieve (requestJson : String) : String :=
  match parseJson? requestJson with
  | none => errJson "cidRetrieve: the request is not JSON"
  | some j =>
      match cidRequestOf j with
      | .error e => errJson e
      | .ok q =>
          match Fetch.step q with
          | .resolve h => okWith [("step", .string "resolve"), ("host", .string h)]
          | .fetch u a addr =>
              okWith [("step", .string "fetch"), ("url", .string u), ("accept", .string a),
                      ("address", match addr with | some x => .string x | none => .null)]
          | .method m =>
              okWith [("step", .string "method"), ("verificationMethod", m.json),
                      ("controllerDocument", .string (withoutFragment q.vm))]
          | .failure f =>
              okWith [("step", .string "error"), ("code", .string f.code), ("problem", f.problem)]

def cidOpNames : List String := ["cidValidate", "cidRetrieve"]

/-- Serve one of `cidOpNames`, or `none` for any other op. -/
def callCid (op : String) (args : List String) : Option String :=
  match op, args with
  | "cidValidate", [a] => some (cidValidate a)
  | "cidRetrieve", [a] => some (cidRetrieve a)
  | "cidValidate", xs => some (errJson s!"cidValidate expects 1 argument, got {xs.length}")
  | "cidRetrieve", xs => some (errJson s!"cidRetrieve expects 1 argument, got {xs.length}")
  | _, _ => none

#guard cidValidate "{\"id\": \"https://c.example\"}" == "{\"ok\":true,\"valid\":true,\"errors\":[]}"
#guard (cidValidate "{\"id\": 1}").startsWith "{\"ok\":true,\"valid\":false,\"errors\":[{\"code\":\"idNotUrl\""
#guard cidRetrieve "{\"vm\":\"https://c.example/d#k\",\"relationship\":\"authentication\"}"
  == "{\"ok\":true,\"step\":\"resolve\",\"host\":\"c.example\"}"
#guard (cidRetrieve "{\"vm\":\"https://c.example/d#k\",\"relationship\":\"proofOfWork\"}").startsWith "{\"ok\":false"
#guard (cidRetrieve "{\"vm\":\"https://10.0.0.1/d#k\",\"relationship\":\"authentication\"}").startsWith
  "{\"ok\":true,\"step\":\"error\",\"code\":\"FETCH_REFUSED\""
#guard callCid "cidRetrieve" [] == some "{\"ok\":false,\"error\":\"cidRetrieve expects 1 argument, got 0\"}"

end L4Wasm.Ops
