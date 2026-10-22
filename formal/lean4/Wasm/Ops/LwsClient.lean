/-
Wasm.Ops.LwsClient — the LWS client ops (https://github.com/danbri/factoidal/issues/917).

  lwsClientStart(opJson, sessionJson)
    -> {"ok":true,"state":{…},"action":{…}} | {"ok":false,"error":"…"}
  lwsClientStep(stateJson, eventJson)
    -> {"ok":true,"state":{…},"action":{…}} | {"ok":false,"error":"…"}

`action` is one of
  {"fetch":{"method","url","headers":[[n,v],…],"bodyBase64"?}}
  {"done":RESULT,"session":{…}}
  {"fail":{"code",…},"session":{…}}
and an event is a response `{"status","headers","bodyBase64"|"body"}` or a
transport error `{"error":"…"}`.

The ops are stateless: the state is the JSON document `state`, which the
host passes back unread with the next event. `session` (the access tokens
and the subject token) goes from the `done` or `fail` of one operation to
the start of the next. Every decision is `L4Factoidal.LWS.Client.step`;
the signatures of notifications are verified with HACL* (`lwsVerifiers`).
Bodies are base64 (RFC 4648 §4) in both directions on the string entry.

The contract is `docs/lws-solid-conformance.md` § "wasm ABI"; the host is
`npm/factoidal/lws/client.mjs`.
-/
import Wasm.Ops.Support
import Wasm.Ops.Lws
import L4Factoidal.LWS.Client.Machine

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.LWS.Client

/-- The envelope of one step. -/
def clientEnvelope (out : ClientState × Action) : String :=
  okWith [("state", stateJson out.1), ("action", actionJson out.1 out.2)]

/-- `lwsClientStart(opJson, sessionJson)`: begin an operation. An empty
`sessionJson` is an empty session. -/
def lwsClientStart (opText sessionText : String) : String :=
  match parseJson opText with
  | .error e => errJson s!"lwsClientStart: the operation is not JSON: {repr e}"
  | .ok oj =>
    match opOfJson oj with
    | .error e => errJson s!"lwsClientStart: {e}"
    | .ok op =>
      let ses : Except String Session :=
        if sessionText.trimAscii.toString == "" then .ok {} else
        match parseJson sessionText with
        | .ok sj => .ok (sessionOfJson sj)
        | .error _ => .error "lwsClientStart: the session is not JSON"
      match ses with
      | .error e => errJson e
      | .ok ses => clientEnvelope (start lwsVerifiers op ses)

/-- `lwsClientStep(stateJson, eventJson)`: give the answer to the request
the last action named. -/
def lwsClientStep (stateText eventText : String) : String :=
  match parseJson stateText, parseJson eventText with
  | .ok sj, .ok ej =>
    match stateOfJson sj with
    | .error e => errJson s!"lwsClientStep: {e}"
    | .ok s => clientEnvelope (step lwsVerifiers s (eventOfJson ej))
  | .error _, _ => errJson "lwsClientStep: the state is not JSON"
  | _, .error _ => errJson "lwsClientStep: the event is not JSON"

def lwsClientOpNames : List String := ["lwsClientStart", "lwsClientStep"]

end L4Wasm.Ops
