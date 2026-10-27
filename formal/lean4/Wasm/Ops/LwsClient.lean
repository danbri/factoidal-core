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
the signatures of notifications are verified, and self-issued credentials
signed, with HACL* (`Authz.hacl`).
Bodies are base64 (RFC 4648 §4) in both directions on the string entry.

The contract is `docs/lws-solid-conformance.md` § "wasm ABI"; the host is
`npm/factoidal/lws/client.mjs`.
-/
import Wasm.Ops.Support
import Wasm.Ops.Lws
import L4Factoidal.LWS.Client.Machine
import L4Factoidal.LWS.Client.Keys

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
      let ses : Except String (Session × Bool) :=
        if sessionText.trimAscii.toString == "" then .ok ({}, true) else
        match parseJson sessionText with
        | .ok sj => .ok (sessionOfJson sj, sessionKeyOk sj)
        | .error _ => .error "lwsClientStart: the session is not JSON"
      match ses with
      | .error e => errJson e
      | .ok (ses, keyOk) =>
        -- A key that is neither a P-256 nor an Ed25519 private JWK ends the
        -- operation before anything is sent.
        if keyOk then clientEnvelope (start L4Factoidal.Authz.hacl op ses)
        else clientEnvelope (failWith { op := op.normalize, session := ses } "badArguments"
          [("reason", .string "the session key is not a P-256 or an Ed25519 private JWK of 32 bytes")])

/-- `lwsClientStep(stateJson, eventJson)`: give the answer to the request
the last action named. -/
def lwsClientStep (stateText eventText : String) : String :=
  match parseJson stateText, parseJson eventText with
  | .ok sj, .ok ej =>
    match stateOfJson sj with
    | .error e => errJson s!"lwsClientStep: {e}"
    | .ok s => clientEnvelope (step L4Factoidal.Authz.hacl s (eventOfJson ej))
  | .error _, _ => errJson "lwsClientStep: the state is not JSON"
  | _, .error _ => errJson "lwsClientStep: the event is not JSON"

/-- `lwsClientNewKey(algorithm, randomBase64)`: a new `did:key` agent from the
host's random bytes (64 are enough for either algorithm). `algorithm` is
`ES256` (a P-256 key) or `EdDSA` (an Ed25519 key). The answer is
`{"ok":true,"key":{"agent","kid","selfIssued"}}`; `selfIssued` is the
member the client's session takes (`Machine.selfIssuedJson`). -/
def lwsClientNewKey (algorithm randomText : String) : String :=
  match L4Factoidal.Authz.SigAlg.ofString? algorithm with
  | none => errJson s!"lwsClientNewKey: unknown algorithm \"{algorithm}\" (ES256, EdDSA)"
  | some alg =>
    match L4Factoidal.LWS.Base64.decode? randomText with
    | none => errJson "lwsClientNewKey: the random bytes are not base64"
    | some random =>
      match newAgent L4Factoidal.Authz.hacl alg random with
      | some a => okWith [("key", newAgentJson a)]
      | none => errJson "lwsClientNewKey: the random bytes do not make a key (64 bytes are needed)"

def lwsClientOpNames : List String := ["lwsClientStart", "lwsClientStep", "lwsClientNewKey"]

end L4Wasm.Ops
