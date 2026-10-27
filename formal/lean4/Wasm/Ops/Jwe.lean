/-
Wasm.Ops.Jwe — the JWE ops (RFC 7516 Compact Serialization) over
`L4Factoidal.JOSE.Jwe` (https://github.com/danbri/factoidal/issues/1085).

AES is a host call-out (`Crypto/CipherCall.lean`, design record
`docs/designissues/2026-10-27-xml-encryption-and-jwe.md`). Each op runs with
`CipherCall.replayCipher answers`. When it needs an AES operation the host has
not answered, it returns that request; the host runs exactly that WebCrypto
call (`npm/factoidal/lib/cipher-host.mjs`, `runWithCipher`) and calls the op
again with the same inputs and one more answer. RSA, P-256 and X25519 run in
the wasm (HACL*).

Byte fields are STANDARD base64 with padding (`atob`/`btoa`), the convention
of `cipher-host.mjs`. A JWE token is its own base64url text.

  jweDecrypt({"token": "<compact>", "jwk": {private JWK}, "answers": [...]})
    -> {"ok":true,"header":{protected header},"plaintext":base64}
     | {"ok":true,"need":{"op","key","iv","aad","data"}}
     | {"ok":false,"error":"..."}

  jweEncrypt({"alg","enc","jwk": {public JWK},"plaintext":base64,
              "header": {extra protected members}, "random": base64,
              "answers": [...]})
    -> {"ok":true,"token":"<compact>"} | {"ok":true,"need":{...}} | {"ok":false,...}

`answers` is a list of `{"request": <a need object as returned>, "answer":
{"ok": base64} | {"refused": true}}`. `random` must hold at least
`Jwe.randomBytesNeeded alg enc` octets (at most 112) from the host's random
source; the host passes the same `random` on every call of one encryption.

A decryption refused by the allowlist names the refusal; every failure after
it is the one message `jweDecrypt: decryption failed`.

Targeted imports only — never the L4Factoidal umbrella.
-/
import Wasm.Ops.Support
import L4Factoidal.JOSE.Jwe
import L4Factoidal.LWS.Snapshot

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Crypto.CipherCall (Req Ans Op replayCipher maxRequests)
open L4Factoidal.JOSE.Jwe
open L4Factoidal.JOSE.JweKey

private def b64 (b : ByteArray) : String := L4Factoidal.LWS.Base64.encode b

private def unb64 (j : Json) (k : String) : Option ByteArray :=
  match j.field? k with
  | none => some ByteArray.empty
  | some (.string s) => L4Factoidal.LWS.Base64.decode? s
  | some _ => none

/-- The need object of a request. -/
def jweReqJson (r : Req) : Json :=
  .object [("op", .string r.op.name), ("key", .string (b64 r.key)), ("iv", .string (b64 r.iv)),
           ("aad", .string (b64 r.aad)), ("data", .string (b64 r.data))]

private def reqOfJson? (j : Json) : Option Req := do
  let op ← (j.getString? "op").bind Op.ofName?
  let key ← unb64 j "key"
  let iv ← unb64 j "iv"
  let aad ← unb64 j "aad"
  let data ← unb64 j "data"
  pure { op := op, key := key, iv := iv, aad := aad, data := data }

private def ansOfJson? (j : Json) : Option Ans :=
  if j.getBool? "refused" == some true then some .refused
  else match j.getString? "ok" with
    | some s => (L4Factoidal.LWS.Base64.decode? s).map .ok
    | none => none

/-- Read `answers`; absent is the empty list. At most `maxRequests`. -/
def jweAnswers (j : Json) : Except String (List (Req × Ans)) :=
  match j.field? "answers" with
  | none => .ok []
  | some (.array xs) =>
      if xs.length > maxRequests then .error s!"more than {maxRequests} answers"
      else xs.foldr (fun x acc => do
          let rest ← acc
          let req ← match (x.field? "request").bind reqOfJson? with
            | some r => pure r
            | none => throw "an answer's request is not {op, key, iv, aad, data} in base64"
          let ans ← match (x.field? "answer").bind ansOfJson? with
            | some a => pure a
            | none => throw "an answer is not {ok: base64} or {refused: true}"
          pure ((req, ans) :: rest)) (.ok [])
  | some _ => .error "answers is not a list"

private def needJson (r : Req) : String := okWith [("need", jweReqJson r)]

/-- `jweDecrypt(argJson)`. -/
def jweDecrypt (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match j.getString? "token", (j.field? "jwk").bind parseDecKey?, jweAnswers j with
      | none, _, _ => errJson "jweDecrypt: missing string member \"token\""
      | _, none, _ =>
          errJson ("jweDecrypt: \"jwk\" is not a private RSA (2048, 3072 or 4096 bits), " ++
            "EC P-256, OKP X25519 or oct key")
      | _, _, .error e => errJson s!"jweDecrypt: {e}"
      | some token, some k, .ok answers =>
          match decrypt nativePrims (replayCipher answers) k token with
          | .ok (h, pt) => okWith [("header", h), ("plaintext", .string (b64 pt))]
          | .error (.need r) => needJson r
          | .error (.refused r) => errJson s!"jweDecrypt: {r.message}"
          | .error .decryptionFailed => errJson "jweDecrypt: decryption failed"

/-- `jweEncrypt(argJson)`. -/
def jweEncrypt (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      let extra : Except String (List (String × Json)) := match j.field? "header" with
        | none => .ok []
        | some (.object fs) => .ok fs
        | some _ => .error "\"header\" is not an object"
      match (j.getString? "alg").bind keyAlgOfString?, (j.getString? "enc").bind encAlgOfString?,
            (j.field? "jwk").bind parseEncKey?, unb64 j "plaintext", unb64 j "random",
            extra, jweAnswers j with
      | none, _, _, _, _, _, _ => errJson "jweEncrypt: \"alg\" is missing or not allowed"
      | _, none, _, _, _, _, _ => errJson "jweEncrypt: \"enc\" is missing or not allowed"
      | _, _, none, _, _, _, _ =>
          errJson ("jweEncrypt: \"jwk\" is not a public RSA (2048, 3072 or 4096 bits), " ++
            "EC P-256, OKP X25519 or oct key")
      | _, _, _, none, _, _, _ => errJson "jweEncrypt: \"plaintext\" is not base64"
      | _, _, _, _, none, _, _ => errJson "jweEncrypt: \"random\" is not base64"
      | _, _, _, _, _, .error e, _ => errJson s!"jweEncrypt: {e}"
      | _, _, _, _, _, _, .error e => errJson s!"jweEncrypt: {e}"
      | some alg, some enc, some key, some pt, some rand, .ok ex, .ok answers =>
          match encrypt nativePrims (replayCipher answers) rand alg enc key pt ex with
          | .ok tok => okWith [("token", .string tok)]
          | .error (.need r) => needJson r
          | .error (.invalid m) => errJson s!"jweEncrypt: {m}"
          | .error .refused => errJson "jweEncrypt: the cipher refused a request"

end L4Wasm.Ops
