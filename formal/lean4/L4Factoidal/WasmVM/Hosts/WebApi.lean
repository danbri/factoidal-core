/-
L4Factoidal.WasmVM.Hosts.WebApi: the `foafnaut_dom.web_api` import, which serves the
web APIs that are pure algorithms to page scripts (record:
docs/designissues/2026-11-08-page-scripts.md, "Web APIs over Lean"). The algorithms are Lean's:

  * the Encoding Standard (`WHATWG.Encoding.Core`, `.Api`): `TextDecoder`,
    `TextEncoder`, `TextDecoderStream`;
  * the URL Standard (`WHATWG.URL.Parser`): `URL`, `URLSearchParams`;
  * forgiving-base64 (`WHATWG.Base64`): `atob`, `btoa`;
  * `Crypto.WebCrypto`, `Crypto.WebCryptoKeys` and `Crypto.WebHacl`:
    `crypto.getRandomValues`, `randomUUID`, and `crypto.subtle` (digest, HMAC, HKDF,
    PBKDF2, ECDSA and ECDH on P-256, Ed25519, X25519, ChaCha20-Poly1305), with the
    primitives HACL*'s (record docs/designissues/2026-11-09-hacl-web-crypto.md).

`web_api(op, flags, ptr, len, buf, cap)`. The `len` bytes at `ptr` are the arguments:
a little-endian u32 count, then each argument as a u32 length and its bytes (strings in
UTF-8, numbers as decimal). The answer is bytes: written at `buf` when they fit in `cap`,
and the length is answered; when they do not fit, nothing is written, the bytes wait and
the answer is their length, and op 0 then writes them (so a stateful op runs once).
Negative answers: -1 none (null, or a failed parse), -2 not an op of this engine (a page
probes with op 1), -3 InvalidCharacterError, -5 over a budget, -6 no entropy,
-20 TypeError, -21 RangeError, -22 OperationError, -23 NotSupportedError, -24
SyntaxError, -25 InvalidAccessError, -26 DataError, -27 QuotaExceededError
(`WebCryptoKeys.Err.code`).

State: the decoders of `TextDecoder`s in the middle of a stream (by the number the page
gave them), the answer that waits, the random generator, and the session's CryptoKeys
(`WebCryptoKeys.Store`: the page holds handles, never key bytes). One call is one operation
on a whole buffer: the boundary is crossed once per `decode`, never per byte.
-/
import L4Factoidal.WasmVM.Hosts.Dom
import L4Factoidal.WHATWG.Encoding.Api
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.WHATWG.Base64
import L4Factoidal.Crypto.WebCrypto
import L4Factoidal.Crypto.WebCryptoKeys
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize
import Std.Data.HashMap

namespace L4Factoidal.WasmVM.Hosts.WebApi
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Hosts.Dom
open L4Factoidal.WHATWG

/-- The largest argument block: 64 MiB. -/
def maxInput : Nat := 1 <<< 26
/-- Decoders in the middle of a stream at one time. -/
def maxDecoders : Nat := 4096
/-- Arguments of one call. -/
def maxFields : Nat := 1 <<< 20

structure State where
  decoders : Std.HashMap Nat Encoding.TextDecoder := {}
  /-- The answer that did not fit; op 0 takes it. -/
  pending : ByteArray := ByteArray.empty
  /-- The embedder's entropy for this session (`Page.Limits.entropy`). -/
  entropy : ByteArray := ByteArray.empty
  /-- The document's encoding as the host decoded the page (`Page.Limits.encoding`, the
  name `WHATWG.Encoding.Sniff.decodeDocument` gave); "" when the host did not say. -/
  docEncoding : String := ""
  rng : Option Crypto.WebCrypto.Drbg := none
  /-- Generate calls of the generator so far (SP 800-90A's reseed counter). -/
  draws : Nat := 0
  /-- The CryptoKeys of the session. -/
  keys : Crypto.WebCryptoKeys.KeyStore := {}
  deriving Inhabited

/-! ## Arguments -/

def u32At (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i + 1]!.toNat * 256 + b[i + 2]!.toNat * 65536 + b[i + 3]!.toNat * 16777216

/-- The arguments of an argument block, `none` when it is malformed. -/
def fields (b : ByteArray) : Option (Array ByteArray) :=
  if b.size < 4 then none else
  let k := u32At b 0
  if k > maxFields then none else
  let r := (List.range k).foldl (fun (acc : Option (Array ByteArray × Nat)) _ =>
    match acc with
    | none => none
    | some (fs, pos) =>
      if pos + 4 > b.size then none else
      let n := u32At b pos
      if pos + 4 + n > b.size then none else
      some (fs.push (b.extract (pos + 4) (pos + 4 + n)), pos + 4 + n)) (some (#[], 4))
  r.map (·.1)

def strArg (fs : Array ByteArray) (i : Nat) : Except Int String :=
  match fs[i]? with
  | some b => match String.fromUTF8? b with | some s => .ok s | none => .error (-20)
  | none => .ok ""

def bytesArg (fs : Array ByteArray) (i : Nat) : ByteArray := fs[i]?.getD ByteArray.empty

def natArg (fs : Array ByteArray) (i : Nat) : Except Int Nat := do
  match (← strArg fs i).toNat? with | some n => .ok n | none => .error (-20)

def ofStr (s : String) : Except Int ByteArray := .ok s.toUTF8

/-! ## Encoding -/

def flag (flags bit : Nat) : Bool := (flags >>> bit) % 2 == 1

/-- op 3, `decode`: arguments label, handle, bytes; flags 1 fatal, 2 ignoreBOM, 4 stream.
A handle other than 0 keeps the decoder while the stream goes on. -/
def decode (s : State) (flags : Nat) (fs : Array ByteArray) : State × Except Int ByteArray :=
  match strArg fs 0, natArg fs 1 with
  | .ok label, .ok handle =>
    let stream := flag flags 2
    let td? := match s.decoders[handle]? with
      | some td => some td
      | none => Encoding.TextDecoder.new? label (flag flags 0) (flag flags 1)
    match td? with
    | none => (s, .error (-21))
    | some td =>
      let (td, r) := td.decodeBytes (bytesArg fs 2) stream
      let decoders := if stream && handle != 0 then s.decoders.insert handle td else s.decoders.erase handle
      if decoders.size > maxDecoders then (s, .error (-5)) else
      ({ s with decoders }, match r with | some b => .ok b | none => .error (-20))
  | .error e, _ | _, .error e => (s, .error e)

def u32le (n : Nat) : ByteArray :=
  ByteArray.mk #[(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8, (n / 16777216 % 256).toUInt8]

/-! ## URL -/

/-- The attributes of a URL, each followed by U+0000: href, origin, protocol, username,
password, host, hostname, port, pathname, search, hash. No attribute has a U+0000 (the
parser percent-encodes it). -/
def components (u : URL.Url) : String :=
  String.join ([u.href, u.origin, u.protocol, u.username, u.password, u.hostGetter, u.hostname,
    u.portGetter, u.pathname, u.search, u.hash].map (· ++ "\x00"))

/-- Strings as `<UTF-16 length>:<string>`, one after another: the page splits them with
no separator to escape. -/
def lengthPrefixed (xs : List String) : String :=
  String.join (xs.map fun x =>
    toString (x.foldl (fun n c => n + if c.toNat > 0xFFFF then 2 else 1) 0) ++ ":" ++ x)

/-! ## The document's character encoding -/

/-- HTML §2.5 "algorithm for extracting a character encoding from a meta element": the
label after the first `charset`, ASCII case-insensitive, that an `=` follows. -/
def extractCharset (content : String) : Option String :=
  let cs := content.toList
  let ws := fun (c : Char) => c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '
  let lower := fun (c : Char) => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
  let rec go (fuel : Nat) (xs : List Char) : Option String :=
    match fuel, xs with
    | 0, _ | _, [] => none
    | fuel + 1, _ :: rest =>
      if (xs.take 7).map lower != "charset".toList then go fuel rest else
      let after := (xs.drop 7).dropWhile ws
      match after with
      | '=' :: more =>
        match more.dropWhile ws with
        | q :: tail =>
          if q == '"' || q == '\'' then
            if tail.contains q then some (String.ofList (tail.takeWhile (· != q))) else none
          else
            let v := (q :: tail).takeWhile (fun c => !ws c && c != ';')
            if v.isEmpty then none else some (String.ofList v)
        | [] => none
      | _ => go fuel (xs.drop 7)
  go (cs.length + 1) cs

/-- The encoding a document declares in a `meta` element (HTML §13.2.3.2, the prescan's
rules on the parsed tree: the first `meta` whose `charset`, or whose `http-equiv`
content-type `content`, names an encoding; UTF-16 is UTF-8 and x-user-defined is
windows-1252).

The hosts give the engine the page as text: UTF-8 when the bytes are UTF-8, else
windows-1252 (`native_html_document.ts`), whatever a `meta` says. A declaration is the
document's encoding only when the page is ASCII (its text, comments and attribute values),
where every ASCII-compatible encoding reads the same characters; otherwise, and with no
declaration, the encoding is UTF-8. A byte-level decode of the page by its declaration
(HTML §13.2.3) is the hosts' to add. -/
def documentEncoding (d : L4Factoidal.DOM.Dom) : Encoding.Encoding := Id.run do
  let nodes := d.treeOrder 0 false
  let ascii := fun (x : String) => x.toList.all (fun (c : Char) => c.toNat < 0x80)
  let pageAscii := nodes.all fun (k : Nat) =>
    let n : L4Factoidal.DOM.Node := d.get k
    ascii n.data && n.attrs.all (fun (a : L4Factoidal.DOM.Attr) => ascii a.value)
  if !pageAscii then return .utf_8
  for k in nodes do
    if L4Factoidal.DOM.Dom.isHtmlElement (d.get k) "meta" then
      let label := match attrValue? d k "charset" with
        | some c => some c
        | none =>
          match attrValue? d k "http-equiv", attrValue? d k "content" with
          | some h, some c => if L4Factoidal.DOM.Dom.asciiLower h == "content-type" then extractCharset c else none
          | _, _ => none
      if let some l := label then
        if let some e := Encoding.getEncoding l then
          return match e with
            | .utf_16be | .utf_16le => .utf_8
            | .x_user_defined => .windows_1252
            | e => e
  return .utf_8

/-- The URL parser with an encoding (URL §4.4; HTML "encoding-parse a URL" passes the
document's encoding): the query is percent-encoded after encoding with it. -/
def parseWith (input : String) (base : Option String) (enc : Encoding.Encoding) : Option URL.Url :=
  match base with
  | none => (URL.basicParse input none none none enc).toOption
  | some b => match (URL.basicParse b).toOption with
    | none => none
    | some bu => (URL.basicParse input (some bu) none none enc).toOption

/-! ## The random generator -/

/-- SP 800-90A Table 2: at most 2^48 generate calls between reseeds. This generator is
never reseeded, so the session refuses after that many. -/
def maxDraws : Nat := 1 <<< 48

/-- The entropy a generator needs: 256 bits, HMAC_DRBG-SHA-256's security strength
(SP 800-90A §10.1, Table 2). -/
def minEntropy : Nat := 32

/-- `n` bytes of the session's HMAC_DRBG, over HACL*'s HMAC-SHA-256. Every random byte of
the API (getRandomValues, randomUUID, generated keys, ECDSA nonces) comes from here. The
generator is instantiated from the embedder's entropy on first use; with less than 256
bits of it there is no generator (-6). -/
def randomBytes (s : State) (n : Nat) : Except Int (ByteArray × State) :=
  if s.entropy.size < minEntropy then .error (-6) else
  if s.draws ≥ maxDraws then .error (-6) else
  let h := Crypto.WebHacl.haclHash .sha256
  let d := match s.rng with
    | some d => d
    | none => Crypto.WebCrypto.Drbg.instantiate h s.entropy ByteArray.empty
  let (out, d) := d.generate h n
  .ok (out, { s with rng := some d, draws := s.draws + 1 })

/-- No path draws from an unseeded generator: every successful draw had at least 256
bits of the embedder's entropy. -/
theorem randomBytes_seeded {s s' : State} {n : Nat} {out : ByteArray}
    (h : randomBytes s n = .ok (out, s')) : s.entropy.size ≥ minEntropy ∧ s.draws < maxDraws := by
  unfold randomBytes at h
  by_cases h1 : s.entropy.size < minEntropy
  · rw [if_pos h1] at h; cases h
  · by_cases h2 : s.draws ≥ maxDraws
    · rw [if_neg h1, if_pos h2] at h; cases h
    · exact ⟨by omega, by omega⟩

theorem randomBytes_entropy {s s' : State} {n : Nat} {out : ByteArray}
    (h : randomBytes s n = .ok (out, s')) : s'.entropy = s.entropy ∧ s'.keys.next = s.keys.next := by
  unfold randomBytes at h
  by_cases h1 : s.entropy.size < minEntropy
  · rw [if_pos h1] at h; cases h
  · by_cases h2 : s.draws ≥ maxDraws
    · rw [if_neg h1, if_pos h2] at h; cases h
    · rw [if_neg h1, if_neg h2] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨rfl, rfl⟩

/-! ## crypto.subtle (op 41): keys behind handles -/

section Subtle
open Crypto.WebCryptoKeys

/-- Fields as one answer: a little-endian u32 count, then each as a u32 length and its
bytes (the argument block's own shape; prelude.js `unpack`). -/
def pack (xs : List ByteArray) : ByteArray :=
  xs.foldl (fun acc x => acc ++ u32le x.size ++ x) (u32le xs.length)

def keyFields (handle : Nat) (k : Key) : List ByteArray :=
  let algo := k.algo
  let pairs : List (String × String) :=
    (match algo.hash with | some h => [("hash", h.name)] | none => []) ++
    (if algo.alg == .hmac then [("length", toString algo.length)] else []) ++
    (if algo.curve != "" then [("namedCurve", algo.curve)] else []) ++
    (if algo.alg.isRsa then [("modulusLength", toString algo.modulusLength),
      ("publicExponent", Crypto.bytesToHex algo.publicExponent)] else [])
  ["key", toString handle, k.type.name, if k.extractable then "1" else "0",
    ",".intercalate (k.usages.map (·.name)), algo.alg.name, toString pairs.length].map (·.toUTF8) ++
    pairs.flatMap fun (a, b) => [a.toUTF8, b.toUTF8]

def jwkFields (ms : List (String × JwkVal)) : List ByteArray :=
  ["jwk".toUTF8, (toString ms.length).toUTF8] ++ ms.flatMap fun (n, v) =>
    match v with
    | .str x => [n.toUTF8, "s".toUTF8, x.toUTF8]
    | .bool b => [n.toUTF8, "b".toUTF8, (if b then "true" else "false").toUTF8]
    | .arr xs => [n.toUTF8, "a".toUTF8, ",".intercalate xs |>.toUTF8]

def exportedFields : Exported → List ByteArray
  | .bytes b => ["bytes".toUTF8, b]
  | .jwk ms => jwkFields ms

/-- A JWK as JSON text (wrapKey with format "jwk": §14.3.11 step 12). -/
def jwkJson (ms : List (String × JwkVal)) : String :=
  JSON.toStringCompact (.object (ms.map fun (n, v) => (n, match v with
    | .str x => JSON.Json.string x
    | .bool b => .bool b
    | .arr xs => .array (xs.map .string))))

/-- JSON text to the `j:` members of a JsonWebKey (unwrapKey with format "jwk": "parse a
JWK", §14.3.12 step 14): DataError unless it is an object whose members have the
JsonWebKey types. -/
def jwkOfJson (b : ByteArray) : Res Args := do
  let some text := String.fromUTF8? b | throw .data
  let some (.object ms) := JSON.parseJson? text | throw .data
  ms.foldlM (fun (acc : Args) (n, v) => match n, v with
    | "key_ops", .array xs => xs.foldlM (fun acc x => match x with
        | .string s => .ok (acc.push ("key_ops[]", s.toUTF8))
        | _ => .error .data) (acc.push ("key_ops", ByteArray.empty))
    | "ext", .bool b => .ok (acc.push ("ext", (if b then "true" else "false").toUTF8))
    | "oth", _ => .ok acc
    | n, .string s => if n == "key_ops" || n == "ext" then .error .data else .ok (acc.push (n, s.toUTF8))
    | _, _ => .error .data) #[]

/-- Add a key to the store and answer its fields. -/
def addKey (st : KeyStore) (k : Key) : Res (KeyStore × List ByteArray) := do
  let (st, h) ← st.add k
  return (st, keyFields h k)

/-- §14.3.10 exportKey: the only operation whose answer is a key's own bytes. -/
def exportOp (st : KeyStore) (a : Args) : Res ByteArray :=
  match keyOf st a "key" with
  | .error e => .error e
  | .ok k =>
    match exportKey k ((a.str? "format").getD "") with
    | .error e => .error e
    | .ok e => .ok (pack (exportedFields e))

theorem exportOp_extractable {st : KeyStore} {a : Args} {out : ByteArray} (h : exportOp st a = .ok out) :
    ∃ k, keyOf st a "key" = .ok k ∧ k.extractable = true := by
  unfold exportOp at h
  split at h
  · cases h
  · rename_i k hk
    split at h
    · cases h
    · rename_i e he
      exact ⟨k, hk, exportKey_extractable he⟩

/-- What exportKey answers does not depend on the bytes of any non-extractable key: a
page learns such a key's bytes from no export, whatever handles it passes. -/
theorem exportOp_blind (st : KeyStore) (a : Args) : exportOp st.blind a = exportOp st a := by
  unfold exportOp
  rw [keyOf_blind]
  cases keyOf st a "key" with
  | error e => rfl
  | ok k =>
    by_cases hx : k.extractable = true
    · simp [Except.map, hx]
    · have hf : k.extractable = false := by simpa using hx
      simp only [Except.map, hf, Bool.false_eq_true, if_false]
      rw [← exportKey_blind k _ hf]

/-- Draw `n` random bytes in a key operation (`Res` errors for the generator's -6). -/
def drawFor (s : State) (n : Nat) : Except Int (ByteArray × State) :=
  if n == 0 then .ok (ByteArray.empty, s) else randomBytes s n

def errInt {α : Type} (r : Res α) : Except Int α := r.mapError Err.code

def lengthArg (a : Args) : Option Nat :=
  match a.str? "length" with
  | some "null" | none => none
  | some x => x.toNat?

/-- One `crypto.subtle` operation (`method, k₁, v₁, …`, see `WebCryptoKeys.Args`). -/
def subtle (s : State) (fs : Array ByteArray) : State × Except Int ByteArray :=
  let a := pairsOf fs
  let p := sub a "a:"
  let algName := (p.str? "name").getD ""
  let method := (fs[0]?.bind String.fromUTF8?).getD ""
  let ext := a.bool "extractable"
  let fail := fun (e : Int) => (s, Except.error e)
  match method with
  | "generateKey" =>
    match errInt (usagesOf a), drawFor s (randNeeded algName p) with
    | .error e, _ | _, .error e => fail e
    | .ok us, .ok (rand, s) =>
      match errInt (generateKey algName p ext us rand) with
      | .error e => (s, .error e)
      | .ok (.one k) =>
        match errInt (addKey s.keys k) with
        | .ok (st, f) => ({ s with keys := st }, .ok (pack f))
        | .error e => (s, .error e)
      | .ok (.pair pk sk) =>
        match errInt (do let (st, f1) ← addKey s.keys pk; let (st, f2) ← addKey st sk; pure (st, f1, f2)) with
        | .ok (st, f1, f2) => ({ s with keys := st }, .ok (pack ("pair".toUTF8 :: f1 ++ f2)))
        | .error e => (s, .error e)
  | "importKey" =>
    match errInt (do
        let us ← usagesOf a
        let k ← importKey algName p ((a.str? "format").getD "") ((a.get? "data").getD .empty) (sub a "j:") ext us
        addKey s.keys k) with
    | .ok (st, f) => ({ s with keys := st }, .ok (pack f))
    | .error e => fail e
  | "exportKey" => (s, errInt (exportOp s.keys a))
  -- structuredClone of a CryptoKey: a second handle to the same key (its own lifetime).
  | "cloneKey" =>
    match errInt (do let k ← keyOf s.keys a "key"; addKey s.keys k) with
    | .ok (st, f) => ({ s with keys := st }, .ok (pack f))
    | .error e => fail e
  | "sign" =>
    match errInt (keyOf s.keys a "key") with
    | .error e => fail e
    | .ok k =>
      match drawFor s (if k.algo.alg == .ecdsa then 256 else if k.algo.alg == .rsaPss then min ((p.nat? "saltLength").getD 0) 512 else 0) with
      | .error e => fail e
      | .ok (rand, s) => (s, errInt ((sign algName p k ((a.get? "data").getD .empty) rand).map fun b => pack ["bytes".toUTF8, b]))
  | "verify" => (s, errInt (do
      let k ← keyOf s.keys a "key"
      let ok ← verify algName p k ((a.get? "signature").getD .empty) ((a.get? "data").getD .empty)
      pure (pack ["bool".toUTF8, (if ok then "1" else "0").toUTF8])))
  | "deriveBits" => (s, errInt (do
      let k ← keyOf s.keys a "baseKey"
      let b ← deriveBits algName p k (lengthArg a) s.keys
      pure (pack ["bytes".toUTF8, b])))
  | "deriveKey" =>
    let t := sub a "t:"
    let tName := (t.str? "name").getD ""
    match errInt (do
        let us ← usagesOf a
        let k ← keyOf s.keys a "baseKey"
        keyFor k algName .deriveKey
        let len ← keyLength tName t
        -- §14.3.7: deriveBits with the key's own algorithm (its usage check is deriveKey).
        let k' := { k with usages := k.usages ++ [.deriveBits] }
        let bits ← deriveBits algName p k' len s.keys
        let nk ← importKey tName t "raw" bits #[] ext us
        addKey s.keys nk) with
    | .ok (st, f) => ({ s with keys := st }, .ok (pack f))
    | .error e => fail e
  | "encrypt" | "decrypt" =>
    match errInt (keyOf s.keys a "key") with
    | .error e => fail e
    | .ok k =>
      match drawFor s (if method == "encrypt" && k.algo.alg == .rsaOaep then 64 else 0) with
      | .error e => fail e
      | .ok (rand, s) => (s, errInt ((crypt (method == "encrypt") algName p k ((a.get? "data").getD .empty) rand).map
          fun b => pack ["bytes".toUTF8, b]))
  | "wrapKey" =>
    match drawFor s 64 with
    | .error e => fail e
    | .ok (rand, s) => (s, errInt (do
      let wk ← keyOf s.keys a "wrappingKey"
      if wk.algo.alg.name != algName || !wk.usages.contains .wrapKey then throw .invalidAccess
      let k ← keyOf s.keys a "key"
      let e ← exportKey k ((a.str? "format").getD "")
      let bytes := match e with | .bytes b => b | .jwk ms => (jwkJson ms).toUTF8
      let wk' := { wk with usages := wk.usages ++ [.encrypt] }
      let c ← crypt true algName p wk' bytes rand
      pure (pack ["bytes".toUTF8, c])))
  | "unwrapKey" =>
    let t := sub a "t:"
    match errInt (do
        let us ← usagesOf a
        let uk ← keyOf s.keys a "unwrappingKey"
        if uk.algo.alg.name != algName || !uk.usages.contains .unwrapKey then throw .invalidAccess
        let uk' := { uk with usages := uk.usages ++ [.decrypt] }
        let bytes ← crypt false algName p uk' ((a.get? "data").getD .empty)
        let format := (a.str? "format").getD ""
        let (data, j) ← if format == "jwk" then do pure (ByteArray.empty, ← jwkOfJson bytes) else pure (bytes, #[])
        let nk ← importKey ((t.str? "name").getD "") t format data j ext us
        addKey s.keys nk) with
    | .ok (st, f) => ({ s with keys := st }, .ok (pack f))
    | .error e => fail e
  | _ => fail (-2)

/-- The private parts of an RSA key, handed to `WebHacl.wipe`. -/
def wipeRsa : Option Crypto.WebCryptoKeys.RsaParts → Nat
  | some r => Crypto.WebHacl.wipe r.d + Crypto.WebHacl.wipe r.p + Crypto.WebHacl.wipe r.q +
      Crypto.WebHacl.wipe r.dp + Crypto.WebHacl.wipe r.dq + Crypto.WebHacl.wipe r.qi
  | none => 0

/-- Forget a key (prelude.js calls this when the page's CryptoKey is collected): its bytes
are zeroed in place when the store held the only reference (`WebHacl.wipe`). -/
def dropKey (s : State) (h : Nat) : State × Nat :=
  match s.keys.keys[h]? with
  | none => (s, 0)
  | some k =>
    let keys := s.keys.keys.erase h
    let n := Crypto.WebHacl.wipe k.material + Crypto.WebHacl.wipe k.pub + wipeRsa k.rsa
    ({ s with keys := { s.keys with keys } }, n)

/-- At the end of a session (`WebScripts` close, or a new start): every key's bytes are
handed to `WebHacl.wipe`, which zeroes them where the store held the last reference. The
state is consumed, so the store's references are the last ones unless an answer still
shares the bytes. The answer is the number of bytes handed over. -/
def wipeAll (s : State) : Nat :=
  s.keys.keys.toList.foldl (fun n (_, k) =>
    let m := k.material
    let p := k.pub
    let r := k.rsa
    n + Crypto.WebHacl.wipe m + Crypto.WebHacl.wipe p + wipeRsa r) 0

end Subtle

/-! ## The operations -/

def run (s : State) (op flags : Nat) (fs : Array ByteArray) (dom : L4Factoidal.DOM.Dom := default) :
    State × Except Int ByteArray :=
  let pure' := fun (r : Except Int ByteArray) => (s, r)
  match op with
  | 1 => pure' (ofStr "1")
  -- The document's encoding (the name, as `characterSet` gives it).
  | 9 => pure' (ofStr (match Encoding.getEncoding s.docEncoding with
    | some e => e.name
    | none => (documentEncoding dom).name))
  -- Encoding
  | 2 => pure' do
    match Encoding.TextDecoder.new? (← strArg fs 0) false false with
    | some td => ofStr td.encodingName
    | none => .error (-1)
  | 3 => decode s flags fs
  | 4 => pure' (match Encoding.encodeUtf8? (bytesArg fs 0) with | some b => .ok b | none => .error (-20))
  | 5 => pure' do
    let (read, written, out) := Encoding.encodeIntoUtf8 (← strArg fs 0) (← natArg fs 1)
    .ok (u32le read ++ u32le written ++ out)
  -- URL
  | 10 => pure' do
    let base ← if flag flags 0 then some <$> strArg fs 1 else pure none
    -- flag 2: parse with the output encoding of the encoding labelled by argument 2.
    let enc := if flag flags 1 then
        (match strArg fs 2 with | .ok l => (Encoding.getEncoding l).map Encoding.getOutputEncoding | _ => none).getD .utf_8
      else .utf_8
    match parseWith (← strArg fs 0) base enc with
    | some u => ofStr (components u)
    | none => .error (-1)
  | 11 => pure' do
    match URL.parseUrl (← strArg fs 0) with
    | none => .error (-2)
    | some u => match u.set (← strArg fs 1) (← strArg fs 2) with
      | some u => ofStr (components u)
      | none => .error (-1)
  | 12 => pure' do
    let q ← strArg fs 0
    let q := if flag flags 0 && q.startsWith "?" then String.ofList (q.toList.drop 1) else q
    ofStr (lengthPrefixed ((URL.urlencodedParse q).flatMap fun (n, v) => [n, v]))
  | 13 => pure' do
    let xs := (← (List.range fs.size).mapM (strArg fs)).toArray
    ofStr (URL.urlencodedSerialize ((List.range (xs.size / 2)).map fun k => (xs[2 * k]!, xs[2 * k + 1]!)))
  -- Base64
  | 20 => pure' do match Base64.atob (← strArg fs 0) with | some r => ofStr r | none => .error (-3)
  | 21 => pure' (match strArg fs 0 with
    | .ok d => match Base64.btoa d with | some r => ofStr r | none => .error (-3)
    | .error _ => .error (-3))
  -- Crypto
  | 30 | 31 =>
    match (if op == 30 then natArg fs 0 else .ok 16) with
    | .error e => (s, .error e)
    | .ok n =>
      if n > 65536 then (s, .error (-5)) else
      match randomBytes s n with
      | .error e => (s, .error e)
      | .ok (out, s) => (s, if op == 30 then .ok out else ofStr (Crypto.WebCrypto.uuidOf out))
  | 32 => pure' do
    match Crypto.WebHacl.HashAlg.ofName? (← strArg fs 0) with
    | some h => .ok (Crypto.WebHacl.hashFast h (bytesArg fs 1))
    | none => .error (-23)
  -- The registry: the registered name and the dictionary members to convert.
  | 40 => pure' do
    match Crypto.WebCryptoKeys.normalizeSpec (← strArg fs 0) (← strArg fs 1) with
    | .ok (reg, ms) => ofStr ("\n".intercalate (reg :: ms))
    | .error e => .error e.code
  | 41 => subtle s fs
  | 42 => match natArg fs 0 with
    | .ok h => let (s, n) := dropKey s h; (s, ofStr (toString n))
    | .error e => (s, .error e)
  | _ => pure' (.error (-2))

section
variable {M : Type} [LinearMemory M]

/-- `web_api(op, flags, ptr, len, buf, cap)`. -/
def serve (mem : Nat) (args : Array Value) (s : State) (st : StoreOf M) (dom : L4Factoidal.DOM.Dom := default) :
    State × StoreOf M × HostResult :=
  let buf := arg args 4
  let cap := arg args 5
  if arg args 0 == 0 then
    if s.pending.size ≤ cap then
      let (st, r) := putOut mem st buf cap s.pending
      ({ s with pending := ByteArray.empty }, st, r)
    else (s, st, ret s.pending.size)
  else
  if arg args 3 > maxInput then (s, st, ret (-5)) else
  match st.readMem mem (arg args 2) (arg args 3) with
  | .error _ => (s, st, codeOrTrap (-8))
  | .ok b =>
    match fields b with
    | none => (s, st, ret (-2))
    | some fs =>
      let (s, r) := run s (arg args 0) (arg args 1) fs dom
      match r with
      | .error e => (s, st, ret e)
      | .ok out =>
        if out.size ≤ cap then let (st, r) := putOut mem st buf cap out; (s, st, r)
        else ({ s with pending := out }, st, ret out.size)

end

/-! ## Checks -/


private def runStr (op flags : Nat) (xs : List String) : String :=
  match (run {} op flags (((fields (pack (xs.map (·.toUTF8)))).getD #[]))).2 with
  | .ok b => String.fromUTF8! b
  | .error e => s!"error {e}"

#guard runStr 2 0 [" Latin1 "] == "windows-1252"
#guard runStr 2 0 ["replacement"] == "error -1"
#guard runStr 3 0 ["utf-8", "0", "hé"] == "hé"
#guard runStr 10 1 ["../c?d#e", "http://x/a/b"] ==
  "http://x/c?d#e\x00http://x\x00http:\x00\x00\x00x\x00x\x00\x00/c\x00?d\x00#e\x00"
#guard runStr 10 0 ["not a url"] == "error -1"
#guard (runStr 11 0 ["http://x/", "port", "8080"]).startsWith "http://x:8080/\x00"
#guard runStr 12 1 ["?a=1&b=%20+&a"] == "1:a1:11:b2:  1:a0:"
#guard runStr 13 0 ["a b", "&"] == "a+b=%26"
#guard runStr 20 0 ["YQ=="] == "a"
#guard runStr 21 0 ["Ā"] == "error -3"
#guard runStr 30 0 ["4"] == "error -6"
-- crypto.subtle without HACL* (the interpreter cannot call it): the registry, an HMAC key
-- imported, exported only when extractable, and the errors in order.
#guard runStr 40 0 ["sign", "ecdsa"] == "ECDSA\nhash:h!"
#guard runStr 40 0 ["encrypt", "AES-GCM"] == "error -23"
private def subtleRun (s : State) (xs : List String) : State × String :=
  let (s, r) := run s 41 0 (((fields (pack (xs.map (·.toUTF8)))).getD #[]))
  (s, match r with
    | .ok b => String.intercalate "|" (((fields b).getD #[]).toList.map fun x => (String.fromUTF8? x).getD "?")
    | .error e => s!"error {e}")
private def hmacImport (ext : String) : List String :=
  ["importKey", "format", "raw", "extractable", ext, "usage", "sign", "a:name", "HMAC", "a:hash", "SHA-256", "data", "secret"]
#guard (subtleRun {} (hmacImport "1")).2 == "key|1|secret|1|sign|HMAC|2|hash|SHA-256|length|48"
#guard (let (s, _) := subtleRun {} (hmacImport "1"); (subtleRun s ["exportKey", "format", "raw", "key", "1"]).2) == "bytes|secret"
#guard (let (s, _) := subtleRun {} (hmacImport "0"); (subtleRun s ["exportKey", "format", "raw", "key", "1"]).2) == "error -25"
#guard (let (s, _) := subtleRun {} (hmacImport "1"); (subtleRun s ["exportKey", "format", "jwk", "key", "1"]).2) ==
  "jwk|5|kty|s|oct|k|s|c2VjcmV0|alg|s|HS256|key_ops|a|sign|ext|b|true"
#guard (subtleRun {} ["importKey", "format", "raw", "extractable", "0", "usage", "verify", "usage", "encrypt",
  "a:name", "HMAC", "a:hash", "SHA-256", "data", "k"]).2 == "error -24"
#guard (subtleRun {} ["importKey", "format", "raw", "extractable", "0", "a:name", "HMAC", "a:hash", "SHA-256", "data", "k"]).2 == "error -24"
#guard (subtleRun {} ["exportKey", "format", "raw", "key", "7"]).2 == "error -20"
#guard (subtleRun {} ["generateKey", "extractable", "1", "usage", "sign", "a:name", "HMAC", "a:hash", "SHA-256"]).2 == "error -6"
#guard extractCharset "text/html; charset=EUC-JP" == some "EUC-JP"
#guard extractCharset "text/html; CHARSET = 'big5' " == some "big5"
#guard extractCharset "charset" == none
#guard extractCharset "x; charset=\"unterminated" == none

end L4Factoidal.WasmVM.Hosts.WebApi
