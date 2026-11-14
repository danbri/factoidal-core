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
    primitives HACL*'s (record docs/designissues/2026-11-09-hacl-web-crypto.md);
  * the Web Neural Network API (`WebNN.Api`, op 140): `navigator.ml`, graph building with
    shape inference, and the CPU reference backend (record
    docs/designissues/2026-11-14-webnn.md).

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

Ops 100 to 119 are WebGL's (`PageGl.Api`), 120 to 139 WebCodecs' (`WebCodecs.Api`).

State: the decoders of `TextDecoder`s in the middle of a stream (by the number the page
gave them), the answer that waits, the random generator, and the session's CryptoKeys
(`WebCryptoKeys.Store`: the page holds handles, never key bytes). One call is one operation
on a whole buffer: the boundary is crossed once per `decode`, never per byte.
-/
import L4Factoidal.Rendering.Observe
import L4Factoidal.WasmVM.Hosts.Dom
import L4Factoidal.WHATWG.Encoding.Api
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.WHATWG.Base64
import L4Factoidal.WHATWG.Compression
import L4Factoidal.Crypto.WebCrypto
import L4Factoidal.Crypto.WebCryptoKeys
import L4Factoidal.Net.Xhr
import L4Factoidal.Net.Storage
import L4Factoidal.ClientStorage.IdbOps
import L4Factoidal.ClientStorage.Manager
import L4Factoidal.ClientStorage.Locks
import L4Factoidal.ClientStorage.Buckets
import L4Factoidal.ClientStorage.CookieStore
import L4Factoidal.ClientStorage.CacheStorage
import L4Factoidal.Net.FetchRules
import L4Factoidal.Net.Cookies
import L4Factoidal.Net.ServiceWorkerScope
import L4Factoidal.Net.EventSource
import L4Factoidal.Net.SecureContext
import L4Factoidal.Net.Multipart
import L4Factoidal.DOM.SvgValues
import L4Factoidal.PageGl.Api
import L4Factoidal.WebCodecs.Api
import L4Factoidal.WebNN.Api
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
  /-- The page's network objects (`Net.Xhr`, ops 60 to 79): off unless the embedder
  said `network:true` (ops then answer -2, and `XMLHttpRequest` is not defined). -/
  net : L4Factoidal.Net.Xhr.State := {}
  /-- The page's Web Storage areas (`Net.Storage`, ops 80 to 85): in memory, by origin. -/
  storage : L4Factoidal.Net.Storage.Store := {}
  /-- IndexedDB (`ClientStorage.Idb`, op 200): the databases and live state of each storage
  key, in memory. -/
  idb : L4Factoidal.ClientStorage.Shed L4Factoidal.ClientStorage.Idb.Shelf := {}
  /-- The origin private file system of each storage key (`ClientStorage.Fs`, op 201), in
  memory: no host file is read or written. -/
  opfs : L4Factoidal.ClientStorage.Shed L4Factoidal.ClientStorage.Fs.Shelf := {}
  /-- The lock manager of each storage key (`ClientStorage.Locks`, op 203). -/
  locks : L4Factoidal.ClientStorage.Shed L4Factoidal.ClientStorage.Locks.Shelf := {}
  /-- The storage buckets of each storage key (`ClientStorage.Buckets`, op 205). -/
  buckets : L4Factoidal.ClientStorage.Shed L4Factoidal.ClientStorage.Buckets.Shelf := {}
  /-- The caches of each storage key (`ClientStorage.Caches`, op 206). -/
  caches : L4Factoidal.ClientStorage.Shed L4Factoidal.ClientStorage.Caches.Shelf := {}
  /-- WebGL: the interface tables and the contexts' state (`PageGl.Api`, ops 100 to 119). -/
  gl : L4Factoidal.PageGl.Api.State := {}
  rng : Option Crypto.WebCrypto.Drbg := none
  /-- Generate calls of the generator so far (SP 800-90A's reseed counter). -/
  draws : Nat := 0
  /-- The CryptoKeys of the session. -/
  keys : Crypto.WebCryptoKeys.KeyStore := {}
  /-- The Web Neural Network objects of the session (`WebNN.Graph`, op 140): contexts, graph
  builders, graphs and tensors. Empty until a page uses `navigator.ml`. -/
  nn : L4Factoidal.WebNN.State := {}
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

/-- The seed of a session's `Math.random`: the first 8 bytes (little-endian) of
SHA-256("foafnaut Math.random" ‖ 0 ‖ entropy), and never 0 (xorshift's fixed point). Both
engines' `Math.random` is xorshift, not a cryptographic generator, and its outputs give
its state away: the hash keeps them from telling anything of the session's entropy, which
also seeds the HMAC_DRBG. `none` without entropy (the engine keeps its own seed).

Used by BubblePopJS's dedicated workers (`Hosts.LeanJSWorkers.start`), each with its own
entropy; without it every worker had the realm snapshot's constant seed (cryptosec
finding F2, record 2026-11-09-crypto-boundary-security.md on wip/cryptosec, which defines
the same function for pages). -/
def mathRandomSeed (entropy : ByteArray) : Option UInt64 :=
  if entropy.size < minEntropy then none else
  let d := Crypto.WebHacl.hashFast .sha256 ("foafnaut Math.random".toUTF8 ++ ByteArray.mk #[0] ++ entropy)
  let x := (List.range 8).foldl (fun (acc : UInt64) i => acc ||| ((d.get! i).toUInt64 <<< (8 * i).toUInt64)) 0
  some (if x == 0 then 1 else x)

/-- Kind: safety property of the seed.
Says: a seed `mathRandomSeed` gives is never 0, xorshift's fixed point, so `Math.random`
never sticks at one value.
Does not say: anything about the quality or secrecy of the seed, or of xorshift. -/
theorem mathRandomSeed_ne_zero {e : ByteArray} {x : UInt64} (h : mathRandomSeed e = some x) : x ≠ 0 := by
  unfold mathRandomSeed at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    split
    · decide
    · rename_i hx; simpa using hx

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

/-- Kind: security invariant (key material). Says: the fields the page receives for a key
(what its `CryptoKey` object is made from: handle, type, extractable, usages, algorithm) are
the same whatever the key's bytes: generateKey, importKey, deriveKey, unwrapKey, cloneKey and
getPublicKey answer with these fields and nothing else of the key, so none of them hands key
bytes to script. For RSA the public exponent and modulus length are in the algorithm, as the
API requires; they are public. Does not say: anything of exportKey and wrapKey
(`exportOp_blind`, `wrapPlain_blind`) or of the outputs of primitives keyed by the bytes. -/
theorem keyFields_blind (handle : Nat) (k : Key) : keyFields handle k.blind = keyFields handle k := rfl

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
    -- Presence only: a multi-prime RSA key is refused by the import (`importRsa`).
    | "oth", _ => .ok (acc.push ("oth", ByteArray.empty))
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
        -- "get key length" reads its own dictionary (prefix `g:`; AES's `length`).
        let g := sub a "g:"
        let len ← keyLength tName (if g.isEmpty then t else g)
        -- §14.3.7: deriveBits with the key's own algorithm (its usage check is deriveKey).
        let k' := { k with usages := k.usages ++ [.deriveBits] }
        -- A derived key this engine has no keys for (AES): the derivation's errors, then the
        -- import's refusal, with no bits derived (`deriveBitsCheck`).
        let bits ← if (algOf? tName).isNone then do
            deriveBitsCheck algName p k' len s.keys
            pure (ByteArray.mk (Array.replicate ((len.getD 0 + 7) / 8) 0))
          else deriveBits algName p k' len s.keys
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
      -- The key's bytes come from exportKey alone (`wrapPlain_extractable`, `wrapPlain_blind`).
      let bytes ← wrapPlain (fun ms => (jwkJson ms).toUTF8) k ((a.str? "format").getD "")
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
  -- getPublicKey (modern algorithms draft): a new handle for the public key of a private key.
  | "getPublicKey" =>
    match errInt (do
        let us ← usagesOf a
        let k ← keyOf s.keys a "key"
        let pk ← getPublicKey k us
        addKey s.keys pk) with
    | .ok (st, f) => ({ s with keys := st }, .ok (pack f))
    | .error e => fail e
  -- SubtleCrypto.supports: a question of the registry, no key made or used.
  | "supports" =>
    let yes := supports ((a.str? "op").getD "") algName p (sub a "t:") (sub a "g:") (lengthArg a) s.keys
    (s, .ok (pack ["bool".toUTF8, (if yes then "1" else "0").toUTF8]))
  | _ => fail (-2)

/-- The method name of a `subtle` call. -/
def subtleMethod (fs : Array ByteArray) : String := (fs[0]?.bind String.fromUTF8?).getD ""

/-- Kind: API contract. Says: `subtle` with the method "exportKey" changes no state and
answers exactly `exportOp` of the session's keys: the export rule in Lean is the whole of what
the operation does. Does not say: what prelude.js does with the answer (it shapes the
ArrayBuffer or the JsonWebKey object from these fields). -/
theorem subtle_exportKey (s : State) (fs : Array ByteArray) (h : subtleMethod fs = "exportKey") :
    subtle s fs = (s, errInt (exportOp s.keys (pairsOf fs))) := by
  unfold subtleMethod at h
  unfold subtle
  simp only [h]

/-- Kind: security invariant (key material), over the API's function. Says: what
`crypto.subtle.exportKey` answers to the page is the same when the bytes of every
non-extractable key of the session are replaced: whatever handle and format the page passes,
it learns nothing of such a key from this operation. With `wrapPlain_blind` (wrapKey reads a key
only through the same export) and `keyFields_blind` (the answers that carry a key carry its
public fields only), exportKey and wrapKey of an extractable key are the only ways key bytes
reach script. Does not say: anything of what the outputs of sign, encrypt or deriveBits reveal
about a key: that is the primitives' strength, HACL*'s and the algorithms'. -/
theorem subtle_exportKey_blind (s : State) (fs : Array ByteArray) (h : subtleMethod fs = "exportKey") :
    (subtle { s with keys := s.keys.blind } fs).2 = (subtle s fs).2 := by
  rw [subtle_exportKey _ _ h, subtle_exportKey _ _ h]
  show errInt (exportOp s.keys.blind (pairsOf fs)) = errInt (exportOp s.keys (pairsOf fs))
  rw [exportOp_blind]

/-- Kind: security invariant (usages), over the API's function. Says: `crypto.subtle.sign`
with a key that lacks the usage "sign" always answers an error, whatever the algorithm,
parameters, data and the state of the random generator: no signature is ever answered. The
error is the generator's when the draw of random bytes fails first, and InvalidAccessError
otherwise (`sign_no_usage`: the signing function is that constant, so no primitive ran).
Does not say: the same of verify, deriveBits, encrypt and decrypt at this level; for them
the statement is on the operation's function (`verify_no_usage`, `deriveBits_no_usage`,
`crypt_no_usage`), which `subtle` calls with the key the page named. -/
theorem subtle_sign_no_usage (s : State) (fs : Array ByteArray) (h : subtleMethod fs = "sign") (k : Key)
    (hk : keyOf s.keys (pairsOf fs) "key" = .ok k) (hu : k.usages.contains .sign = false) :
    ∃ e, (subtle s fs).2 = .error e := by
  unfold subtleMethod at h
  unfold subtle
  simp only [h, hk, errInt, Except.mapError]
  split
  · rename_i e _; exact ⟨e, rfl⟩
  · rename_i rand s' _
    refine ⟨Err.invalidAccess.code, ?_⟩
    rw [sign_no_usage hu]
    rfl

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
  -- Observers of layout (`Rendering/Observe.lean`). 170: one intersection observation from
  -- rectangles in layout units, a root margin and thresholds; 171: a root margin as
  -- `IntersectionObserver.rootMargin` reads it back, or an error for one that does not parse.
  | 170 => pure' do match L4Factoidal.Rendering.Observe.entryText (← strArg fs 0) with | some r => ofStr r | none => .error (-1)
  | 171 => pure' do match L4Factoidal.Rendering.Observe.margin? (← strArg fs 0) with
    | some m => ofStr (L4Factoidal.Rendering.Observe.marginText m)
    | none => .error (-3)
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
  -- digest: the name as registered, the data, then the normalized algorithm's members
  -- (`a:` pairs, read by SHA-3 and cSHAKE only).
  | 32 => pure' do
    let name ← strArg fs 0
    match Crypto.WebHacl.HashAlg.ofName? name with
    | some h => .ok (Crypto.WebHacl.hashFast h (bytesArg fs 1))
    | none =>
      let p := Crypto.WebCryptoKeys.sub (Crypto.WebCryptoKeys.pairsOf (fs.extract 1 fs.size)) "a:"
      (Crypto.WebCryptoKeys.digestExt name p (bytesArg fs 1)).mapError (·.code)
  -- The registry: the registered name and the dictionary members to convert.
  | 40 => pure' do
    match Crypto.WebCryptoKeys.normalizeSpec (← strArg fs 0) (← strArg fs 1) with
    | .ok (reg, ms) => ofStr ("\n".intercalate (reg :: ms))
    | .error e => .error e.code
  | 41 => subtle s fs
  -- Compression Standard: 50 compress, 51 decompress, 52 the format, 53 ask again (WHATWG.Compression.op)
  | 50 | 51 | 52 | 53 => pure' do L4Factoidal.WHATWG.Compression.op op (← strArg fs 0) (bytesArg fs 1)
  -- Secure Contexts: is the environment with this top-level creation URL a secure context
  -- ("1" or "0"); decides whether the `[SecureContext]` members of `crypto` exist.
  | 43 => pure' do ofStr (if L4Factoidal.Net.SecureContext.secureContext (← strArg fs 0) then "1" else "0")
  | 42 => match natArg fs 0 with
    | .ok h => let (s, n) := dropKey s h; (s, ofStr (toString n))
    | .error e => (s, .error e)
  | code =>
    if (60 ≤ code && code < 80) || code == 98 || code == 99 || (150 ≤ code && code ≤ 153) then
      let (net, r) := L4Factoidal.Net.Xhr.op s.net code fs
      ({ s with net }, r)
    -- Web Storage: the area is named by the session's page origin, never by an argument.
    else if 80 ≤ code && code < 86 then
      let (storage, r) := L4Factoidal.Net.Storage.op s.storage s.net.page.origin code fs
      ({ s with storage }, r)
    -- IndexedDB: one command (its name is the first argument) on the shelf of the session's
    -- storage key, which is the page's origin, never an argument. The answer is its tokens.
    else if code == 200 then
      let (idb, out) := L4Factoidal.ClientStorage.Idb.opFor s.idb { origin := s.net.page.origin } fs
      ({ s with idb }, .ok (pack out))
    -- The File System API (201) and StorageManager (202), for the same storage key.
    else if code == 201 then
      let (opfs, out) := L4Factoidal.ClientStorage.Fs.opFor s.opfs { origin := s.net.page.origin } fs
      ({ s with opfs }, .ok (pack out))
    else if code == 202 then
      (s, .ok (pack (L4Factoidal.ClientStorage.Manager.op s.idb s.opfs s.caches { origin := s.net.page.origin } fs)))
    -- Web Locks (203): the lock manager of the same storage key.
    else if code == 203 then
      let (locks, out) := L4Factoidal.ClientStorage.Locks.opFor s.locks { origin := s.net.page.origin } fs
      ({ s with locks }, .ok (pack out))
    -- The Cookie Store API (204): the jar of `document.cookie`; the host and the secure flag are
    -- the session's page's, never arguments.
    else if code == 204 then
      let (cookies, out) := L4Factoidal.ClientStorage.CookieStore.op s.net.cookies s.net.page.origin s.net.page.secure fs
      ({ s with net := { s.net with cookies } }, .ok (pack out))
    -- The Cache API (206): the caches of the same storage key.
    else if code == 206 then
      let (caches, out) := L4Factoidal.ClientStorage.Caches.opFor s.caches { origin := s.net.page.origin } fs
      ({ s with caches }, .ok (pack out))
    -- Storage Buckets (205): the buckets of the same storage key.
    else if code == 205 then
      let (buckets, out) := L4Factoidal.ClientStorage.Buckets.opFor s.buckets { origin := s.net.page.origin } fs
      ({ s with buckets }, .ok (pack out))
    -- Blob URLs (File API §8.3): 90 `createObjectURL(type, bytes)`, 91 `revokeObjectURL(url)`.
    -- The store is the network state's and names each URL's origin (the session's page
    -- origin, never an argument); the UUID is drawn here.
    else if code == 90 then
      match randomBytes s 16 with
      | .error e => (s, .error e)
      | .ok (r, s) =>
        match L4Factoidal.Net.BlobUrls.add s.net.blobs s.net.page.origin (Crypto.WebCrypto.uuidOf r)
            ((strArg fs 0).toOption.getD "") (bytesArg fs 1) with
        | some (blobs, url) => ({ s with net := { s.net with blobs } }, ofStr url)
        | none => (s, .error (-5))
    else if code == 91 then
      ({ s with net := { s.net with blobs :=
          L4Factoidal.Net.BlobUrls.revoke s.net.blobs s.net.page.origin ((strArg fs 0).toOption.getD "") } }, ofStr "")
    -- The Fetch API's rules: MIME type of a body, `Headers` validation, a `Request`'s method.
    else if 86 ≤ code && code < 90 then pure' (L4Factoidal.Net.FetchRules.op code fs)
    -- `document.cookie`: the host and the secure flag are the session's page's, never arguments.
    else if code == 96 || code == 97 then
      -- the jar is the network's too (`Net.Xhr.State.cookies`); the time a script gives is kept
      let (cookies, r) := L4Factoidal.Net.Cookies.op s.net.cookies s.net.page.origin s.net.page.secure code fs
      let now := max s.net.now ((L4Factoidal.Net.Cookies.strAt fs 1).toNat?.getD 0)
      ({ s with net := { s.net with cookies, now } }, r)
    -- The values the SVG DOM reflects: a length, a number, a number list, a transform list.
    else if 92 ≤ code && code < 96 then pure' (L4Factoidal.DOM.SvgValues.op code fs)
    -- WebGL: the rendering context interfaces (and, later ops, the contexts' state machine).
    else if 100 ≤ code && code < 120 then
      let (gl, r) := L4Factoidal.PageGl.Api.op s.gl code fs
      ({ s with gl }, r)
    -- WebCodecs: frame layouts and copy plans, configuration checks (pure functions of the arguments).
    else if 120 ≤ code && code < 140 then pure' (L4Factoidal.WebCodecs.Api.op code fs)
    -- The Web Neural Network API (`L4Factoidal.WebNN.api`): one command and its arguments.
    else if code == 140 then
      let (nn, out) := L4Factoidal.WebNN.api s.nn fs
      ({ s with nn }, .ok out)
    -- Service workers: `register()`'s URL checks and registration matching (pure, no state).
    else if code == 154 || code == 155 then pure' (L4Factoidal.Net.ServiceWorkerScope.op code fs)
    -- EventSource: whether a response is an event stream, and its events (Net.EventSource);
    -- fields: the last event ID, the reconnection time, the status, the type, the bytes.
    else if code == 162 then
      let str := fun (i : Nat) => (strArg fs i).toOption.getD ""
      if !L4Factoidal.Net.EventSource.isStream ((str 2).toNat?.getD 0) (str 3) then pure' (ofStr "{\"stream\":false}") else
      let p : L4Factoidal.Net.EventSource.Parser := { lastEventId := str 0, idBuffer := str 0, retry := (str 1).toNat? }
      let (p, evs) := L4Factoidal.Net.EventSource.parse p (L4Factoidal.WHATWG.Encoding.utf8DecodeWithoutBOM (bytesArg fs 4))
      let j := L4Factoidal.JSON.Json.object [("stream", .bool true), ("id", .string p.lastEventId),
        ("retry", match p.retry with | some r => .number (toString r) | none => .null),
        ("events", .array (evs.map fun e => .array [.string e.type, .string e.data, .string e.lastEventId]))]
      pure' (ofStr j.toString)
    -- A multipart/form-data body's entries (`formData()`, Net.Multipart): empty is a failure.
    else if code == 164 then pure' (.ok (L4Factoidal.Net.Multipart.op fs))
    -- A close code and reason (`WebSocketError`, Net.WebSocket.closeCheck): "" or the exception.
    else if code == 163 then
      let str := fun (i : Nat) => (strArg fs i).toOption.getD ""
      match L4Factoidal.Net.WebSocket.closeCheck (str 0).toNat? (str 1) with
      | some (n, m) => pure' (ofStr ("err\u0000" ++ n ++ "\u0000" ++ m))
      | none => pure' (ofStr "")
    -- WebSocket (Net.WebSocket through Net.Xhr): the key and each masking key are fresh
    -- bytes of the engine's generator; only a page with the network on has connections.
    else if 156 ≤ code && code ≤ 161 then
      if !s.net.enabled then pure' (.error (-2)) else
      let want := if code == 156 then 96 else if code == 157 || code == 158 then 4 else 0
      if want == 0 then
        let (net, r) := L4Factoidal.Net.Xhr.wsOp s.net code fs ByteArray.empty
        ({ s with net }, r)
      else
        match randomBytes s want with
        | .error e => (s, .error e)
        | .ok (e, s) =>
          let (net, r) := L4Factoidal.Net.Xhr.wsOp s.net code fs e
          ({ s with net }, r)
    else pure' (.error (-2))

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
