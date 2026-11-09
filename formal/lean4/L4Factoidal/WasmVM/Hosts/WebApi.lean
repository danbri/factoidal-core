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

/-- What Lean makes of the host's answer to a crypto request. -/
inductive HostKind where
  | key (extractable : Bool) | bytes | bool | jwk
  deriving Inhabited

structure HostWait where
  /-- The page's callback (a prelude callback handle) that takes the answer, in a task. -/
  wake : Nat
  kind : HostKind
  deriving Inhabited

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
  /-- crypto.subtle's primitives are the host's (the Hub: the browser's own crypto.subtle,
  `Page.Limits.cryptoHost`); Lean still decides every rule. -/
  hostMode : Bool := false
  /-- Requests for the host, given with the next turn's answer (`crypto`). -/
  hostReqs : Array JSON.Json := #[]
  /-- Requests the host has not answered: the page's callback to wake and what to make of
  the answer. -/
  hostWaits : Std.HashMap Nat HostWait := {}
  /-- Answers the page has not yet taken (op 43). -/
  hostAnswers : Std.HashMap Nat (Except Int ByteArray) := {}
  nextReq : Nat := 1
  /-- Work done so far (`opWork` units), charged to script time by `Page.serveExtra`. -/
  work : Nat := 0
  deriving Inhabited

/-- The state a session starts with (every engine: `Page.start`, `PageAot`, `LeanJS.start`):
its own entropy and settings, and nothing of any earlier session. -/
def State.fresh (entropy : ByteArray) (docEncoding : String) (hostMode : Bool) : State :=
  { entropy, docEncoding, hostMode }

/-- A session starts with no random generator (it is instantiated from this session's own
entropy on first use: `randomBytes`), no draws, no keys, handles from 1, no pending answer
and no work. So no generator state, key or answer comes from a snapshot, a realm or another
session. -/
theorem State.fresh_clean (e : ByteArray) (d : String) (m : Bool) :
    (State.fresh e d m).rng = none ∧ (State.fresh e d m).draws = 0 ∧ (State.fresh e d m).keys.keys.isEmpty ∧
    (State.fresh e d m).keys.next = 1 ∧ (State.fresh e d m).keys.bytes = 0 ∧ (State.fresh e d m).pending.size = 0 ∧
    (State.fresh e d m).work = 0 ∧ (State.fresh e d m).entropy = e := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp [State.fresh]

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

Before this, every session of a process had the same `Math.random` sequence: BubblePopJS's
seed was a constant in its realm snapshot, and QuickJS-NG's was set once when the guest was
prepared (cryptosec finding F2, record 2026-11-09-crypto-boundary-security.md). -/
def mathRandomSeed (entropy : ByteArray) : Option UInt64 :=
  if entropy.size < minEntropy then none else
  let d := Crypto.WebHacl.hashFast .sha256 ("foafnaut Math.random".toUTF8 ++ ByteArray.mk #[0] ++ entropy)
  let x := (List.range 8).foldl (fun (acc : UInt64) i => acc ||| ((d.get! i).toUInt64 <<< (8 * i).toUInt64)) 0
  some (if x == 0 then 1 else x)

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

/-- The first draw of a fresh session instantiates the generator from that session's
entropy, and from nothing else. -/
theorem randomBytes_fresh (e : ByteArray) (d : String) (m : Bool) (n : Nat) (h : e.size ≥ 32) :
    randomBytes (State.fresh e d m) n =
      .ok ((Crypto.WebCrypto.Drbg.instantiate (Crypto.WebHacl.haclHash .sha256) e ByteArray.empty).generate
        (Crypto.WebHacl.haclHash .sha256) n |>.1,
        { State.fresh e d m with
          rng := some ((Crypto.WebCrypto.Drbg.instantiate (Crypto.WebHacl.haclHash .sha256) e ByteArray.empty).generate
            (Crypto.WebHacl.haclHash .sha256) n |>.2), draws := 1 }) := by
  unfold randomBytes
  have h1 : ¬ (State.fresh e d m).entropy.size < minEntropy := by simp [State.fresh, minEntropy]; omega
  have h2 : ¬ (State.fresh e d m).draws ≥ maxDraws := by simp [State.fresh, maxDraws]
  rw [if_neg h1, if_neg h2]
  rfl

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
  let some (.object ms0) := JSON.parseJson? text | throw .data
  -- A member named twice: the last one, as JSON.parse and the IDL conversion would make it
  -- (cryptosec F15: Lean read the first, so one wrapped key had two meanings). One pass.
  let ms := (ms0.reverse.foldl (fun ((seen, acc) : Std.HashSet String × List (String × JSON.Json)) (n, v) =>
    if seen.contains n then (seen, acc) else (seen.insert n, (n, v) :: acc)) ({}, [])).2
  ms.foldlM (fun (acc : Args) (n, v) => match n, v with
    | "key_ops", .array xs => xs.foldlM (fun acc x => match x with
        | .string s => .ok (acc.push ("key_ops[]", s.toUTF8))
        | _ => .error .data) (acc.push ("key_ops", ByteArray.empty))
    | "ext", .bool b => .ok (acc.push ("ext", (if b then "true" else "false").toUTF8))
    | "oth", _ => .ok (acc.push ("oth", ByteArray.empty))  -- Lean refuses a multi-prime key (F14)
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
      match drawFor s (if k.algo.alg == .ecdsa then 32 else if k.algo.alg == .rsaPss then min ((p.nat? "saltLength").getD 0) 512 else 0) with
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
  | some r => r.d.wipe + r.p.wipe + r.q.wipe + r.dp.wipe + r.dq.wipe + r.qi.wipe
  | none => 0

/-- Forget a key (prelude.js calls this when the page's CryptoKey is collected): its bytes
are zeroed in place when the store held the only reference (`WebHacl.wipe`). -/
def dropKey (s : State) (h : Nat) : State × Nat :=
  match s.keys.keys[h]? with
  | none => (s, 0)
  | some k =>
    let keys := s.keys.keys.erase h
    let n := k.secret.wipe + Crypto.WebHacl.wipe k.pub + wipeRsa k.rsa
    -- The browser's CryptoKey goes when no Lean key (a structuredClone copy) still names it.
    let reqs := match k.host with
      | some hh => if keys.fold (fun found _ k' => found || k'.host == some hh) false then s.hostReqs
        else s.hostReqs.push (.object [("id", .number "0"), ("op", .string "drop"), ("key", .number (toString hh))])
      | none => s.hostReqs
    ({ s with keys := { s.keys with keys, bytes := s.keys.bytes - k.footprint }, hostReqs := reqs }, n)

/-- At the end of a session (`WebScripts` close, or a new start): every key's bytes are
zeroed in place (`WebHacl.zeroNow`): the session and everything in it is being dropped, so
no holder that lives on shares them. (Reference-counted `wipe` zeroed none here: the
store, the session and the held state all still referenced each key while it ran.) The
answer is the number of bytes zeroed. -/
def wipeAll (s : State) : Nat :=
  s.keys.keys.toList.foldl (fun n (_, k) =>
    let m := k.secret
    let p := k.pub
    let z := Crypto.WebHacl.zeroNow
    n + m.zeroNow + z p + (match k.rsa with
      | some r => r.d.zeroNow + r.p.zeroNow + r.q.zeroNow + r.dp.zeroNow + r.dq.zeroNow + r.qi.zeroNow
      | none => 0)) 0

end Subtle


/-! ## crypto.subtle on the Hub: the browser does the primitives

With `hostMode` (the Hub, `Page.Limits.cryptoHost`), an operation is decided here as
natively: the registry, the usages, extractability, the key types, the JWK members, the
error of each refusal. What is left, the primitive, is a request to the host (the
browser's crypto.subtle, `labs/demos/foafnaut/crypto_host.mjs`). Keys are the browser's
CryptoKeys in the host's table; Lean holds their attributes and the host's number, never
their bytes. The page's promise waits on a callback that Lean queues as a task when the
host answers (`hostDone`). Record docs/designissues/2026-11-09-hacl-web-crypto.md, "The
Hub". -/

section Host
open Crypto.WebCryptoKeys

def b64url (b : ByteArray) : String := JOSE.Base64Url.encode b

/-- A member of a normalized algorithm for the host, by its WebIDL type (`normalizeSpec`). -/
def memberJson (st : KeyStore) (t : String) (v : ByteArray) : Res JSON.Json := do
  let str := (String.fromUTF8? v).getD ""
  match t with
  | "h" => return .object [("name", .string str)]
  | "b" | "n" => return .object [("$b", .string (b64url v))]
  | "l" | "o" => return .number (toString (str.toNat?.getD 0))
  | "k" =>
    let some k := (str.toNat?).bind (st.keys[·]?) | throw .typeError
    let some h := k.host | throw .invalidAccess
    return .object [("$key", .number (toString h))]
  | _ => return .string str

/-- The normalized algorithm `p` (op `op`) as the host's dictionary. -/
def algJson (st : KeyStore) (op : String) (p : Args) : Res JSON.Json := do
  let name := (p.str? "name").getD ""
  let (reg, ms) ← normalizeSpec op name true
  let members ← ms.foldlM (fun (acc : List (String × JSON.Json)) m => do
    let k := (m.splitOn ":").headD ""
    let t := ((m.splitOn ":").getD 1 "").replace "!" ""
    match p.get? k with
    | some v => return acc ++ [(k, ← memberJson st t v)]
    | none => return acc) []
  return .object (("name", .string reg) :: members)

def hostKeyOf (st : KeyStore) (a : Args) (field : String) : Res (Key × Nat) := do
  let k ← keyOf st a field
  let some h := k.host | throw .invalidAccess
  return (k, h)

def numJ (n : Nat) : JSON.Json := .number (toString n)
def bytesJ (b : ByteArray) : JSON.Json := .object [("$b", .string (b64url b))]
def usagesJ (us : List Usage) : JSON.Json := .array (us.map (.string ∘ Usage.name))

/-- A JsonWebKey (`j:` members) as JSON for the host. -/
def jwkJsonOf (j : Args) : JSON.Json :=
  let ops := (j.all "key_ops[]").filterMap String.fromUTF8?
  .object (j.toList.filterMap fun (k, v) =>
    if k == "key_ops[]" then none
    else if k == "key_ops" then some (k, .array (ops.map .string))
    else if k == "ext" then some (k, .bool (v == "true".toUTF8))
    else some (k, .string ((String.fromUTF8? v).getD "")))

def isSecretAlg (a : Alg) : Bool :=
  a == .hmac || a == .hkdf || a == .pbkdf2 || a == .chacha || a.isAes

/-- The key type an import makes, from its format and data (§14.3.9 and each algorithm). -/
def importType (alg : Alg) (format : String) (j : Args) : KeyType :=
  if isSecretAlg alg then .secret
  else if format == "pkcs8" then .privateKey
  else if format == "jwk" then (if j.has "d" then .privateKey else .publicKey)
  else .publicKey

def useOf (alg : Alg) : String :=
  if alg == .ecdsa || alg == .ed25519 || alg == .hmac || alg == .rsaPkcs1 || alg == .rsaPss then "sig" else "enc"

/-- The checks of one operation and its request to the host: the request's fields (with
"op") and the kind of answer. -/
def hostPlan (st : KeyStore) (method : String) (a : Args) : Res (List (String × JSON.Json) × HostKind) := do
  let p := sub a "a:"
  let algName := (p.str? "name").getD ""
  let ext := a.bool "extractable"
  let data := (a.get? "data").getD .empty
  match method with
  | "digest" =>
    return ([("op", .string "digest"), ("algorithm", .object [("name", .string algName)]), ("data", bytesJ data)], .bytes)
  | "generateKey" =>
    let us ← usagesOf a
    let some alg := algOf? algName | throw .notSupported
    if isSecretAlg alg then
      checkUsages (allowedUsages alg .secret) us
      if alg.isAes && !([128, 192, 256].contains ((p.nat? "length").getD 0)) then throw .operation
      if alg == .hmac && p.nat? "length" == some 0 then throw .operation
    else
      checkUsages (allowedUsages alg .publicKey ++ allowedUsages alg .privateKey) us
      if alg == .ecdsa || alg == .ecdh then
        if !(["P-256", "P-384", "P-521"].contains ((p.str? "namedCurve").getD "")) then throw .notSupported
    return ([("op", .string "generateKey"), ("algorithm", ← algJson st "generateKey" p), ("extractable", .bool ext),
      ("usages", usagesJ us)], .key ext)
  | "importKey" =>
    let us ← usagesOf a
    let some alg := algOf? algName | throw .notSupported
    let format := (a.str? "format").getD ""
    let j := sub a "j:"
    if (alg == .hkdf || alg == .pbkdf2) && format != "raw" && format != "raw-secret" then throw .notSupported
    checkUsages (allowedUsages alg (importType alg format j)) us
    if (alg == .hkdf || alg == .pbkdf2) && ext then throw .syntax
    if format == "jwk" then jwkCommon j us ext (useOf alg)
    -- A P-256 public point is Lean's to check (hostile input), not left to the host.
    if (alg == .ecdsa || alg == .ecdh) && (p.str? "namedCurve") == some "P-256" then
      let point : Option ByteArray :=
        if format == "raw" || format == "raw-public" then some data
        else if format == "spki" then
          match readSpki data.toList with
          | some (oid, _, key) => if oid == oidEcPublicKey then some (ByteArray.mk key.toArray) else none
          | none => none
        else if format == "jwk" then
          match (j.str? "x").bind unb64?, (j.str? "y").bind unb64? with
          | some x, some y => if x.size == 32 && y.size == 32 then some (ByteArray.mk #[4] ++ x ++ y) else none
          | _, _ => none
        else none
      if let some pt := point then
        if pt.size == 65 && pt.get! 0 == 4 && !p256OnCurve (pt.extract 1 65) then throw .data
      -- And a private scalar, 0 < d < n.
      let d : Option ByteArray :=
        if format == "jwk" then (j.str? "d").bind unb64?
        else if format == "pkcs8" then
          match readPkcs8 data.toList with
          | some (_, _, pk) =>
            match expect 0x30 pk with
            | some (ec, _) => match expect 0x02 ec with
              | some (_, r) => (expect 0x04 r).map fun (x, _) => ByteArray.mk x.toArray
              | none => none
            | none => none
          | none => none
        else none
      if let some dv := d then
        if dv.size == 32 && !p256ScalarOk dv then throw .data
    let keyData := if format == "jwk" then jwkJsonOf j else bytesJ data
    return ([("op", .string "importKey"), ("format", .string format), ("keyData", keyData),
      ("algorithm", ← algJson st "importKey" p), ("extractable", .bool ext), ("usages", usagesJ us)], .key ext)
  | "exportKey" =>
    let (k, h) ← hostKeyOf st a "key"
    if k.algo.alg == .hkdf || k.algo.alg == .pbkdf2 then throw .notSupported
    if !k.extractable then throw .invalidAccess
    let format := (a.str? "format").getD ""
    return ([("op", .string "exportKey"), ("format", .string format), ("key", numJ h)],
      if format == "jwk" then .jwk else .bytes)
  | "sign" | "verify" =>
    let (k, h) ← hostKeyOf st a "key"
    keyFor k algName (if method == "sign" then .sign else .verify)
    if k.type != .secret && k.type != (if method == "sign" then .privateKey else .publicKey) then throw .invalidAccess
    return ([("op", .string method), ("algorithm", ← algJson st method p), ("key", numJ h), ("data", bytesJ data)] ++
      (if method == "verify" then [("signature", bytesJ ((a.get? "signature").getD .empty))] else []),
      if method == "sign" then .bytes else .bool)
  | "encrypt" | "decrypt" =>
    let (k, h) ← hostKeyOf st a "key"
    keyFor k algName (if method == "encrypt" then .encrypt else .decrypt)
    if k.type != .secret && k.type != (if method == "encrypt" then .publicKey else .privateKey) then throw .invalidAccess
    return ([("op", .string method), ("algorithm", ← algJson st method p), ("key", numJ h), ("data", bytesJ data)], .bytes)
  | "deriveBits" =>
    let (k, h) ← hostKeyOf st a "baseKey"
    keyFor k algName .deriveBits
    if k.algo.alg == .ecdh || k.algo.alg == .x25519 then
      if k.type != .privateKey then throw .invalidAccess
      let pk ← keyOf st p "public"
      if pk.type != .publicKey || pk.algo.alg != k.algo.alg then throw .invalidAccess
      -- §24.3 deriveBits step 6: the curves must be the same (as natively; cryptosec F10).
      if k.algo.alg == .ecdh && pk.algo.curve != k.algo.curve then throw .invalidAccess
    let len : JSON.Json := match a.str? "length" with | some "null" | none => .null | some x => numJ (x.toNat?.getD 0)
    return ([("op", .string "deriveBits"), ("algorithm", ← algJson st "deriveBits" p), ("baseKey", numJ h),
      ("length", len)], .bytes)
  | "deriveKey" =>
    let us ← usagesOf a
    let (k, h) ← hostKeyOf st a "baseKey"
    keyFor k algName .deriveKey
    return ([("op", .string "deriveKey"), ("algorithm", ← algJson st "deriveBits" p), ("baseKey", numJ h),
      ("derivedKeyType", ← algJson st "importKey" (sub a "t:")), ("extractable", .bool ext), ("usages", usagesJ us)], .key ext)
  | "wrapKey" =>
    let (wk, wh) ← hostKeyOf st a "wrappingKey"
    if wk.algo.alg.name != algName || !wk.usages.contains .wrapKey then throw .invalidAccess
    let (k, h) ← hostKeyOf st a "key"
    if k.algo.alg == .hkdf || k.algo.alg == .pbkdf2 then throw .notSupported
    if !k.extractable then throw .invalidAccess
    let alg ← match algJson st "wrapKey" p with | .ok j => pure j | .error _ => algJson st "encrypt" p
    return ([("op", .string "wrapKey"), ("format", .string ((a.str? "format").getD "")), ("key", numJ h),
      ("wrappingKey", numJ wh), ("algorithm", alg)], .bytes)
  | "unwrapKey" =>
    let us ← usagesOf a
    let (uk, uh) ← hostKeyOf st a "unwrappingKey"
    if uk.algo.alg.name != algName || !uk.usages.contains .unwrapKey then throw .invalidAccess
    let alg ← match algJson st "unwrapKey" p with | .ok j => pure j | .error _ => algJson st "decrypt" p
    return ([("op", .string "unwrapKey"), ("format", .string ((a.str? "format").getD "")), ("wrappedKey", bytesJ data),
      ("unwrappingKey", numJ uh), ("algorithm", alg), ("unwrappedKeyAlgorithm", ← algJson st "importKey" (sub a "t:")),
      ("extractable", .bool ext), ("usages", usagesJ us)], .key ext)
  | _ => throw .notSupported

/-- One operation in host mode: Lean's checks, then a request (`["pending", id]`), or the
answer at once (cloneKey, a refusal). `wake` is the page's callback for the answer. -/
def hostSubtle (s : State) (fs : Array ByteArray) : State × Except Int ByteArray :=
  let a := pairsOf fs
  let method := (fs[0]?.bind String.fromUTF8?).getD ""
  if method == "cloneKey" then subtle s fs else
  match a.nat? "wake" with
  | none => (s, .error (-20))
  | some wake =>
    match errInt (hostPlan s.keys method a) with
    | .error e => (s, .error e)
    | .ok (fields, kind) =>
      let id := s.nextReq
      ({ s with nextReq := id + 1, hostReqs := s.hostReqs.push (.object (("id", numJ id) :: fields)),
                hostWaits := s.hostWaits.insert id { wake, kind } },
       .ok (pack ["pending".toUTF8, (toString id).toUTF8]))

def errOfName (n : String) : Err :=
  match n with
  | "TypeError" => .typeError | "NotSupportedError" => .notSupported | "SyntaxError" => .syntax
  | "InvalidAccessError" => .invalidAccess | "DataError" => .data | "QuotaExceededError" => .quota
  | _ => .operation

def jstr (j : JSON.Json) (k : String) : String := match j.field? k with | some (.string x) => x | _ => ""
def jnat (j : JSON.Json) (k : String) : Nat := match j.field? k with | some (.number n) => n.toNat?.getD 0 | _ => 0

def jwkMember : String × JSON.Json → String × JwkVal
  | (n, .bool b) => (n, .bool b)
  | (n, .array xs) => (n, .arr (xs.filterMap fun x => match x with | .string u => some u | _ => none))
  | (n, .string x) => (n, .str x)
  | (n, _) => (n, .str "")

/-- The Lean key for the host's key `h`: attributes only, no bytes. -/
def hostKeyOf? (h : Nat) (type : KeyType) (a : Alg) (j : JSON.Json) : Key :=
  let alg := (j.field? "algorithm").getD .null
  let hash := match alg.field? "hash" with | some hj => Crypto.WebHacl.HashAlg.ofName? (jstr hj "name") | none => none
  let us := match j.field? "usages" with
    | some (.array xs) => xs.filterMap fun x => match x with | .string u => Usage.ofName? u | _ => none
    | _ => []
  let pe := match alg.field? "publicExponent" with
    | some (.string b) => (unb64? b).getD .empty | _ => .empty
  { type, extractable := j.field? "extractable" == some (.bool true),
    algo := { alg := a, hash, length := jnat alg "length", curve := jstr alg "namedCurve",
              modulusLength := jnat alg "modulusLength", publicExponent := pe },
    usages := us, host := some h }

def hostKeyType? (j : JSON.Json) : Option KeyType :=
  match jstr j "type" with
  | "secret" => some KeyType.secret | "public" => some .publicKey | "private" => some .privateKey | _ => none

def hostNum? (j : JSON.Json) : Option Nat := match j.field? "h" with | some (.number n) => n.toNat? | _ => none

/-- A key the host made, as a Lean key (attributes only) with the host's number. -/
def hostKey (j : JSON.Json) : Option Key := do
  let h ← hostNum? j
  let type ← hostKeyType? j
  let a ← algOf? (jstr ((j.field? "algorithm").getD .null) "name")
  return hostKeyOf? h type a j

/-- A key the host made holds no key bytes in Lean: its secret is empty, it has no RSA
parts, and it names the host's key. So the store of a host-mode session (whose keys all
come from here, or are `cloneKey` copies of these) has no Lean-held secret, and no request
to the host can carry one: a request is built from the page's arguments, key attributes
and host numbers (`hostPlan`). -/
theorem hostKey_no_secret {j : JSON.Json} {k : Key} (h : hostKey j = some k) :
    k.secret = Crypto.WebHacl.Secret.empty ∧ k.rsa = none ∧ k.host.isSome := by
  unfold hostKey at h
  cases h1 : hostNum? j with
  | none => simp [h1] at h
  | some n =>
    cases h2 : hostKeyType? j with
    | none => simp [h1, h2] at h
    | some t =>
      cases h3 : algOf? (jstr ((j.field? "algorithm").getD .null) "name") with
      | none => simp [h1, h2, h3] at h
      | some a =>
        simp only [h1, h2, h3, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩

/-- The host answered request `id`: Lean makes the page's answer and names the callback to
run (queued as a task by the caller). -/
def hostDone (s : State) (id : Nat) (ans : JSON.Json) : State × Option Nat :=
  match s.hostWaits[id]? with
  | none => (s, none)
  | some w =>
    let s := { s with hostWaits := s.hostWaits.erase id }
    let r : Except Int ByteArray × State :=
      match ans.field? "error" with
      | some (.string n) => (.error (errOfName n).code, s)
      | some _ => (.error Err.operation.code, s)
      | none =>
        match w.kind with
        | .bytes => match ans.field? "bytes" with
          | some (.string b) => match unb64? b with
            | some x => (.ok (pack ["bytes".toUTF8, x]), s)
            | none => (.error Err.operation.code, s)
          | _ => (.error Err.operation.code, s)
        | .bool => (.ok (pack ["bool".toUTF8, (if ans.field? "bool" == some (.bool true) then "1" else "0").toUTF8]), s)
        | .jwk => match ans.field? "jwk" with
          | some (.object ms) => (.ok (pack (jwkFields (ms.map jwkMember))), s)
          | _ => (.error Err.operation.code, s)
        | .key _ =>
          let ks := match ans.field? "pair" with
            | some (.array xs) => xs.filterMap hostKey
            | _ => ((ans.field? "key").bind hostKey).toList
          -- §14.3.6 step 10 and §14.3.9 step 10: a secret or private key with no usages.
          let empty := ks.any fun k => (k.type == .secret || k.type == .privateKey) && k.usages.isEmpty
          if ks.isEmpty then (.error Err.operation.code, s) else
          if empty then
            let drops := ks.filterMap (·.host) |>.map fun h =>
              JSON.Json.object [("id", numJ 0), ("op", .string "drop"), ("key", numJ h)]
            (.error Err.syntax.code, { s with hostReqs := s.hostReqs ++ drops.toArray })
          else
            match ks.foldlM (fun (acc : KeyStore × List ByteArray) k => do
                let (st, f) ← addKey acc.1 k
                pure (st, acc.2 ++ f)) (s.keys, []) with
            | .ok (st, f) => (.ok (pack (if ks.length == 2 then "pair".toUTF8 :: f else f)), { s with keys := st })
            | .error e => (.error e.code, s)
    let (r, s) := r
    ({ s with hostAnswers := s.hostAnswers.insert id r }, some w.wake)

end Host

/-! ## Work: what an operation costs, decided from its arguments before it runs

An operation of `web_api` runs inside one host call, outside the script's step budget. So
that no call can hold the engine for long (cryptosec finding F3: an HMAC key of 2^31 bits
took 9 s, and PBKDF2 allowed 2^32 - 1 iterations, about an hour), `runCharged` first
works out an upper bound of the operation's work from its arguments and the session's
keys (`opWork`), refuses it with -5 (an OperationError in crypto.subtle) above
`maxOpWork`, and otherwise adds it to `State.work`, which `Page.serveExtra` charges to
script time like the page's own WebAssembly (`stepsPerWork`).

The unit is one compression of a 64- or 128-byte hash block by HACL*, about 0.27 µs
natively (PBKDF2-SHA-256 at 2,000,000 iterations: 8,000,000 units, 2.2 s). Other
primitives are counted in the same unit from their measured times (record, "Work"). -/

/-- At most this much work in one call: 2^24 units, about 4.5 s natively. -/
def maxOpWork : Nat := 1 <<< 24

/-- Script time per unit (instructions at `ScriptClock.instructionsPerMs`, 100,000 a ms):
0.27 µs is 27 instructions. -/
def stepsPerWork : Nat := 27

/-- A hash of `n` bytes in blocks of `blk`: the blocks, and the padding block. -/
def hashWork (blk n : Nat) : Nat := n / blk + 2

/-- HMAC with a key of `k` bytes over `m` bytes: the inner hash over the padded key block
and the message (with its padding), the outer hash's two blocks, and the key's own hash
when it is longer than a block (HACL* hashes a long key on every call). -/
def hmacWork (blk k m : Nat) : Nat := (if k > blk then hashWork blk k else 0) + (blk + m + 8) / blk + 1 + 2

/-- `n` bytes of the HMAC_DRBG (SHA-256): one HMAC per 32 bytes, then the update. -/
def drbgWork (n : Nat) : Nat := 4 * (n / 32) + 24

/-- A P-256 scalar multiplication (sign, verify, ECDH, a public key), an Ed25519 or X25519
one, and RSA's modular exponentiation with a modulus of `k` octets (private: constant time,
the exponent is |n| bits; public: a short exponent). -/
def p256Work : Nat := 1500
def okpWork : Nat := 400
def rsaPrivWork (k : Nat) : Nat := (k / 64 + 1) ^ 3 * 400
def rsaPubWork (k : Nat) : Nat := (k / 64 + 1) ^ 2 * 40

open Crypto.WebCryptoKeys in
/-- The work of a key operation with key `k` of algorithm `alg` on `n` bytes of data. -/
def keyOpWork (alg : Alg) (k : Key) (hash : Option Crypto.WebHacl.HashAlg) (n : Nat) : Nat :=
  let blk := (hash.map (·.block)).getD 64
  let rsaK := ((k.rsa.map (·.n.size)).getD 0)
  match alg with
  | .hmac => hmacWork ((k.algo.hash.map (·.block)).getD 64) k.secret.size n
  | .ecdsa | .ecdh => hashWork blk n + p256Work
  | .ed25519 => hashWork 64 n + okpWork
  | .x25519 => okpWork
  | .chacha => n / 64 + 8
  | .rsaPkcs1 | .rsaPss | .rsaOaep => hashWork blk n + rsaPrivWork rsaK
  | _ => hashWork 64 n

open Crypto.WebCryptoKeys in
/-- Derived bits: HKDF's extract and expand, PBKDF2's iterations for each block, or one
ECDH. `len` is in bits. -/
def deriveWork (k : Key) (p : Args) (len : Nat) : Nat :=
  let h := ((p.str? "hash").bind Crypto.WebHacl.HashAlg.ofName?).getD .sha512
  let blocks := max 1 ((len / 8 + h.size - 1) / h.size)
  match k.algo.alg with
  | .hkdf => hmacWork h.block ((p.get? "salt").getD .empty).size k.secret.size +
      blocks * hmacWork h.block h.size (h.size + ((p.get? "info").getD .empty).size + 1)
  | .pbkdf2 => blocks * ((p.nat? "iterations").getD 0) * hmacWork h.block k.secret.size (h.size + 4)
      + blocks * hmacWork h.block k.secret.size (((p.get? "salt").getD .empty).size + 4)
  | .ecdh => p256Work
  | .x25519 => okpWork
  | _ => 0

/-- An HMAC is charged at least its four compressions (inner key block and message, outer
two blocks), and its key's and message's blocks. -/
theorem hmacWork_ge (blk k m : Nat) (hb : 0 < blk) : 4 ≤ hmacWork blk k m ∧ m / blk ≤ hmacWork blk k m := by
  unfold hmacWork
  have h1 : 1 ≤ (blk + m + 8) / blk := (Nat.le_div_iff_mul_le hb).2 (by omega)
  have h2 : m / blk ≤ (blk + m + 8) / blk := Nat.div_le_div_right (by omega)
  constructor <;> omega

open Crypto.WebCryptoKeys in
/-- PBKDF2 is charged in proportion to its work: at least four compressions for each of its
`iterations` HMACs in each output block (so 2^32 - 1 iterations are refused before they
run, `runCharged_refuses`). -/
theorem deriveWork_pbkdf2 (k : Key) (p : Args) (len : Nat) (hk : k.algo.alg = .pbkdf2) :
    ∃ h : Crypto.WebHacl.HashAlg,
      max 1 ((len / 8 + h.size - 1) / h.size) * ((p.nat? "iterations").getD 0) * 4 ≤ deriveWork k p len := by
  unfold deriveWork
  rw [hk]
  generalize ((p.str? "hash").bind Crypto.WebHacl.HashAlg.ofName?).getD .sha512 = h
  refine ⟨h, ?_⟩
  simp only
  have hb : 0 < h.block := by cases h <;> decide
  have h4 := (hmacWork_ge h.block k.secret.size (h.size + 4) hb).1
  have := Nat.mul_le_mul_left (max 1 ((len / 8 + h.size - 1) / h.size) * ((p.nat? "iterations").getD 0)) h4
  omega

open Crypto.WebCryptoKeys in
/-- The work of one `crypto.subtle` operation (op 41), an upper bound decided from the
arguments and the session's keys, before anything runs. -/
def subtleWork (s : State) (fs : Array ByteArray) : Nat :=
  let a := pairsOf fs
  let p := sub a "a:"
  let algName := (p.str? "name").getD ""
  let method := (fs[0]?.bind String.fromUTF8?).getD ""
  let data := ((a.get? "data").getD .empty).size
  let hash := (p.str? "hash").bind Crypto.WebHacl.HashAlg.ofName?
  let key := fun (f : String) => (keyOf s.keys a f).toOption
  let keyWork := fun (f : String) => match key f with
    | some k => keyOpWork k.algo.alg k hash data
    | none => 0
  match method with
  | "generateKey" => drbgWork (randNeeded algName p) + 8 * p256Work
  | "importKey" => data / 64 + 2 * p256Work
  | "exportKey" => (match key "key" with | some k => k.footprint / 32 + 8 | none => 8)
  | "cloneKey" => 8
  | "sign" | "verify" | "encrypt" | "decrypt" => drbgWork 512 + keyWork "key"
  | "deriveBits" | "deriveKey" =>
    -- deriveBits: its length argument; deriveKey: the derived key's length member (HMAC's
    -- `length`), else 1,024 bits, more than any other derived key here has.
    let len := if method == "deriveKey" then ((sub a "t:").nat? "length").getD 1024
      else ((a.str? "length").bind String.toNat?).getD 0
    match key "baseKey" with
    | some k => deriveWork k p len + 2 * p256Work + len / 256
    | none => 8
  | "wrapKey" => drbgWork 64 + (match key "key" with | some k => k.footprint / 32 + 8 | none => 8) +
      (match key "wrappingKey" with | some k => keyOpWork k.algo.alg k hash ((match key "key" with
        | some x => x.footprint | none => 0) * 2) | none => 0)
  | "unwrapKey" => data / 64 + 2 * p256Work + keyWork "unwrappingKey"
  | _ => 8

/-- The work of a call (`op`, its arguments): the arguments read once, and what the
operation does. -/
def opWork (s : State) (op : Nat) (fs : Array ByteArray) : Nat :=
  fs.foldl (fun n b => n + b.size) 0 / 64 + 1 +
  match op with
  | 30 => drbgWork (((fs[0]?.bind String.fromUTF8?).bind String.toNat?).getD 0)
  | 31 => drbgWork 16
  | 32 => hashWork 64 ((fs[1]?.map (·.size)).getD 0)
  | 33 => 8
  | 41 => if s.hostMode then 8 else subtleWork s fs
  | _ => 0

/-- One call, charged: refused with -5 when its work is above `maxOpWork` (and then nothing
ran and the state is as it was), else run, with its work added to `State.work`. -/
def runCharged (run : State → Nat → Nat → Array ByteArray → State × Except Int ByteArray)
    (s : State) (op flags : Nat) (fs : Array ByteArray) : State × Except Int ByteArray :=
  let w := opWork s op fs
  if w > maxOpWork then (s, .error (-5)) else
  let (s', r) := run s op flags fs
  ({ s' with work := s.work + w }, r)

theorem runCharged_refuses {run : State → Nat → Nat → Array ByteArray → State × Except Int ByteArray}
    {s : State} {op flags : Nat} {fs : Array ByteArray} (h : opWork s op fs > maxOpWork) :
    runCharged run s op flags fs = (s, .error (-5)) := by
  unfold runCharged; simp [h]

/-- Every call is charged exactly its work, which is at most `maxOpWork`; a call above
the bound is not run and charges nothing. -/
theorem runCharged_work (run : State → Nat → Nat → Array ByteArray → State × Except Int ByteArray)
    (s : State) (op flags : Nat) (fs : Array ByteArray) :
    (runCharged run s op flags fs).1.work = s.work + (if opWork s op fs > maxOpWork then 0 else opWork s op fs) ∧
    (runCharged run s op flags fs).1.work ≤ s.work + maxOpWork := by
  unfold runCharged
  by_cases h : opWork s op fs > maxOpWork
  · simp [h]
  · simp only [h, if_false]; constructor <;> simp <;> omega

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
  -- The session's Math.random seed (`mathRandomSeed`), 8 bytes little-endian: the
  -- QuickJS-NG guest takes it when a page starts.
  | 33 => pure' (match mathRandomSeed s.entropy with
    | some x => .ok (ByteArray.mk ((List.range 8).map fun i => (x >>> (8 * i).toUInt64).toUInt8).toArray)
    | none => .error (-6))
  | 32 => pure' do
    match Crypto.WebHacl.HashAlg.ofName? (← strArg fs 0) with
    | some h => .ok (Crypto.WebHacl.hashFast h (bytesArg fs 1))
    | none => .error (-23)
  -- The registry: the registered name and the dictionary members to convert.
  | 40 => pure' do
    if !s.hostMode && Crypto.WebHacl.haclLinked () != 1 then .error (-2) else
    match Crypto.WebCryptoKeys.normalizeSpec (← strArg fs 0) (← strArg fs 1) s.hostMode with
    | .ok (reg, ms) => ofStr ("\n".intercalate (reg :: ms))
    | .error e => .error e.code
  | 41 => if s.hostMode then hostSubtle s fs else subtle s fs
  -- Where crypto.subtle's primitives are: the host's ("host", the Hub) or HACL*'s.
  | 44 => pure' (ofStr (if s.hostMode then "host" else "native"))
  -- The answer of a request the host has answered (its callback is running).
  | 43 => match natArg fs 0 with
    | .ok id => match s.hostAnswers[id]? with
      | some r => ({ s with hostAnswers := s.hostAnswers.erase id }, r)
      | none => (s, .error (-1))
    | .error e => (s, .error e)
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
      let (s, r) := runCharged (fun s op flags fs => run s op flags fs dom) s (arg args 0) (arg args 1) fs
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
private def runHost (op : Nat) (xs : List String) : String :=
  match (run { hostMode := true } op 0 (((fields (pack (xs.map (·.toUTF8)))).getD #[]))).2 with
  | .ok b => String.fromUTF8! b
  | .error e => s!"error {e}"
#guard runHost 40 ["sign", "ecdsa"] == "ECDSA\nhash:h!"
#guard runHost 40 ["encrypt", "AES-GCM"] == "AES-GCM\nadditionalData:b\niv:b!\ntagLength:o"
#guard runHost 40 ["sign", "AES-GCM"] == "error -23"
-- Host mode: Lean's checks first, then a request for the browser (the Hub).
#guard runHost 41 ["generateKey", "wake", "5", "extractable", "1", "usage", "sign", "a:name", "AES-GCM", "a:length", "128"] == "error -24"
#guard runHost 41 ["generateKey", "wake", "5", "extractable", "1", "usage", "encrypt", "a:name", "AES-GCM", "a:length", "100"] == "error -22"
#guard (runHost 41 ["generateKey", "wake", "5", "extractable", "1", "usage", "encrypt", "a:name", "AES-GCM", "a:length", "128"]).length > 0
#guard (let (s, _) := run { hostMode := true } 41 0 ((fields (pack (["digest", "wake", "3", "a:name", "SHA-256", "data", "abc"].map (·.toUTF8)))).getD #[])
        s.hostReqs.size == 1 && (((s.hostReqs[0]?).map (·.toString)).getD "").startsWith "{\"id\":1,\"op\":\"digest\"")
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
-- Work (cryptosec F3): a call above `maxOpWork` is refused before it runs, and the others
-- are charged. PBKDF2 at 2^32 - 1 iterations, and an HMAC key of 2^32 - 1 bits:
private def chargedCode (s : State) (xs : List String) : Int × Nat :=
  let (s', r) := runCharged (fun s op fl fs => run s op fl fs) s 41 0 ((fields (pack (xs.map (·.toUTF8)))).getD #[])
  (match r with | .ok _ => 0 | .error e => e, s'.work)
#guard (let (s, _) := subtleRun {} ["importKey", "format", "raw", "extractable", "0", "usage", "deriveBits", "a:name", "PBKDF2", "data", "pw"]
  (chargedCode s ["deriveBits", "baseKey", "1", "length", "256", "a:name", "PBKDF2", "a:hash", "SHA-256", "a:iterations", "4294967295", "a:salt", "s"]).1) == -5
#guard (let (s, _) := subtleRun {} ["importKey", "format", "raw", "extractable", "0", "usage", "deriveBits", "a:name", "PBKDF2", "data", "pw"]
  opWork s 41 ((fields (pack (["deriveBits", "baseKey", "1", "length", "256", "a:name", "PBKDF2", "a:hash", "SHA-256",
    "a:iterations", "600000", "a:salt", "s"].map (·.toUTF8)))).getD #[]) |> fun w => 600000 * 4 ≤ w && w ≤ maxOpWork)
#guard (chargedCode {} ["generateKey", "extractable", "0", "usage", "sign", "a:name", "HMAC", "a:hash", "SHA-256", "a:length", "4294967295"]).1 == -5
#guard (chargedCode {} ["generateKey", "extractable", "0", "usage", "sign", "a:name", "HMAC", "a:hash", "SHA-256", "a:length", "512"]).1 == -6
-- A dropped handle (op 42) is an InvalidAccessError, never another key; a clone keeps
-- the original's extractable flag and usages.
#guard (subtleRun { keys := { next := 5 } } ["exportKey", "format", "raw", "key", "3"]).2 == "error -25"
#guard (subtleRun { keys := { next := 5 } } ["exportKey", "format", "raw", "key", "9"]).2 == "error -20"
#guard (let (s, _) := subtleRun {} (hmacImport "0"); (subtleRun s ["cloneKey", "key", "1"]).2) == "key|2|secret|0|sign|HMAC|2|hash|SHA-256|length|48"
#guard (let (s, _) := subtleRun {} (hmacImport "0"); let (s, _) := subtleRun s ["cloneKey", "key", "1"]
  (subtleRun s ["exportKey", "format", "raw", "key", "2"]).2) == "error -25"
-- An unwrapped JWK with a member twice is read as JSON.parse reads it: the last one (F15).
#guard ((jwkOfJson "{\"k\":\"AAAA\",\"kty\":\"oct\",\"k\":\"BBBB\"}".toUTF8).toOption.map fun a => a.str? "k") == some (some "BBBB")
#guard ((jwkOfJson "{\"kty\":\"RSA\",\"oth\":[]}".toUTF8).toOption.map fun a => a.has "oth") == some true
#guard extractCharset "text/html; charset=EUC-JP" == some "EUC-JP"
#guard extractCharset "text/html; CHARSET = 'big5' " == some "big5"
#guard extractCharset "charset" == none
#guard extractCharset "x; charset=\"unterminated" == none

end L4Factoidal.WasmVM.Hosts.WebApi
