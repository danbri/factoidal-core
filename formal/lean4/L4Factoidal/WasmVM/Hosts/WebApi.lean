/-
L4Factoidal.WasmVM.Hosts.WebApi: the `foafnaut_dom.web_api` import, which serves the
web APIs that are pure algorithms to page scripts (record:
docs/designissues/2026-11-08-page-scripts.md, "Web APIs over Lean"). The algorithms are Lean's:

  * the Encoding Standard (`WHATWG.Encoding.Core`, `.Api`): `TextDecoder`,
    `TextEncoder`, `TextDecoderStream`;
  * the URL Standard (`WHATWG.URL.Parser`): `URL`, `URLSearchParams`;
  * forgiving-base64 (`WHATWG.Base64`): `atob`, `btoa`;
  * `Crypto.WebCrypto`: `crypto.getRandomValues`, `randomUUID`, and `crypto.subtle`
    digest, HMAC, HKDF and PBKDF2.

`web_api(op, flags, ptr, len, buf, cap)`. The `len` bytes at `ptr` are the arguments:
a little-endian u32 count, then each argument as a u32 length and its bytes (strings in
UTF-8, numbers as decimal). The answer is bytes: written at `buf` when they fit in `cap`,
and the length is answered; when they do not fit, nothing is written, the bytes wait and
the answer is their length, and op 0 then writes them (so a stateful op runs once).
Negative answers: -1 none (null, or a failed parse), -2 not an op of this engine (a page
probes with op 1), -3 InvalidCharacterError, -5 over a budget, -6 no entropy,
-20 TypeError, -21 RangeError, -22 OperationError, -23 NotSupportedError.

State: the decoders of `TextDecoder`s in the middle of a stream (by the number the page
gave them), the answer that waits, and the random generator. One call is one operation
on a whole buffer: the boundary is crossed once per `decode`, never per byte.
-/
import L4Factoidal.WasmVM.Hosts.Dom
import L4Factoidal.WHATWG.Encoding.Api
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.WHATWG.Base64
import L4Factoidal.Crypto.WebCrypto
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
  rng : Option Crypto.WebCrypto.Drbg := none
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

/-! ## The operations -/

def run (s : State) (op flags : Nat) (fs : Array ByteArray) (dom : L4Factoidal.DOM.Dom := default) :
    State × Except Int ByteArray :=
  let pure' := fun (r : Except Int ByteArray) => (s, r)
  match op with
  | 1 => pure' (ofStr "1")
  -- The document's encoding (the name, as `characterSet` gives it).
  | 9 => pure' (ofStr (documentEncoding dom).name)
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
      let rng? := match s.rng with
        | some d => some d
        | none => if s.entropy.isEmpty then none else some (Crypto.WebCrypto.Drbg.instantiate s.entropy ByteArray.empty)
      match rng? with
      | none => (s, .error (-6))
      | some d =>
        let (out, d) := d.generate n
        ({ s with rng := some d }, if op == 30 then .ok out else ofStr (Crypto.WebCrypto.uuidOf out))
  | 32 => pure' do
    match Crypto.WebCrypto.digest? (← strArg fs 0) (bytesArg fs 1) with
    | some d => .ok d
    | none => .error (-23)
  | 33 | 34 | 35 | 36 => pure' do
    match Crypto.WebCrypto.hashOf? (← strArg fs 0) with
    | none => .error (-23)
    | some h =>
      match op with
      | 33 => .ok (Crypto.WebCrypto.hmac h (bytesArg fs 1) (bytesArg fs 2))
      | 34 => .ok (ByteArray.mk #[if Crypto.WebCrypto.hmacVerify h (bytesArg fs 1) (bytesArg fs 2) (bytesArg fs 3) then 1 else 0])
      | 35 =>
        match Crypto.WebCrypto.hkdf h (bytesArg fs 1) (bytesArg fs 2) (bytesArg fs 3) (← natArg fs 4) with
        | some b => .ok b
        | none => .error (-22)
      | _ =>
        let it ← natArg fs 3
        if it == 0 then .error (-22) else .ok (Crypto.WebCrypto.pbkdf2 h (bytesArg fs 1) (bytesArg fs 2) it (← natArg fs 4))
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

private def pack (xs : List ByteArray) : ByteArray :=
  xs.foldl (fun acc x => acc ++ u32le x.size ++ x) (u32le xs.length)

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
#guard extractCharset "text/html; charset=EUC-JP" == some "EUC-JP"
#guard extractCharset "text/html; CHARSET = 'big5' " == some "big5"
#guard extractCharset "charset" == none
#guard extractCharset "x; charset=\"unterminated" == none

end L4Factoidal.WasmVM.Hosts.WebApi
