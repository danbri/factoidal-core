/-
L4Factoidal.HTTP.Wire — HTTP/1.1 message framing for a server: read ONE
request from the bytes a connection has delivered so far, and write one
response.

Spec: RFC 9112, HTTP/1.1 (https://www.rfc-editor.org/rfc/rfc9112): §2.2
message parsing, §3 request line, §5 field syntax, §6 message body
(§6.1 Transfer-Encoding, §6.3 message body length), §7.1 chunked transfer
coding, §9.3 persistence. RFC 9110 §15 for the reason phrases.

`HTTP/Server.lean` decides routing, negotiation and status codes over a
parsed `Request`; `HTTP/Client.lean` parses a RESPONSE. Until this module
there was no parser for a REQUEST MESSAGE, so a socket host would have had to
decide where a request ends and what its headers are. That is HTTP
semantics, and it belongs here (iron rule 7): the host hands the bytes it
has read to `frameRequest` and is told one of three things —

  * `incomplete` — read more bytes (`need`, when the engine already knows
    the total length the message will have);
  * `request` — one complete request, how many bytes it used, and whether
    the connection stays open after the response (§9.3);
  * `reject` — the bytes are not an acceptable request; answer with the
    status given and close the connection.

What is admitted:

  * the request line `method SP request-target SP HTTP-version` (§3); a
    version other than HTTP/1.0 or HTTP/1.1 is 505; a request-target in
    absolute-form (§3.2.2) is reduced to its path and query;
  * header fields `name ":" OWS value OWS` (§5); a name with whitespace
    before the colon and an obsolete line folding are 400 (§5.1, §5.2);
    names are lower-cased, values trimmed;
  * a body by `Content-Length` (§6.3 rule 6; differing or malformed
    values are 400) or by the chunked transfer coding (§7.1; any other
    transfer coding is 501, §6.1); a body above `maxBodyBytes` is 413,
    a header section above `maxHeadBytes` is 431 (RFC 6585 §5);
  * the body must be UTF-8. Every payload this server reads — a SPARQL
    query or update (SPARQL 1.1 Protocol §2.1.2, §2.2.1) and Turtle or
    N-Triples — is defined as UTF-8 text, so other bytes are a 400.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.HTTP.Server

namespace L4Factoidal.HTTP.Wire

open L4Factoidal.HTTP

/-- The largest header section admitted, in bytes. -/
def maxHeadBytes : Nat := 65536

/-- The largest request body admitted, in bytes. -/
def maxBodyBytes : Nat := 16 * 1024 * 1024

/-- What the bytes a connection has delivered so far contain. -/
inductive Frame where
  /-- Not yet a whole request. `need` is the total byte count the request
  will have, when the header section already says it. -/
  | incomplete (need : Option Nat)
  /-- One request, the bytes it used, and whether the connection persists. -/
  | request (req : Request) (consumed : Nat) (keepAlive : Bool)
  /-- Not an acceptable request: answer `status` and close. -/
  | reject (status : Nat) (reason : String)
  deriving Repr

/-! ## Bytes -/

private def byteAt (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b[i] else 0

/-- The first index `i ≥ start` where `b[i..i+4)` is CR LF CR LF. -/
def findHeadEnd (b : ByteArray) (start : Nat := 0) : Option Nat := Id.run do
  if b.size < 4 then return none
  for i in [start : b.size - 3] do
    if byteAt b i == 13 && byteAt b (i + 1) == 10 &&
       byteAt b (i + 2) == 13 && byteAt b (i + 3) == 10 then
      return some i
  return none

/-- The first index `i ≥ start` where `b[i..i+2)` is CR LF. -/
def findCrlf (b : ByteArray) (start : Nat) : Option Nat := Id.run do
  if b.size < 2 then return none
  for i in [start : b.size - 1] do
    if byteAt b i == 13 && byteAt b (i + 1) == 10 then return some i
  return none

/-! ## Text helpers -/

private def isOws (c : Char) : Bool := c == ' ' || c == '\t'

private def trimOws (s : String) : String :=
  String.ofList (((s.toList.dropWhile isOws).reverse.dropWhile isOws).reverse)

/-- RFC 9110 §5.6.2 `tchar`. -/
def isTchar (c : Char) : Bool :=
  c.isAlphanum || "!#$%&'*+-.^_`|~".toList.contains c

def isToken (s : String) : Bool := !s.isEmpty && s.toList.all isTchar

private def lowerAscii (s : String) : String :=
  String.ofList (s.toList.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c)

/-- Split at the first occurrence of `c`. -/
private def splitFirst (s : String) (c : Char) : String × Option String :=
  match s.toList.findIdx? (· == c) with
  | none => (s, none)
  | some i => (String.ofList (s.toList.take i), some (String.ofList (s.toList.drop (i + 1))))

/-- The comma-separated members of a header value, trimmed and lower-cased. -/
def listMembers (v : String) : List String :=
  ((v.splitOn ",").map (fun m => lowerAscii (trimOws m))).filter (!·.isEmpty)

/-! ## The request line and the header section -/

/-- §3.2: origin-form `/path?query` as is; absolute-form
`http://authority/path?query` reduced to its path and query; asterisk-form
`*` as is. Anything else is not a request-target this server accepts. -/
def splitTarget (target : String) : Option (String × String) :=
  let target :=
    let lower := lowerAscii target
    let rest? :=
      if lower.startsWith "http://" then some (String.ofList (target.toList.drop 7))
      else if lower.startsWith "https://" then some (String.ofList (target.toList.drop 8))
      else none
    match rest? with
    | none => target
    | some rest =>
        let chars := rest.toList
        match chars.findIdx? (fun c => c == '/' || c == '?') with
        | none => "/"
        | some i =>
            let tail := String.ofList (chars.drop i)
            if tail.startsWith "?" then "/" ++ tail else tail
  if target == "*" then some ("*", "")
  else if !target.startsWith "/" then none
  else
    match splitFirst target '?' with
    | (p, none) => some (p, "")
    | (p, some q) => some (p, q)

/-- One header line `name ":" OWS value OWS` (§5.1). -/
def parseHeaderLine (line : String) : Except String (String × String) :=
  if line.startsWith " " || line.startsWith "\t" then
    .error "obsolete line folding is not accepted (RFC 9112 section 5.2)"
  else
    match splitFirst line ':' with
    | (_, none) => .error s!"header line without a colon: {line.take 80}"
    | (name, some value) =>
        if !isToken name then
          .error s!"header field name is not a token (RFC 9112 section 5.1): {name.take 80}"
        else .ok (lowerAscii name, trimOws value)

/-- The request line and the header fields of a header section (the text
before CR LF CR LF). Error: the status and the reason. -/
def parseHead (head : String) :
    Except (Nat × String) (String × String × String × String × List (String × String)) := do
  let lines := head.splitOn "\r\n"
  match lines with
  | [] => throw (400, "empty request")
  | requestLine :: headerLines =>
    match requestLine.splitOn " " with
    | [method, target, version] =>
      if !isToken method then throw (400, s!"method is not a token: {method.take 40}")
      if !(version.startsWith "HTTP/") then throw (400, s!"malformed HTTP-version: {version.take 40}")
      if version != "HTTP/1.1" && version != "HTTP/1.0" then
        throw (505, s!"HTTP version {version.take 40} is not supported")
      match splitTarget target with
      | none => throw (400, s!"request-target is not in origin-form or absolute-form: {target.take 80}")
      | some (path, qs) =>
        let headers ← match headerLines.mapM parseHeaderLine with
          | .ok hs => pure hs
          | .error e => throw (400, e)
        pure (method, path, qs, version, headers)
    | _ => throw (400, s!"malformed request line: {requestLine.take 80}")

/-! ## The message body -/

/-- One hexadecimal digit. -/
private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `chunk-size`: one or more hexadecimal digits (§7.1). -/
def parseHexSize (s : String) : Option Nat :=
  if s.isEmpty || s.length > 15 then none
  else s.toList.foldlM (fun acc c => (hexDigit? c).map (acc * 16 + ·)) 0

/-- The decoded chunked body starting at `pos`, and the index just past the
trailer section. Total: each step consumes at least one CR LF, so `fuel`
(the byte count) bounds the loop. -/
def decodeChunked (b : ByteArray) (pos : Nat) (limit : Nat) :
    Except (Nat × String) (Option (ByteArray × Nat)) :=
  go b.size pos ByteArray.empty
where
  go : Nat → Nat → ByteArray → Except (Nat × String) (Option (ByteArray × Nat))
    | 0, _, _ => .ok none
    | fuel + 1, p, acc =>
      match findCrlf b p with
      | none => .ok none
      | some lineEnd =>
        match String.fromUTF8? (b.extract p lineEnd) with
        | none => .error (400, "chunk-size line is not text")
        | some line =>
          match parseHexSize (trimOws (splitFirst line ';').1) with
          | none => .error (400, s!"malformed chunk-size: {line.take 40}")
          | some 0 =>
            -- The trailer section: header lines up to an empty line.
            trailer fuel (lineEnd + 2) acc
          | some size =>
            if acc.size + size > limit then .error (413, s!"request body exceeds {limit} bytes")
            else
              let dataStart := lineEnd + 2
              if dataStart + size + 2 > b.size then .ok none
              else if byteAt b (dataStart + size) != 13 || byteAt b (dataStart + size + 1) != 10 then
                .error (400, "chunk data is not followed by CR LF")
              else go fuel (dataStart + size + 2) (acc ++ b.extract dataStart (dataStart + size))
  trailer : Nat → Nat → ByteArray → Except (Nat × String) (Option (ByteArray × Nat))
    | 0, _, _ => .ok none
    | fuel + 1, p, acc =>
      match findCrlf b p with
      | none => .ok none
      | some lineEnd => if lineEnd == p then .ok (some (acc, p + 2)) else trailer fuel (lineEnd + 2) acc

/-- §6.3 rule 5: every Content-Length value, which must agree. -/
def contentLength (headers : List (String × String)) : Except (Nat × String) (Option Nat) := do
  let values := (headers.filter (·.1 == "content-length")).flatMap (fun h => listMembers h.2)
  match values with
  | [] => pure none
  | v :: rest =>
    if !(v.toList.all Char.isDigit) || v.isEmpty || v.length > 15 then
      throw (400, s!"malformed Content-Length: {v.take 40}")
    if rest.any (· != v) then throw (400, "differing Content-Length values")
    pure v.toNat?

/-- §9.3: HTTP/1.1 persists unless `Connection: close`; HTTP/1.0 persists
only with `Connection: keep-alive`. -/
def persists (version : String) (headers : List (String × String)) : Bool :=
  let options := (headers.filter (·.1 == "connection")).flatMap (fun h => listMembers h.2)
  if version == "HTTP/1.1" then !options.contains "close"
  else options.contains "keep-alive"

/-! ## Framing one request -/

/-- Read one request from the start of `b`. -/
def frameRequest (b : ByteArray) (headLimit : Nat := maxHeadBytes)
    (bodyLimit : Nat := maxBodyBytes) : Frame :=
  match findHeadEnd b with
  | none =>
    if b.size > headLimit then .reject 431 s!"header section exceeds {headLimit} bytes"
    else .incomplete none
  | some headEnd =>
    if headEnd > headLimit then .reject 431 s!"header section exceeds {headLimit} bytes" else
    match String.fromUTF8? (b.extract 0 headEnd) with
    | none => .reject 400 "header section is not text"
    | some head =>
      match parseHead head with
      | .error (status, reason) => .reject status reason
      | .ok (method, path, qs, version, headers) =>
        let bodyStart := headEnd + 4
        let finish (body : ByteArray) (consumed : Nat) : Frame :=
          match String.fromUTF8? body with
          | none => .reject 400 "request content is not UTF-8"
          | some text =>
            .request { method, path, queryStr := qs, version, headers, body := text }
              consumed (persists version headers)
        let codings := (headers.filter (·.1 == "transfer-encoding")).flatMap (fun h => listMembers h.2)
        if !codings.isEmpty then
          -- §6.1: only `chunked` is understood; it must be the only coding.
          if codings != ["chunked"] then
            .reject 501 s!"transfer coding {String.intercalate ", " codings} is not implemented"
          else
            match decodeChunked b bodyStart bodyLimit with
            | .error (status, reason) => .reject status reason
            | .ok none => .incomplete none
            | .ok (some (body, endPos)) => finish body endPos
        else
          match contentLength headers with
          | .error (status, reason) => .reject status reason
          | .ok none => finish ByteArray.empty bodyStart
          | .ok (some len) =>
            if len > bodyLimit then .reject 413 s!"request body exceeds {bodyLimit} bytes"
            else if bodyStart + len > b.size then .incomplete (some (bodyStart + len))
            else finish (b.extract bodyStart (bodyStart + len)) (bodyStart + len)

/-! ## Writing one response -/

/-- RFC 9110 §15: the reason phrase of a status code. -/
def reasonPhrase : Nat → String
  | 100 => "Continue" | 200 => "OK" | 201 => "Created" | 202 => "Accepted"
  | 204 => "No Content" | 301 => "Moved Permanently" | 302 => "Found"
  | 303 => "See Other" | 304 => "Not Modified" | 400 => "Bad Request"
  | 401 => "Unauthorized" | 403 => "Forbidden" | 404 => "Not Found"
  | 405 => "Method Not Allowed" | 406 => "Not Acceptable" | 409 => "Conflict"
  | 411 => "Length Required" | 413 => "Content Too Large" | 414 => "URI Too Long"
  | 415 => "Unsupported Media Type" | 421 => "Misdirected Request" | 422 => "Unprocessable Content"
  | 431 => "Request Header Fields Too Large" | 500 => "Internal Server Error"
  | 501 => "Not Implemented" | 503 => "Service Unavailable"
  | 505 => "HTTP Version Not Supported"
  | _ => "Status"

/-- §6.3: a 1xx, 204 or 304 response has no content and, for 204 and 1xx,
no Content-Length (RFC 9110 §8.6). -/
def statusHasNoContent (status : Nat) : Bool :=
  status / 100 == 1 || status == 204 || status == 304

private def safeFieldValue (v : String) : String :=
  String.ofList (v.toList.filter fun c => c != '\r' && c != '\n')

/-- The response message: the status line, the response's own header
fields (any `content-length`, `connection` or `transfer-encoding` it carries
is replaced by the framing this function decides), `content-length`, and
`connection: close` when the connection ends. A response to HEAD carries the
header section only (RFC 9110 §9.3.2). -/
def formatResponse (r : Response) (keepAlive : Bool) (headOnly : Bool := false) : String :=
  let framing := ["content-length", "connection", "transfer-encoding"]
  let own := r.headers.filter fun (k, _) => !framing.contains (lowerAscii k)
  let noContent := statusHasNoContent r.status
  let statusLine := s!"HTTP/1.1 {r.status} {reasonPhrase r.status}\r\n"
  let fields := String.join (own.map fun (k, v) => k ++ ": " ++ safeFieldValue v ++ "\r\n")
  let length := if noContent then "" else s!"content-length: {r.body.utf8ByteSize}\r\n"
  let conn := if keepAlive then "" else "connection: close\r\n"
  statusLine ++ fields ++ length ++ conn ++ "\r\n" ++
    (if noContent || headOnly then "" else r.body)

/-! ## Checks -/

private def bytes (s : String) : ByteArray := s.toUTF8

private def reqOf : Frame → Option (Request × Nat × Bool)
  | .request r n k => some (r, n, k)
  | _ => none

private def statusOf : Frame → Option Nat
  | .reject s _ => some s
  | _ => none

private def isIncomplete : Frame → Bool
  | .incomplete _ => true
  | _ => false

-- A GET with no body: everything up to the blank line is consumed.
#guard (reqOf (frameRequest (bytes "GET /sparql?query=ASK%7B%7D HTTP/1.1\r\nHost: a\r\n\r\n"))).map
  (fun (r, n, k) => (r.method, r.path, r.queryStr, r.header? "host", n, k)) ==
  some ("GET", "/sparql", "query=ASK%7B%7D", some "a", 49, true)
-- Header names are case-insensitive and values trimmed.
#guard (reqOf (frameRequest (bytes "GET / HTTP/1.1\r\nCONTENT-type:  text/plain \r\n\r\n"))).map
  (fun (r, _, _) => r.header? "content-type") == some (some "text/plain")
-- Content-Length frames the body; the bytes after it belong to the next request.
#guard (reqOf (frameRequest (bytes "POST /s HTTP/1.1\r\nContent-Length: 3\r\n\r\nabcGET"))).map
  (fun (r, n, _) => (r.body, n)) == some ("abc", 42)
-- A body that has not all arrived is incomplete, and the total is known.
#guard match frameRequest (bytes "POST /s HTTP/1.1\r\nContent-Length: 10\r\n\r\nabc") with
  | .incomplete (some 50) => true
  | _ => false
-- No blank line yet: incomplete.
#guard isIncomplete (frameRequest (bytes "GET / HTTP/1.1\r\nHost: a\r\n"))
-- The chunked transfer coding (RFC 9112 section 7.1), with a trailer field.
#guard (reqOf (frameRequest (bytes "POST /s HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n2;x=y\r\nde\r\n0\r\nT: v\r\n\r\nNEXT"))).map
  (fun (r, n, _) => (r.body, n)) == some ("abcde", 78)
#guard isIncomplete (frameRequest (bytes "POST /s HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nab"))
-- Refusals, with the status RFC 9112 names.
#guard statusOf (frameRequest (bytes "POST /s HTTP/1.1\r\nTransfer-Encoding: gzip, chunked\r\n\r\n")) == some 501
#guard statusOf (frameRequest (bytes "POST /s HTTP/1.1\r\nContent-Length: 3\r\nContent-Length: 4\r\n\r\nabcd")) == some 400
#guard statusOf (frameRequest (bytes "POST /s HTTP/1.1\r\nContent-Length: x\r\n\r\n")) == some 400
#guard statusOf (frameRequest (bytes "GET / HTTP/2.0\r\n\r\n")) == some 505
#guard statusOf (frameRequest (bytes "GET / HTTP/1.1\r\nBad Name: v\r\n\r\n")) == some 400
#guard statusOf (frameRequest (bytes "GET / HTTP/1.1\r\nA: b\r\n folded\r\n\r\n")) == some 400
#guard statusOf (frameRequest (bytes "GET nopath HTTP/1.1\r\n\r\n")) == some 400
#guard statusOf (frameRequest (bytes "POST /s HTTP/1.1\r\nContent-Length: 5\r\n\r\nabcde") 65536 4) == some 413
#guard statusOf (frameRequest (ByteArray.mk #[71, 69, 84, 32, 47, 32, 72, 84, 84, 80, 47, 49, 46, 49,
  13, 10, 67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 49, 13, 10, 13, 10, 0xFF])) == some 400
-- Absolute-form is reduced to the path and query.
#guard (reqOf (frameRequest (bytes "GET http://h:8/sparql?query=x HTTP/1.1\r\n\r\n"))).map
  (fun (r, _, _) => (r.path, r.queryStr)) == some ("/sparql", "query=x")
-- Persistence (RFC 9112 section 9.3).
#guard (reqOf (frameRequest (bytes "GET / HTTP/1.1\r\nConnection: close\r\n\r\n"))).map (·.2.2) == some false
#guard (reqOf (frameRequest (bytes "GET / HTTP/1.0\r\n\r\n"))).map (·.2.2) == some false
#guard (reqOf (frameRequest (bytes "GET / HTTP/1.0\r\nConnection: Keep-Alive\r\n\r\n"))).map (·.2.2) == some true
-- The response: length in bytes, not characters; 204 has neither body nor length.
#guard formatResponse { status := 200, headers := [("content-type", "text/plain"), ("Content-Length", "99")], body := "é" } true ==
  "HTTP/1.1 200 OK\r\ncontent-type: text/plain\r\ncontent-length: 2\r\n\r\né"
#guard formatResponse { status := 204, body := "x" } false ==
  "HTTP/1.1 204 No Content\r\nconnection: close\r\n\r\n"
#guard formatResponse { status := 200, body := "abc" } true (headOnly := true) ==
  "HTTP/1.1 200 OK\r\ncontent-length: 3\r\n\r\n"

end L4Factoidal.HTTP.Wire
