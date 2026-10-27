/-
L4Factoidal.LWS.Client.Wire — the request and response records of the LWS
client, the header fields it reads, and the JSON form both take across the
wasm ABI. https://github.com/danbri/factoidal/issues/917

Design record: `docs/designissues/2026-10-22-lws-client.md`.

Everything the client reads from a response is read here, in Lean: header
lookup (case-insensitive, RFC 9110 §5.1), the `Link` field (RFC 8288 §3,
through `LWS.Linkset.parseLinkValue`, one link value at a time so that one
malformed value does not hide the others), the `WWW-Authenticate` Bearer
parameters (RFC 6750 §3, RFC 9728 §5.1 `resource_metadata`), `Allow`
(RFC 9110 §10.2.1), `Accept-Patch` (RFC 5789 §3.1), the scheme and authority
of a URL (RFC 3986 §3, through `Notifications.urlParts?`), the RFC 8414 §3.1
metadata URL of an authorization server, and the
`application/x-www-form-urlencoded` body of a token request (the WHATWG URL
Standard §5.2, the serializer RFC 6749 §4.1.3 points to).

A host gives a response as a status, header pairs and a body; it reads none
of them.
-/
import L4Factoidal.LWS.Linkset
import L4Factoidal.LWS.Notifications
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.HTTP.Server

namespace L4Factoidal.LWS.Client

open L4Factoidal.JSON
open L4Factoidal.LWS

/-! ## Requests and responses -/

/-- A request the client asks the host to send. `url` is absolute. -/
structure Req where
  method : String
  url : String
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty

instance : Inhabited Req := ⟨{ method := "GET", url := "" }⟩

/-- A response the host received: header names in any case. -/
structure Resp where
  status : Nat
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
  /-- The host's clock when the response arrived, seconds since the Unix
  epoch (`iat` and `exp` of a self-issued credential). -/
  now : Nat := 0
  /-- Random bytes from the host's random source (an ECDSA nonce, a `jti`). -/
  random : ByteArray := ByteArray.empty

/-- The header fields of a request other than `Authorization`. Two requests
that differ only in the access token they carry are the same request
(a resend with a fresh token is a repeat). -/
def headersSansAuth (hs : List (String × String)) : List (String × String) :=
  (hs.filter (fun (n, _) => n.toLower != "authorization")).map (fun (n, v) => (n.toLower, v))

/-- Are two requests the same request: method, URL, the header fields other
than `Authorization`, and the content? -/
def Req.same (a b : Req) : Bool :=
  a.method == b.method && a.url == b.url &&
  headersSansAuth a.headers == headersSansAuth b.headers && a.body.data == b.body.data

/-- The value of header `name` in a list of header pairs, case-insensitive.
Repeated fields are combined with ", " (RFC 9110 §5.3). -/
def headerIn (hs : List (String × String)) (name : String) : Option String :=
  match (hs.filter (fun (n, _) => n.toLower == name.toLower)).map (·.2) with
  | [] => none
  | v :: vs => some (vs.foldl (fun acc x => acc ++ ", " ++ x) v)

def Req.header? (r : Req) (name : String) : Option String := headerIn r.headers name
def Resp.header? (r : Resp) (name : String) : Option String := headerIn r.headers name

/-- A response is a success (2xx). -/
def Resp.ok (r : Resp) : Bool := 200 ≤ r.status && r.status < 300

/-- The content of a response as JSON, if it is UTF-8 JSON. -/
def Resp.json? (r : Resp) : Option Json :=
  (String.fromUTF8? r.body).bind parseJson?

/-! ## URLs -/

/-- Resolve a reference against the URL of the request it came from
(RFC 3986 §5.2). -/
def resolve (base ref : String) : String := L4Factoidal.Syntax.resolveIri base ref

/-- Do two URLs have the same scheme and authority (RFC 3986 §3.1, §3.2,
compared after the normalisation of RFC 9421 §2.2: lower case, default port
removed)? `false` when either is not an `http` or `https` URL. -/
def sameOrigin (a b : String) : Bool :=
  match Notifications.urlParts? a, Notifications.urlParts? b with
  | some (s1, a1, _), some (s2, a2, _) => s1 == s2 && a1 == a2
  | _, _ => false

/-- The RFC 8414 §3.1 metadata URL of an issuer, with the well-known suffix
`lws-configuration` (lws10-core §Authorization Server Metadata: "This
metadata resource MUST be available at a URL with the path
/.well-known/lws-configuration"): the suffix goes between the host and the
path of the issuer. -/
def asMetadataUrl (issuer : String) : String :=
  match issuer.splitOn "://" with
  | [scheme, rest] =>
      let authCs := rest.toList.takeWhile (fun c => c != '/')
      let pathCs := rest.toList.drop authCs.length
      let pathCs := if pathCs.getLast? == some '/' then pathCs.dropLast else pathCs
      scheme ++ "://" ++ String.ofList authCs ++ "/.well-known/lws-configuration" ++
        String.ofList pathCs
  | _ => issuer

#guard asMetadataUrl "https://as.example" == "https://as.example/.well-known/lws-configuration"
#guard asMetadataUrl "https://as.example/" == "https://as.example/.well-known/lws-configuration"
#guard asMetadataUrl "http://h:9/t/s/1/as" == "http://h:9/.well-known/lws-configuration/t/s/1/as"

/-! ## Header fields the client reads -/

/-- The links of a response (RFC 8288 §3), targets resolved against
`base`. A link value that does not parse is skipped, so one malformed value
does not hide the others. -/
def linksOf (base : String) (r : Resp) : List Link :=
  match r.header? "link" with
  | none => []
  | some v =>
      let parts := (splitTop ',' v.toList false false [] #[]).toList.map trimS |>.filter (· != "")
      parts.flatMap (fun p => match parseLinkValue p with
        | .ok ls => ls.map (fun l => { l with target := resolve base l.target })
        | .error _ => [])

/-- The target of the first link with relation `rel` (compared without case
for registered relation names, exactly for extension relations, RFC 8288
§2.1). -/
def linkTarget? (base : String) (r : Resp) (rel : String) : Option String :=
  ((linksOf base r).find? (fun l => l.rel.toLower == rel.toLower)).map (·.target)

/-- The comma-separated tokens of a field value, trimmed, empty ones dropped
(`Allow`, `Accept-Patch`). -/
def fieldTokens (v : String) : List String :=
  (v.splitOn ",").map (fun t => trimS t) |>.filter (· != "")

/-- The methods of an `Allow` field (RFC 9110 §10.2.1), upper case. -/
def allowOf (r : Resp) : List String := ((r.header? "allow").map fieldTokens).getD [] |>.map String.toUpper

/-- The media types of an `Accept-Patch` field (RFC 5789 §3.1), lower case,
parameters dropped. -/
def acceptPatchOf (r : Resp) : List String :=
  ((r.header? "accept-patch").map fieldTokens).getD [] |>.map (fun t => (trimS ((t.splitOn ";").headD "")).toLower)

/-- The parameters of a Bearer challenge in a `WWW-Authenticate` field
(RFC 6750 §3, RFC 9110 §11.6.1). `none` when the field has no Bearer
challenge. The field may carry other challenges before it. -/
def bearerParams (v : String) : Option (List (String × String)) :=
  let parts := (splitTop ',' v.toList false false [] #[]).toList.map trimS
  -- The challenge starts with the part whose first token is "Bearer".
  let rec find : List String → Option (List String)
    | [] => none
    | p :: ps =>
        let low := p.toLower
        if low == "bearer" then some ps
        else if low.startsWith "bearer " then some ((trimS (String.ofList (p.toList.drop 7))) :: ps)
        else find ps
  match find parts with
  | none => none
  | some ps =>
      some (ps.filterMap (fun p => match p.splitOn "=" with
        | k :: vs =>
            match unquote (String.intercalate "=" vs) with
            | some val => some ((trimS k).toLower, val)
            | none => none
        | [] => none))

/-- The `resource_metadata` parameter of a 401's Bearer challenge (RFC 9728
§5.1). -/
def resourceMetadata? (r : Resp) : Option String :=
  (r.header? "www-authenticate").bind bearerParams |>.bind (fun ps => ps.lookup "resource_metadata")

#guard bearerParams "Bearer resource_metadata=\"https://s.example/.well-known/oauth-protected-resource/a\", error=\"invalid_token\"" ==
  some [("resource_metadata", "https://s.example/.well-known/oauth-protected-resource/a"), ("error", "invalid_token")]
#guard bearerParams "DPoP algs=\"ES256\"" == none

/-! ## `application/x-www-form-urlencoded` -/

private def hexUpper (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- The form serializer of the WHATWG URL Standard §5.2: ASCII letters,
digits and `*-._` stay, space is `+`, every other byte of the UTF-8
encoding is `%XX`. -/
def formEncode (s : String) : String :=
  s.toUTF8.foldl (fun acc b =>
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '*' || c == '-' || c == '.' || c == '_' then acc.push c
    else if b == 32 then acc.push '+'
    else (acc.push '%').push (hexUpper (b.toNat / 16)) |>.push (hexUpper (b.toNat % 16))) ""

/-- A form body from name and value pairs. -/
def formBody (pairs : List (String × String)) : String :=
  "&".intercalate (pairs.map (fun (k, v) => formEncode k ++ "=" ++ formEncode v))

/-- The name and value pairs of a form body, both decoded. -/
def formPairs (body : ByteArray) : List (String × String) :=
  match String.fromUTF8? body with
  | none => []
  | some t =>
      (t.splitOn "&").filter (· != "") |>.map (fun p => match p.splitOn "=" with
        | k :: vs => (L4Factoidal.HTTP.formDecode k, L4Factoidal.HTTP.formDecode (String.intercalate "=" vs))
        | [] => ("", ""))

#guard formBody [("grant_type", "urn:ietf:params:oauth:grant-type:token-exchange"), ("resource", "https://s.example/a b")] ==
  "grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Atoken-exchange&resource=https%3A%2F%2Fs.example%2Fa+b"
#guard formPairs (formBody [("a", "x=y&z"), ("b", "é")]).toUTF8 == [("a", "x=y&z"), ("b", "é")]

/-! ## JSON form of requests and responses (the wasm ABI) -/

/-- A string member, or `d`. -/
def jStr (j : Json) (k : String) (d : String := "") : String := (j.getString? k).getD d

/-- A natural number member, or `d`. -/
def jNat (j : Json) (k : String) (d : Nat := 0) : Nat :=
  match j.field? k with
  | some (.number s) => s.toNat?.getD d
  | _ => d

/-- A natural number member, if there is one. -/
def jNat? (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number s) => s.toNat?
  | _ => none

/-- A Boolean member, or `d`. -/
def jBool (j : Json) (k : String) (d : Bool := false) : Bool := (j.getBool? k).getD d

/-- The string elements of an array member. -/
def jStrs (j : Json) (k : String) : List String :=
  match j.getArray? k with
  | some xs => xs.filterMap Json.asString?
  | none => []

/-- A member as JSON, or `null`. -/
def jAny (j : Json) (k : String) : Json := (j.field? k).getD .null

/-- Header pairs `[[name, value], ...]`. -/
def jHeaders (j : Json) (k : String) : List (String × String) :=
  match j.getArray? k with
  | some xs => xs.filterMap (fun x => match x with
      | .array [.string n, .string v] => some (n, v)
      | _ => none)
  | none => []

/-- Content: `bodyBase64` (RFC 4648 §4) or the text `body`. -/
def jBody (j : Json) : ByteArray :=
  match j.getString? "bodyBase64" with
  | some t => (Base64.decode? t).getD ByteArray.empty
  | none => ((j.getString? "body").getD "").toUTF8

def headersJson (hs : List (String × String)) : Json :=
  .array (hs.map (fun (n, v) => .array [.string n, .string v]))

def strsJson (xs : List String) : Json := .array (xs.map Json.string)

def natJson (n : Nat) : Json := .number (toString n)

/-- A request as the host sends it: `{method, url, headers, bodyBase64?}`. -/
def reqJson (r : Req) : Json :=
  .object ([ ("method", .string r.method), ("url", .string r.url)
           , ("headers", headersJson r.headers) ] ++
    (if r.body.size == 0 then [] else [("bodyBase64", .string (Base64.encode r.body))]))

def reqOfJson (j : Json) : Req :=
  { method := jStr j "method", url := jStr j "url", headers := jHeaders j "headers", body := jBody j }

/-- A response as the host gives it: `{status, headers, bodyBase64 | body}`. -/
def respOfJson (j : Json) : Resp :=
  { status := jNat j "status", headers := jHeaders j "headers", body := jBody j
    now := jNat j "now"
    random := ((j.getString? "randomBase64").bind Base64.decode?).getD ByteArray.empty }

def respJson (r : Resp) : Json :=
  .object [ ("status", natJson r.status), ("headers", headersJson r.headers)
          , ("bodyBase64", .string (Base64.encode r.body)) ]

end L4Factoidal.LWS.Client
