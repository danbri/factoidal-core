/-
L4Factoidal.LWS.Client.Report — the result shapes a driver of the LWS client
reports, read from a response in Lean. https://github.com/danbri/factoidal/issues/1065

The `lws-driver/1` adapter protocol (ebremer/lws-client `driver/PROTOCOL.md`
§3.1) names the shapes Metadata, Item, Page, Storage and Subscription, and
§3.2 the error kinds. Each is keyed by `Link` relations (RFC 8288 §3), by
members of a storage description (lws10-core §Discovery) or by an HTTP
status. A host gives the client a response as a status, header pairs and a
body (`Wire.lean`) and reads none of them; the client's `done` document
carries these shapes in its `report` member, and its `fail` document carries
the error shape in `report`. Nothing here feeds a request.

* `metadataJson`: status, entity tag, `Last-Modified`, `Content-Type`,
  `Content-Length`, every link (one per relation type), and the links of the
  relations `linkset`, `up`, `lws#storage`, `type`; `Allow` (RFC 9110
  §10.2.1) and `Accept-Patch` (RFC 5789 §3.1).
* `itemJson`, `pageJson`: a member of a listing and one page of it
  (lws10-core §Pagination: `first`, `next`, `prev`, `last` are link relations).
* `storageJson`: the storage description, its StorageRoot, its services, its
  verification methods and its `MoveResource` capability.
* `subscriptionJson`, `bodyJson`, `acceptQueryOf`, `errorReport`.
-/
import L4Factoidal.LWS.Client.Wire

namespace L4Factoidal.LWS.Client

open L4Factoidal.JSON
open L4Factoidal.LWS

/-! ## Small readers -/

/-- The elements of a member that is a value or an array of values; empty
when the member is absent or `null`. -/
def listAt (j : Json) (k : String) : List Json :=
  match j.field? k with
  | some (.array xs) => xs
  | some .null => []
  | some x => [x]
  | none => []

/-- The `type` of a JSON object as a list (a string or an array). -/
def typesOf (j : Json) : List String :=
  match j.field? "type" with
  | some (.string t) => [t]
  | some (.array xs) => xs.filterMap Json.asString?
  | _ => []

/-- `[(k, v)]` for a present member, `[]` otherwise. -/
def optMember (k : String) : Option Json → List (String × Json)
  | some v => [(k, v)]
  | none => []

def optStr (k : String) (v : Option String) : List (String × Json) :=
  optMember k (v.map Json.string)

/-- Does a list of type names name `term`, written bare, after `#` or after
`:` (a prefixed name)? -/
def hasTypeTerm (ts : List String) (term : String) : Bool :=
  ts.any fun t => t == term || t.endsWith ("#" ++ term) || t.endsWith (":" ++ term)

/-! ## Metadata -/

def linkJson (l : Link) : Json :=
  .object [ ("href", .string l.target), ("rel", .string l.rel)
          , ("params", .object (l.attrs.map fun (k, v) => (k, Json.string v))) ]

/-- The `Content-Length` of a response, when it is a decimal number. -/
def contentLength? (r : Resp) : Option Nat :=
  (r.header? "content-length").bind fun v =>
    let v := trimS v
    if v != "" && v.toList.all Char.isDigit then v.toNat? else none

/-- The first link of relation `rel` of a response. -/
def firstLink? (links : List Link) (rel : String) : Option String :=
  (links.find? fun l => l.rel.toLower == rel.toLower).map (·.target)

/-- Metadata of the resource at `url`, from the status and the header fields
of a response. -/
def metadataJson (url : String) (r : Resp) : Json :=
  let links := linksOf url r
  .object
    ([("url", .string url), ("status", natJson r.status)] ++
     optStr "etag" (r.header? "etag") ++ optStr "lastModified" (r.header? "last-modified") ++
     optStr "contentType" (r.header? "content-type") ++
     optMember "contentLength" ((contentLength? r).map natJson) ++
     [("links", .array (links.map linkJson))] ++
     optStr "linkset" (firstLink? links "linkset") ++ optStr "parent" (firstLink? links "up") ++
     optStr "storage" (firstLink? links lwsStorageRel) ++
     [ ("types", strsJson ((links.filter fun l => l.rel.toLower == "type").map (·.target)))
     , ("allow", strsJson (allowOf r)), ("acceptPatch", strsJson (acceptPatchOf r)) ])

/-! ## Listings -/

/-- One member of a listing: a bare identifier or an object with `id`,
`type`, `format`, `size`, `modified`. Identifiers are resolved against `base`. -/
def itemJson (base : String) (m : Json) : Json :=
  match m with
  | .object _ =>
      .object ([("id", .string (resolve base ((m.getString? "id").getD ""))), ("types", strsJson (typesOf m))] ++
        optStr "format" (m.getString? "format") ++ optMember "size" (m.field? "size") ++
        optStr "modified" (m.getString? "modified"))
  | .string s => .object [("id", .string (resolve base s)), ("types", .array [])]
  | _ => .object [("id", .string ""), ("types", .array [])]

/-- A page of a listing, from the response that carried it. The page `id` is
the document's, else the URL the page was read from. `none` when the body is
not a JSON object. -/
def pageJson (url : String) (r : Resp) : Option Json :=
  match r.json? with
  | some doc@(.object _) =>
      let links := linksOf url r
      some (.object
        ([("id", Json.string (((doc.getString? "id").map (resolve url)).getD url))] ++ [("types", strsJson (typesOf doc))] ++
         optMember "totalItems" (doc.field? "totalItems") ++
         [("items", .array ((listAt doc "items").map (itemJson url)))] ++
         optStr "first" (firstLink? links "first") ++ optStr "next" (firstLink? links "next") ++
         optStr "prev" (firstLink? links "prev") ++ optStr "last" (firstLink? links "last") ++
         [("metadata", metadataJson url r)]))
  | _ => none

/-! ## The storage description -/

def storageJson (base : String) (desc : Json) : Json :=
  let services := listAt desc "service"
  let root := services.find? fun sv => hasTypeTerm (typesOf sv) "StorageRoot"
  let move := (listAt desc "capability").find? fun c => hasTypeTerm (typesOf c) "MoveResource"
  let service (sv : Json) : Json :=
    .object (optStr "id" (sv.getString? "id") ++ [("types", strsJson (typesOf sv))] ++
      optStr "serviceEndpoint" ((sv.getString? "serviceEndpoint").map (resolve base)) ++
      optMember "subscriptionType" ((sv.field? "subscriptionType").map fun v =>
        match v with
        | .array _ => v
        | _ => .array [v]))
  let method (vm : Json) : Json :=
    .object (optStr "id" (vm.getString? "id") ++ optStr "type" (vm.getString? "type") ++
      optStr "controller" (vm.getString? "controller"))
  .object
    (optStr "id" (desc.getString? "id") ++ [("types", strsJson (typesOf desc))] ++
     optStr "storageRoot" ((root.bind fun sv => sv.getString? "serviceEndpoint").map (resolve base)) ++
     [("services", .array (services.map service))] ++
     [("verificationMethods", .array ((listAt desc "verificationMethod").map method))] ++
     (match move with
      | some c =>
          [("moveCapability", .object
            ([("appliesTo", if (listAt c "appliesTo").isEmpty then strsJson ["DataResource"]
                            else .array (listAt c "appliesTo"))] ++
             optMember "preservesIdentifier" (c.field? "preservesIdentifier")))]
      | none => []) ++
     [("raw", desc)])

/-! ## Subscriptions -/

def subscriptionJson (url : String) (r : Resp) : Json :=
  let raw := (r.json?).getD (.object [])
  .object ([ ("subscription", .string (((raw.getString? "id").map (resolve url)).getD url))
           , ("types", strsJson (typesOf raw)) ] ++
    optMember "expires" (raw.field? "expires") ++ [("raw", raw)])

/-! ## Bodies -/

/-- Is a media type textual: `text/*`, `application/json`, `application/xml`,
or a `+json` or `+xml` structured syntax suffix (RFC 6839)? -/
def textualType (contentType : String) : Bool :=
  let mt := (trimS ((contentType.splitOn ";").headD "")).toLower
  mt.startsWith "text/" || mt == "application/json" || mt == "application/xml" ||
    mt.endsWith "+json" || mt.endsWith "+xml"

/-- A body as text when its media type is textual and its bytes are UTF-8,
as base64 otherwise (RFC 4648 §4). -/
def bodyJson (contentType : Option String) (body : ByteArray) : Json :=
  match contentType, String.fromUTF8? body with
  | some ct, some t =>
      if textualType ct then .object [("text", .string t)]
      else .object [("base64", .string (Base64.encode body))]
  | _, _ => .object [("base64", .string (Base64.encode body))]

/-! ## Query formats -/

/-- The media types of an `Accept-Query` field (the QUERY method draft §3):
a list of tokens or strings, parameters dropped. -/
def acceptQueryOf (r : Resp) : List String :=
  match r.header? "accept-query" with
  | none => []
  | some v =>
      (splitTop ',' v.toList false false [] #[]).toList.filterMap fun p =>
        let t := trimS ((p.splitOn ";").headD "")
        if t == "" then none else (unquote t).orElse fun _ => some t

/-! ## Errors -/

/-- The name an HTTP status has in the driver protocol (§3.2). -/
def statusKind : Nat → Option String
  | 400 => some "BadRequestError" | 401 => some "UnauthorizedError" | 403 => some "ForbiddenError"
  | 404 => some "NotFoundError" | 405 => some "MethodNotAllowedError" | 406 => some "NotAcceptableError"
  | 409 => some "ConflictError" | 410 => some "GoneError" | 412 => some "PreconditionFailedError"
  | 415 => some "UnsupportedMediaTypeError" | 422 => some "UnprocessableContentError"
  | 501 => some "NotImplementedError" | 507 => some "InsufficientStorageError"
  | _ => none

/-- The engine failure codes that are authentication failures. -/
def authenticationCodes : List String := ["authorization", "discoveryValidation", "credential"]

/-- The engine failure codes that are responses breaking the specification. -/
def protocolCodes : List String :=
  [ "malformedDescription", "malformedLinkset", "malformedListing", "noEtag", "noLinkset"
  , "noMoveCapability", "noService", "noStorageLink", "noSubscriptionType", "notAdvertised"
  , "methodRefused" ]

private def truncateChars (s : String) (n : Nat) : String := String.ofList (s.toList.take n)

/-- The driver protocol's error (§3.2) for an engine `fail` document. -/
def errorReport (e : Json) : Json :=
  let code := jStr e "code"
  let status := jNat? e "status"
  let message := code ++ (match status with | some n => " (status " ++ toString n ++ ")" | none => "") ++
    ": " ++ truncateChars (toStringCompact e) 600
  let hs := jHeaders e "headers"
  let body := e.getString? "body"
  let bodyDoc : Option Json := body.bind parseJson?
  let withStatus (kind : String) (extra : List (String × Json)) : Json :=
    .object ([("kind", .string kind)] ++ optMember "status" (status.map natJson) ++
      [("message", .string message)] ++ extra)
  if code == "badArguments" then .object [("kind", .string "InvalidArguments"), ("message", .string message)]
  else if code == "transport" then .object [("kind", .string "TransportError"), ("message", .string message)]
  else if authenticationCodes.contains code then
    withStatus "AuthenticationError"
      (optStr "oauthError" (bodyDoc.bind fun b => b.getString? "error") ++
       optStr "oauthErrorDescription" (bodyDoc.bind fun b => b.getString? "error_description"))
  else match status with
  | some n =>
      let isJson := (headerIn hs "content-type").any fun ct => (ct.toLower.splitOn "json").length > 1
      withStatus ((statusKind n).getD "HttpError")
        ((if isJson then optMember "problem" bodyDoc else []) ++
         (if n == 405 then [("allow", strsJson (((headerIn hs "allow").map fieldTokens).getD []))] else []) ++
         (if n == 415 then [("acceptPatch", strsJson (((headerIn hs "accept-patch").map fieldTokens).getD []))] else []))
  | none =>
      if protocolCodes.contains code then .object [("kind", .string "ProtocolError"), ("message", .string message)]
      else .object [("kind", .string "InternalError"), ("message", .string message)]

/-- The error of a notification that failed verification. -/
def signatureError (reason : String) : Json :=
  .object [("kind", .string "SignatureVerificationError"), ("message", .string reason)]

#guard statusKind 404 == some "NotFoundError"
#guard statusKind 418 == none
#guard textualType "text/plain; charset=utf-8" && textualType "image/svg+xml" && !textualType "image/png"
#guard (bodyJson (some "image/png") "ab".toUTF8) == .object [("base64", .string "YWI=")]
#guard (bodyJson (some "text/plain") "ab".toUTF8) == .object [("text", .string "ab")]
#guard (bodyJson none "ab".toUTF8) == .object [("base64", .string "YWI=")]

end L4Factoidal.LWS.Client
