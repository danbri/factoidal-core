/-
L4Factoidal.WebDAV.Local — the storage operations as LWS requests.
https://github.com/danbri/factoidal/issues/1066

A `local` mount is an LWS storage directory, opened by the ops `lws-serve`
uses (`lwsOpen` with `insecureNoAuth`: the WebDAV server is the storage's
owner, design record § "Local mounts"). Each storage operation is ONE LWS
request (`localRequest`), stepped by `L4Factoidal.LWS.Operations.step`
through the storage handle with no HTTP between; its response is read back
by `answerOf`, which `Remote` shares.

    head p    HEAD p
    list p    GET p, Accept: application/lws+json (the handle is opened with
              pagination off, so one page holds every member)
    get p     GET p
    put p     PUT p, Content-Type (when given), If-None-Match: * (only new)
    delete p  DELETE p, Depth: infinity for a container (lws10-core
              §Delete Resource: "Clients MUST use the Depth: infinity header
              to request for a recursive delete")

A listing's `modified` (`xsd:dateTime` in UTC, `LWS.Binding.isoDateTime`)
becomes an HTTP-date for `DAV:getlastmodified` (`httpDateOfIso`).
-/
import L4Factoidal.WebDAV.Backend
import L4Factoidal.LWS.Operations
import L4Factoidal.LWS.HttpDate
import L4Factoidal.JSON.Parser

namespace L4Factoidal.WebDAV

open L4Factoidal.JSON

/-- One request to a local storage handle. -/
structure LwsReq where
  method : String
  target : String
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
deriving Inhabited

def mediaLwsJson : String := "application/lws+json"

/-- The LWS request of a storage operation. -/
def localRequest : BOp → LwsReq
  | .head p => { method := "HEAD", target := p }
  | .list p => { method := "GET", target := p, headers := [("accept", mediaLwsJson)] }
  | .get p => { method := "GET", target := p }
  | .put p ct body onlyNew =>
    { method := "PUT", target := p, body
      headers := (if ct == "" then [] else [("content-type", ct)]) ++
                 (if onlyNew then [("if-none-match", "*")] else []) }
  | .delete p =>
    { method := "DELETE", target := p
      headers := if p.endsWith "/" then [("depth", "infinity")] else [] }

def headerIn (hs : List (String × String)) (name : String) : Option String :=
  (hs.find? (fun (n, _) => n.toLower == name)).map (·.2)

/-- Two digits at a position of a character list. -/
def digitsAt (cs : List Char) (i n : Nat) : Option Nat :=
  let ds := (cs.drop i).take n
  if ds.length == n && ds.all Char.isDigit then String.ofList ds |>.toNat? else none

/-- `YYYY-MM-DDTHH:MM:SSZ` (what `LWS.Binding.isoDateTime` writes) as an
HTTP-date (RFC 9110 §5.6.7). -/
def httpDateOfIso (s : String) : Option String := do
  let cs := s.toList
  let y ← digitsAt cs 0 4
  let mo ← digitsAt cs 5 2
  let d ← digitsAt cs 8 2
  let h ← digitsAt cs 11 2
  let mi ← digitsAt cs 14 2
  let se ← digitsAt cs 17 2
  if !(1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ 31 && h < 24 && mi < 60 && se < 61) then none
  let t := L4Factoidal.LWS.unixOfCivil y mo d (h * 3600 + mi * 60 + se)
  if t < 0 then none else some (L4Factoidal.LWS.httpDate t.toNat)

#guard httpDateOfIso "2001-09-09T01:46:42Z" == some "Sun, 09 Sep 2001 01:46:42 GMT"
#guard httpDateOfIso "1970-01-01T00:00:00Z" == some "Thu, 01 Jan 1970 00:00:00 GMT"
#guard httpDateOfIso "garbage" == none

/-- The storage path of a listing item's `id`: the id with the storage
root's IRI removed. `none` when the id is not under the root. -/
def pathOfId (root id : String) : Option String :=
  if id.startsWith root then some ("/" ++ dropS id root.length)
  else if id.startsWith "/" then some id else none

/-- One listing item (`LWS.Binding.itemJson`) as metadata. -/
def metaOfItem (root : String) (j : Json) : Option Meta := do
  let id ← j.getString? "id"
  let path ← pathOfId root id
  let isColl := j.getString? "type" == some "Container"
  let length := match j.field? "size" with
    | some (.number n) => n.toNat?
    | _ => none
  pure { path, isColl
         contentType := if isColl then none else j.getString? "format"
         length
         modified := (j.getString? "modified").bind httpDateOfIso }

/-- The metadata a response's header fields give. -/
def metaOfHeaders (path : String) (hs : List (String × String)) : Meta :=
  { path, isColl := path.endsWith "/"
    etag := headerIn hs "etag"
    contentType := headerIn hs "content-type"
    length := (headerIn hs "content-length").bind String.toNat?
    modified := headerIn hs "last-modified" }

/-- Read a storage's answer to an operation: its status, header fields and
content. `root` is the IRI of the storage root (listing ids are absolute).
`items`: the listing members when the answer came from a client that
gathered every page (`Remote`), otherwise read from the content. -/
def answerOf (root : String) (op : BOp) (status : Nat) (hs : List (String × String))
    (body : ByteArray) (items : Option (List Json) := none) : BAns :=
  let ok := 200 ≤ status && status < 300
  let detail := if ok then "" else ((String.fromUTF8? body).getD "").take 300 |>.toString
  match op with
  | .list p =>
    if !ok then { status, detail } else
    let its : List Json := match items with
      | some xs => xs
      | none => match (String.fromUTF8? body).bind parseJson? with
        | some j => (j.getArray? "items").getD []
        | none => []
    let members := its.filterMap (metaOfItem root)
    { status, info := some (metaOfHeaders p hs), members := members.filter (·.path != p) }
  | .get p => { status, info := some (metaOfHeaders p hs), body := if ok then body else ByteArray.empty, detail }
  | op => { status, info := if ok then some (metaOfHeaders op.path hs) else none, detail }

#guard (answerOf "http://localhost/" (.list "/a/") 200 []
          ("{\"items\":[{\"id\":\"http://localhost/a/b.txt\",\"type\":\"DataResource\",\"format\":\"text/plain\",\"size\":5,\"modified\":\"2001-09-09T01:46:42Z\"}," ++
           "{\"id\":\"http://localhost/a/c/\",\"type\":\"Container\",\"modified\":\"2001-09-09T01:46:42Z\"}]}").toUTF8).members ==
  [ { path := "/a/b.txt", isColl := false, contentType := some "text/plain", length := some 5,
      modified := some "Sun, 09 Sep 2001 01:46:42 GMT" },
    { path := "/a/c/", isColl := true, modified := some "Sun, 09 Sep 2001 01:46:42 GMT" } ]
#guard (localRequest (.delete "/a/")).headers == [("depth", "infinity")]
#guard (localRequest (.put "/a/" "" ByteArray.empty true)).headers == [("if-none-match", "*")]

end L4Factoidal.WebDAV
