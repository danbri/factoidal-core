/-
L4Factoidal.LWS.PaginationLinksTests — build-time checks of container
pagination (https://github.com/danbri/factoidal/issues/887) and of
client-managed links and `Prefer: set-linkset`
(https://github.com/danbri/factoidal/issues/888) through `LWS.step`, the
function the hosts call. Each behaviour has a positive and a negative case.
-/
import L4Factoidal.LWS.Tests

namespace L4Factoidal.LWS.PaginationLinksTests

open L4Factoidal.LWS
open L4Factoidal.LWS.Tests (emptyStorage req rtext hdr turtle)
open L4Factoidal.JSON
open L4Factoidal.HTTP (Request Response)

/-! ## Pagination -/

def pcfg : Config := { baseIri := "http://example.org/", pageSize := 2 }

def prun (r : Request) (st : MemState) : Response × MemState := step MemStore pcfg r st

/-- Five members written in an order that is not the path order. -/
def five : MemState :=
  ["e", "b", "d", "a", "c"].foldl (fun st n =>
    (prun (req "PUT" ("/c/" ++ n) [("content-type", "text/plain")] n) st).2) emptyStorage

def linkTo (resp : Response) (rel : String) : Option String :=
  ((hdr resp "link").getD "" |>.splitOn ", ").findSome? (fun l =>
    if (l.splitOn ("; rel=\"" ++ rel ++ "\"")).length > 1 then
      some (String.ofList (((l.splitOn ">").headD "").toList.drop 1))
    else none)

def itemIds (resp : Response) : List String :=
  match parseJson (rtext resp) with
  | .ok j => ((j.getArray? "items").getD []).filterMap (·.getString? "id")
  | .error _ => []

def totalItems (resp : Response) : Option String :=
  match parseJson (rtext resp) with
  | .ok (.object fs) => match fs.lookup "totalItems" with | some (.number n) => some n | _ => none
  | _ => none

/-- Follow `rel="next"` from the container, at most `fuel` pages (a loop
with an accumulator). -/
def walk (st : MemState) (acc : Array (List String × Response)) :
    Nat → String → Array (List String × Response)
  | 0, _ => acc
  | fuel + 1, target =>
      let (resp, _) := prun (req "GET" target) st
      let acc := acc.push (itemIds resp, resp)
      match linkTo resp "next" with
      | some t => walk st acc fuel t
      | none => acc

def pagesOfFive : List (List String × Response) := (walk five #[] 10 "/c/").toList

-- Concatenating the pages gives every member once, in path order.
#guard (pagesOfFive.map (·.1)).flatten ==
  ["a", "b", "c", "d", "e"].map ("http://example.org/c/" ++ ·)
#guard (pagesOfFive.map (·.1.length)) == [2, 2, 1]
-- Every page: 200, totalItems is the full count, rel="first" and rel="last".
#guard pagesOfFive.all (fun (_, r) => r.status == 200 && totalItems r == some "5" &&
  linkTo r "first" == some "/c/?page=1" && linkTo r "last" == some "/c/?page=3")
-- rel="next" on every page but the last; rel="prev" on every page but the first.
#guard (pagesOfFive.map (fun (_, r) => (linkTo r "next").isSome)) == [true, true, false]
#guard (pagesOfFive.map (fun (_, r) => linkTo r "prev")) == [none, some "/c/?page=1", some "/c/?page=2"]
-- Each page has its own entity tag, and If-None-Match with it gives 304.
#guard (pagesOfFive.map (fun (_, r) => hdr r "etag")).eraseDups.length == 3
#guard pagesOfFive.all (fun (_, r) => match hdr r "etag" with
  | some t => (prun (req "GET" ((linkTo r "first").getD "") [("if-none-match", t)]) five).1.status ==
                (if linkTo r "prev" == none then 304 else 200)
  | none => false)
-- A page that does not exist is 404; a malformed page name is 404.
#guard (prun (req "GET" "/c/?page=4") five).1.status == 404
#guard (prun (req "GET" "/c/?page=0") five).1.status == 404
#guard (prun (req "GET" "/c/?page=x") five).1.status == 404
-- At or below the threshold there is no pagination.
#guard (linkTo (step MemStore { pcfg with pageSize := 5 } (req "GET" "/c/") five).1 "first").isNone
#guard (itemIds (step MemStore { pcfg with pageSize := 0 } (req "GET" "/c/") five).1).length == 5
-- A change to the membership changes the leading clock of every page's tag.
#guard (match hdr (prun (req "GET" "/c/?page=3") five).1 "etag",
              hdr (prun (req "GET" "/c/?page=3")
                (prun (req "PUT" "/c/f" [("content-type", "text/plain")] "f") five).2).1 "etag" with
        | some a, some b => (a.splitOn "-").headD "" != (b.splitOn "-").headD ""
        | _, _ => false)
-- The Turtle representation of a page has the full count and only the page.
#guard (let r := (prun (req "GET" "/c/?page=3" [("accept", "text/turtle")]) five).1;
        ((rtext r).splitOn "lws:totalItems 5").length > 1 &&
        ((rtext r).splitOn "<http://example.org/c/e> a lws:DataResource").length > 1 &&
        ((rtext r).splitOn "<http://example.org/c/a> a lws:DataResource").length == 1)

/-! ## `paginateAlways`: a listing that fits on one page is one paginated page

Touchstone `core/pagination#pagination-single-page`: a paginated listing of
five members on one page carries `rel="first"` and neither `rel="next"` nor
`rel="prev"`. -/

def acfg : Config := { pcfg with pageSize := 100, paginateAlways := true }
def onePage : Response := (step MemStore acfg (req "GET" "/c/") five).1

-- Positive: rel="first" and rel="last" name page 1, all five items, totalItems 5,
-- no rel="next" and no rel="prev".
#guard onePage.status == 200 && linkTo onePage "first" == some "/c/?page=1" &&
  linkTo onePage "last" == some "/c/?page=1"
#guard (linkTo onePage "next").isNone && (linkTo onePage "prev").isNone
#guard (itemIds onePage).length == 5 && totalItems onePage == some "5"
-- Page 2 does not exist; an empty container is one empty page.
#guard (step MemStore acfg (req "GET" "/c/?page=2") five).1.status == 404
#guard (let r := (step MemStore acfg (req "GET" "/") emptyStorage).1
        r.status == 200 && linkTo r "first" == some "/?page=1" && (linkTo r "next").isNone)
-- The page's tag is a current tag of the container: If-Match with it lets a
-- DELETE through (Touchstone sends If-Match with the tag of a GET), and a
-- stale tag still gives 412.
#guard (match hdr onePage "etag" with
        | some t => (step MemStore acfg (req "DELETE" "/c/" [("if-match", t), ("depth", "infinity")]) five).1.status == 204
        | none => false)
#guard (step MemStore acfg (req "DELETE" "/c/" [("if-match", "\"0-stale\""), ("depth", "infinity")]) five).1.status == 412
-- Negative: without the option the same listing is not paginated.
#guard (linkTo (step MemStore { acfg with paginateAlways := false } (req "GET" "/c/") five).1 "first").isNone
-- Negative: page size 0 turns pagination off even with the option.
#guard (linkTo (step MemStore { acfg with pageSize := 0 } (req "GET" "/c/") five).1 "first").isNone
-- Above the page size the option changes nothing: three pages of two.
#guard (walk five #[] 10 "/c/").toList.map (·.1.length) ==
  ((let ac : Config := { pcfg with paginateAlways := true }
    let rec go (acc : List Nat) : Nat → String → List Nat
      | 0, _ => acc.reverse
      | f + 1, t =>
          let r := (step MemStore ac (req "GET" t) five).1
          match linkTo r "next" with
          | some n => go ((itemIds r).length :: acc) f n
          | none => ((itemIds r).length :: acc).reverse
    go [] 10 "/c/"))

/-! ## Client-managed links and `Prefer: set-linkset` -/

def lws (r : Request) (st : MemState) : Response × MemState := step MemStore Tests.cfg r st

def licField : String := "<https://creativecommons.org/licenses/by/4.0/>; rel=\"license\""
def plain : List (String × String) := [("content-type", "text/plain")]

def withLicence : MemState :=
  (lws (req "PUT" "/lic.txt" (plain ++ [("prefer", "set-linkset"), ("link", licField)]) "x")
    emptyStorage).2

def linksetText (st : MemState) (p : String) : String :=
  rtext (lws (req "GET" (p ++ "?linkset")) st).1

def hasLicence (st : MemState) : Bool :=
  ((linksetText st "/lic.txt").splitOn
    "\"license\":[{\"href\":\"https://creativecommons.org/licenses/by/4.0/\"}]").length > 1

-- PUT with Prefer: set-linkset stores the client link in the linkset.
#guard hasLicence withLicence
-- Without the preference the Link field has no effect on the linkset.
#guard !hasLicence (lws (req "PUT" "/lic.txt" (plain ++ [("link", licField)]) "x") emptyStorage).2
-- A later PUT without the preference keeps the client links.
#guard hasLicence (lws (req "PUT" "/lic.txt" plain "y") withLicence).2
-- A PUT with the preference and no Link field replaces them with none.
#guard !hasLicence (lws (req "PUT" "/lic.txt" (plain ++ [("prefer", "set-linkset")]) "y") withLicence).2
-- The protection rule: a server-managed relation is refused with 409 and
-- nothing is written. For `type` that holds when the link names a class of
-- the server; another target is a declared type (lws10-index §Type and
-- Relation Derivation, https://github.com/danbri/factoidal/issues/912).
#guard (serverManagedRels.filter (· != "type")).all (fun rel =>
  let (resp, st) := lws (req "PUT" "/lic.txt" (plain ++ [("prefer", "set-linkset"),
    ("link", "<https://example.org/x>; rel=\"" ++ rel ++ "\"")]) "z") withLicence
  resp.status == 409 && hdr resp "content-type" == some "application/problem+json" &&
  (lws (req "GET" "/lic.txt") st).1.content == "x".toUTF8 && hasLicence st)
#guard nativeTypeTargets.all (fun t =>
  let (resp, st) := lws (req "PUT" "/lic.txt" (plain ++ [("prefer", "set-linkset"),
    ("link", "<" ++ t ++ ">; rel=\"type\"")]) "z") withLicence
  resp.status == 409 && (lws (req "GET" "/lic.txt") st).1.content == "x".toUTF8 && hasLicence st)
-- A declared type replaces the client links, and the PUT says it applied the preference.
#guard
  let (resp, st) := lws (req "PUT" "/lic.txt" (plain ++ [("prefer", "set-linkset"),
    ("link", "<https://example.org/x>; rel=\"type\"")]) "z") withLicence
  (resp.status == 204 || resp.status == 200) && hdr resp "preference-applied" == some "set-linkset" &&
  !hasLicence st
-- A malformed link is refused with 400.
#guard (lws (req "PUT" "/lic.txt" (plain ++ [("prefer", "set-linkset"),
  ("link", "<a b>; rel=\"license\"")]) "z") withLicence).1.status == 400
#guard (lws (req "PUT" "/lic.txt" (plain ++ [("prefer", "set-linkset"),
  ("link", "<a>; rel=\"Not A Rel\"")]) "z") withLicence).1.status == 400
-- POST stores the client links and does not store the type hint.
#guard (let (resp, st) := lws (req "POST" "/" (plain ++ [("slug", "p"),
          ("link", "<https://example.org/me>; rel=\"author\", <https://www.w3.org/ns/lws#DataResource>; rel=\"type\"")]) "p")
          withLicence
        resp.status == 201 &&
        ((linksetText st "/p").splitOn "\"author\":[{\"href\":\"https://example.org/me\"}]").length > 1 &&
        ((linksetText st "/p").splitOn "\"type\":[").length == 2)
-- JSON Patch on a resource with the preference adds links (a partial update).
#guard (let st0 := (lws (req "PUT" "/d.json" (("content-type", "application/json") ::
            [("prefer", "set-linkset"), ("link", licField)]) "{\"n\":1}") emptyStorage).2
        let (resp, st) := lws (req "PATCH" "/d.json" [("content-type", "application/json-patch+json"),
            ("prefer", "set-linkset"), ("link", "<https://example.org/me>; rel=\"author\"")]
            "[{\"op\":\"replace\",\"path\":\"/n\",\"value\":2}]") st0
        resp.status == 204 && ((linksetText st "/d.json").splitOn "\"license\"").length > 1 &&
        ((linksetText st "/d.json").splitOn "\"author\"").length > 1)
-- JSON Patch on the linkset adds a client link; the resource's tag is unchanged.
#guard (let (resp, st) := lws (req "PATCH" "/lic.txt?linkset" [("content-type", "application/json-patch+json")]
          "[{\"op\":\"add\",\"path\":\"/linkset/0/author\",\"value\":[{\"href\":\"https://example.org/me\"}]}]")
          withLicence
        resp.status == 204 &&
        ((linksetText st "/lic.txt").splitOn "\"author\"").length > 1 &&
        hdr (lws (req "GET" "/lic.txt") st).1 "etag" == hdr (lws (req "GET" "/lic.txt") withLicence).1 "etag" &&
        hdr (lws (req "GET" "/lic.txt?linkset") st).1 "etag" !=
          hdr (lws (req "GET" "/lic.txt?linkset") withLicence).1 "etag" &&
        st.clock > withLicence.clock)
-- A JSON Patch that replaces a server-managed link is 409.
#guard (lws (req "PATCH" "/lic.txt?linkset" [("content-type", "application/json-patch+json")]
          "[{\"op\":\"replace\",\"path\":\"/linkset/0/type/0/href\",\"value\":\"https://www.w3.org/ns/lws#Container\"}]")
          withLicence).1.status == 409
-- A JSON Patch that adds a link of a server-managed relation is 409.
#guard (lws (req "PATCH" "/lic.txt?linkset" [("content-type", "application/json-patch+json")]
          "[{\"op\":\"add\",\"path\":\"/linkset/0/items\",\"value\":[{\"href\":\"x\"}]}]")
          withLicence).1.status == 409
-- PUT on the linkset replaces the client links; the server links are kept.
#guard (let (resp, st) := lws (req "PUT" "/lic.txt?linkset" [("content-type", "application/linkset+json")]
          "{\"linkset\":[{\"anchor\":\"http://example.org/lic.txt\",\"author\":[{\"href\":\"https://example.org/me\"}]}]}")
          withLicence
        resp.status == 204 && !hasLicence st &&
        ((linksetText st "/lic.txt").splitOn "\"up\":[{\"href\":\"http://example.org/\"}]").length > 1 &&
        ((linksetText st "/lic.txt").splitOn "\"author\"").length > 1)
-- A failed If-Match on the linkset is 412 and changes nothing.
#guard (let (resp, st) := lws (req "PUT" "/lic.txt?linkset" [("content-type", "application/linkset+json"),
          ("if-match", "\"nope\"")] "{\"linkset\":[{\"anchor\":\"http://example.org/lic.txt\"}]}") withLicence
        resp.status == 412 && hasLicence st)
-- `linksetPut := false` (LWS §Metadata: "If the server does not support PUT,
-- it MUST reject the request with 405 Method Not Allowed"): Allow leaves PUT
-- out, a PUT answers 405 with Allow and changes nothing, PATCH still works.
def noPut : Config := { Tests.cfg with linksetPut := false }
#guard (let r := (step MemStore noPut (req "GET" "/lic.txt?linkset") withLicence).1
        hdr r "allow" == some "GET, HEAD, OPTIONS, PATCH")
#guard (let (resp, st) := step MemStore noPut (req "PUT" "/lic.txt?linkset"
          [("content-type", "application/linkset+json")]
          "{\"linkset\":[{\"anchor\":\"http://example.org/lic.txt\"}]}") withLicence
        resp.status == 405 && hdr resp "allow" == some "GET, HEAD, OPTIONS, PATCH" && hasLicence st)
#guard (step MemStore noPut (req "OPTIONS" "/lic.txt?linkset") withLicence).1.headers.lookup "allow" ==
  some "GET, HEAD, OPTIONS, PATCH"
#guard (step MemStore noPut (req "PATCH" "/lic.txt?linkset" [("content-type", "application/json-patch+json")]
          "[{\"op\":\"add\",\"path\":\"/linkset/0/author\",\"value\":[{\"href\":\"https://example.org/me\"}]}]")
          withLicence).1.status == 204
-- Negative: by default Allow names PUT, and the same PUT is not 405.
#guard hdr (lws (req "GET" "/lic.txt?linkset") withLicence).1 "allow" == some "GET, HEAD, OPTIONS, PATCH, PUT"
#guard (lws (req "PUT" "/lic.txt?linkset" [("content-type", "application/linkset+json")]
          "{\"linkset\":[{\"anchor\":\"http://example.org/lic.txt\"}]}") withLicence).1.status == 204
-- The client links survive the snapshot round trip.
#guard (match memStateOfJson (snapshotJson withLicence) with
        | .ok st => hasLicence st
        | .error _ => false)

end L4Factoidal.LWS.PaginationLinksTests
