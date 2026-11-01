/-
L4Factoidal.WebAnnotation.ProtocolSuite — the W3C Web Annotation Protocol
server tests, run against `WebAnnotation.Protocol.step` in Lean.

The W3C suite for the Protocol (web-platform-tests `annotation-protocol/`,
vendored in `third_party/testing/web-annotation/`) is one page,
`server/server-manual.html`. A tester gives it a container URL and an
annotation URL, and it sends requests from the browser. This module is the
same request list and the same assertions, with the assertion texts of
that page as the check names, sent to the Lean handler over the reference
`LWS.MemStore`. The container is first filled with the suite's own 41
sample annotations (`annotation-protocol/files/annotations/*.json`) by
POST, so its listing has more than one page.

Three differences from the page, each stated in the check:

* The page tests on `first`, `last`, `partOf`, `next` and `prev` start a
  request that their test does not wait for, so in a browser they pass
  whatever the server answers. Here the request is made and the check
  decides.
* When `first` is an embedded page (§4.2.1, the default preference), the
  page check follows its `id`.
* Checks that the page does not make, marked `extra`, cover the other
  rules of §5 and §6: a GET after DELETE answers 410 and the container no
  longer lists the annotation, `If-Match` mismatch answers 412, a change to
  `canonical` answers 409, a body that is not an annotation answers 415,
  and the pages together hold every annotation once.
* A check marked `xfail` is a SHOULD that the handler does not meet yet,
  with its open issue: the Turtle representation of §3.1
  (https://github.com/danbri/factoidal/issues/1197). It is expected to
  fail; the harness fails the run when it passes.

`run` also returns every annotation that the server sent, so that the
harness checks each with the Data Model MUST tests.
-/
import L4Factoidal.WebAnnotation.Protocol

namespace L4Factoidal.WebAnnotation.ProtocolSuite

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.WebAnnotation.Protocol

/-- One assertion of the page (or an `extra` one). -/
structure Check where
  level : String
  name : String
  ok : Bool
deriving Repr

def headerOf (r : Response) (name : String) : Option String :=
  (r.headers.find? (fun (k, _) => k.toLower == name.toLower)).map (·.2)

def has (r : Response) (name sub : String) : Bool :=
  match headerOf r name with
  | some v => (v.splitOn sub).length > 1
  | none => false

def bodyJson (r : Response) : Json := (parseJson? r.body).getD .null

def strField (j : Json) (k : String) : Option String := strOf? (j.field? k)

/-- The IRI of a page reference: a string, or an embedded page's `id`. -/
def refIri : Option Json → Option String
  | some (.string s) => some s
  | some j@(.object _) => strField j "id"
  | _ => none

def mkReq (cfg : Protocol.Config) (method iri : String) (headers : List (String × String) := [])
    (body : String := "") : Request :=
  let rest := if iri.startsWith cfg.baseIri then
    String.ofList (iri.toList.drop cfg.baseIri.length) else iri
  let parts := rest.splitOn "?"
  { method, path := "/" ++ parts.headD "", queryStr := "?".intercalate (parts.drop 1),
    headers := headers.map (fun (k, v) => (k.toLower, v)), body }

def jsonLd : List (String × String) := [("Content-Type", "application/ld+json")]

/-- Run the page's requests. `samples` are (slug, annotation) pairs POSTed
first; `canonical` is the `urn:uuid:` IRI of the page's own annotation. -/
def run (cfg : Protocol.Config) (samples : List (String × Json)) (canonical : String) :
    List Check × List (String × Json) := Id.run do
  let S := MemStore
  let mut s := init S cfg {}
  let mut checks : List Check := []
  let mut sent : List (String × Json) := []
  let containerPath := cfg.containers.headD "/annotations/"
  let containerUrl := iriOfPath cfg.baseIri containerPath
  let must (n : String) (ok : Bool) : Check := { level := "must", name := n, ok }
  let should (n : String) (ok : Bool) : Check := { level := "should", name := n, ok }
  let extra (n : String) (ok : Bool) : Check := { level := "extra", name := n, ok }
  -- Fill the container.
  let mut created := 0
  for (slug, j) in samples do
    let (s', r) := step S cfg s (mkReq cfg "POST" containerUrl (("Slug", slug) :: jsonLd)
      (toStringCompact j))
    s := s'
    if r.status == 201 then
      created := created + 1
      sent := (s!"POST {slug}", bodyJson r) :: sent
  checks := extra s!"each of the {samples.length} sample annotations is created by POST (201)"
    (created == samples.length) :: checks
  let annotationUrl := iriOfPath cfg.baseIri (containerPath ++ ((samples.head?.map (·.1)).getD "anno"))
  let get (st : State MemState) (iri : String) (hs : List (String × String) := []) : Response :=
    (step S cfg st (mkReq cfg "GET" iri hs)).2
  let status (st : State MemState) (m iri : String) : Nat := (step S cfg st (mkReq cfg m iri)).2.status
  checks := must "Container MUST end in a \"/\" character" (containerUrl.endsWith "/") :: checks
  -- Container tests.
  let c := get s containerUrl
  let cb := bodyJson c
  checks := checks.reverse ++ [
    must "Containers MUST support GET (check Allow on GET)" (has c "Allow" "GET"),
    must "Containers MUST support HEAD (check Allow on GET)" (has c "Allow" "HEAD"),
    must "Containers MUST support OPTIONS (check Allow on GET)" (has c "Allow" "OPTIONS"),
    must "Containers MUST have a Content-Type header with the application/ld+json media type" (has c "Content-Type" "application/ld+json"),
    must "Containers MUST response with the JSON-LD representation (by default)" (has c "Content-Type" "application/ld+json"),
    must "Containers MUST return a description of the container with BasicContainer" ((typeValues cb).contains "BasicContainer"),
    must "Containers MUST return a description of the container with AnnotationCollection" ((typeValues cb).contains "AnnotationCollection"),
    must "Containers MUST return a Link header (rfc5988) on all responses" (headerOf c "Link").isSome,
    must "Containers MUST have an ETag header" (headerOf c "ETag").isSome,
    must "Containers MUST have a Vary header with Accept in the value" (has c "Vary" "Accept"),
    must "Containers MUST advertise its type by including a link where the rel parameter value is type and the target IRI is the appropriate Container Type" (has c "Link" "<http://www.w3.org/ns/ldp#BasicContainer>; rel=\"type\""),
    must "Containers MUST advertise that it imposes Annotation protocol specific constraints by including a link where the target IRI is http://www.w3.org/TR/annotation-protocol/, and the rel parameter value is the IRI http://www.w3.org/ns/ldp#constrainedBy" (has c "Link" "<http://www.w3.org/TR/annotation-protocol/>; rel=\"http://www.w3.org/ns/ldp#constrainedBy\""),
    must "Containers MUST support HEAD method" (status s "HEAD" containerUrl == 200),
    must "Containers MUST support OPTIONS method" (status s "OPTIONS" containerUrl == 200),
    must "Containers MUST include a Content-Location header with the IRI as its value" (headerOf c "Content-Location").isSome,
    must "Container's Content-Location and `id` MUST match" (headerOf c "Content-Location" == strField cb "id" && (strField cb "id").isSome)]
  for item in ((cb.field? "first").bind (·.field? "items")).elim [] (fun j => match j with | .array xs => xs | _ => []) do
    sent := ("GET container, first page item", item) :: sent
  let firstIri := refIri (cb.field? "first")
  let lastIri := refIri (cb.field? "last")
  let fp := firstIri.map (fun i => bodyJson (get s i))
  let lp := lastIri.map (fun i => bodyJson (get s i))
  let multi := firstIri != lastIri
  checks := checks ++ [
    must "Annotation Pages must have a link to the container they are part of, using the partOf property" (fp.any (fun j => (j.field? "partOf").isSome)),
    must "Annotation Pages MUST have a link to the previous page in the sequence, using the prev property (if not the first page)" (multi && lp.any (fun j => (j.field? "prev").isSome)),
    must "Annotation Pages MUST have a link to the next page in the sequence, using the next property (if not the last page)" (multi && fp.any (fun j => (j.field? "next").isSome))]
  -- Annotation tests.
  let a := get s annotationUrl
  sent := ("GET annotation", bodyJson a) :: sent
  checks := checks ++ [
    must "Annotations MUST support GET (check Allow on GET)" (has a "Allow" "GET"),
    must "Annotations MUST support HEAD (check Allow on GET)" (has a "Allow" "HEAD"),
    must "Annotations MUST support OPTIONS (check Allow on GET)" (has a "Allow" "OPTIONS"),
    must "Annotations MUST have a Content-Type header with the application/ld+json media type" (has a "Content-Type" "application/ld+json"),
    must "Annotations MUST have a Link header entry where the target IRI is http://www.w3.org/ns/ldp#Resource and the rel parameter value is type" (has a "Link" "<http://www.w3.org/ns/ldp#Resource>; rel=\"type\""),
    must "Annotations MUST have an ETag header" (headerOf a "ETag").isSome,
    must "Annotations MUST have a Vary header with Accept in the value" (has a "Vary" "Accept"),
    must "Annotations MUST support HEAD method" (status s "HEAD" annotationUrl == 200),
    must "Annotations MUST support OPTIONS method" (status s "OPTIONS" annotationUrl == 200)]
  -- Creation, update and deletion.
  let theAnnotation : Json := .object [
    ("@context", .string annoContext), ("type", .string "Annotation"),
    ("body", .object [("type", .string "TextualBody"), ("value", .string "I like this page!")]),
    ("target", .string "http://www.example.com/index.html"),
    ("canonical", .string canonical)]
  let (s1, cr) := step S cfg s (mkReq cfg "POST" containerUrl jsonLd (toStringCompact theAnnotation))
  let cj := bodyJson cr
  sent := ("POST the page's annotation", cj) :: sent
  let newId := (strField cj "id").getD ""
  checks := checks ++ [
    must "Created Annotation MUST have an id property" (strField cj "id").isSome,
    must "Created Annotation MUST have an id that starts with the Container IRI" (newId.startsWith containerUrl && newId != containerUrl),
    must "Created Annotation MUST preserve any canonical IRI" (strField cj "canonical" == some canonical),
    must "Annotation Server MUST respond with a 201 Created code if the creation is successful" (cr.status == 201),
    should "Location header SHOULD match the id of the new Annotation" (headerOf cr "Location" == some newId)]
  let updated : Json := match cj with
    | .object fs => .object (fs.map (fun (k, v) => if k == "target" then (k, .string "http://other.example/") else (k, v)))
    | j => j
  let (s2, ur) := step S cfg s1 (mkReq cfg "PUT" newId jsonLd (toStringCompact updated))
  sent := ("PUT the page's annotation", bodyJson ur) :: sent
  checks := checks ++ [
    must "Annotation update must be done with the PUT method" (ur.status == 200 && strField (bodyJson ur) "target" == some "http://other.example/")]
  let (s3, dr) := step S cfg s2 (mkReq cfg "DELETE" newId)
  let newPath' := "/" ++ String.ofList (newId.toList.drop cfg.baseIri.length)
  checks := checks ++ [
    must "Annotation deletion with DELETE method MUST return a 204 status" (dr.status == 204),
    extra "§5.3, §6: a GET after DELETE answers 410" (status s3 "GET" newId == 410),
    extra "§5.3: the IRI of the deleted Annotation is removed from the Annotation Container" (!((memberPaths S s3.store containerPath).contains newPath')),
    should "Annotation server SHOULD use HTTPS rather than HTTP" (containerUrl.toLower.startsWith "https:")]
  -- Preferences.
  let pr := get s containerUrl [("Prefer", "return=representation;include=\"http://www.w3.org/ns/ldp#PreferMinimalContainer\"")]
  let pj := bodyJson pr
  let pf := (refIri (pj.field? "first")).map (fun i => bodyJson (get s i))
  let pfItems := (pf.bind (·.field? "items")).elim [] (fun j => match j with | .array xs => xs | _ => [])
  for item in pfItems do sent := ("GET minimal container's first page item", item) :: sent
  checks := checks ++ [
    should "SHOULD return the full annotation descriptions" (!pfItems.isEmpty && pfItems.all (fun i => (i.field? "@context").isSome)),
    should "SHOULD include the total property with the total number of annotations in the container" (pj.field? "total").isSome,
    should "SHOULD have a link to the first page of its contents using `first`" (pj.field? "first").isSome,
    should "SHOULD have a link to the last page of its contents using `last`" (pj.field? "last").isSome,
    should "Response contains annotations via `items` when it SHOULD NOT" (pj.field? "items").isNone,
    should "Response contains annotations via `ldp:contains` when it SHOULD NOT" (pj.field? "ldp:contains").isNone,
    should "SHOULD include Prefer in the Vary header" (has pr "Vary" "Prefer"),
    should "SHOULD NOT [receive] the Prefer header when requesting the page" (headerOf pr "Prefer").isNone]
  -- Further rules of §4.2, §5 and §6.
  let ir := get s containerUrl [("Prefer", "return=representation;include=\"http://www.w3.org/ns/oa#PreferContainedIRIs\"")]
  let ij := bodyJson ir
  let irisFirst := (ij.field? "first").bind (·.field? "items")
  let turtle := get s annotationUrl [("Accept", "text/turtle")]
  let tag := (headerOf a "ETag").getD ""
  let (_, badMatch) := step S cfg s (mkReq cfg "DELETE" annotationUrl [("If-Match", "\"00000000\"")])
  let (_, goodMatch) := step S cfg s (mkReq cfg "DELETE" annotationUrl [("If-Match", tag)])
  let aj := bodyJson a
  let changedCanon : Json := match aj with
    | .object fs => .object (fs ++ [("canonical", .string "urn:uuid:changed")])
    | j => j
  let (s4, _) := step S cfg s (mkReq cfg "PUT" annotationUrl jsonLd (toStringCompact changedCanon))
  let (_, canonAgain) := step S cfg s4 (mkReq cfg "PUT" annotationUrl jsonLd
    (toStringCompact (match changedCanon with
      | .object fs => .object (fs.map (fun (k, v) => if k == "canonical" then (k, .string "urn:uuid:other") else (k, v)))
      | j => j)))
  let notAnno : Json := .object [("@context", .string annoContext), ("type", .string "Person")]
  let (_, na) := step S cfg s (mkReq cfg "POST" containerUrl jsonLd (toStringCompact notAnno))
  let (_, plainText) := step S cfg s (mkReq cfg "POST" containerUrl [("Content-Type", "text/plain")] "x")
  -- Walk the description pages from `first` with `next`.
  let mut walked : List String := []
  let mut next := firstIri
  for _ in List.range (samples.length + 2) do
    match next with
    | none => break
    | some i =>
      let pg := bodyJson (get s i)
      for item in ((pg.field? "items").elim [] (fun j => match j with | .array xs => xs | _ => [])) do
        walked := walked ++ [(strField item "id").getD ""]
      next := strField pg "next"
  let total := (memberPaths S s.store containerPath).length
  checks := checks ++ [
    extra "§4.2.1: PreferContainedIRIs embeds a first page whose items are IRIs" (match irisFirst with
      | some (.array xs) => !xs.isEmpty && xs.all (fun x => match x with | .string _ => true | _ => false)
      | _ => false),
    extra "§4.2: the Content-Location of the IRI view differs from the description view" (headerOf ir "Content-Location" != headerOf c "Content-Location"),
    extra "§6: a DELETE whose If-Match does not match answers 412" (badMatch.status == 412),
    extra "§5.3: a DELETE whose If-Match matches answers 204" (goodMatch.status == 204),
    extra "§5.2: a PUT that changes a canonical that was set answers 409" (canonAgain.status == 409),
    extra "§6: a POST of a body that is not an Annotation answers 415" (na.status == 415),
    extra "§6: a POST of a body that is not JSON-LD answers 415" (plainText.status == 415),
    { level := "xfail", name := "§3.1: a GET with Accept: text/turtle answers text/turtle (https://github.com/danbri/factoidal/issues/1197)",
      ok := has turtle "Content-Type" "text/turtle" },
    extra s!"§4.2: following next from first gives every annotation once ({total})"
      (walked.length == total && walked.eraseDups.length == total && total == samples.length)]
  return (checks, sent.reverse)

end L4Factoidal.WebAnnotation.ProtocolSuite
