/-
L4Factoidal.LWS.MoveTests — `#guard`s for moving resources (LWS 1.0 core
§Moving Resources, `L4Factoidal.LWS.Move`),
https://github.com/danbri/factoidal/issues/914.

Each check runs `step` on the reference store `MemStore`, so the request
goes through the linkset PATCH or PUT exactly as a host sends it. The
authorization checks run `Authorization.decide` with a stub verifier; the
notification check runs `Notifications.serverStep`. Host checks over HTTP:
`node tests/lws/draft-binding.mjs`, the "Moving Resources" rows.
-/
import L4Factoidal.LWS.Notifications

namespace L4Factoidal.LWS.MoveTests

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)

private def cfg : Config := { baseIri := "http://localhost/", moves := true }

private def st0 : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := .empty, mtime := 1000 }], clock := 1001 }

private def req (m t : String) (hs : List (String × String) := []) (body : String := "") : Request :=
  { method := m, path := t, queryStr := "", headers := hs, body }

private def run (st : MemState) (r : Request) (c : Config := cfg) : Response × MemState :=
  step MemStore c r st

private def runAll (st : MemState) (rs : List Request) : MemState :=
  rs.foldl (fun s r => (run s r).2) st

private def putText (t body : String) : Request := req "PUT" t [("content-type", "text/plain")] body
private def putDir (t : String) : Request := req "PUT" t [("content-type", "text/turtle")] ""

/-- A JSON Patch that replaces the `up` target, as Touchstone and the
draft's examples send it. -/
private def moveTo (t dest : String) : Request :=
  req "PATCH" (t ++ "?linkset") [("content-type", "application/json-patch+json")]
    ("[{\"op\":\"replace\",\"path\":\"/linkset/0/up/0/href\",\"value\":\"" ++ dest ++ "\"}]")

private def patchLs (t patch : String) : Request :=
  req "PATCH" (t ++ "?linkset") [("content-type", "application/json-patch+json")] patch

private def stA : MemState := runAll st0
  [ putText "/src/a.txt" "a resource on the move", putDir "/dst/",
    putText "/src/box/inner.txt" "carried along", putText "/other.txt" "not a container" ]

private def status (st : MemState) (r : Request) : Nat := (run st r).1.status
private def exists? (st : MemState) (t : String) : Bool := (memLookup st t).isSome
private def j (s : String) : Json := (parseJson? s).getD .null
private def listed (st : MemState) (c : String) : List String :=
  ((j (run st (req "GET" c [("accept", "application/lws+json")])).1.body).getArray? "items").getD []
    |>.filterMap (·.getString? "id")
private def etag (st : MemState) (t : String) : Option String :=
  (run st (req "GET" t [("accept", "application/lws+json")])).1.headers.lookup "etag"

/-! ## Discovery (§Storage Capabilities) -/

private def capability (c : Config) : Option Json :=
  ((j (run st0 (req "GET" storagePath) c).1.body).getArray? "capability").bind (·.head?)

#guard (capability cfg).bind (·.getString? "type") == some "MoveResource"
#guard (capability cfg).bind (·.field? "appliesTo") ==
  some (.array [.string "DataResource", .string "Container"])
#guard (capability cfg).bind (·.field? "preservesIdentifier") == some (.bool false)
-- Negative: a storage that does not move describes no capability ...
#guard capability { cfg with moves := false } == none
-- ... and refuses the change of an up link with 409 ("A server that does not
-- allow it MUST reject the request with an appropriate 4xx status code").
#guard status stA (moveTo "/src/a.txt" "http://localhost/dst/") == 200
#guard (run stA (moveTo "/src/a.txt" "http://localhost/dst/") { cfg with moves := false }).1.status == 409
#guard exists? (run stA (moveTo "/src/a.txt" "http://localhost/dst/") { cfg with moves := false }).2 "/src/a.txt"

/-! ## A data resource moves (§Moving Resources, "Effect on containment") -/

private def mv1 : Response × MemState := run stA (moveTo "/src/a.txt" "http://localhost/dst/")
private def stB : MemState := mv1.2

-- 200 with the new linkset and Content-Location (identifiers are not preserved).
#guard mv1.1.status == 200
#guard mv1.1.headers.lookup "content-location" == some "/dst/a.txt?linkset"
#guard mv1.1.headers.lookup "content-type" == some "application/linkset+json"
#guard (((j mv1.1.body).getArray? "linkset").bind (·.head?)).bind (·.getString? "anchor") ==
  some "http://localhost/dst/a.txt"
-- The resource is at its new path with the same bytes and media type; nothing at the old one.
#guard exists? stB "/dst/a.txt" && !exists? stB "/src/a.txt"
#guard (memLookup stB "/dst/a.txt").map (·.body.toList) == (memLookup stA "/src/a.txt").map (·.body.toList)
#guard (memLookup stB "/dst/a.txt").map (·.contentType) == some "text/plain"
#guard status stB (req "GET" "/src/a.txt") == 404
-- One listing loses it, the other gains it; both containers get a new ETag.
#guard listed stB "/dst/" == ["http://localhost/dst/a.txt"]
#guard !(listed stB "/src/").contains "http://localhost/src/a.txt"
#guard (listed stA "/src/").contains "http://localhost/src/a.txt"
#guard etag stA "/src/" != etag stB "/src/" && etag stA "/dst/" != etag stB "/dst/"
-- Its up link now names the destination.
#guard ((run stB (req "GET" "/dst/a.txt")).1.headers.lookup "link").map
  (fun v => decide ((v.splitOn "</dst/>; rel=\"up\"").length > 1)) == some true

/-! ## Client links travel with the resource -/

private def stL : MemState := (run stA (patchLs "/src/a.txt"
  "[{\"op\":\"add\",\"path\":\"/linkset/0/license\",\"value\":[{\"href\":\"https://creativecommons.org/licenses/by/4.0/\"}]}]")).2
private def stL2 : MemState := (run stL (moveTo "/src/a.txt" "http://localhost/dst/")).2

#guard (memLookup stL2 "/dst/a.txt").map (·.links.map (·.rel)) == some ["license"]
-- A path-absolute target is accepted too (the draft's second example).
#guard status stA (moveTo "/src/a.txt" "/dst/") == 200

/-! ## A container moves with its descendants -/

private def stC : MemState := (run stA (moveTo "/src/box/" "http://localhost/dst/")).2

#guard status stA (moveTo "/src/box/" "http://localhost/dst/") == 200
#guard exists? stC "/dst/box/" && exists? stC "/dst/box/inner.txt"
#guard !exists? stC "/src/box/" && !exists? stC "/src/box/inner.txt"
#guard listed stC "/dst/" == ["http://localhost/dst/box/"]
#guard listed stC "/dst/box/" == ["http://localhost/dst/box/inner.txt"]

/-! ## Refusals -/

-- Into itself, and into its own descendant (409, the draft's third example).
private def stD : MemState := (run stA (putDir "/src/box/deeper/")).2
#guard status stD (moveTo "/src/box/" "http://localhost/src/box/") == 409
#guard status stD (moveTo "/src/box/" "http://localhost/src/box/deeper/") == 409
#guard exists? (run stD (moveTo "/src/box/" "http://localhost/src/box/deeper/")).2 "/src/box/inner.txt"
-- To a container that does not exist, and to a data resource.
#guard status stA (moveTo "/src/a.txt" "http://localhost/nowhere/") == 409
#guard status stA (moveTo "/src/a.txt" "http://localhost/other.txt") == 409
-- Removing the up link, or giving two.
#guard status stA (patchLs "/src/a.txt" "[{\"op\":\"remove\",\"path\":\"/linkset/0/up\"}]") == 409
#guard status stA (patchLs "/src/a.txt"
  "[{\"op\":\"add\",\"path\":\"/linkset/0/up/-\",\"value\":{\"href\":\"http://localhost/dst/\"}}]") == 409
-- The storage root.
#guard status stA (patchLs "/"
  "[{\"op\":\"add\",\"path\":\"/linkset/0/up\",\"value\":[{\"href\":\"http://localhost/dst/\"}]}]") == 409
-- Another storage.
#guard status stA (moveTo "/src/a.txt" "http://elsewhere.example/dst/") == 409
-- The destination already holds a resource of that name.
private def stE : MemState := (run stA (putText "/dst/a.txt" "already here")).2
#guard status stE (moveTo "/src/a.txt" "http://localhost/dst/") == 409
#guard (memLookup (run stE (moveTo "/src/a.txt" "http://localhost/dst/")).2 "/dst/a.txt").map
  (·.body.toList) == some "already here".toUTF8.toList
-- A stale If-Match is 412 and moves nothing.
#guard status stA ({ moveTo "/src/a.txt" "http://localhost/dst/" with
  headers := [("content-type", "application/json-patch+json"), ("if-match", "\"stale\"")] }) == 412
-- The same parent is no move: the patch is accepted and nothing moves.
#guard status stA (moveTo "/src/a.txt" "http://localhost/src/") == 204
#guard exists? (run stA (moveTo "/src/a.txt" "http://localhost/src/")).2 "/src/a.txt"

/-! ## The plan names every moved path -/

#guard ((planMove MemStore stA "/src/box/" "/dst/").toOption.map (fun p =>
  p.moves.length == 2 && p.moves.contains ("/src/box/inner.txt", "/dst/box/inner.txt") &&
  p.moves.contains ("/src/box/", "/dst/box/"))) == some true
#guard movedPath "/a.txt" "/d/a.txt" "/a.txt.acl" == some "/d/a.txt.acl"
#guard movedPath "/a.txt" "/d/a.txt" "/a.txtx" == none
#guard movedPath "/c/" "/d/c/" "/c/x/y" == some "/d/c/x/y"
#guard movedPath "/c/" "/d/c/" "/cc/x" == none
#guard depth "/a/b/" == 2 && depth "/" == 0

/-! ## Authorization (§Moving Resources, "Authorization") -/

section Authz

open L4Factoidal.LWS.Authorization
open L4Factoidal.JOSE

private def stubV : Verifiers :=
  { es256 := fun _ _ sig => sig == "good".toUTF8
    rs256 := fun _ _ _ _ => false
    eddsa := fun _ _ _ => false }

private def zeros : ByteArray := ⟨Array.replicate 32 0⟩
private def issuerA : String := "https://as.example"
private def alice : String := "https://id.example/alice"
private def bob : String := "https://id.example/bob"
private def acfg : AuthzConfig :=
  { issuers := [{ issuer := issuerA, keys := [{ kid := some "k1", key := .ec zeros zeros }],
                  fetchedAt := some 1000 }] }
private def b64 (s : String) : String := Base64Url.encodeUtf8 s
private def tokFor (sub : String) : String :=
  b64 "{\"alg\":\"ES256\",\"typ\":\"at+jwt\",\"kid\":\"k1\"}" ++ "." ++
  b64 ("{\"iss\":\"https://as.example\",\"sub\":\"" ++ sub ++
    "\",\"aud\":\"http://localhost/.well-known/lws-storage\",\"exp\":1300,\"iat\":1000}") ++ "." ++
  Base64Url.encode "good".toUTF8

private def acl (c : String) (modes : String) : String :=
  "@prefix acl: <http://www.w3.org/ns/auth/acl#> .\n" ++
  "<http://localhost" ++ c ++ ".acl#owner> a acl:Authorization ; acl:agent <" ++ alice ++ "> ;\n" ++
  "  acl:accessTo <http://localhost" ++ c ++ "> ; acl:default <http://localhost" ++ c ++ "> ;\n" ++
  "  acl:mode acl:Read, acl:Write, acl:Control .\n" ++
  "<http://localhost" ++ c ++ ".acl#bob> a acl:Authorization ; acl:agent <" ++ bob ++ "> ;\n" ++
  "  acl:accessTo <http://localhost" ++ c ++ "> ; acl:default <http://localhost" ++ c ++ "> ;\n" ++
  "  acl:mode " ++ modes ++ " .\n"

private def aclEntry (c modes : String) : Entry :=
  { path := c ++ ".acl", kind := .metadataResource, contentType := "text/turtle",
    body := textBytes (acl c modes), mtime := 1 }

-- bob may write in /src/; only read /ro/ (plus Append); read /dst/; read and append /in/.
private def stZ : MemState :=
  let base := runAll st0 [ putText "/src/a.txt" "x", putText "/ro/b.txt" "y", putText "/src/sub/c.txt" "w",
                           putDir "/dst/", putDir "/in/" ]
  { base with entries := [ aclEntry "/" "acl:Read", aclEntry "/src/" "acl:Read, acl:Write",
                           aclEntry "/ro/" "acl:Read, acl:Append", aclEntry "/dst/" "acl:Read",
                           aclEntry "/in/" "acl:Read, acl:Append" ] ++ base.entries }

private def asBob (r : Request) : Request :=
  { r with headers := r.headers ++ [("authorization", "Bearer " ++ tokFor bob)] }

private def decision (r : Request) : Nat :=
  match decide stubV MemStore cfg acfg 1100 r stZ with
  | .respond resp => resp.status
  | .proceed _ => 0
  | .fetch _ _ => 1

-- Delete of the resource and create in the destination: allowed.
#guard decision (asBob (moveTo "/src/a.txt" "http://localhost/in/")) == 0
-- No create in the destination: 403.
#guard decision (asBob (moveTo "/src/a.txt" "http://localhost/dst/")) == 403
-- No delete of the resource (Append only): 403.
#guard decision (asBob (moveTo "/ro/b.txt" "http://localhost/in/")) == 403
-- Without a token: 401.
#guard decision (moveTo "/src/a.txt" "http://localhost/in/") == 401
-- A linkset PATCH that moves nothing needs no more than before.
#guard decision (asBob (patchLs "/src/a.txt"
  "[{\"op\":\"add\",\"path\":\"/linkset/0/license\",\"value\":[{\"href\":\"https://example.org/l\"}]}]")) == 0
-- A container move needs the delete of every resource below it: allowed
-- when bob may write the whole subtree, refused (403) when one resource
-- below it is read-only for him (its ACL resource is in the subtree too,
-- and deleting an ACL resource needs acl:Control).
private def stY : MemState :=
  { stZ with entries := aclEntry "/src/sub/locked/" "acl:Read" ::
      (runAll stZ [putText "/src/sub/locked/d.txt" "z"]).entries }
#guard decision (asBob (moveTo "/src/sub/" "http://localhost/in/")) == 0
#guard (match decide stubV MemStore cfg acfg 1100
    (asBob (moveTo "/src/sub/" "http://localhost/in/")) stY with
  | .respond resp => resp.status == 403
  | _ => false)


end Authz

/-! ## The Move notification (§Activity Types) -/

section Notify

open L4Factoidal.LWS.Notifications

private def stubN : JOSE.Verifiers :=
  { es256 := fun _ _ _ => false, rs256 := fun _ _ _ _ => false, eddsa := fun _ _ _ => false }

private def ncfg : Config := { cfg with notifications := true }
private def az : Authorization.AuthzConfig := { insecureNoAuth := true }

private def step1 (st : MemState) (ns : NotifState) (r : Request) :
    Response × MemState × NotifState × List Delivery :=
  match serverStep stubN MemStore ncfg az none st.clock r st ns with
  | .inl _ => (⟨599, [], "", none⟩, st, ns, [])
  | .inr x => x

private def subBody (topic : String) : String :=
  "{\"type\":\"WebhookSubscription\",\"topic\":[\"http://localhost" ++ topic ++
  "\"],\"inbox\":\"http://hook.example/in\"}"

private def subscribed (topic : String) : MemState × NotifState :=
  let (_, st, ns, _) := step1 stA {} (req "POST" subscriptionsPath
    [("content-type", "application/lws+json")] (subBody topic))
  (st, ns)

private def moveActs (topic : String) (r : Request) : List Json :=
  let (st, ns) := subscribed topic
  let (_, _, _, ds) := step1 st ns r
  ds.flatMap (fun d => match (j d.body).field? "activity" with
    | some (.array xs) => xs
    | some o => [o]
    | none => [])

-- One Move activity, origin the old container, target the new, object the new identifier.
#guard (moveActs "/src/" (moveTo "/src/a.txt" "http://localhost/dst/")).map (fun a =>
  (a.field? "type", a.getString? "origin", a.getString? "target",
   (a.field? "object").bind (·.getString? "id"))) ==
  [(some (.array [.string "Move"]), some "http://localhost/src/", some "http://localhost/dst/",
    some "http://localhost/dst/a.txt")]
-- A subscription to the destination hears it too.
#guard (moveActs "/dst/" (moveTo "/src/a.txt" "http://localhost/dst/")).length == 1
-- Negative: a refused move announces nothing, and a subscription elsewhere hears nothing.
#guard (moveActs "/src/" (moveTo "/src/a.txt" "http://localhost/nowhere/")).isEmpty
#guard (moveActs "/other.txt" (moveTo "/src/a.txt" "http://localhost/dst/")).isEmpty
-- A linkset change that moves nothing is an Update, as before.
#guard ((moveActs "/src/" (patchLs "/src/a.txt"
  "[{\"op\":\"add\",\"path\":\"/linkset/0/license\",\"value\":[{\"href\":\"https://example.org/l\"}]}]")).map
  (·.field? "type")) == [some (.array [.string "Update"])]

end Notify

/-- The registry row of §Moving Resources: a data resource and a container
move, and a cycle is refused. -/
def lwsGuardMoveResource : Bool :=
  status stA (moveTo "/src/a.txt" "http://localhost/dst/") == 200 &&
  status stA (moveTo "/src/box/" "http://localhost/dst/") == 200 &&
  status stD (moveTo "/src/box/" "http://localhost/src/box/deeper/") == 409

#guard lwsGuardMoveResource

end L4Factoidal.LWS.MoveTests

