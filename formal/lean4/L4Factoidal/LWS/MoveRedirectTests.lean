/-
L4Factoidal.LWS.MoveRedirectTests — `#guard`s for the 301 answers at the
previous identifiers of moved resources (`L4Factoidal.LWS.MoveRedirect`),
https://github.com/danbri/factoidal/issues/914.

LWS 1.0 core §Moving Resources: "Such a server SHOULD respond to subsequent
requests on the previous identifiers of the resource and of its auxiliary
resources with 301 Moved Permanently, including a `Location` header field
pointing at the new identifier."

Each request runs as the wasm layer runs it: `MoveRedirect.answer?` first,
then `step` on the reference store `MemStore`, then `MoveRedirect.after`
with the move plan computed on the store before the step. Host checks:
`node tests/lws/draft-binding.mjs`, the "Moving Resources" rows.
-/
import L4Factoidal.LWS.MoveRedirect

namespace L4Factoidal.LWS.MoveRedirectTests

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.LWS.MoveRedirect
open L4Factoidal.HTTP (Request Response)

private def stubV : JOSE.Verifiers :=
  { es256 := fun _ _ _ => false, rs256 := fun _ _ _ _ => false, eddsa := fun _ _ _ => false }

private def cfg : Config := { baseIri := "http://localhost/", moves := true }
private def open_ : Authorization.AuthzConfig := { insecureNoAuth := true }

private def st0 : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := .empty, mtime := 1000 }], clock := 1001 }

private def req (m t : String) (hs : List (String × String) := []) (body : String := "") : Request :=
  { method := m, path := t, queryStr := "", headers := hs, body }

private def putText (t body : String) : Request := req "PUT" t [("content-type", "text/plain")] body
private def putDir (t : String) : Request := req "PUT" t [("content-type", "text/turtle")] ""
private def moveTo (t dest : String) : Request :=
  req "PATCH" (t ++ "?linkset") [("content-type", "application/json-patch+json")]
    ("[{\"op\":\"replace\",\"path\":\"/linkset/0/up/0/href\",\"value\":\"" ++ dest ++ "\"}]")

/-- A storage with its redirect table and the last answer. -/
structure W where
  st : MemState
  es : List (String × String) := []
  resp : Response := ⟨200, [], "", none⟩

private def run1 (w : W) (r : Request) (c : Config := cfg) (a : Authorization.AuthzConfig := open_) : W :=
  match answer? stubV MemStore c a w.st.clock r w.st w.es with
  | some (.inr resp) => { w with resp }
  | some (.inl _) => { w with resp := ⟨599, [], "", none⟩ }
  | none =>
      let plan? := movePlanOf? MemStore c.baseIri c.moves c.moveContainers r w.st
      let (resp, st') := step MemStore c r w.st
      ⟨st', after MemStore c.redirectsMax plan? resp.status st' w.es, resp⟩

private def runAll (w : W) (rs : List Request) : W := rs.foldl (fun w r => run1 w r) w

private def loc (w : W) : Option String := w.resp.headers.lookup "location"

private def wA : W := runAll ⟨st0, [], ⟨200, [], "", none⟩⟩
  [ putText "/src/a.txt" "a resource on the move", putDir "/dst/", putDir "/far/",
    putText "/src/box/inner.txt" "carried along" ]
private def wM : W := run1 wA (moveTo "/src/a.txt" "http://localhost/dst/")

/-! ## The previous identifier answers 301 -/

#guard wM.resp.status == 200
#guard wM.es.head? == some ("/src/a.txt", "/dst/a.txt")
#guard (run1 wM (req "GET" "/src/a.txt")).resp.status == 301
#guard loc (run1 wM (req "GET" "/src/a.txt")) == some "http://localhost/dst/a.txt"
-- Every method, and the linkset resource with its query kept.
#guard (run1 wM (req "HEAD" "/src/a.txt")).resp.status == 301
#guard (run1 wM (putText "/src/a.txt" "x")).resp.status == 301
#guard loc (run1 wM (req "GET" "/src/a.txt?linkset")) == some "http://localhost/dst/a.txt?linkset"
-- A 301 changes nothing.
#guard (memLookup (run1 wM (putText "/src/a.txt" "x")).st "/src/a.txt").isNone
-- The new identifier answers 200 as before.
#guard (run1 wM (req "GET" "/dst/a.txt")).resp.status == 200

/-! ## Containers: every descendant -/

private def wB : W := run1 wM (moveTo "/src/box/" "http://localhost/dst/")
#guard wB.resp.status == 200
#guard loc (run1 wB (req "GET" "/src/box/")) == some "http://localhost/dst/box/"
#guard loc (run1 wB (req "GET" "/src/box/inner.txt")) == some "http://localhost/dst/box/inner.txt"
-- Negative: a path below the old container that never held a resource.
#guard (run1 wB (req "GET" "/src/box/never.txt")).resp.status == 404

/-! ## A chain of moves answers the current identifier -/

private def wC : W := run1 wB (moveTo "/dst/a.txt" "http://localhost/far/")
#guard wC.resp.status == 200
#guard loc (run1 wC (req "GET" "/src/a.txt")) == some "http://localhost/far/a.txt"
#guard loc (run1 wC (req "GET" "/dst/a.txt")) == some "http://localhost/far/a.txt"

/-! ## The entry goes when its paths change -/

-- A new resource at the previous path (POST with the old name; a PUT there
-- is a request to the moved resource, so it answers 301): it answers, and
-- the pair is gone.
private def wN : W := run1 wC (req "POST" "/src/" [("content-type", "text/plain"), ("slug", "a.txt")] "new")
#guard wN.resp.status == 201
#guard (run1 wN (req "GET" "/src/a.txt")).resp.status == 200
#guard !(wN.es.any (·.1 == "/src/a.txt"))
-- ... and deleting the new resource does not bring the old redirect back.
#guard (run1 (run1 wN (req "DELETE" "/src/a.txt")) (req "GET" "/src/a.txt")).resp.status == 404
-- The moved resource deleted: its previous paths answer 404.
private def wD : W := run1 wC (req "DELETE" "/far/a.txt")
#guard wD.resp.status == 204
#guard (run1 wD (req "GET" "/src/a.txt")).resp.status == 404
#guard (run1 wD (req "GET" "/dst/a.txt")).resp.status == 404
-- Every pair kept holds in the store (`after_ok`), checked here on each state.
#guard [wM, wB, wC, wN, wD].all (fun w => w.es.all (holds MemStore w.st))

/-! ## Negative cases -/

-- A path that was never moved.
#guard (run1 wM (req "GET" "/src/other.txt")).resp.status == 404
-- A refused move (destination missing) records nothing.
#guard (run1 wA (moveTo "/src/a.txt" "http://localhost/nowhere/")).es.isEmpty
-- Under authorization, an anonymous agent that may not read the new
-- identifier gets no 301 (§Privacy Considerations, "Redirects": "Servers
-- SHOULD apply the same access control to such responses as to the moved
-- resource itself").
#guard (answer? stubV MemStore cfg {} 2000 (req "GET" "/src/a.txt") wM.st wM.es).isNone
-- The bound: at most `redirectsMax` pairs.
#guard (run1 wA (moveTo "/src/box/" "http://localhost/dst/") { cfg with redirectsMax := 1 }).es.length == 1
#guard (record MemStore wB.st 2 { src := "/x", dest := "/", dst := "/y", moves := [] } wB.es).length ≤ 2

/-! ## Persistence -/

#guard (stateOfJson MemStore wC.st 256 (stateJson wC.es)).toOption == some wC.es
-- A pair that no longer holds is pruned when a snapshot is read.
#guard (stateOfJson MemStore wD.st 256 (stateJson wC.es)).toOption == some wD.es
#guard wD.es.length < wC.es.length
-- Negative: a member that is not two storage paths is refused.
#guard (stateOfJson MemStore wC.st 256 (.array [.array [.string "/a", .string "../b"]])).toOption.isNone
#guard (stateOfJson MemStore wC.st 256 (.string "x")).toOption.isNone

end L4Factoidal.LWS.MoveRedirectTests
