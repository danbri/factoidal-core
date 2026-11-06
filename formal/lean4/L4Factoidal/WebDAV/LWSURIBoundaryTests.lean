import L4Factoidal.LWS.Authorization

/- Diagnostic tests for issue https://github.com/danbri/factoidal/issues/1202.
   XFAIL rows below are unresolved URI-equivalence requirements, not passes.
   Resources/ACLs are created through LWS.step; only the empty storage root
   is provisioned in the fixture. No WebDAV or host storage bypass is used. -/
namespace L4Factoidal.WebDAV.LWSURIBoundaryTests
open L4Factoidal.LWS L4Factoidal.LWS.Authorization L4Factoidal.HTTP

private def cfg : Config := {baseIri:="http://localhost/"}
private def empty : MemState :=
  {entries:=[{path:="/",kind:=.storageRoot,contentType:="text/turtle",body:=ByteArray.empty,mtime:=0}]}
private def req (method path : String) (body : String := "") (ct : String := "text/plain") : Request :=
  {method,path,queryStr:="",headers:=[("content-type",ct)],body,bytes:=some body.toUTF8}
private def put (st : MemState) (path body : String) (ct : String := "text/plain") : MemState :=
  (step MemStore cfg (req "PUT" path body ct) st).2
private def read (st : MemState) (path : String) : Response :=
  (step MemStore cfg (req "GET" path) st).1
private def text (r : Response) : String := (String.fromUTF8? r.content).getD ""
private def V : L4Factoidal.JOSE.Verifiers :=
  {es256:=fun _ _ _ => false,rs256:=fun _ _ _ _ => false,eddsa:=fun _ _ _ => false}
private def secure (st : MemState) (method path : String) : Nat :=
  match authorizedStep V MemStore cfg {} 1000 (req method path) st with
  | .inr (response,_) => response.status
  | .inl _ => 0
private def publicACL (path : String) : String :=
  "@prefix acl: <http://www.w3.org/ns/auth/acl#> . " ++
  "<http://localhost/public-rule> a acl:Authorization; acl:agentClass <http://xmlns.com/foaf/0.1/Agent>; " ++
  "acl:accessTo <http://localhost"++path++">; acl:mode acl:Read ."
private def publicResource (path : String) : MemState :=
  put (put empty path "public") (path++".acl") (publicACL path) "text/turtle"

-- Reserved literal ':' and escaped '%3A' are intentionally distinct.
#guard let st := put (put empty "/colon:name" "raw") "/colon%3Aname" "escaped"
       text (read st "/colon:name") == "raw" && text (read st "/colon%3Aname") == "escaped"
-- Neither read-only ACL permits anonymous writes through either spelling.
#guard let st := publicResource "/pub"
       secure st "PUT" "/pub" == 401 && secure st "PUT" "/%70ub" == 401

#guard let st := publicResource "/pub"
       secure st "GET" "/pub" == 200 && secure st "GET" "/%70ub" == 401

-- Current boundary counterexamples, explicitly expected failures of the
-- desired URI contract. These guards characterize the defect until repaired.
private def hexReadEquivalent : Bool :=
  let st := put empty "/%C3%A9" "utf8"
  (read st "/%c3%a9").status == 200 && text (read st "/%c3%a9") == "utf8"
private def unreservedReadEquivalent : Bool :=
  let st := put empty "/a" "letter"
  (read st "/%61").status == 200 && text (read st "/%61") == "letter"
private def authorizationEquivalent : Bool :=
  let st := publicResource "/pub"
  secure st "GET" "/pub" == 200 && secure st "GET" "/%70ub" == 200
private def refusesCollision : Bool :=
  let st := put (put empty "/a" "first") "/%61" "second"
  -- Desired future behavior: no successful arbitrary choice once equivalent
  -- physical keys coexist. Conflict diagnosis must also preserve auth policy.
  !((read st "/a").status == 200) && !((read st "/%61").status == 200)
#guard !hexReadEquivalent
#guard !unreservedReadEquivalent
#guard !authorizationEquivalent
#guard !refusesCollision

#eval IO.println "LWS URI boundary: 3 invariant/observation guards; 4 known XFAIL requirements (hex case, unreserved, authorization equivalence, colliding keys); no HTTP/WASM result"
end L4Factoidal.WebDAV.LWSURIBoundaryTests
