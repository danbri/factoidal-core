/-
L4Factoidal.LWS.Linkset — client-managed links, the `Link` request header
field, `Prefer: set-linkset`, and the linkset document of a resource.

Source: the W3C Linked Web Storage Working Group editor's draft,
https://w3c.github.io/lws-protocol/lws10-core/, read 2026-10-21 at
w3c/lws-protocol commit 9a08ff65a6670cc5d308ed5e531032f23af30fcc
(2026-10-19). Statements this module decides (verbatim):

* §Metadata, "Metadata Types": "System Managed | Maintained by the server;
  Read-Only. Includes `linkset`, `type`, `format`, `size`, `modified`." and
  "Core Metadata | Managed by the client (subject to server restrictions).
  Includes `up`, `items`, `title`, `creator`." and "User-Defined | Custom
  vocabularies and indexes created by the user."
* §Metadata, "Managing Metadata": "Servers MAY restrict modifications to
  specific links (like `up` or `items`) to maintain system integrity.
  Servers MUST preserve the links a client is not permitted to modify when
  applying a patch. A server that allows clients to modify the `up` link
  thereby allows resources to be moved between containers; such a server
  MUST describe a `MoveResource` capability".
* §Update Resource: "clients MAY include `Link` headers in the PUT/PATCH
  request to the resource URI and specify the preference `'Prefer:
  set-linkset'` (as defined in [RFC7240]). In this case, the server MUST
  interpret the provided `Link` headers as a replacement (for PUT) or partial
  update (for PATCH) to the linkset".
* §Create Resource: "Clients MAY provide initial user-managed metadata for
  the new resource by including one or more `Link` headers in the POST
  request ... Server-managed metadata MUST be generated automatically by the
  server upon creation and MUST NOT be overridden by client-provided links."

Server choices, each stated once:

* The links a client may not set (`serverManagedRels`) are the system
  managed relations, plus `up` and `items` (this server describes no
  `MoveResource` capability, and containment is derived from paths), plus
  `https://www.w3.org/ns/lws#storage`, which §Discovery fixes. A client
  link with one of them in a `Prefer: set-linkset` request or in a linkset
  document that changes it is refused with 409 Conflict (RFC 9110 §15.5.10:
  "the request could not be completed due to a conflict with the current
  state of the target resource"). On POST such a link is not stored and
  does not change the server's link (the `type` link of a POST is the
  interaction-model hint of §Create Resource).
* A client link must be well formed (`linkValid`): RFC 8288 §3.3 relation
  type syntax, a URI-reference target with none of the characters RFC 3986
  excludes, attribute names that are RFC 9110 tokens other than `rel` and
  `anchor`. A malformed `Link` field or link is refused with 400.
* A link with an `anchor` parameter is refused with 400: the linkset of a
  resource has one link context, the resource (RFC 8288 §3.2).
-/
import L4Factoidal.LWS.Binding

namespace L4Factoidal.LWS

open L4Factoidal.JSON

/-- Remove leading and trailing ASCII white space. -/
def trimS (s : String) : String := s.trimAscii.toString

/-! ## Which links the server manages -/

/-- The relations a client may not set or change. -/
def serverManagedRels : List String :=
  ["linkset", "type", "format", "size", "modified", "up", "items", lwsStorageRel]

/-- Is a relation server-managed? Registered relation types compare without
case (RFC 8288 §2.1.1). -/
def serverManaged (rel : String) : Bool := serverManagedRels.contains rel.toLower

/-! ## Syntax checks (RFC 8288, RFC 3986, RFC 9110) -/

private def isLoAlpha (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
private def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
private def isDig (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Characters that RFC 3986 §2 never allows unencoded in a URI reference
(and controls and space). -/
def uriExcluded (c : Char) : Bool :=
  c.toNat ≤ 32 || c.toNat == 127 || "<>\"{}|\\^`".toList.contains c

/-- RFC 3986 §3.1 `scheme ":" ...`: an absolute URI. -/
def absoluteUri (s : String) : Bool :=
  match s.splitOn ":" with
  | sch :: _ :: _ =>
      (match sch.toList with
       | c :: cs => isAlpha c && cs.all (fun c => isAlpha c || isDig c || c == '+' || c == '-' || c == '.')
       | [] => false) &&
      !(s.any uriExcluded)
  | _ => false

/-- RFC 8288 §3.3: `relation-type = reg-rel-type / ext-rel-type`,
`reg-rel-type = LOALPHA *( LOALPHA / DIGIT / "." / "-" )`,
`ext-rel-type = URI`. -/
def relTypeValid (r : String) : Bool :=
  match r.toList with
  | c :: cs => (isLoAlpha c && cs.all (fun c => isLoAlpha c || isDig c || c == '.' || c == '-'))
               || absoluteUri r
  | [] => false

/-- A link target: a non-empty URI-reference with no excluded character. -/
def linkTargetValid (t : String) : Bool := t != "" && !(t.any uriExcluded)

/-- RFC 9110 §5.6.2 `token`. -/
def tokenValid (s : String) : Bool :=
  s != "" && s.all (fun c => isAlpha c || isDig c || "!#$%&'*+-.^_`|~".toList.contains c)

/-- Is a client link well formed? -/
def linkValid (l : Link) : Bool :=
  relTypeValid l.rel && linkTargetValid l.target &&
  l.attrs.all (fun (k, _) => tokenValid k && k.toLower != "rel" && k.toLower != "anchor")

/-! ## The `Link` request header field (RFC 8288 §3) -/

/-- Split at `sep` outside double quotes and outside `<...>`, a loop with an
accumulator. -/
def splitTop (sep : Char) : List Char → Bool → Bool → List Char → Array String → Array String
  | [], _, _, cur, acc => acc.push (String.ofList cur.reverse)
  | c :: cs, inQ, inA, cur, acc =>
      if inQ then
        if c == '\\' then
          match cs with
          | d :: ds => splitTop sep ds inQ inA (d :: c :: cur) acc
          | [] => splitTop sep [] inQ inA (c :: cur) acc
        else splitTop sep cs (c != '"') inA (c :: cur) acc
      else if inA then splitTop sep cs inQ (c != '>') (c :: cur) acc
      else if c == '"' then splitTop sep cs true inA (c :: cur) acc
      else if c == '<' then splitTop sep cs inQ true (c :: cur) acc
      else if c == sep then splitTop sep cs inQ inA [] (acc.push (String.ofList cur.reverse))
      else splitTop sep cs inQ inA (c :: cur) acc

/-- RFC 9110 §5.6.4 `quoted-string` body without its quotes, or the token. -/
def unquote (v : String) : Option String :=
  let v := trimS v
  if v.startsWith "\"" then
    if v.length ≥ 2 && v.endsWith "\"" then
      let inner := (v.toList.drop 1).dropLast
      some (String.ofList (unescape inner []))
    else none
  else if tokenValid v then some v else none
where
  unescape : List Char → List Char → List Char
    | [], acc => acc.reverse
    | '\\' :: d :: ds, acc => unescape ds (d :: acc)
    | c :: cs, acc => unescape cs (c :: acc)

/-- One `link-value`: the links it states (one per relation of `rel`). -/
def parseLinkValue (v : String) : Except String (List Link) := do
  let v := trimS v
  if !v.startsWith "<" then .error "a link value starts with <" else
  match (String.ofList (v.toList.drop 1)).splitOn ">" with
  | target :: rest =>
      let params := (splitTop ';' (String.intercalate ">" rest).toList false false [] #[]).toList
      let params := params.map trimS |>.filter (· != "")
      if !((trimS (String.intercalate ">" rest)).startsWith ";") && params != [] then
        .error "a link value has text after the target that is not a parameter" else
      let mut rels : Option (List String) := none
      let mut attrs : Array (String × String) := #[]
      for p in params do
        let (k, val) := match p.splitOn "=" with
          | [k] => ((trimS k).toLower, some "")
          | k :: vs => ((trimS k).toLower, unquote (String.intercalate "=" vs))
          | [] => ("", none)
        let some val := val | throw s!"the parameter {k} has a malformed value"
        if !tokenValid k then throw s!"the parameter name {k} is not a token"
        if k == "anchor" then throw "a link with an anchor parameter is not accepted"
        if k == "rel" then
          -- RFC 8288 §3.3: "occurrences after the first MUST be ignored"
          if rels.isNone then rels := some ((val.splitOn " ").filter (· != ""))
        else attrs := attrs.push (k, val)
      match rels with
      | none => .error "a link value has no rel parameter"
      | some [] => .error "a link value has an empty rel parameter"
      | some rs => .ok (rs.map (fun r => { target, rel := r, attrs := attrs.toList }))
  | [] => .error "a link value has no target"

/-- The links of a `Link` field value (several link values, comma
separated). -/
def parseLinkField (v : String) : Except String (List Link) := do
  let parts := (splitTop ',' v.toList false false [] #[]).toList.map trimS |>.filter (· != "")
  let mut out : Array Link := #[]
  for p in parts do
    let ls ← parseLinkValue p
    out := out ++ ls.toArray
  return out.toList

/-- Does a `Prefer` field value (RFC 7240 §2) carry the preference
`set-linkset`? -/
def preferSetLinkset (v : String) : Bool :=
  (splitTop ',' v.toList false false [] #[]).toList.any (fun p =>
    (trimS ((((p.splitOn ";").headD p).splitOn "=").headD "")).toLower == "set-linkset")

/-- The client links a request's `Link` field states, checked: 400 for a
malformed field or link, 409 for a server-managed relation. -/
def clientLinksOf (field : Option String) : Except (Nat × String) (List Link) :=
  match field with
  | none => .ok []
  | some v =>
      match parseLinkField v with
      | .error m => .error (400, m)
      | .ok ls =>
          match ls.find? (fun l => !linkValid l) with
          | some l => .error (400, s!"the link to {l.target} with rel {l.rel} is not well formed")
          | none =>
              match ls.find? (fun l => serverManaged l.rel) with
              | some l => .error (409, s!"the relation {l.rel} is server-managed")
              | none => .ok ls

/-- The client links of a POST: the well-formed links with a relation the
client may set. A server-managed relation is not stored (§Create Resource:
it "MUST NOT be overridden"). A malformed field is refused with 400. -/
def postLinksOf (field : Option String) : Except (Nat × String) (List Link) :=
  match field with
  | none => .ok []
  | some v =>
      match parseLinkField v with
      | .error m => .error (400, m)
      | .ok ls =>
          match ls.find? (fun l => !linkValid l) with
          | some l => .error (400, s!"the link to {l.target} with rel {l.rel} is not well formed")
          | none => .ok (ls.filter (fun l => !serverManaged l.rel))

/-- A partial update (PATCH with `Prefer: set-linkset`): the new links are
added to the old ones, and a link already present is not repeated. -/
def mergeLinks (old new : List Link) : List Link :=
  old ++ (new.filter (fun l => !old.contains l)).eraseDups

/-! ## The linkset document (RFC 9264 §4.2) -/

/-- A target object: `href` and the target attributes. -/
def targetObject (l : Link) : Json :=
  .object (("href", .string l.target) :: l.attrs.map (fun (k, v) => (k, .string v)))

/-- Group links by relation, relations in order of first appearance. -/
def groupByRel (ls : List Link) : List (String × List Link) :=
  let rels := (ls.map (·.rel)).eraseDups
  rels.map (fun r => (r, ls.filter (·.rel == r)))

/-- The server-managed links of a resource, as relation groups. -/
def serverLinkGroups (baseIri path : String) (kind : ResourceKind) : List (String × List Link) :=
  (match parent? path with
   | some p => [("up", [{ target := iriOfPath baseIri p, rel := "up" }])]
   | none => []) ++
  [ ("type", [{ target := if kind.isContainer then lwsContainerType else lwsDataResourceType,
                rel := "type" }])
  , (lwsStorageRel, [{ target := iriOfPath baseIri storagePath, rel := lwsStorageRel }]) ]

/-- The `application/linkset+json` document of a resource: one link
context, anchored at the resource; the server-managed links, then the client
links. -/
def linksetDoc (baseIri path : String) (kind : ResourceKind) (client : List Link) : Json :=
  let groups := serverLinkGroups baseIri path kind ++ groupByRel client
  .object [ ("linkset", .array [ .object (
    ("anchor", .string (iriOfPath baseIri path)) ::
    groups.map (fun (r, ls) => (r, .array (ls.map targetObject)))) ]) ]

/-- A target object read back as a link of relation `rel`. -/
def linkOfTarget (rel : String) (j : Json) : Except (Nat × String) Link :=
  match j with
  | .object fs =>
      match fs.lookup "href" with
      | some (.string t) =>
          let rest := fs.filter (·.1 != "href")
          match rest.mapM (fun (k, v) => match v with | .string s => some (k, s) | _ => none) with
          | some attrs => .ok { target := t, rel, attrs }
          | none => .error (400, "a target attribute is not a string")
      | _ => .error (400, "a target object has no string href")
  | _ => .error (400, "a link target is not an object")

/-- The client links a linkset document states, checked against the
resource's server-managed links. The document must have one link context
anchored at the resource. A server-managed relation must carry exactly the
server's links; when `keepAbsent` holds (a PUT, a full replacement) it may
also be absent, and the server's links are kept. Every other relation is a
client link and must be well formed. -/
def clientLinksOfDoc (baseIri path : String) (kind : ResourceKind) (keepAbsent : Bool)
    (doc : Json) : Except (Nat × String) (List Link) := do
  let ctxs ← match doc.getArray? "linkset" with
    | some cs => pure cs
    | none => throw (400, "a linkset document has a \"linkset\" array")
  let ctx ← match ctxs with
    | [c] => pure c
    | _ => throw (409, "the linkset of a resource has one link context")
  let fields ← match ctx with
    | .object fs => pure fs
    | _ => throw (400, "a link context is an object")
  if ctx.getString? "anchor" != some (iriOfPath baseIri path) then
    throw (409, "the link context must be anchored at the resource")
  let server := serverLinkGroups baseIri path kind
  for (r, ls) in server do
    match fields.lookup r with
    | none => if !keepAbsent then throw (409, s!"the server-managed relation {r} was removed")
    | some (.array ts) =>
        let got ← ts.mapM (linkOfTarget r)
        if got != ls then throw (409, s!"the relation {r} is server-managed")
    | some _ => throw (400, s!"the relation {r} does not have an array of targets")
  let mut out : Array Link := #[]
  for (r, v) in fields do
    if r == "anchor" || server.any (·.1 == r) then continue
    if serverManaged r then throw (409, s!"the relation {r} is server-managed")
    match v with
    | .array ts =>
        for t in ts do
          let l ← linkOfTarget r t
          if !linkValid l then throw (400, s!"the link to {l.target} with rel {r} is not well formed")
          out := out.push l
    | _ => throw (400, s!"the relation {r} does not have an array of targets")
  return out.toList

/-! ## Checks -/

private def lic : Link :=
  { target := "https://creativecommons.org/licenses/by/4.0/", rel := "license" }

#guard parseLinkField "<https://creativecommons.org/licenses/by/4.0/>; rel=\"license\"" == .ok [lic]
#guard parseLinkField "<a>; rel=\"x y\", <b>; rel=z; title=\"t, u\"" ==
  .ok [{ target := "a", rel := "x" }, { target := "a", rel := "y" },
       { target := "b", rel := "z", attrs := [("title", "t, u")] }]
#guard (parseLinkField "<a>; rel=x; rel=y" |>.toOption.map (·.map (·.rel))) == some ["x"]
#guard (parseLinkField "<a>").toOption.isNone
#guard (parseLinkField "a; rel=x").toOption.isNone
#guard (parseLinkField "<a>; anchor=\"#b\"; rel=x").toOption.isNone
#guard preferSetLinkset "set-linkset" && preferSetLinkset "return=minimal, Set-Linkset"
#guard !preferSetLinkset "return=minimal" && !preferSetLinkset "set-linksets"
#guard relTypeValid "license" && relTypeValid "https://example.org/rel" && relTypeValid "a.b-c"
#guard !relTypeValid "License" && !relTypeValid "" && !relTypeValid "1x" && !relTypeValid "a b"
-- The relations of the draft's "System Managed" row, `up` and `items`, and
-- `lws#storage` are server-managed; a core or user-defined one is not.
#guard ["linkset", "type", "format", "size", "modified", "up", "items",
        "https://www.w3.org/ns/lws#storage", "TYPE"].all serverManaged
#guard !serverManaged "license" && !serverManaged "title" && !serverManaged "creator" &&
  !serverManaged "author" && !serverManaged "https://example.org/rel"
-- The protection rule: every server-managed relation is refused, in any case.
#guard serverManagedRels.all (fun r =>
  match clientLinksOf (some ("<https://example.org/x>; rel=\"" ++ r ++ "\"")) with
  | .error (409, _) => true | _ => false)
#guard (clientLinksOf (some "<x>; rel=\"TYPE\"")).toOption.isNone
#guard clientLinksOf (some "<https://example.org/me>; rel=\"author\"") ==
  .ok [{ target := "https://example.org/me", rel := "author" }]
#guard (match clientLinksOf (some "<a b>; rel=\"author\"") with | .error (400, _) => true | _ => false)
#guard (match clientLinksOf (some "<a>; rel=\"Bad Rel\"") with | .error (400, _) => true | _ => false)
#guard postLinksOf (some "<http://www.w3.org/ns/ldp#BasicContainer>; rel=\"type\", <a>; rel=\"author\"") ==
  .ok [{ target := "a", rel := "author" }]
#guard mergeLinks [lic] [lic, { target := "a", rel := "author" }] == [lic, { target := "a", rel := "author" }]

private def base : String := "http://example.org/"

-- A linkset document written by `linksetDoc` reads back as its client links.
#guard clientLinksOfDoc base "/d.txt" .dataResource false (linksetDoc base "/d.txt" .dataResource [lic]) == .ok [lic]
#guard clientLinksOfDoc base "/d.txt" .dataResource true (linksetDoc base "/d.txt" .dataResource []) == .ok []
-- A document that changes a server-managed link is refused with 409.
#guard (match clientLinksOfDoc base "/d.txt" .dataResource true
    (linksetDoc base "/d.txt" .container []) with | .error (409, _) => true | _ => false)
-- A document that adds a link with a server-managed relation is refused.
#guard (match clientLinksOfDoc base "/d.txt" .dataResource true
    (.object [("linkset", .array [.object [("anchor", .string "http://example.org/d.txt"),
      ("items", .array [.object [("href", .string "x")]])]])]) with
    | .error (409, _) => true | _ => false)
-- A PUT document may leave the server links out; a PATCH result may not.
#guard (clientLinksOfDoc base "/d.txt" .dataResource true
    (.object [("linkset", .array [.object [("anchor", .string "http://example.org/d.txt")]])])) == .ok []
#guard (match clientLinksOfDoc base "/d.txt" .dataResource false
    (.object [("linkset", .array [.object [("anchor", .string "http://example.org/d.txt")]])]) with
    | .error (409, _) => true | _ => false)
-- Another anchor is refused.
#guard (match clientLinksOfDoc base "/d.txt" .dataResource true
    (linksetDoc base "/e.txt" .dataResource []) with | .error (409, _) => true | _ => false)

end L4Factoidal.LWS
