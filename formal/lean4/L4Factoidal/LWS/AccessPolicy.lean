/-
L4Factoidal.LWS.AccessPolicy — the data model and the access profile of
LWS 1.0 core §Access Requests and Grants, and the decision what an access
grant permits. https://github.com/danbri/factoidal/issues/913

Source: w3c/lws-protocol 9a08ff65 (2026-10-19), `lws10-core/lws-access-requests.html`,
included by `lws10-core/index.html` as section "Access Requests and Grants",
and the definitions of `lws10-core/index.html` §Terminology. The endpoints
(Protocol, Notifications) are `L4Factoidal.LWS.AccessGrants`; this module
holds what `Authorization.decide` needs and nothing that depends on it.

## What the draft says, and where it is decided

* Terminology: "access grant — a data object created by a storage
  controller, expressing an ability for an agent to perform specific
  actions on Storage Resources within certain defined constraints"; "access
  request — a data object submitted by an agent, expressing a request to
  perform specific actions on Storage Resources, including the desired scope
  and constraints"; "storage controller — an agent that controls all
  resources in a storage".
* Overview: "An agent does not present an access grant to a server as an
  authorization token. Rather, the access grant serves as a record of what
  was authorized, to whom, and under what constraints. When an access grant
  is created or revoked (deleted), it is the responsibility of the server to
  adjust any underlying access policy to account for the change." Here the
  grants ARE part of the access policy: `grantAllows` is consulted by
  `Authorization.decide` beside Web Access Control, so a created grant
  takes effect on the next request and a deleted one stops (theorem
  `grantsPermit_revoke`).
* Types: "For an access request, the value MUST include the term
  AccessRequest. For an access grant, the value MUST include the term
  AccessGrant." `parseDoc`.
* Storage: "The value of the storage property MUST be a URI. This property
  is REQUIRED." The server also requires it to name THIS storage (the draft:
  "identifies the LWS storage to which the access request or access grant
  is scoped"): a grant for another storage would permit nothing here.
* Inbox: "The value of the inbox property MUST be a URI. This property is
  OPTIONAL." `isUri`.
* Access: "The value of the access property MUST be a collection of one or
  more objects. This property is REQUIRED."
* Access Profile, Types: "MUST include the term AccessPolicy".
* Actions: "The value of the action property MUST be a collection of one or
  more strings. Each value MUST correspond to an operation recognized by the
  server. The following values MUST be supported: read, modify, create, and
  delete." with "read — retrieve a resource or its metadata (HTTP GET,
  HEAD)", "modify — modify an existing resource (HTTP PUT, PATCH)", "create
  — create a new resource within a container (HTTP POST)", "delete — remove
  an existing resource (HTTP DELETE)". `Action`, `actionOf`.
* Assignee: "The value of the assignee property MUST be a URI. Public access
  MAY be assigned using the Agent class from the FOAF vocabulary, identified
  by the URI http://xmlns.com/foaf/0.1/Agent. This property is REQUIRED."
  `assigneeMatches`.
* Targets: "The target property MUST be an object containing the following
  properties: type [...] value — a collection of one or more strings used
  to identify the target resources", with the matchers `DataResource`,
  `Container` and `StorageResource`. "This property is OPTIONAL."
  `targetMatches`.
* Constraints: "Each constraint object MUST include the following
  properties: leftOperand [...] operator [...] rightOperand", "When multiple
  constraint objects are present, all of them MUST be satisfied." and "A
  server advertising support for this profile MUST support the following
  leftOperand values: client [...] format [...] type [...] purpose [...]
  dateTime". The examples fix the operators: `eq` and `isAnyOf` for
  client, format, type and purpose, `gteq` and `lteq` for dateTime ("The
  gteq operator defines the start of the window and the lteq operator
  defines the end. The rightOperand value for temporal constraints is an
  XML Schema dateTime string"). `satisfied`.

## Server choices the draft leaves open, each stated once

* A grant permits exactly what it says, never more: an action it lists, on
  a resource whose path it lists, to the agent it names (or anyone, for
  `foaf:Agent`), when every constraint holds (theorem `grantsPermit_sound`).
  A grant on a container does not reach its members (the draft does not say
  that it does). A policy without `target` names no resource and permits
  nothing. A grant never reaches an ACL resource (`actionOf`; the draft's
  four actions do not include control).
* `actionOf` maps a request to one action and one target: GET, HEAD and
  OPTIONS are `read` of the resource; POST is `create` in the container;
  PUT and PATCH are `modify` of an existing resource, or `create` in the
  parent container of a missing one; DELETE is `delete`. A request on the
  metadata (`.meta`) or linkset of a resource acts on the resource:
  reading it is `read`, changing or deleting it is `modify`.
* `client` is the `client_id` claim of the access token (RFC 9068 §2.2,
  "client_id REQUIRED"). A request without a token has no client and
  satisfies no `client` constraint.
* `format` is the media type stored for the resource; `type` is a type IRI
  in its `Link: rel="type"` header fields (the kind, `lws#DataResource` or
  `lws#Container`, and the client's type links).
* `purpose`: the draft does not say how a request states a purpose, so no
  request satisfies a `purpose` constraint, and a policy with one permits
  nothing (it is accepted, as the profile requires).
* `dateTime` is the server clock at the request, in seconds; a constraint
  outside its window makes the policy permit nothing (theorem
  `policyPermits_excluded`; a grant whose window has closed is the expired
  grant of theorem `recordPermits_expired`).
* An unknown action, matcher, leftOperand or operator is refused at POST
  (400) rather than stored and ignored.
-/
import L4Factoidal.LWS.Operations
import L4Factoidal.Solid.Server.Methods

namespace L4Factoidal.LWS.AccessPolicy

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.Solid.Server (authorizationSubject targetsAcl)

/-- `foaf:Agent`, the assignee that gives public access. -/
def foafAgent : String := "http://xmlns.com/foaf/0.1/Agent"

/-! ## The data model -/

/-- The four actions of §Actions. -/
inductive Action where
  | read | modify | create | delete
deriving DecidableEq, Repr, Inhabited

def Action.ofString? : String → Option Action
  | "read" => some .read
  | "modify" => some .modify
  | "create" => some .create
  | "delete" => some .delete
  | _ => none

/-- The three target matchers of §Targets. -/
inductive Matcher where
  | storageResource | dataResource | container
deriving DecidableEq, Repr, Inhabited

/-- A matcher written as a term or as its absolute URL. -/
def Matcher.ofString? (s : String) : Option Matcher :=
  if s == "StorageResource" || s == lwsNs ++ "StorageResource" then some .storageResource
  else if s == "DataResource" || s == lwsDataResourceType then some .dataResource
  else if s == "Container" || s == lwsContainerType then some .container
  else none

/-- Does the matcher match a resource that is (or is not) a container? -/
def Matcher.accepts : Matcher → Bool → Bool
  | .storageResource, _ => true
  | .dataResource, c => !c
  | .container, c => c

/-- The five leftOperands of §Constraints. -/
inductive Operand where
  | client | format | type | purpose | dateTime
deriving DecidableEq, Repr, Inhabited

def Operand.ofString? : String → Option Operand
  | "client" => some .client
  | "format" => some .format
  | "type" => some .type
  | "purpose" => some .purpose
  | "dateTime" => some .dateTime
  | _ => none

/-- The operators the profile's examples use. -/
inductive Operator where
  | eq | isAnyOf | gt | gteq | lt | lteq
deriving DecidableEq, Repr, Inhabited

def Operator.ofString? : String → Option Operator
  | "eq" => some .eq
  | "isAnyOf" => some .isAnyOf
  | "gt" => some .gt
  | "gteq" => some .gteq
  | "lt" => some .lt
  | "lteq" => some .lteq
  | _ => none

/-- One constraint. `values` is the right operand: one string, or the
strings of an array. `instant` is a `dateTime` right operand in seconds
since the Unix epoch. -/
structure Constraint where
  left : Operand
  op : Operator
  values : List String := []
  instant : Int := 0
deriving DecidableEq, Repr, Inhabited

/-- One access policy of the profile (an element of `access`). `target`
holds the matcher and the storage paths the `value` IRIs name. -/
structure Policy where
  actions : List Action
  assignee : String
  target : Option (Matcher × List String) := none
  constraints : List Constraint := []
deriving DecidableEq, Repr, Inhabited

/-- One stored access request or access grant: its identifier (the last
segment of its path), the agent that made it, when, the document as it is
served (without `id`, which the endpoint adds), and the parsed policies. -/
structure Record where
  id : String
  creator : Option String
  created : Nat
  doc : Json
  policies : List Policy
  inbox : Option String := none

instance : Inhabited Record :=
  ⟨{ id := "", creator := none, created := 0, doc := .null, policies := [] }⟩

/-- The access state of one storage. `seq` names new records; `revision`
advances on every change, so the host knows to persist. -/
structure AccessState where
  requests : List Record := []
  grants : List Record := []
  seq : Nat := 0
  revision : Nat := 0

instance : Inhabited AccessState := ⟨{}⟩

/-! ## What a grant permits -/

/-- What one request asks to do, for the grant check. -/
structure Ctx where
  agent : Option String
  client : Option String := none
  now : Int
  action : Action
  path : String
  /-- The target resource, when it exists. -/
  entry : Option Entry := none

/-- Is the target a container? From the stored kind, or from the path when
the resource does not exist. -/
def Ctx.isContainer (c : Ctx) : Bool :=
  match c.entry with
  | some e => e.kind.isContainer
  | none => pathIsContainer c.path

/-- The media type of the target (§Format Constraints: "the media type of
the target HTTP resource"). -/
def Ctx.format? (c : Ctx) : Option String := c.entry.map (fun e => baseMedia e.contentType)

/-- The type IRIs of the target's `Link: rel="type"` header fields
(§Resource Type Constraints: "the resource types advertised in HTTP Link
headers"): its kind and its client type links. -/
def Ctx.types (c : Ctx) : List String :=
  match c.entry with
  | none => []
  | some e =>
      (if e.kind.isContainer then lwsContainerType else lwsDataResourceType) ::
        (e.links.filter (fun l => l.rel == "type")).map (·.target)

/-- `eq` and `isAnyOf` over a string operand. -/
def matchesValues (op : Operator) (vs : List String) (x : String) : Bool :=
  match op with
  | .eq | .isAnyOf => vs.contains x
  | _ => false

/-- Does constraint `k` hold for the request `c`? -/
def satisfied (k : Constraint) (c : Ctx) : Bool :=
  match k.left with
  | .client =>
      match c.client with
      | some x => matchesValues k.op k.values x
      | none => false
  | .format =>
      match c.format? with
      | some f => matchesValues k.op k.values f
      | none => false
  | .type => c.types.any (matchesValues k.op k.values)
  | .purpose => false
  | .dateTime =>
      match k.op with
      | .eq => decide (c.now = k.instant)
      | .gt => decide (k.instant < c.now)
      | .gteq => decide (k.instant ≤ c.now)
      | .lt => decide (c.now < k.instant)
      | .lteq => decide (c.now ≤ k.instant)
      | .isAnyOf => false

/-- Does the policy name this agent? `foaf:Agent` names every agent and
the anonymous one. -/
def assigneeMatches (p : Policy) (agent : Option String) : Bool :=
  p.assignee == foafAgent || agent == some p.assignee

/-- Does the policy name this resource? -/
def targetMatches (p : Policy) (c : Ctx) : Bool :=
  match p.target with
  | none => false
  | some (m, ps) => ps.contains c.path && m.accepts c.isContainer

/-- Does one policy permit the request? -/
def policyPermits (p : Policy) (c : Ctx) : Bool :=
  p.actions.contains c.action && assigneeMatches p c.agent && targetMatches p c &&
    p.constraints.all (fun k => satisfied k c)

/-- Does one grant permit the request? Some policy of it does. -/
def recordPermits (g : Record) (c : Ctx) : Bool := g.policies.any (fun p => policyPermits p c)

/-- Do the grants permit the request? -/
def grantsPermit (gs : List Record) (c : Ctx) : Bool := gs.any (fun g => recordPermits g c)

/-! ## Requests as actions -/

variable {σ : Type}

/-- The action a request performs and the path it is checked on, or `none`
when no grant can permit it (an ACL resource, or a method outside the four
actions). See the module header. -/
def actionOf (S : Store σ) (st : σ) (method p : String) : Option (Action × String) :=
  if targetsAcl p then none else
  let subj := authorizationSubject p
  let aux := subj != p
  match method with
  | "GET" | "HEAD" | "OPTIONS" => some (.read, subj)
  | "POST" => if aux then none else some (.create, subj)
  | "PUT" | "PATCH" =>
      if aux || (S.lookup st subj).isSome then some (.modify, subj)
      else (parent? subj).map (fun q => (.create, q))
  | "DELETE" => if aux then some (.modify, subj) else some (.delete, subj)
  | _ => none

/-- Do the grants permit this request by this agent and client at `now`? -/
def grantAllows (S : Store σ) (st : σ) (gs : List Record) (who client : Option String)
    (now : Int) (method p : String) : Bool :=
  match actionOf S st method p with
  | none => false
  | some (act, q) =>
      grantsPermit gs { agent := who, client, now, action := act, path := q,
                        entry := S.lookup st q }

/-! ## Expiry and revocation -/

/-- A `dateTime` constraint whose window does not hold `now`. -/
def Constraint.excludes (now : Int) (k : Constraint) : Bool :=
  k.left == .dateTime && match k.op with
    | .eq => decide (now ≠ k.instant)
    | .gt => decide (now ≤ k.instant)
    | .gteq => decide (now < k.instant)
    | .lt => decide (k.instant ≤ now)
    | .lteq => decide (k.instant < now)
    | .isAnyOf => true

/-- A policy whose time window does not hold `now`: it has expired, or it
is not valid yet. -/
def Policy.outside (now : Int) (p : Policy) : Bool := p.constraints.any (Constraint.excludes now)

/-- A grant every policy of which is outside its window at `now`. -/
def Record.expired (now : Int) (g : Record) : Bool := g.policies.all (Policy.outside now)

/-- Revoke (delete) the grant `id`. -/
def revoke (id : String) (gs : List Record) : List Record := gs.filter (fun g => g.id != id)

/-! ## Theorems -/

/-- **Soundness.** When the grants permit a request, one policy of one
grant lists the request's action, lists the target's path under a matcher
that accepts it, names the agent (or `foaf:Agent`), and every one of its
constraints holds. Nothing else makes `grantsPermit` true. -/
theorem grantsPermit_sound {gs : List Record} {c : Ctx} (h : grantsPermit gs c = true) :
    ∃ g ∈ gs, ∃ p ∈ g.policies, c.action ∈ p.actions ∧
      (∃ m ps, p.target = some (m, ps) ∧ c.path ∈ ps ∧ m.accepts c.isContainer = true) ∧
      (p.assignee = foafAgent ∨ c.agent = some p.assignee) ∧
      ∀ k ∈ p.constraints, satisfied k c = true := by
  unfold grantsPermit at h
  obtain ⟨g, hg, hr⟩ := List.any_eq_true.mp h
  unfold recordPermits at hr
  obtain ⟨p, hp, hpp⟩ := List.any_eq_true.mp hr
  refine ⟨g, hg, p, hp, ?_⟩
  unfold policyPermits at hpp
  simp only [Bool.and_eq_true] at hpp
  obtain ⟨⟨⟨ha, hs⟩, ht⟩, hc⟩ := hpp
  refine ⟨by simpa using ha, ?_, ?_, ?_⟩
  · unfold targetMatches at ht
    split at ht
    · simp at ht
    · rename_i m ps hpt
      simp only [Bool.and_eq_true] at ht
      exact ⟨m, ps, hpt, by simpa using ht.1, ht.2⟩
  · unfold assigneeMatches at hs
    simpa using hs
  · intro k hk
    exact List.all_eq_true.mp hc k hk

/-- **A constraint outside its window is not satisfied.** -/
theorem satisfied_excluded {k : Constraint} {c : Ctx} (h : k.excludes c.now = true) :
    satisfied k c = false := by
  unfold Constraint.excludes at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hl, ho⟩ := h
  unfold satisfied
  rw [hl]
  cases hop : k.op <;> rw [hop] at ho <;> simp at ho ⊢ <;> omega

/-- **An expired or not yet valid policy permits nothing.** -/
theorem policyPermits_excluded {p : Policy} {c : Ctx} (h : p.outside c.now = true) :
    policyPermits p c = false := by
  unfold Policy.outside at h
  obtain ⟨k, hk, hx⟩ := List.any_eq_true.mp h
  have hs := satisfied_excluded hx
  unfold policyPermits
  have : p.constraints.all (fun k => satisfied k c) = false := by
    rw [List.all_eq_false]
    exact ⟨k, hk, by simp [hs]⟩
  simp [this]

/-- **An expired grant permits nothing**: when every policy of a grant is
outside its time window, the grant permits no request. -/
theorem recordPermits_expired {g : Record} {c : Ctx} (h : g.expired c.now = true) :
    recordPermits g c = false := by
  unfold Record.expired at h
  unfold recordPermits
  rw [List.any_eq_false]
  intro p hp
  simp [policyPermits_excluded (List.all_eq_true.mp h p hp)]

/-- **A revoked grant permits nothing.** After `revoke id`, whatever the
grants permit, a grant other than `id` permits. -/
theorem grantsPermit_revoke {id : String} {gs : List Record} {c : Ctx}
    (h : grantsPermit (revoke id gs) c = true) :
    ∃ g ∈ gs, g.id ≠ id ∧ recordPermits g c = true := by
  unfold grantsPermit revoke at h
  obtain ⟨g, hg, hr⟩ := List.any_eq_true.mp h
  have hm := List.mem_filter.mp hg
  exact ⟨g, hm.1, by simpa using hm.2, hr⟩

/-- Revoking the only grant leaves nothing permitted. -/
theorem grantsPermit_revoke_only (g : Record) (c : Ctx) :
    grantsPermit (revoke g.id [g]) c = false := by
  simp [grantsPermit, revoke]

/-- **No grant reaches an ACL resource.** -/
theorem grantAllows_acl (S : Store σ) (st : σ) (gs : List Record) (who client : Option String)
    (now : Int) (method p : String) (h : targetsAcl p = true) :
    grantAllows S st gs who client now method p = false := by
  simp [grantAllows, actionOf, h]

/-- **Request-level soundness.** A request the grants allow is not on an
ACL resource, maps to an action and a path, and some policy of some grant
lists that action and that path for that agent. -/
theorem grantAllows_sound {S : Store σ} {st : σ} {gs : List Record} {who client : Option String}
    {now : Int} {method p : String} (h : grantAllows S st gs who client now method p = true) :
    targetsAcl p = false ∧ ∃ act q, actionOf S st method p = some (act, q) ∧
      ∃ g ∈ gs, ∃ pol ∈ g.policies, act ∈ pol.actions ∧
        (∃ m ps, pol.target = some (m, ps) ∧ q ∈ ps) ∧
        (pol.assignee = foafAgent ∨ who = some pol.assignee) := by
  unfold grantAllows at h
  split at h
  · simp at h
  · rename_i act q hact
    refine ⟨?_, act, q, hact, ?_⟩
    · cases ha : targetsAcl p
      · rfl
      · simp [actionOf, ha] at hact
    · obtain ⟨g, hg, pol, hp, h1, ⟨m, ps, h2, h3, _⟩, h4, _⟩ := grantsPermit_sound h
      exact ⟨g, hg, pol, hp, h1, ⟨m, ps, h2, h3⟩, h4⟩

/-- A read is `read` of the subject resource. -/
theorem actionOf_get (S : Store σ) (st : σ) (p : String) (h : targetsAcl p = false) :
    actionOf S st "GET" p = some (.read, authorizationSubject p) := by
  simp [actionOf, h]

/-- A delete of a primary resource is `delete` of it. -/
theorem actionOf_delete (S : Store σ) (st : σ) (p : String) (h : targetsAcl p = false)
    (hp : authorizationSubject p = p) :
    actionOf S st "DELETE" p = some (.delete, p) := by
  simp [actionOf, h, hp]

/-! ## Reading documents -/

/-- An absolute URI (RFC 3986 §4.3): a scheme (a letter, then letters,
digits, `+`, `-`, `.`), a colon, and no space, control or excluded
character. -/
def isUri (s : String) : Bool :=
  let bad (ch : Char) : Bool := ch.toNat ≤ 0x20 || ch.toNat == 0x7f || "<>\"{}|\\^`".toList.contains ch
  match s.splitOn ":" with
  | scheme :: _ :: _ =>
      (match scheme.toList with
       | c :: rest => c.isAlpha && rest.all (fun ch => ch.isAlphanum || ch == '+' || ch == '-' || ch == '.')
       | [] => false) && !s.any bad
  | _ => false

/-- A term (§Types: "terms and absolute URL strings"): no colon, no space. -/
def isTerm (s : String) : Bool :=
  s != "" && !s.any (fun ch => ch == ':' || ch.toNat ≤ 0x20)

/-- A string, or an array of strings. -/
def stringsOf? : Json → Option (List String)
  | .string s => some [s]
  | .array xs => xs.mapM (fun x => match x with | .string s => some s | _ => none)
  | _ => none

/-- Does a type value list include the term `t` (or its LWS IRI)? -/
def hasType (vs : List String) (t : String) : Bool := vs.contains t || vs.contains (lwsNs ++ t)

/-- The `@context` of §JSON-LD Serialization as an ordered set: "MUST
include an @context property whose value is an ordered set that includes
https://www.w3.org/ns/lws/v1". Object entries (extension terms) are kept. -/
def contextOf? : Json → Option (List Json)
  | .string s => some [.string s]
  | .array xs => if xs.all (fun x => match x with | .string _ | .object _ => true | _ => false)
                 then some xs else none
  | .object fs => some [.object fs]
  | _ => none

/-- The storage path a target value names: an IRI below `baseIri`, a valid
path, not an ACL resource, and not a server endpoint under `/.well-known/`. -/
def targetPath? (baseIri t : String) : Option String :=
  if t.startsWith baseIri then
    let p := "/" ++ (t.drop baseIri.length).toString
    if validTarget p && !targetsAcl p && !p.startsWith "/.well-known/" then some p else none
  else none

/-! ### xsd:dateTime -/

/-- A time zone offset `hh:mm`, in seconds. -/
def zoneOffset? (z : String) : Option Int :=
  match z.splitOn ":" with
  | [h, m] => do
      let h ← httpDigits? h 2
      let m ← httpDigits? m 2
      if h ≤ 14 && m ≤ 59 then some ((h * 3600 + m * 60 : Nat) : Int) else none
  | _ => none

/-- The time part without its zone, and the zone offset (0 for `Z` and
for no zone). -/
def splitZone? (t : String) : Option (String × Int) :=
  if t.endsWith "Z" then some ((t.dropEnd 1).toString, 0) else
  match t.splitOn "+", t.splitOn "-" with
  | [a, z], [_] => (zoneOffset? z).map (fun o => (a, o))
  | [_], [a, z] => (zoneOffset? z).map (fun o => (a, -o))
  | [_], [_] => some (t, 0)
  | _, _ => none

/-- An XML Schema 1.1 `dateTime` (`yyyy-mm-ddThh:mm:ss(.s+)?(zone)?`, year
of four or more digits, no sign) as seconds since the Unix epoch; a
fractional second is dropped, and a value without a zone is read as UTC. -/
def parseXsdDateTime? (s : String) : Option Int :=
  match s.splitOn "T" with
  | [d, t] =>
      match d.splitOn "-" with
      | [y, m, dd] => do
          let y ← if y.length ≥ 4 && y.all Char.isDigit then y.toNat? else none
          let m ← httpDigits? m 2
          let dd ← httpDigits? dd 2
          let (tm, off) ← splitZone? t
          let (main, frac) := match tm.splitOn "." with
            | [a] => (a, "0")
            | [a, f] => (a, f)
            | _ => ("", "")
          if frac == "" || !frac.all Char.isDigit then none
          let sec ← httpTimeOfDay? main
          let v ← httpDateValue? y m dd sec
          some (v - off)
      | _ => none
  | _ => none

/-! ### Policies and documents -/

/-- Read one constraint object (§Constraints). -/
def parseConstraint (j : Json) : Except String Constraint := do
  let l ← (j.getString? "leftOperand").elim (.error "a constraint needs a leftOperand string") .ok
  let left ← (Operand.ofString? l).elim
    (.error ("leftOperand \"" ++ l ++ "\" is not supported")) .ok
  let o ← (j.getString? "operator").elim (.error "a constraint needs an operator string") .ok
  let op ← (Operator.ofString? o).elim (.error ("operator \"" ++ o ++ "\" is not supported")) .ok
  let right ← (j.field? "rightOperand").elim (.error "a constraint needs a rightOperand") .ok
  match left with
  | .dateTime =>
      if op == .isAnyOf then .error "isAnyOf does not apply to dateTime" else
      match right with
      | .string v =>
          match parseXsdDateTime? v with
          | some t => .ok { left, op, values := [v], instant := t }
          | none => .error ("rightOperand \"" ++ v ++ "\" is not an XML Schema dateTime")
      | _ => .error "a dateTime rightOperand is an XML Schema dateTime string"
  | _ =>
      let norm (v : String) : String := if left == .format then baseMedia v else v
      match op, right with
      | .eq, .string v => .ok { left, op, values := [norm v] }
      | .isAnyOf, .array _ =>
          match stringsOf? right with
          | some (v :: vs) => .ok { left, op, values := (v :: vs).map norm }
          | _ => .error "an isAnyOf rightOperand is a non-empty array of strings"
      | _, _ => .error ("operator \"" ++ o ++ "\" with this rightOperand is not supported for \"" ++ l ++ "\"")

/-- Read a target object (§Targets). -/
def parseTarget (baseIri : String) (t : Json) : Except String (Matcher × List String) := do
  match t with
  | .object _ => pure ()
  | _ => .error "target is an object"
  let ty ← (t.getString? "type").elim (.error "target needs a type string") .ok
  let m ← (Matcher.ofString? ty).elim
    (.error ("target type \"" ++ ty ++ "\" is not a matcher this server supports")) .ok
  let vs ← ((t.field? "value").bind stringsOf?).elim
    (.error "target value is a collection of one or more strings") .ok
  if vs.isEmpty || !(t.field? "value").any (fun v => match v with | .array _ => true | _ => false) then
    .error "target value is a collection of one or more strings"
  let ps ← vs.mapM (fun v => (targetPath? baseIri v).elim
    (.error ("target value " ++ v ++ " is not a resource of this storage")) .ok)
  .ok (m, ps.eraseDups)

/-- Read one access policy (§Access Profile). -/
def parsePolicy (baseIri : String) (j : Json) : Except String Policy := do
  match j with
  | .object _ => pure ()
  | _ => .error "every member of access is an object"
  let tys ← ((j.field? "type").bind stringsOf?).elim
    (.error "a policy needs a type, a string or an array of strings") .ok
  if !tys.all (fun t => isTerm t || isUri t) then
    .error "a policy type value is not a term or an absolute URL"
  if !hasType tys "AccessPolicy" then .error "a policy type must include AccessPolicy"
  let acts ← match j.field? "action" with
    | some (.array xs) =>
        if xs.isEmpty then .error "action is a collection of one or more strings" else
        xs.mapM (fun x => match x with
          | .string s => (Action.ofString? s).elim
              (.error ("action \"" ++ s ++ "\" is not an operation this server recognizes")) .ok
          | _ => .error "every action is a string")
    | _ => .error "a policy needs action, a collection of one or more strings"
  let assignee ← (j.getString? "assignee").elim (.error "a policy needs an assignee URI") .ok
  if !isUri assignee then .error "assignee is not a URI"
  let target ← match j.field? "target" with
    | none => .ok none
    | some t => (parseTarget baseIri t).map some
  let cs ← match j.field? "constraint" with
    | none => .ok []
    | some (.array xs) => xs.mapM parseConstraint
    | some _ => .error "constraint is a collection of constraint objects"
  .ok { actions := acts.eraseDups, assignee, target, constraints := cs }

/-- What a document is once read: the policies, the inbox, and the
document to serve (with `@context` as an array and without `id`). -/
structure Parsed where
  policies : List Policy
  inbox : Option String
  doc : Json

/-- Read an access request (`kind` = `AccessRequest`) or an access grant
(`AccessGrant`) (§Data Model, §Types, §Storage, §Inbox, §Access, §JSON-LD
Serialization). `storageIris` are the IRIs that name this storage. -/
def parseDoc (baseIri : String) (storageIris : List String) (kind : String) (j : Json) :
    Except String Parsed := do
  let fs ← match j with
    | .object fs => .ok fs
    | _ => .error "the document is not a JSON object"
  let ctx ← ((j.field? "@context").bind contextOf?).elim
    (.error "@context is required: an ordered set that includes https://www.w3.org/ns/lws/v1") .ok
  if !ctx.any (fun x => x == .string lwsProfile) then
    .error "@context must include https://www.w3.org/ns/lws/v1"
  let tys ← ((j.field? "type").bind stringsOf?).elim
    (.error "type is required: a string or an array of strings") .ok
  if !tys.all (fun t => isTerm t || isUri t) then .error "a type value is not a term or an absolute URL"
  if !hasType tys kind then .error ("type must include " ++ kind)
  let storage ← (j.getString? "storage").elim (.error "storage is required: a URI") .ok
  if !isUri storage then .error "storage is not a URI"
  if !storageIris.contains storage then .error ("storage " ++ storage ++ " is not this storage")
  let inbox ← match j.field? "inbox" with
    | none => .ok none
    | some (.string u) => if isUri u then .ok (some u) else .error "inbox is not a URI"
    | some _ => .error "inbox is not a URI"
  let acc ← match j.field? "access" with
    | some (.array (x :: xs)) => .ok (x :: xs)
    | _ => .error "access is required: a collection of one or more objects"
  let policies ← acc.mapM (parsePolicy baseIri)
  let doc := Json.object (fs.filterMap (fun (k, v) =>
    if k == "id" then none
    else if k == "@context" then some (k, .array ctx)
    else some (k, v)))
  .ok { policies, inbox, doc }

/-! ## Persistence -/

def recordJson (r : Record) : Json :=
  .object [ ("id", .string r.id)
          , ("creator", match r.creator with | some c => .string c | none => .null)
          , ("created", .number (toString r.created))
          , ("doc", r.doc) ]

/-- The durable form: the base IRI the documents were written under, the
counter, the requests and the grants. -/
def stateJson (baseIri : String) (s : AccessState) : Json :=
  .object [ ("baseIri", .string baseIri)
          , ("seq", .number (toString s.seq))
          , ("requests", .array (s.requests.map recordJson))
          , ("grants", .array (s.grants.map recordJson)) ]

private def natOf? (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number s) => s.toNat?
  | _ => none

/-- Read the durable form back; every document is read again by
`parseDoc`, so a stored grant permits exactly what a posted one would. The
documents are read against the base IRI they were written under (member
`baseIri`), so a storage reopened under another origin keeps its grants:
their targets are storage paths. -/
def stateOfJson (baseIri : String) (storageIris : List String) (j : Json) :
    Except String AccessState := do
  let (baseIri, storageIris) := match j.getString? "baseIri" with
    | some b => (b, storageIris ++ [storageIdOf b, b])
    | none => (baseIri, storageIris)
  let one (kind : String) (it : Json) : Except String Record := do
    let id ← (it.getString? "id").elim (.error "access: a record has no id") .ok
    if id == "" || id.any (fun c => c == '/' || c == '?' || c == '#') then
      .error "access: a record id is not one path segment"
    let doc ← (it.field? "doc").elim (.error "access: a record has no doc") .ok
    let p ← (parseDoc baseIri storageIris kind doc).mapError (fun e => "access: " ++ e)
    .ok { id, creator := it.getString? "creator", created := (natOf? it "created").getD 0
          doc := p.doc, policies := p.policies, inbox := p.inbox }
  let reqs ← ((j.getArray? "requests").getD []).mapM (one "AccessRequest")
  let grants ← ((j.getArray? "grants").getD []).mapM (one "AccessGrant")
  .ok { requests := reqs, grants, seq := (natOf? j "seq").getD 0 }

end L4Factoidal.LWS.AccessPolicy
