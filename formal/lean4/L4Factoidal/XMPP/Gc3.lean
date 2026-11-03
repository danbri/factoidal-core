/-
L4Factoidal.XMPP.Gc3 — "Groupchat 3.0" (GC3), the XSF's early-stage successor to MUC, as a
total function over shared group state:

  step : Service → (from : full JID) → Stanza → Service × List Delivery

THERE IS NO PUBLISHED GC3 SPECIFICATION. The source is Matthew Wild, "Groupchat 3.0", slides,
2025-01-30 (https://matthewwild.co.uk/uploads/xmpp-gc3-jan-2025.pdf: "Very early spec,
prototype implementations in progress (Prosody, xmpp-rs)"); a search on 2026-11-03 found no
ProtoXEP and no registered namespace. What the slides fix, and this module does:

  * joins are persistent: membership is an ACCOUNT's, not linked to presence; an offline
    member is still in the group; the nick is set at join and shared by all its clients;
  * participant JIDs are stable: the resource is a participant id (as XEP-0421) that does not
    change when the nick changes;
  * presence is optional: a member chooses whether it receives membership events;
  * one affiliation scale, no roles (the slides' "maybe").

Every wire format below is INVENTED for this prototype and listed, each with an xfail, in
https://github.com/danbri/factoidal/issues/1236: the namespace `urn:xmpp:gc3:prototype:0`
(deliberately not a plausible final name), the IQ payloads `<join/>`, `<leave/>`, `<nick/>`,
`<remove/>`, `<members/>`, the `<event/>` notice, the id form `p1`, `p2`, …, and a separate
service domain. Where an existing XEP fits, its real namespace is used: XEP-0421
`<occupant-id/>` and XEP-0172 `<nick/>` on every message.

The membership transition relation is `apply`, and every command in it carries its actor, the
authenticated account the session supplied. Theorem `apply_no_ghost`: no transition adds a
member except that member's own join (the property asked for in
`docs/designissues/2026-09-07-attestation-and-adversarial-server.md`, "Membership changes only
by authenticated member commands").

Not covered: knocking, configuration, history and MAM, MLS or any encryption, spaces,
persistence across a restart. `maxGroups` and `maxMembers` bound the state.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XMPP.Core
import L4Factoidal.XMPP.Wire

namespace L4Factoidal.XMPP.Gc3

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP (Jid)
open L4Factoidal.XMPP.Core (Stanza StanzaKind findAttr)

/-- INVENTED (issue 1236): there is no registered GC3 namespace. -/
def ns : String := "urn:xmpp:gc3:prototype:0"
def nsOccupantId : String := "urn:xmpp:occupant-id:0"
def nsNick : String := "http://jabber.org/protocol/nick"
def nsDiscoInfo : String := "http://jabber.org/protocol/disco#info"
def nsDiscoItems : String := "http://jabber.org/protocol/disco#items"
def nsStanzas : String := "urn:ietf:params:xml:ns:xmpp-stanzas"

def bareOf (s : String) : String :=
  match Jid.parse s with
  | some j => Jid.render { j with resourcepart := none }
  | none => s

/-! ## State -/

inductive Affiliation where
  | owner
  | member
  deriving Repr, DecidableEq, Inhabited

def Affiliation.name : Affiliation → String
  | .owner => "owner"
  | .member => "member"

structure Member where
  /-- The member's account. Used only as a delivery address. -/
  bare : String
  nick : String
  /-- The stable participant id: the resource of the member's group JID. -/
  id : String
  affiliation : Affiliation
  /-- Does this member receive membership events? -/
  presence : Bool
  deriving Repr, DecidableEq, Inhabited

structure Group where
  name : String
  members : List Member
  nextId : Nat := 1
  deriving Repr, DecidableEq, Inhabited

structure Service where
  domain : String
  groups : List Group := []
  maxGroups : Nat := 64
  maxMembers : Nat := 256
  deriving Repr, Inhabited

def Group.byBare (g : Group) (b : String) : Option Member := g.members.find? (·.bare == b)
def Service.group? (svc : Service) (name : String) : Option Group := svc.groups.find? (·.name == name)
def Service.groupJid (svc : Service) (name : String) : String := name ++ "@" ++ svc.domain
def Service.put (svc : Service) (g : Group) : Service :=
  let others := svc.groups.filter (·.name != g.name)
  { svc with groups := if g.members.isEmpty then others else others ++ [g] }

/-! ## The membership transition relation -/

/-- A change to a group, with its ACTOR: the authenticated account that asked. -/
inductive Command where
  | join (actor nick : String) (presence : Bool)
  | leave (actor : String)
  | rename (actor nick : String)
  | remove (actor targetId : String)

/-- Apply a command; `none` means refused, and the group is unchanged. -/
def apply (g : Group) : Command → Option Group
  | .join a nick p =>
    match g.byBare a with
    | some _ => some g
    | none =>
      if g.members.any (·.nick == nick) then none
      else some { g with
        members := g.members ++ [⟨a, nick, "p" ++ toString g.nextId,
          if g.members.isEmpty then .owner else .member, p⟩]
        nextId := g.nextId + 1 }
  | .leave a =>
    if (g.byBare a).isSome then some { g with members := g.members.filter (·.bare != a) } else none
  | .rename a nick =>
    match g.byBare a with
    | none => none
    | some _ =>
      if g.members.any (fun o => o.nick == nick && o.bare != a) then none
      else some { g with members := g.members.map (fun o => if o.bare == a then { o with nick := nick } else o) }
  | .remove a t =>
    match g.byBare a with
    | some m => if m.affiliation == .owner then some { g with members := g.members.filter (·.id != t) } else none
    | none => none

/-! ## Deliveries -/

inductive Body where
  /-- A group message, from `group@service/<id>`. -/
  | message (id nick : String) (stanzaId : Option String) (payload : List Node)
  /-- A membership event (INVENTED form, issue 1236), from the group's bare JID. -/
  | event (type id nick : String)
  | iqResult (stanzaId : Option String) (fromAddr : String) (children : List Node)
  | error (kind : StanzaKind) (stanzaId : Option String) (fromAddr : String) (errType cond : String)
  deriving Inhabited

structure Delivery where
  /-- A bare JID when `held`, else the asking session's full JID. -/
  to : String
  held : Bool
  group : String
  body : Body
  deriving Inhabited

/-- A client's payload minus anything that would claim an identity: GC3 elements, XEP-0421
`<occupant-id/>` and XEP-0172 `<nick/>`. Only the group says who sent a message. -/
def sanitize (payload : List Node) : List Node :=
  payload.filter (fun n => match n with
    | .element _ attrs _ =>
      let x := findAttr attrs "xmlns"
      x != some ns && x != some nsOccupantId && x != some nsNick
    | _ => true)

/-- A group message from a member to every member's account. -/
def message (svc : Service) (name from_ : String) (sid : Option String) (payload : List Node) :
    List Delivery :=
  let gj := svc.groupJid name
  match svc.group? name with
  | none => [⟨from_, false, gj, .error .message sid gj "cancel" "item-not-found"⟩]
  | some g =>
    match g.byBare (bareOf from_) with
    | none => [⟨from_, false, gj, .error .message sid gj "modify" "not-acceptable"⟩]
    | some me => g.members.map (fun m => ⟨m.bare, true, gj, .message me.id me.nick sid (sanitize payload)⟩)

/-- Membership events go to the members that asked for them. -/
def events (svc : Service) (g : Group) (type : String) (m : Member) : List Delivery :=
  (g.members.filter (·.presence)).map (fun o => ⟨o.bare, true, svc.groupJid g.name, .event type m.id m.nick⟩)

/-! ## The dispatch -/

private def child (tag : String) (ps : List Node) : Option Node :=
  ps.find? (fun n => match n with
    | .element t attrs _ => t == tag && findAttr attrs "xmlns" == some ns
    | _ => false)

private def attrOf (n : Node) (name : String) : Option String :=
  match n with
  | .element _ attrs _ => findAttr attrs name
  | _ => none

private def textOf (n : Node) : String :=
  match n with
  | .element _ _ cs => String.join (cs.filterMap (fun c => match c with | .text t => some t | _ => none))
  | _ => ""

private def feature (v : String) : Node := .element "feature" [⟨"var", v⟩] []

private def memberNode (m : Member) : Node :=
  .element "member" [⟨"id", m.id⟩, ⟨"nick", m.nick⟩, ⟨"affiliation", m.affiliation.name⟩] []

/-- An IQ to a group: the membership commands, the member list, disco. -/
def groupIq (svc : Service) (name from_ : String) (st : Stanza) : Service × List Delivery :=
  let gj := svc.groupJid name
  let actor := bareOf from_
  let err (cond : String) (t : String := "cancel") : Service × List Delivery :=
    (svc, [⟨from_, false, gj, .error .iq st.id gj t cond⟩])
  let ok (svc' : Service) (children : List Node) (more : List Delivery) : Service × List Delivery :=
    (svc', ⟨from_, false, gj, .iqResult st.id gj children⟩ :: more)
  let ty := st.type.getD "get"
  let existing := svc.group? name
  let g : Group := existing.getD ⟨name, [], 1⟩
  if ty == "result" || ty == "error" then (svc, [])
  else if ty == "get" then
    if (child "members" st.payload).isSome then
      match existing with
      | none => err "item-not-found"
      | some g =>
        -- Members only: the list is not public.
        if (g.byBare actor).isNone then err "forbidden" "auth"
        else ok svc [.element "members" [⟨"xmlns", ns⟩] (g.members.map memberNode)] []
    else if st.payload.any (fun n => match n with
        | .element "query" attrs _ => findAttr attrs "xmlns" == some nsDiscoInfo | _ => false) then
      match existing with
      | none => err "item-not-found"
      | some _ => ok svc [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
          [.element "identity" [⟨"category", "conference"⟩, ⟨"type", "text"⟩, ⟨"name", name⟩] [],
           feature ns, feature nsOccupantId]] []
    else err "feature-not-implemented"
  else
    match child "join" st.payload, child "leave" st.payload, child "nick" st.payload, child "remove" st.payload with
    | some j, _, _, _ =>
      let nick := (attrOf j "nick").getD (((Jid.parse actor).bind (·.localpart)).getD actor)
      let presence := attrOf j "presence" == some "true"
      if nick.isEmpty then err "bad-request" "modify"
      else if existing.isNone && svc.groups.length ≥ svc.maxGroups then err "resource-constraint" "wait"
      else if (g.byBare actor).isNone && g.members.length ≥ svc.maxMembers then err "resource-constraint" "wait"
      else
        match apply g (.join actor nick presence) with
        | none => err "conflict"
        | some g' =>
          match g'.byBare actor with
          | none => err "internal-server-error"
          | some me =>
            let fresh := (g.byBare actor).isNone
            ok (svc.put g') [.element "joined" [⟨"xmlns", ns⟩, ⟨"id", me.id⟩, ⟨"nick", me.nick⟩,
              ⟨"affiliation", me.affiliation.name⟩] []] (if fresh then events svc g' "joined" me else [])
    | none, some _, _, _ =>
      match g.byBare actor, apply g (.leave actor) with
      | some me, some g' => ok (svc.put g') [] (events svc g' "left" me)
      | _, _ => err "item-not-found"
    | none, none, some n, _ =>
      let nick := textOf n
      if nick.isEmpty then err "bad-request" "modify"
      else
        match apply g (.rename actor nick) with
        | none => err (if (g.byBare actor).isNone then "item-not-found" else "conflict")
        | some g' =>
          match g'.byBare actor with
          | some me => ok (svc.put g') [] (events svc g' "renamed" me)
          | none => err "internal-server-error"
    | none, none, none, some r =>
      match attrOf r "id" with
      | none => err "bad-request" "modify"
      | some t =>
        match g.members.find? (·.id == t), apply g (.remove actor t) with
        | some gone, some g' =>
          ok (svc.put g') [] (events svc g' "removed" gone ++ [⟨gone.bare, true, gj, .event "removed" gone.id gone.nick⟩])
        | none, _ => err "item-not-found"
        | some _, none => err "forbidden" "auth"
    | none, none, none, none => err "feature-not-implemented"

def serviceIq (svc : Service) (from_ : String) (st : Stanza) : List Delivery :=
  let ty := st.type.getD "get"
  let has (x : String) := st.payload.any (fun n => match n with
    | .element "query" attrs _ => findAttr attrs "xmlns" == some x | _ => false)
  if ty == "result" || ty == "error" then []
  else if ty == "get" && has nsDiscoInfo then
    [⟨from_, false, svc.domain, .iqResult st.id svc.domain [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
      [.element "identity" [⟨"category", "conference"⟩, ⟨"type", "text"⟩, ⟨"name", "Factoidal GC3 (prototype)"⟩] [],
       feature ns, feature nsDiscoInfo]]⟩]
  else [⟨from_, false, svc.domain, .error .iq st.id svc.domain "cancel" "feature-not-implemented"⟩]

def step (svc : Service) (from_ : String) (st : Stanza) : Service × List Delivery :=
  match st.to with
  | none => (svc, [])
  | some to =>
    if to.domainpart != svc.domain then (svc, [])
    else
      match to.localpart, to.resourcepart, st.kind with
      | none, _, .iq => (svc, serviceIq svc from_ st)
      | none, _, _ => (svc, [])
      | some name, none, .iq => groupIq svc name from_ st
      | some name, none, .message =>
        if st.type == some "groupchat" then (svc, message svc name from_ st.id st.payload)
        else if st.type == some "error" then (svc, [])
        else (svc, [⟨from_, false, svc.groupJid name, .error .message st.id (svc.groupJid name) "modify" "bad-request"⟩])
      | some _, _, .presence => (svc, [])
      | some name, _, kind =>
        if st.type == some "error" || st.type == some "result" then (svc, [])
        else (svc, [⟨from_, false, svc.groupJid name, .error kind st.id (svc.groupJid name) "cancel" "feature-not-implemented"⟩])

/-! ## Rendering -/

def Delivery.render (d : Delivery) : String :=
  let idAttr (id : Option String) : List Attribute := (id.map (Attribute.mk "id")).toList
  Wire.render <| match d.body with
  | .message id nick sid payload =>
    .element "message" ([⟨"from", d.group ++ "/" ++ id⟩, ⟨"to", d.to⟩, ⟨"type", "groupchat"⟩] ++ idAttr sid)
      (payload ++ [.element "occupant-id" [⟨"xmlns", nsOccupantId⟩, ⟨"id", id⟩] [],
                   .element "nick" [⟨"xmlns", nsNick⟩] [.text nick]])
  | .event type id nick =>
    .element "message" [⟨"from", d.group⟩, ⟨"to", d.to⟩, ⟨"type", "groupchat"⟩]
      [.element "event" [⟨"xmlns", ns⟩, ⟨"type", type⟩, ⟨"id", id⟩, ⟨"nick", nick⟩] []]
  | .iqResult sid fromAddr children =>
    .element "iq" ([⟨"from", fromAddr⟩, ⟨"to", d.to⟩, ⟨"type", "result"⟩] ++ idAttr sid) children
  | .error kind sid fromAddr errType cond =>
    .element kind.tagName ([⟨"from", fromAddr⟩, ⟨"to", d.to⟩, ⟨"type", "error"⟩] ++ idAttr sid)
      [.element "error" [⟨"type", errType⟩] [.element cond [⟨"xmlns", nsStanzas⟩] []]]

/-! ## Theorems -/

/-- NO GHOST MEMBER. A member present after a transition was a member before, or the
transition is that member's OWN join (its actor is the member). No command lets one account
add another. -/
theorem apply_no_ghost (g g' : Group) (c : Command) (h : apply g c = some g') (b : String)
    (hb : b ∈ g'.members.map (·.bare)) :
    b ∈ g.members.map (·.bare) ∨ ∃ nick p, c = .join b nick p := by
  cases c with
  | join a nick p =>
    simp only [apply] at h
    cases hm : g.byBare a with
    | some _ => simp only [hm, Option.some.injEq] at h; subst h; exact Or.inl hb
    | none =>
      simp only [hm] at h
      split at h
      · cases h
      · cases h
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact Or.inl hb
        · exact Or.inr ⟨nick, p, rfl⟩
  | leave a =>
    simp only [apply] at h
    split at h
    · cases h
      left
      simp only [List.mem_map, List.mem_filter] at hb ⊢
      obtain ⟨o, ⟨ho, _⟩, rfl⟩ := hb
      exact ⟨o, ho, rfl⟩
    · cases h
  | rename a nick =>
    simp only [apply] at h
    cases hm : g.byBare a with
    | none => simp [hm] at h
    | some _ =>
      simp only [hm] at h
      split at h
      · cases h
      · cases h
        left
        simp only [List.map_map, List.mem_map, Function.comp] at hb ⊢
        obtain ⟨o, ho, hob⟩ := hb
        refine ⟨o, ho, ?_⟩
        rw [← hob]
        split <;> rfl
  | remove a t =>
    simp only [apply] at h
    cases hm : g.byBare a with
    | none => simp [hm] at h
    | some m =>
      simp only [hm] at h
      split at h
      · cases h
        left
        simp only [List.mem_map, List.mem_filter] at hb ⊢
        obtain ⟨o, ⟨ho, _⟩, rfl⟩ := hb
        exact ⟨o, ho, rfl⟩
      · cases h

/-- STABLE PARTICIPANT JIDS. A rename changes no member's id, so every group JID
`group@service/<id>` is the same after it. -/
theorem apply_rename_ids (g g' : Group) (a nick : String) (h : apply g (.rename a nick) = some g') :
    g'.members.map (·.id) = g.members.map (·.id) := by
  simp only [apply] at h
  cases hm : g.byBare a with
  | none => simp [hm] at h
  | some _ =>
    simp only [hm] at h
    split at h
    · cases h
    · cases h
      rw [List.map_map]
      congr 1
      funext o
      simp only [Function.comp]
      split <;> rfl

/-- Only an owner removes. -/
theorem apply_remove_owner (g g' : Group) (a t : String) (h : apply g (.remove a t) = some g') :
    ∃ m, g.byBare a = some m ∧ m.affiliation = .owner := by
  simp only [apply] at h
  cases hm : g.byBare a with
  | none => simp [hm] at h
  | some m =>
    simp only [hm] at h
    split at h
    · rename_i ho
      exact ⟨m, rfl, by simpa using ho⟩
    · cases h

/-- A join never adds a nick already in the group. -/
theorem apply_join_nicks_nodup (g g' : Group) (a nick : String) (p : Bool)
    (hnd : (g.members.map (·.nick)).Nodup) (h : apply g (.join a nick p) = some g') :
    (g'.members.map (·.nick)).Nodup := by
  simp only [apply] at h
  cases hm : g.byBare a with
  | some _ => simp only [hm, Option.some.injEq] at h; subst h; exact hnd
  | none =>
    simp only [hm] at h
    split at h
    · cases h
    · rename_i hany
      cases h
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      intro heq
      subst heq
      apply hany
      simp only [List.any_eq_true, beq_iff_eq]
      simp only [List.mem_map] at hx
      obtain ⟨o, ho, rfl⟩ := hx
      exact ⟨o, ho, rfl⟩

/-- Fan-out: a member's message goes to exactly the members' accounts, held for offline ones,
from the sender's own participant id. -/
theorem message_recipients (svc : Service) (name from_ : String) (sid : Option String) (p : List Node)
    (g : Group) (me : Member) (hg : svc.group? name = some g) (hm : g.byBare (bareOf from_) = some me) :
    (message svc name from_ sid p).map (·.to) = g.members.map (·.bare) ∧
    ∀ d ∈ message svc name from_ sid p, d.held = true ∧ d.body = .message me.id me.nick sid (sanitize p) := by
  constructor
  · simp [message, hg, hm, List.map_map, Function.comp_def]
  · intro d hd
    simp [message, hg, hm] at hd
    obtain ⟨_, _, rfl⟩ := hd
    exact ⟨rfl, rfl⟩

/-- A non-member's message reaches nobody but the sender. -/
theorem message_nonmember (svc : Service) (name from_ : String) (sid : Option String) (p : List Node)
    (h : ∀ g, svc.group? name = some g → g.byBare (bareOf from_) = none) :
    ∀ d ∈ message svc name from_ sid p, d.to = from_ := by
  intro d hd
  unfold message at hd
  cases hg : svc.group? name with
  | none => simp [hg] at hd; simp [hd]
  | some g => simp [hg, h g hg] at hd; simp [hd]

/-! ## Checks -/

private def svc0 : Service := { domain := "gc3.example.com" }
private def iq (to ty : String) (payload : List Node) : Stanza :=
  { kind := .iq, id := some "q", from_ := none, to := Jid.parse to, type := some ty, payload }
private def joinEl (nick : String) (presence : Bool) : Node :=
  .element "join" [⟨"xmlns", ns⟩, ⟨"nick", nick⟩, ⟨"presence", if presence then "true" else "false"⟩] []
private def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
private def G : String := "tea@gc3.example.com"
private def body (t : String) : Node := .element "body" [] [.text t]

private def two : Service :=
  let (s1, _) := step svc0 "juliet@example.com/a" (iq G "set" [joinEl "jul" true])
  (step s1 "romeo@example.com/x" (iq G "set" [joinEl "rom" false])).1

-- The first join creates the group: owner, id p1; the second is a member, id p2; Juliet
-- (presence) hears the join, Romeo (no presence) is not sent membership events.
#guard
  let (s1, d1) := step svc0 "juliet@example.com/a" (iq G "set" [joinEl "jul" true])
  let (_, d2) := step s1 "romeo@example.com/x" (iq G "set" [joinEl "rom" false])
  has d1[0]!.render "id=\"p1\"" && has d1[0]!.render "affiliation=\"owner\"" &&
  has d2[0]!.render "id=\"p2\"" && has d2[0]!.render "affiliation=\"member\"" &&
  d2.length == 2 && d2[1]!.to == "juliet@example.com" && has d2[1]!.render "type=\"joined\""

-- Persistent: a join from another client of the same account is no change.
#guard
  let (s, ds) := step two "juliet@example.com/b" (iq G "set" [joinEl "other" true])
  (s.group? "tea").map (·.members.length) == some 2 && has ds[0]!.render "nick=\"jul\"" && ds.length == 1

-- A message goes to both accounts (held), from tea@…/p2 with XEP-0421 occupant-id and
-- XEP-0172 nick; a forged occupant-id is dropped.
#guard
  let forged : Node := .element "occupant-id" [⟨"xmlns", nsOccupantId⟩, ⟨"id", "p1"⟩] []
  let st : Stanza := { kind := .message, id := some "m1", from_ := none, to := Jid.parse G, type := some "groupchat", payload := [body "hi", forged] }
  let (_, ds) := step two "romeo@example.com/x" st
  ds.map (·.to) == ["juliet@example.com", "romeo@example.com"] && ds.all (·.held) &&
  ds.all (fun d => has d.render "from=\"tea@gc3.example.com/p2\"" && has d.render "id=\"p2\"" &&
    !has d.render "id=\"p1\"" && has d.render ">rom</nick>")

-- A rename keeps the participant id.
#guard
  let (s, _) := step two "romeo@example.com/x" (iq G "set" [.element "nick" [⟨"xmlns", ns⟩] [.text "romeo"]])
  (s.group? "tea").map (·.members.map (fun m => (m.id, m.nick))) == some [("p1", "jul"), ("p2", "romeo")]

-- Only the owner removes; a member's attempt is forbidden and changes nothing.
#guard
  let rm : Node := .element "remove" [⟨"xmlns", ns⟩, ⟨"id", "p1"⟩] []
  let (s1, d1) := step two "romeo@example.com/x" (iq G "set" [rm])
  let (s2, _) := step two "juliet@example.com/a" (iq G "set" [.element "remove" [⟨"xmlns", ns⟩, ⟨"id", "p2"⟩] []])
  has d1[0]!.render "forbidden" && (s1.group? "tea").map (·.members.length) == some 2 &&
  (s2.group? "tea").map (·.members.map (·.id)) == some ["p1"]

-- A non-member cannot post or read the member list.
#guard
  let st : Stanza := { kind := .message, id := some "m2", from_ := none, to := Jid.parse G, type := some "groupchat", payload := [body "spam"] }
  let (_, a) := step two "mallory@example.com/z" st
  let (_, b) := step two "mallory@example.com/z" (iq G "get" [.element "members" [⟨"xmlns", ns⟩] []])
  a.map (·.to) == ["mallory@example.com/z"] && has a[0]!.render "not-acceptable" && has b[0]!.render "forbidden"

-- The member list carries ids, nicks and affiliations, and no real JID.
#guard
  let (_, ds) := step two "juliet@example.com/a" (iq G "get" [.element "members" [⟨"xmlns", ns⟩] []])
  has ds[0]!.render "id=\"p2\"" && !has ds[0]!.render "romeo@example.com"

-- A taken nick is a conflict.
#guard
  let (_, ds) := step two "mallory@example.com/z" (iq G "set" [joinEl "jul" false])
  has ds[0]!.render "conflict"

end L4Factoidal.XMPP.Gc3
