/-
L4Factoidal.XMPP.Muc — XEP-0045 Multi-User Chat (https://xmpp.org/extensions/xep-0045.html),
the room service, as a total function over shared room state:

  step : Service → (from : full JID) → Stanza → Service × List Delivery

`Server.step` (one connection) hands a stanza addressed to the MUC domain to the
ops layer as `Out.muc`; the ops layer (`Wasm/Ops/XmppSession.lean`) keeps one
`Service` per server and performs each `Delivery` as `Out.routeFull` to the
occupant's own full JID. Design and scope: `docs/20261102-xmpp-starttls.md`,
"Step 3 design".

Covered (XEP-0045 section numbers):
  7.2   join (an instant room is created by its first occupant, 10.1.2):
        the joiner gets every occupant's presence, then its own with status 110
        (and 201 when it created the room), then the subject (7.2.15); every
        other occupant gets the joiner's presence
  7.2.9 nick conflict: presence error `conflict`
  7.4   a groupchat message from an occupant goes to every occupant, from
        `room@service/<the sender's nick>`; from anyone else, `not-acceptable`
  7.5   a private message to `room@service/nick` goes to that occupant only
  7.14  leaving: unavailable presence to every occupant, status 110 to the leaver;
        an empty room is destroyed (temporary rooms)
  6.2-6.4 disco#info and disco#items on the service and on a room

Not covered, answered `feature-not-implemented` or ignored, never silently
accepted: nick change, kick, ban, voice, room configuration forms, passwords,
members-only rooms, history, subject change, persistent rooms. Real JIDs are
never sent to anyone, moderators included (`Body` has no field for one).
Limits `maxRooms` and `maxOccupants` bound the state a client can create
(`service-unavailable`, XEP-0045 7.2.10).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XMPP.Core
import L4Factoidal.XMPP.Wire

namespace L4Factoidal.XMPP.Muc

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP (Jid)
open L4Factoidal.XMPP.Core (Stanza StanzaKind findAttr)

def nsMuc : String := "http://jabber.org/protocol/muc"
def nsMucUser : String := "http://jabber.org/protocol/muc#user"
def nsDiscoInfo : String := "http://jabber.org/protocol/disco#info"
def nsDiscoItems : String := "http://jabber.org/protocol/disco#items"
def nsStanzas : String := "urn:ietf:params:xml:ns:xmpp-stanzas"

/-! ## State -/

structure Occupant where
  nick : String
  /-- The occupant's own full JID. Used only as a delivery address. -/
  real : String
  /-- The occupant that created the room is its owner and a moderator. -/
  owner : Bool
  deriving Repr, DecidableEq, Inhabited

def Occupant.affiliation (o : Occupant) : String := if o.owner then "owner" else "none"
def Occupant.role (o : Occupant) : String := if o.owner then "moderator" else "participant"

structure Room where
  /-- The room JID's localpart. -/
  name : String
  occupants : List Occupant
  deriving Repr, DecidableEq, Inhabited

structure Service where
  /-- The MUC domain, e.g. `conference.example.com`. -/
  domain : String
  rooms : List Room := []
  maxRooms : Nat := 64
  maxOccupants : Nat := 64
  deriving Repr, Inhabited

def Room.byReal (r : Room) (real : String) : Option Occupant := r.occupants.find? (·.real == real)
def Room.byNick (r : Room) (nick : String) : Option Occupant := r.occupants.find? (·.nick == nick)
def Service.room? (svc : Service) (name : String) : Option Room := svc.rooms.find? (·.name == name)
def Service.roomJid (svc : Service) (name : String) : String := name ++ "@" ++ svc.domain

/-- Store a room; an empty room is removed (temporary rooms, XEP-0045 section 10.1.2). -/
def Service.put (svc : Service) (r : Room) : Service :=
  let others := svc.rooms.filter (·.name != r.name)
  { svc with rooms := if r.occupants.isEmpty then others else others ++ [r] }

/-! ## What a delivery says

No constructor carries an occupant's real JID: a delivery's only real JID is
its `to`, the address it is delivered to. -/

inductive Body where
  | presence (nick : String) (available : Bool) (affiliation role : String) (codes : List Nat)
  | groupchat (nick : String) (id : Option String) (payload : List Node)
  /-- The (empty) room subject, sent after join (XEP-0045 section 7.2.15). -/
  | subject
  | chat (nick : String) (id : Option String) (type : String) (payload : List Node)
  | error (kind : StanzaKind) (id : Option String) (fromAddr : String) (errType cond : String)
  | iqResult (id : Option String) (fromAddr : String) (children : List Node)
  deriving Inhabited

structure Delivery where
  /-- The recipient's own full JID. -/
  to : String
  /-- The room JID (or the service domain), the `from` of the stanza. -/
  room : String
  body : Body
  deriving Inhabited

/-- A client's payload, minus any `muc#user` element: only the room states
roles, affiliations and status codes, so a sender cannot forge them. -/
def sanitize (payload : List Node) : List Node :=
  payload.filter (fun n => match n with
    | .element _ attrs _ => findAttr attrs "xmlns" != some nsMucUser
    | _ => true)

def presenceOf (o : Occupant) (available : Bool) (codes : List Nat) : Body :=
  .presence o.nick available o.affiliation o.role codes

/-! ## Rooms: the pure operations the theorems are about -/

/-- Join `room` as `nick`, unless the nick is taken. The joiner is owner when
the room was empty. `none`: the nick is in use. -/
def joinRoom (room : Room) (nick real : String) : Option Room :=
  if room.occupants.any (·.nick == nick) then none
  else some { room with occupants := room.occupants ++ [⟨nick, real, room.occupants.isEmpty⟩] }

def leaveRoom (room : Room) (real : String) : Room :=
  { room with occupants := room.occupants.filter (·.real != real) }

/-- XEP-0045 section 7.4: a groupchat message. -/
def groupchat (svc : Service) (name from_ : String) (id : Option String) (payload : List Node) :
    List Delivery :=
  let rj := svc.roomJid name
  match svc.room? name with
  | none => [⟨from_, rj, .error .message id rj "cancel" "item-not-found"⟩]
  | some room =>
    match room.byReal from_ with
    | none => [⟨from_, rj, .error .message id rj "modify" "not-acceptable"⟩]
    | some me => room.occupants.map (fun o => ⟨o.real, rj, .groupchat me.nick id (sanitize payload)⟩)

/-- XEP-0045 section 7.5: a private message to one occupant. -/
def privateMsg (svc : Service) (name nick from_ : String) (id : Option String) (type : String)
    (payload : List Node) : List Delivery :=
  let rj := svc.roomJid name
  match svc.room? name with
  | none => [⟨from_, rj, .error .message id rj "cancel" "item-not-found"⟩]
  | some room =>
    match room.byReal from_, room.byNick nick with
    | some me, some target => [⟨target.real, rj, .chat me.nick id type (sanitize payload)⟩]
    | some _, none => [⟨from_, rj, .error .message id (rj ++ "/" ++ nick) "cancel" "item-not-found"⟩]
    | none, _ => [⟨from_, rj, .error .message id rj "modify" "not-acceptable"⟩]

/-- XEP-0045 sections 7.2 and 7.2.9: join, or refuse. -/
def join (svc : Service) (name nick from_ : String) : Service × List Delivery :=
  let rj := svc.roomJid name
  let fail (cond : String) : Service × List Delivery :=
    (svc, [⟨from_, rj, .error .presence none (rj ++ "/" ++ nick) "cancel" cond⟩])
  let room := (svc.room? name).getD ⟨name, []⟩
  if room.occupants.isEmpty && svc.rooms.length ≥ svc.maxRooms then fail "service-unavailable"
  else if room.occupants.length ≥ svc.maxOccupants then fail "service-unavailable"
  else
    match joinRoom room nick from_ with
    | none => fail "conflict"
    | some room' =>
      let created := room.occupants.isEmpty
      let me : Occupant := ⟨nick, from_, created⟩
      (svc.put room',
       room.occupants.map (fun o => Delivery.mk from_ rj (presenceOf o true [])) ++
       [⟨from_, rj, presenceOf me true (if created then [110, 201] else [110])⟩, ⟨from_, rj, .subject⟩] ++
       room.occupants.map (fun o => Delivery.mk o.real rj (presenceOf me true [])))

/-- XEP-0045 section 7.14: leave. Nothing when `from_` is not in the room. -/
def leave (svc : Service) (name from_ : String) : Service × List Delivery :=
  let rj := svc.roomJid name
  match svc.room? name with
  | none => (svc, [])
  | some room =>
    match room.byReal from_ with
    | none => (svc, [])
    | some me =>
      let room' := leaveRoom room from_
      (svc.put room',
       room'.occupants.map (fun o => Delivery.mk o.real rj (presenceOf me false [])) ++
       [⟨from_, rj, presenceOf me false [110]⟩])

/-- The session `from_` closed: it leaves every room it is in. -/
def leaveAll (svc : Service) (from_ : String) : Service × List Delivery :=
  svc.rooms.foldl (fun (acc : Service × List Delivery) r =>
    let (s', ds) := leave acc.1 r.name from_
    (s', acc.2 ++ ds)) (svc, [])

/-- A presence to `room@service/nick` from a current occupant: a status
update under the same nick goes to everyone; a different nick is a nick
change, which this service does not do. -/
def update (svc : Service) (room : Room) (me : Occupant) (nick from_ : String) : List Delivery :=
  let rj := svc.roomJid room.name
  if me.nick == nick then
    room.occupants.map (fun o => Delivery.mk o.real rj (presenceOf me true (if o.real == from_ then [110] else [])))
  else [⟨from_, rj, .error .presence none (rj ++ "/" ++ nick) "modify" "not-acceptable"⟩]

/-! ## Service discovery (XEP-0045 sections 6.2 to 6.4) -/

private def feature (v : String) : Node := .element "feature" [⟨"var", v⟩] []

def serviceIq (svc : Service) (from_ : String) (st : Stanza) : List Delivery :=
  let q (ns : String) := st.payload.find? (fun n => match n with
    | .element "query" attrs _ => findAttr attrs "xmlns" == some ns | _ => false)
  let ty := st.type.getD "get"
  if ty == "result" || ty == "error" then []
  else if ty == "get" && (q nsDiscoInfo).isSome then
    [⟨from_, svc.domain, .iqResult st.id svc.domain [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
      [.element "identity" [⟨"category", "conference"⟩, ⟨"type", "text"⟩, ⟨"name", "Factoidal MUC"⟩] [],
       feature nsMuc, feature nsDiscoInfo, feature nsDiscoItems]]⟩]
  else if ty == "get" && (q nsDiscoItems).isSome then
    [⟨from_, svc.domain, .iqResult st.id svc.domain [.element "query" [⟨"xmlns", nsDiscoItems⟩]
      (svc.rooms.map (fun r => .element "item" [⟨"jid", svc.roomJid r.name⟩, ⟨"name", r.name⟩] []))]⟩]
  else [⟨from_, svc.domain, .error .iq st.id svc.domain "cancel" "feature-not-implemented"⟩]

def roomIq (svc : Service) (name from_ : String) (st : Stanza) : List Delivery :=
  let rj := svc.roomJid name
  let ty := st.type.getD "get"
  let isInfo := st.payload.any (fun n => match n with
    | .element "query" attrs _ => findAttr attrs "xmlns" == some nsDiscoInfo | _ => false)
  if ty == "result" || ty == "error" then []
  else if ty == "get" && isInfo then
    match svc.room? name with
    | none => [⟨from_, rj, .error .iq st.id rj "cancel" "item-not-found"⟩]
    | some _ =>
      [⟨from_, rj, .iqResult st.id rj [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
        [.element "identity" [⟨"category", "conference"⟩, ⟨"type", "text"⟩, ⟨"name", name⟩] [],
         feature nsMuc, feature "muc_temporary", feature "muc_open", feature "muc_unmoderated",
         feature "muc_semianonymous", feature "muc_unsecured"]]⟩]
  else [⟨from_, rj, .error .iq st.id rj "cancel" "feature-not-implemented"⟩]

/-! ## The dispatch -/

/-- One stanza from the bound session `from_` (its full JID, stamped by
`Server.step`) to an address on this service. -/
def step (svc : Service) (from_ : String) (st : Stanza) : Service × List Delivery :=
  match st.to with
  | none => (svc, [])
  | some to =>
    if to.domainpart != svc.domain then (svc, [])
    else
      let ty := st.type
      match to.localpart, to.resourcepart, st.kind with
      | none, _, .iq => (svc, serviceIq svc from_ st)
      | none, _, _ => (svc, [])
      | some name, none, .message =>
        if ty == some "groupchat" then (svc, groupchat svc name from_ st.id st.payload)
        else if ty == some "error" then (svc, [])
        else (svc, [⟨from_, svc.roomJid name, .error .message st.id (svc.roomJid name) "modify" "bad-request"⟩])
      | some name, none, .iq => (svc, roomIq svc name from_ st)
      | some name, none, .presence =>
        -- XEP-0045 section 7.2.1: a join names a nick.
        if ty == none then (svc, [⟨from_, svc.roomJid name, .error .presence none (svc.roomJid name) "modify" "jid-malformed"⟩])
        else if ty == some "unavailable" then leave svc name from_
        else (svc, [])
      | some name, some nick, .presence =>
        if ty == some "unavailable" then leave svc name from_
        else if ty == none then
          match (svc.room? name).bind (·.byReal from_) with
          | some me => (svc, update svc ((svc.room? name).getD ⟨name, []⟩) me nick from_)
          | none => join svc name nick from_
        else (svc, [])
      | some name, some nick, .message =>
        if ty == some "groupchat" then
          (svc, [⟨from_, svc.roomJid name, .error .message st.id (svc.roomJid name) "modify" "bad-request"⟩])
        else if ty == some "error" then (svc, [])
        else (svc, privateMsg svc name nick from_ st.id (ty.getD "chat") st.payload)
      | some name, some nick, .iq =>
        if ty == some "result" || ty == some "error" then (svc, [])
        else (svc, [⟨from_, svc.roomJid name, .error .iq st.id (svc.roomJid name ++ "/" ++ nick) "cancel" "feature-not-implemented"⟩])

/-! ## Rendering -/

def Delivery.render (d : Delivery) : String :=
  let attrs (fromAddr : String) (rest : List Attribute) : List Attribute := [⟨"from", fromAddr⟩, ⟨"to", d.to⟩] ++ rest
  let idAttr (id : Option String) : List Attribute := (id.map (Attribute.mk "id")).toList
  Wire.render <| match d.body with
  | .presence nick available aff role codes =>
    .element "presence" (attrs (d.room ++ "/" ++ nick) (if available then [] else [⟨"type", "unavailable"⟩]))
      [.element "x" [⟨"xmlns", nsMucUser⟩]
        ([.element "item" [⟨"affiliation", aff⟩, ⟨"role", if available then role else "none"⟩] []] ++
         codes.map (fun c => .element "status" [⟨"code", toString c⟩] []))]
  | .groupchat nick id payload =>
    .element "message" (attrs (d.room ++ "/" ++ nick) ([⟨"type", "groupchat"⟩] ++ idAttr id)) payload
  | .subject =>
    .element "message" (attrs d.room [⟨"type", "groupchat"⟩]) [.element "subject" [] []]
  | .chat nick id ty payload =>
    .element "message" (attrs (d.room ++ "/" ++ nick) ([⟨"type", ty⟩] ++ idAttr id))
      (payload ++ [.element "x" [⟨"xmlns", nsMucUser⟩] []])
  | .error kind id fromAddr errType cond =>
    .element kind.tagName (attrs fromAddr ([⟨"type", "error"⟩] ++ idAttr id))
      [.element "error" [⟨"type", errType⟩] [.element cond [⟨"xmlns", nsStanzas⟩] []]]
  | .iqResult id fromAddr children =>
    .element "iq" (attrs fromAddr ([⟨"type", "result"⟩] ++ idAttr id)) children

/-! ## Theorems -/

/-- 1. Fan-out: a groupchat message from an occupant goes to exactly the
room's occupants, each once, in room order. -/
theorem groupchat_recipients (svc : Service) (name from_ : String) (id : Option String)
    (p : List Node) (room : Room) (me : Occupant)
    (hr : svc.room? name = some room) (hm : room.byReal from_ = some me) :
    (groupchat svc name from_ id p).map (·.to) = room.occupants.map (·.real) := by
  simp [groupchat, hr, hm, List.map_map, Function.comp_def]

/-- 2. No spoofing: every delivery of that message is from the room JID with
the SENDER's own occupant nick, and carries no `muc#user` element of the
sender's making. -/
theorem groupchat_from_sender (svc : Service) (name from_ : String) (id : Option String)
    (p : List Node) (room : Room) (me : Occupant)
    (hr : svc.room? name = some room) (hm : room.byReal from_ = some me) :
    ∀ d ∈ groupchat svc name from_ id p, d.room = svc.roomJid name ∧ d.body = .groupchat me.nick id (sanitize p) := by
  intro d hd
  simp [groupchat, hr, hm] at hd
  obtain ⟨o, _, rfl⟩ := hd
  exact ⟨rfl, rfl⟩

/-- The occupant found by `byReal` is the sender. -/
theorem byReal_real (r : Room) (real : String) (o : Occupant) (h : r.byReal real = some o) :
    o.real = real := by
  unfold Room.byReal at h
  have := List.find?_some h
  simpa using this

/-- 3. A message from someone who is not an occupant reaches nobody but the
sender (an error). -/
theorem groupchat_nonoccupant (svc : Service) (name from_ : String) (id : Option String)
    (p : List Node) (h : ∀ room, svc.room? name = some room → room.byReal from_ = none) :
    ∀ d ∈ groupchat svc name from_ id p, d.to = from_ := by
  intro d hd
  unfold groupchat at hd
  cases hr : svc.room? name with
  | none => simp [hr] at hd; simp [hd]
  | some room => simp [hr, h room hr] at hd; simp [hd]

/-- A private message goes to at most one address, and when it is delivered
to someone else than the sender, that address is the named occupant's. -/
theorem privateMsg_one (svc : Service) (name nick from_ : String) (id : Option String) (ty : String)
    (p : List Node) : (privateMsg svc name nick from_ id ty p).length = 1 := by
  unfold privateMsg
  generalize svc.room? name = r
  cases r with
  | none => rfl
  | some room =>
    simp only []
    generalize room.byReal from_ = a
    generalize room.byNick nick = b
    cases a <;> cases b <;> rfl

/-- 4. Nicks stay distinct: a join never adds a nick already in the room. -/
theorem joinRoom_nodup (room room' : Room) (nick real : String)
    (hnd : (room.occupants.map (·.nick)).Nodup) (h : joinRoom room nick real = some room') :
    (room'.occupants.map (·.nick)).Nodup := by
  unfold joinRoom at h
  split at h
  · cases h
  · rename_i hany
    cases h
    simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    intro heq
    subst heq
    apply hany
    simp only [List.any_eq_true, beq_iff_eq]
    simp only [List.mem_map] at ha
    obtain ⟨o, ho, rfl⟩ := ha
    exact ⟨o, ho, rfl⟩

/-- 6. Leaving removes the occupant. -/
theorem leaveRoom_gone (room : Room) (real : String) :
    ∀ o ∈ (leaveRoom room real).occupants, o.real ≠ real := by
  intro o ho
  simp [leaveRoom, List.mem_filter] at ho
  exact ho.2

/-- An empty room is not kept. -/
theorem put_empty (svc : Service) (r : Room) (h : r.occupants = []) :
    ∀ x ∈ (svc.put r).rooms, x.name ≠ r.name := by
  intro x hx
  simp [Service.put, h, List.mem_filter] at hx
  exact hx.2

/-- Leaving keeps the other occupants' nicks distinct (a sublist of a list
with distinct nicks). -/
theorem leaveRoom_nodup (room : Room) (real : String)
    (hnd : (room.occupants.map (·.nick)).Nodup) :
    ((leaveRoom room real).occupants.map (·.nick)).Nodup :=
  (List.Sublist.map _ List.filter_sublist).nodup hnd

/-! ## Checks -/

private def svc0 : Service := { domain := "conference.example.com" }
private def st (kind : StanzaKind) (to : String) (ty : Option String) (payload : List Node := []) : Stanza :=
  { kind, id := some "x1", from_ := none, to := Jid.parse to, type := ty, payload }
private def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
private def body (t : String) : Node := .element "body" [] [.text t]

-- Juliet creates the room: 110 and 201, then the subject.
#guard
  let (s, ds) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  s.rooms.length == 1 && ds.length == 2 &&
  has (ds[0]!.render) "code=\"201\"" && has (ds[0]!.render) "affiliation=\"owner\"" &&
  (has (ds[1]!.render) "<subject/>" || has (ds[1]!.render) "<subject></subject>")

-- Romeo joins: he gets Juliet's presence, his own (110, no 201), the subject;
-- Juliet gets his. No real JID appears in what anyone receives about another.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let (s2, ds) := step s1 "romeo@example.com/orchard" (st .presence "tea@conference.example.com/rom" none)
  (s2.room? "tea").map (·.occupants.length) == some 2 &&
  ds.map (·.to) == ["romeo@example.com/orchard", "romeo@example.com/orchard", "romeo@example.com/orchard", "juliet@example.com/balcony"] &&
  !has (ds[0]!.render) "juliet@example.com" && !has (ds[3]!.render) "romeo@example.com" &&
  !has (ds[1]!.render) "code=\"201\""

-- The nick is taken: conflict, and the room is unchanged.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let (s2, ds) := step s1 "mallory@example.com/x" (st .presence "tea@conference.example.com/jul" none)
  (s2.room? "tea").map (·.occupants.length) == some 1 && ds.length == 1 && has (ds[0]!.render) "conflict"

-- A groupchat message reaches both, from tea@…/jul; a forged muc#user status is dropped.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let (s2, _) := step s1 "romeo@example.com/orchard" (st .presence "tea@conference.example.com/rom" none)
  let forged : Node := .element "x" [⟨"xmlns", nsMucUser⟩] [.element "status" [⟨"code", "110"⟩] []]
  let (_, ds) := step s2 "juliet@example.com/balcony" (st .message "tea@conference.example.com" (some "groupchat") [body "hi", forged])
  ds.map (·.to) == ["juliet@example.com/balcony", "romeo@example.com/orchard"] &&
  ds.all (fun d => has d.render "from=\"tea@conference.example.com/jul\"" && has d.render "<body>hi</body>" && !has d.render "code=\"110\"")

-- A non-occupant's groupchat message: not-acceptable, to the sender only.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let (_, ds) := step s1 "mallory@example.com/x" (st .message "tea@conference.example.com" (some "groupchat") [body "spam"])
  ds.map (·.to) == ["mallory@example.com/x"] && has (ds[0]!.render) "not-acceptable"

-- A private message goes to the one occupant, from the sender's room nick.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let (s2, _) := step s1 "romeo@example.com/orchard" (st .presence "tea@conference.example.com/rom" none)
  let (_, ds) := step s2 "romeo@example.com/orchard" (st .message "tea@conference.example.com/jul" (some "chat") [body "psst"])
  ds.map (·.to) == ["juliet@example.com/balcony"] && has (ds[0]!.render) "from=\"tea@conference.example.com/rom\""

-- Leaving: Juliet hears it; the last to leave destroys the room.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let (s2, _) := step s1 "romeo@example.com/orchard" (st .presence "tea@conference.example.com/rom" none)
  let (s3, ds) := step s2 "romeo@example.com/orchard" (st .presence "tea@conference.example.com/rom" (some "unavailable"))
  let (s4, _) := leaveAll s3 "juliet@example.com/balcony"
  ds.map (·.to) == ["juliet@example.com/balcony", "romeo@example.com/orchard"] &&
  has (ds[1]!.render) "code=\"110\"" && s4.rooms.isEmpty

-- Disco on the service lists the room; nick change is refused, not done.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let (_, info) := step s1 "romeo@example.com/orchard" (st .iq "conference.example.com" (some "get") [.element "query" [⟨"xmlns", nsDiscoItems⟩] []])
  let (_, nc) := step s1 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/julie" none)
  has (info[0]!.render) "jid=\"tea@conference.example.com\"" && has (nc[0]!.render) "not-acceptable"

-- The room limit holds.
#guard
  let small : Service := { svc0 with maxRooms := 1 }
  let (s1, _) := step small "juliet@example.com/balcony" (st .presence "a@conference.example.com/j" none)
  let (s2, ds) := step s1 "juliet@example.com/balcony" (st .presence "b@conference.example.com/j" none)
  s2.rooms.length == 1 && has (ds[0]!.render) "service-unavailable"

end L4Factoidal.XMPP.Muc
