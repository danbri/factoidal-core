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
        other occupant gets the joiner's presence. An outcast is refused with
        `forbidden` (7.2.7)
  7.2.9 nick conflict: presence error `conflict`, for a nick in use (a nick that
        differs only in case counts as in use) and for a nick reserved for another
        account (`Service.reserved`). A nick that cannot be told from another by eye
        (`nickOk`) is refused with `not-acceptable`
  7.4   a groupchat message from an occupant goes to every occupant, from
        `room@service/<the sender's nick>`; from anyone else, `not-acceptable`
  7.5   a private message to `room@service/nick` goes to that occupant only
  7.14  leaving: unavailable presence to every occupant, status 110 to the leaver;
        an empty room is destroyed (temporary rooms)
  6.2-6.4 disco#info and disco#items on the service and on a room
XEP-0421 occupant ids, when `Service.idSeed` is set: every presence and groupchat message of a room
carries `<occupant-id/>`, a keyed digest of the room and the account, so an account has one id in a
room on every resource and at every join, and a new nick cannot pass for the old one. It gives no
JID away, and another room shows another id. A client's own `<occupant-id/>` is dropped.
  7.2.6 members-only rooms, from a list per room in the server's configuration
        (`Service.memberLists`): anyone else gets presence error
        `registration-required`, and the room is hidden from them. An admin or an
        owner can add members to the list (9.3); the configured names stay. A room
        with no list is open to every account of the server
  8.2   kick (`role='none'`): status 307 (and 110 to the person who is removed)
  8.3-8.5 grant and revoke voice (`role='participant'`, `role='visitor'`), the voice list.
        A visitor cannot send to the room (`forbidden`). A revoked voice stays with the
        account until a moderator gives it back, also across a new join
  9.1-9.5 ban (`affiliation='outcast'`, status 301), the ban list, member grant, revoke
        (status 321 when the person may no longer stay), the member list
  9.6-9.8 grant and revoke moderator (`role='moderator'`, `role='participant'`), the list
  10.3-10.8 grant and revoke admin and owner, the lists, under `muc#admin` or `muc#owner`.
        A request with more than one item is done in full or not at all
  10.1.2 the empty form of an instant room is accepted from an owner

Affiliations belong to a room and an account, not to a session (`Service.acls`, one `Acl` for each
room name, kept when the room is empty). `Service.affOfKey` is the one place that states a person's
affiliation: a configured owner (`Service.serviceOwners`, `Service.roomOwners`) first, then the
`Acl`, then the configured member list. A configured owner cannot be changed over XMPP.

First owner: with an owner configuration (`Service.firstOwner` is false) nobody becomes an owner by
being first in a room, and `Acl`s are kept across a restart (`StateCodec`, `/xmpp/muc/`). With no
owner configuration (`Service.firstOwner` is true), the first occupant of a room with no owner is its
owner, as before, and the room's `Acl` goes with the room: an ordinary account then adds nothing that
stays after the room.

Moderators see nicks, not real JIDs (XEP-0045 section 5.1.2 allows them in a semi-anonymous room; this
service does not send them in presence). An admin can act on a nick (`<item nick='...'
affiliation='outcast'/>`), and the affiliation lists, which only admins and owners get, name bare JIDs.

Not covered, answered `feature-not-implemented` or ignored, never silently
accepted: nick change, room configuration forms, room destruction by an owner (10.9), passwords,
history, subject change (a client's `<subject/>` is dropped, `sanitize`), persistent rooms. No bare
JID goes to anyone but an admin or an owner, and no full JID goes to anyone (`Body` has no field for
one).
Limits `maxRooms` and `maxOccupants` bound the state a client can create
(`service-unavailable`, XEP-0045 7.2.10); `maxAclRooms` and `maxAclEntries` bound the kept
affiliations (`resource-constraint`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XMPP.Core
import L4Factoidal.XMPP.Wire
import L4Factoidal.XMPP.Gc3
import L4Factoidal.XMPP.Scram

namespace L4Factoidal.XMPP.Muc

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP (Jid)
open L4Factoidal.XMPP.Core (Stanza StanzaKind findAttr)

def nsMuc : String := "http://jabber.org/protocol/muc"
def nsMucUser : String := "http://jabber.org/protocol/muc#user"
def nsMucAdmin : String := "http://jabber.org/protocol/muc#admin"
def nsMucOwner : String := "http://jabber.org/protocol/muc#owner"
def nsData : String := "jabber:x:data"
def nsDiscoInfo : String := "http://jabber.org/protocol/disco#info"
def nsDiscoItems : String := "http://jabber.org/protocol/disco#items"
def nsStanzas : String := "urn:ietf:params:xml:ns:xmpp-stanzas"

/-! ## State -/

/-- XEP-0045 section 5.2: an account's long-lived relation to a room. -/
inductive Affiliation where
  | unaffiliated | member | admin | owner | outcast
  deriving Repr, DecidableEq, Inhabited

/-- XEP-0045 section 5.1: a session's relation to a room while it is there. The role `none` is not
a value here: an occupant has a role, and a person with the role `none` is not in the room. -/
inductive Role where
  | participant | visitor | moderator
  deriving Repr, DecidableEq, Inhabited

def Affiliation.text : Affiliation → String
  | .unaffiliated => "none"
  | .member => "member"
  | .admin => "admin"
  | .owner => "owner"
  | .outcast => "outcast"

def Affiliation.ofText? : String → Option Affiliation
  | "none" => some .unaffiliated
  | "member" => some .member
  | "admin" => some .admin
  | "owner" => some .owner
  | "outcast" => some .outcast
  | _ => none

theorem Affiliation.ofText_text (a : Affiliation) : Affiliation.ofText? a.text = some a := by
  cases a <;> rfl

/-- The order of XEP-0045 section 5.2. Admin is 2: from there, an affiliation has room powers. -/
def Affiliation.rank : Affiliation → Nat
  | .owner => 3
  | .admin => 2
  | .member => 1
  | .unaffiliated => 0
  | .outcast => 0

def Role.text : Role → String
  | .moderator => "moderator"
  | .participant => "participant"
  | .visitor => "visitor"

structure Occupant where
  nick : String
  /-- The occupant's own full JID. Used only as a delivery address. -/
  real : String
  /-- As shown in presence. `Service.affOf` decides; this field only reports. -/
  aff : Affiliation := .unaffiliated
  role : Role := .participant
  /-- The XEP-0421 occupant id; empty: none. -/
  occId : String := ""
  deriving Repr, DecidableEq, Inhabited

structure Room where
  /-- The room JID's localpart. -/
  name : String
  occupants : List Occupant
  deriving Repr, DecidableEq, Inhabited

/-- A members-only room (XEP-0045 section 7.2.6) and who may join it; also the owners
that the configuration names for a room. -/
structure MemberList where
  /-- The room JID's localpart. -/
  room : String
  /-- Bare JIDs. -/
  members : List String
  deriving Repr, DecidableEq, Inhabited

/-- One account's kept state in one room. -/
structure AclEntry where
  /-- `keyOf` of the account. -/
  jid : String
  aff : Affiliation := .unaffiliated
  /-- A moderator revoked this account's voice (XEP-0045 section 8.4). It stays across a new join:
  a role alone ends with the session, and a person could get the voice back by leaving. -/
  muted : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- What a room keeps when it has no occupants. -/
structure Acl where
  /-- The room JID's localpart. -/
  room : String
  entries : List AclEntry
  deriving Repr, DecidableEq, Inhabited

structure Service where
  /-- The MUC domain, e.g. `conference.example.com`. -/
  domain : String
  rooms : List Room := []
  memberLists : List MemberList := []
  /-- Reserved nicks (XEP-0045 section 7.2.9): `nickKey` of the nick, and the bare
  JID it is for. The server reserves each account's name for that account. -/
  reserved : List (String × String) := []
  /-- The key of the occupant ids, from the host's random source. Empty: no ids. -/
  idSeed : String := ""
  /-- Affiliations and revoked voices, for each room name that has any. -/
  acls : List Acl := []
  /-- Is the first occupant of a room with no owner its owner? False when the server has an owner
  configuration, also an empty one. -/
  firstOwner : Bool := true
  /-- Owners of every room (`keyOf` of the bare JIDs), from the configuration. -/
  serviceOwners : List String := []
  /-- Owners of one room (`keyOf` of the bare JIDs), from the configuration. -/
  roomOwners : List MemberList := []
  maxRooms : Nat := 64
  maxOccupants : Nat := 64
  maxAclRooms : Nat := 256
  maxAclEntries : Nat := 1000
  deriving Repr, Inhabited

def Room.byReal (r : Room) (real : String) : Option Occupant := r.occupants.find? (·.real == real)
def Room.byNick (r : Room) (nick : String) : Option Occupant := r.occupants.find? (·.nick == nick)
def Service.room? (svc : Service) (name : String) : Option Room := svc.rooms.find? (·.name == name)
def Service.roomJid (svc : Service) (name : String) : String := name ++ "@" ++ svc.domain

/-- The bare JID of a full JID. -/
def bareOf (full : String) : String := (full.splitOn "/").headD full

/-- An account as the affiliations compare it: a bare JID in lower case, so that a ban cannot miss
for a difference of case. There is no PRECIS here (https://github.com/danbri/factoidal/issues/676). -/
def keyOf (jid : String) : String := (bareOf jid).toLower

def Service.acl? (svc : Service) (name : String) : Option Acl := svc.acls.find? (·.room == name)

def Service.entriesOf (svc : Service) (name : String) : List AclEntry :=
  ((svc.acl? name).map (·.entries)).getD []

def Service.entry? (svc : Service) (name key : String) : Option AclEntry :=
  (svc.entriesOf name).find? (·.jid == key)

/-- Does the configuration name this account as an owner of this room? -/
def Service.configuredOwner (svc : Service) (name key : String) : Bool :=
  svc.serviceOwners.contains key || svc.roomOwners.any (fun l => l.room == name && l.members.contains key)

/-- Is this account on the configured member list of this room? -/
def Service.listed (svc : Service) (name key : String) : Bool :=
  svc.memberLists.any (fun l => l.room == name && l.members.any (fun m => keyOf m == key))

/-- An account's affiliation in a room. The one place that says it. -/
def Service.affOfKey (svc : Service) (name key : String) : Affiliation :=
  if svc.configuredOwner name key then .owner
  else
    let base : Affiliation := if svc.listed name key then .member else .unaffiliated
    match svc.entry? name key with
    | some e => if e.aff == .unaffiliated then base else e.aff
    | none => base

def Service.affOf (svc : Service) (name from_ : String) : Affiliation := svc.affOfKey name (keyOf from_)

def Service.mutedKey (svc : Service) (name key : String) : Bool :=
  match svc.entry? name key with
  | some e => e.muted
  | none => false

/-- Every owner of a room that the service knows. A name can be there twice. -/
def Service.ownersOf (svc : Service) (name : String) : List String :=
  svc.serviceOwners ++ (svc.roomOwners.filter (·.room == name)).flatMap (·.members) ++
    ((svc.entriesOf name).filter (·.aff == .owner)).map (·.jid)

/-- XEP-0045 section 5.1.2: the role an affiliation brings on entry. -/
def defaultRole (a : Affiliation) (muted : Bool) : Role :=
  if a.rank ≥ 2 then .moderator else if muted then .visitor else .participant

/-- Keep `aff` and `muted` for an account in a room. An entry that says nothing is not kept, and an
`Acl` with no entries is not kept. -/
def Service.nextEntries (svc : Service) (name key : String) (aff : Affiliation) (muted : Bool) : List AclEntry :=
  let rest := (svc.entriesOf name).filter (·.jid != key)
  if aff == .unaffiliated && !muted then rest else rest ++ [⟨key, aff, muted⟩]

def Service.setEntry (svc : Service) (name key : String) (aff : Affiliation) (muted : Bool) : Service :=
  let entries := svc.nextEntries name key aff muted
  let others := svc.acls.filter (·.room != name)
  { svc with acls := if entries.isEmpty then others else others ++ [⟨name, entries⟩] }

/-- Would one more entry for this account pass a limit? -/
def Service.aclFull (svc : Service) (name key : String) : Bool :=
  match svc.acl? name with
  | none => decide (svc.acls.length ≥ svc.maxAclRooms)
  | some a => !a.entries.any (·.jid == key) && decide (a.entries.length ≥ svc.maxAclEntries)

/-- A full-width form of an ASCII character (U+FF01 to U+FF5E), as that character. -/
def narrow (c : Char) : Char :=
  let n := c.toNat
  if 0xff01 ≤ n && n ≤ 0xff5e then Char.ofNat (n - 0xfee0) else c

/-- A nick as it is compared: two nicks that differ only in ASCII case or in width are one nick.
There is no PRECIS here (https://github.com/danbri/factoidal/issues/676), so look-alike letters of
other scripts stay apart. -/
def nickKey (n : String) : String := (n.map narrow).toLower

/-- A character that prints as nothing, or as a space: controls, the Unicode spaces, soft hyphen,
zero-width and direction marks. -/
def unseen (c : Char) : Bool :=
  let n := c.toNat
  n < 0x20 || (0x7f ≤ n && n ≤ 0xa0) || n == 0xad || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200f) ||
  (0x2028 ≤ n && n ≤ 0x202f) || (0x205f ≤ n && n ≤ 0x206f) || n == 0x3000 || n == 0xfeff

/-- Can this nick be read and told from another? Not empty, at most 64 bytes, no space at either
end, no two spaces together, no unseen character. -/
def nickOk (n : String) : Bool :=
  !n.isEmpty && decide (n.utf8ByteSize ≤ 64) && n.trim == n && (n.splitOn "  ").length == 1 && !n.any unseen

/-- Why `from_` (a full JID) may not have this nick: the error type and condition. -/
def Service.nickRefusal (svc : Service) (nick from_ : String) : Option (String × String) :=
  if !nickOk nick then some ("modify", "not-acceptable")
  else match svc.reserved.find? (·.1 == nickKey nick) with
    | some (_, owner) => if owner != bareOf from_ then some ("cancel", "conflict") else none
    | none => none

/-- May `from_` (a full JID) enter this room? An outcast may not. Every other account may, unless
the room has a member list: then it needs an affiliation. -/
def Service.mayJoin (svc : Service) (name from_ : String) : Bool :=
  let a := svc.affOf name from_
  a != .outcast && (a != .unaffiliated || !svc.memberLists.any (·.room == name))

/-- The XEP-0421 id of an account in a room: 16 bytes of an HMAC under `idSeed`, so it is the same
for each resource and each join, and cannot be turned back into the JID. -/
def Service.occupantId (svc : Service) (name from_ : String) : String :=
  if svc.idSeed.isEmpty then ""
  else Scram.b64Encode ((L4Factoidal.Crypto.hmacSha256 svc.idSeed.toUTF8
    ("occupant:" ++ name ++ ":" ++ bareOf from_).toUTF8).extract 0 16)

/-- Store a room; an empty room is removed (temporary rooms, XEP-0045 section 10.1.2). -/
def Service.put (svc : Service) (r : Room) : Service :=
  let others := svc.rooms.filter (·.name != r.name)
  { svc with rooms := if r.occupants.isEmpty then others else others ++ [r] }

/-- Store a room that someone left. With no owner configuration, an empty room's `Acl` goes with it. -/
def Service.putLeft (svc : Service) (r : Room) : Service :=
  let s := svc.put r
  if r.occupants.isEmpty && svc.firstOwner then { s with acls := s.acls.filter (·.room != r.name) } else s

/-! ## What a delivery says

No constructor carries an occupant's real JID: a delivery's only real JID is
its `to`, the address it is delivered to. -/

inductive Body where
  | presence (nick : String) (available : Bool) (affiliation role : String) (codes : List Nat) (occId : String)
  /-- An occupant that a moderator or an admin removed (XEP-0045 sections 8.2, 9.1, 9.4). -/
  | removed (nick : String) (affiliation : String) (codes : List Nat) (actor reason : Option String) (occId : String)
  | groupchat (nick : String) (id : Option String) (payload : List Node) (occId : String)
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
roles, affiliations and status codes, so a sender cannot forge them. Minus any
`<subject/>` too: this service has no subject change. Minus any `<occupant-id/>`
(XEP-0421 section 4: the service removes a client's). -/
def sanitize (payload : List Node) : List Node :=
  payload.filter (fun n => match n with
    | .element tag attrs _ =>
      tag != "subject" && findAttr attrs "xmlns" != some nsMucUser && findAttr attrs "xmlns" != some Gc3.nsOccupantId
    | _ => true)

def presenceOf (o : Occupant) (available : Bool) (codes : List Nat) : Body :=
  .presence o.nick available o.aff.text o.role.text codes o.occId

/-! ## Rooms: the pure operations the theorems are about -/

/-- Join `room` as `nick`, unless the nick is taken. `none`: the nick is in use. -/
def joinRoom (room : Room) (nick real : String) (occId : String := "")
    (aff : Affiliation := .unaffiliated) (role : Role := .participant) : Option Room :=
  if room.occupants.any (fun o => nickKey o.nick == nickKey nick) then none
  else some { room with occupants := room.occupants ++ [⟨nick, real, aff, role, occId⟩] }

def leaveRoom (room : Room) (real : String) : Room :=
  { room with occupants := room.occupants.filter (·.real != real) }

/-- XEP-0045 section 7.4: a groupchat message. A visitor has no voice (section 5.1.2). -/
def groupchat (svc : Service) (name from_ : String) (id : Option String) (payload : List Node) :
    List Delivery :=
  let rj := svc.roomJid name
  match svc.room? name with
  | none => [⟨from_, rj, .error .message id rj "cancel" "item-not-found"⟩]
  | some room =>
    match room.byReal from_ with
    | none => [⟨from_, rj, .error .message id rj "modify" "not-acceptable"⟩]
    | some me =>
      if me.role == .visitor then [⟨from_, rj, .error .message id rj "auth" "forbidden"⟩]
      else room.occupants.map (fun o => ⟨o.real, rj, .groupchat me.nick id (sanitize payload) me.occId⟩)

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
  if !svc.mayJoin name from_ then
    (svc, [⟨from_, rj, .error .presence none (rj ++ "/" ++ nick) "auth"
      (if svc.affOf name from_ == .outcast then "forbidden" else "registration-required")⟩])
  else if let some (t, c) := svc.nickRefusal nick from_ then
    (svc, [⟨from_, rj, .error .presence none (rj ++ "/" ++ nick) t c⟩])
  else if room.occupants.isEmpty && svc.rooms.length ≥ svc.maxRooms then fail "service-unavailable"
  else if room.occupants.length ≥ svc.maxOccupants then fail "service-unavailable"
  else
    let created := room.occupants.isEmpty
    -- With no owner configuration, the first occupant of a room with no owner is its owner.
    let svc1 := if created && svc.firstOwner && (svc.ownersOf name).isEmpty
      then svc.setEntry name (keyOf from_) .owner false else svc
    let aff := svc1.affOf name from_
    let role := defaultRole aff (svc1.mutedKey name (keyOf from_))
    match joinRoom room nick from_ (svc.occupantId name from_) aff role with
    | none => fail "conflict"
    | some room' =>
      let me : Occupant := ⟨nick, from_, aff, role, svc.occupantId name from_⟩
      (svc1.put room',
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
      (svc.putLeft room',
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
      ((svc.rooms.filter (fun r => svc.mayJoin r.name from_)).map (fun r => .element "item" [⟨"jid", svc.roomJid r.name⟩, ⟨"name", r.name⟩] []))]⟩]
  else [⟨from_, svc.domain, .error .iq st.id svc.domain "cancel" "feature-not-implemented"⟩]

def roomIq (svc : Service) (name from_ : String) (st : Stanza) : List Delivery :=
  let rj := svc.roomJid name
  let ty := st.type.getD "get"
  let isInfo := st.payload.any (fun n => match n with
    | .element "query" attrs _ => findAttr attrs "xmlns" == some nsDiscoInfo | _ => false)
  if ty == "result" || ty == "error" then []
  else if ty == "get" && isInfo then
    match (svc.room? name).filter (fun _ => svc.mayJoin name from_) with
    | none => [⟨from_, rj, .error .iq st.id rj "cancel" "item-not-found"⟩]
    | some _ =>
      [⟨from_, rj, .iqResult st.id rj [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
        [.element "identity" [⟨"category", "conference"⟩, ⟨"type", "text"⟩, ⟨"name", name⟩] [],
         feature nsMuc, feature "muc_temporary", feature Gc3.nsOccupantId,
         feature (if svc.memberLists.any (·.room == name) then "muc_membersonly" else "muc_open"), feature "muc_unmoderated",
         feature "muc_semianonymous", feature "muc_unsecured"]]⟩]
  else [⟨from_, rj, .error .iq st.id rj "cancel" "feature-not-implemented"⟩]

/-! ## Moderation (XEP-0045 sections 8 to 10)

`affRefusal` and `roleRefusal` are the privilege tables of sections 5.1.2 and 5.2.1; `setAff` and
`setRole` act on them. A refusal is the error type and condition. -/

abbrev Refusal := String × String

def refuseForbidden : Refusal := ("auth", "forbidden")
def refuseNotAllowed : Refusal := ("cancel", "not-allowed")
def refuseConflict : Refusal := ("cancel", "conflict")
def refuseBadRequest : Refusal := ("modify", "bad-request")
def refuseNotFound : Refusal := ("cancel", "item-not-found")
def refuseFull : Refusal := ("wait", "resource-constraint")

/-- May someone with affiliation `actor` kick, or revoke the voice of, this target? A lower affiliation
cannot act on a higher one (section 8.2), and a moderator cannot act on a moderator of the same
affiliation (section 5.1.2). So only an owner acts on an admin, and nobody on an owner. -/
def mayDiscipline (actor target : Affiliation) (targetRole : Role) : Bool :=
  decide (target.rank < actor.rank) ||
    (decide (target.rank = actor.rank) && decide (target.rank < 2) && targetRole != .moderator)

/-- The table of a role change. `new`: the role asked for; `none`: a kick (section 8.2). -/
def roleRefusal (actorRole : Role) (actor target : Affiliation) (targetRole : Role) (self : Bool) :
    Option Role → Option Refusal
  | some .moderator => if actor.rank < 2 then some refuseForbidden else none
  | some .participant =>
    if targetRole == .moderator then
      if actor.rank < 2 then some refuseForbidden
      else if target.rank ≥ 2 then some refuseNotAllowed
      else none
    else if actorRole != .moderator then some refuseForbidden
    else none
  | some .visitor =>
    if actorRole != .moderator then some refuseForbidden
    else if self then some refuseConflict
    -- Section 8.4: nobody revokes the voice of an admin or an owner.
    else if target.rank ≥ 2 || !mayDiscipline actor target targetRole then some refuseNotAllowed
    else none
  | none =>
    if actorRole != .moderator then some refuseForbidden
    else if self then some refuseConflict
    else if !mayDiscipline actor target targetRole then some refuseNotAllowed
    else none

/-- The table of an affiliation change (sections 9 and 10): an admin edits the ban and member lists,
and does not touch an admin or an owner; an owner edits every list. A configured owner stays, a room
keeps one owner (section 10.6), and nobody bans themselves (section 9.1). -/
def Service.affRefusal (svc : Service) (name actorKey key : String) (new : Affiliation) : Option Refusal :=
  let actor := svc.affOfKey name actorKey
  let cur := svc.affOfKey name key
  if actor.rank < 2 then some refuseForbidden
  else if new.rank ≥ 2 && actor != .owner then some refuseForbidden
  else if cur.rank ≥ 2 && actor != .owner then some refuseNotAllowed
  else if new == .outcast && key == actorKey then some refuseConflict
  else if svc.configuredOwner name key && new != .owner then some refuseNotAllowed
  else if cur == .member && new == .unaffiliated && svc.listed name key then some refuseNotAllowed
  else if new != .owner && (svc.ownersOf name).contains key && ((svc.ownersOf name).filter (· != key)).isEmpty
    then some refuseConflict
  else none

/-- Keep a new affiliation. An admin or an owner has a voice. -/
def Service.assign (svc : Service) (name key : String) (new : Affiliation) : Service :=
  svc.setEntry name key new (decide (new.rank < 2) && svc.mutedKey name key)

/-- The presence of each changed occupant, to every occupant of the room. -/
private def announce (rj : String) (room : Room) (changed : List Occupant) : List Delivery :=
  changed.flatMap (fun c => room.occupants.map (fun o =>
    Delivery.mk o.real rj (presenceOf c true (if o.real == c.real then [110] else []))))

/-- The presence of a removal: with the actor and the reason to the person removed, then to everyone
who stays (sections 8.2 and 9.1). -/
private def announceRemoved (rj : String) (stay : List Occupant) (o : Occupant) (aff : Affiliation) (code : Nat)
    (actor reason : Option String) : List Delivery :=
  ⟨o.real, rj, .removed o.nick aff.text [110, code] actor reason o.occId⟩ ::
    stay.map (fun x => Delivery.mk x.real rj (.removed o.nick aff.text [code] none none o.occId))

/-- An affiliation change for `key`. Everyone who may no longer be in the room goes: status 301 for a
ban, 321 for a lost membership. The others of that account are shown with the new affiliation. -/
def setAff (svc : Service) (name from_ key : String) (new : Affiliation) (reason : Option String) :
    Except Refusal (Service × List Delivery) :=
  match svc.affRefusal name (keyOf from_) key new with
  | some r => .error r
  | none =>
    if new == svc.affOfKey name key then .ok (svc, [])
    else if new != .unaffiliated && svc.aclFull name key then .error refuseFull
    else
      let s1 := svc.assign name key new
      match svc.room? name with
      | none => .ok (s1, [])
      | some room =>
        let rj := svc.roomJid name
        let actor := (room.byReal from_).map (·.nick)
        let aff := s1.affOfKey name key
        let (stay, gone) := room.occupants.partition (fun o => s1.mayJoin name o.real)
        let fresh (o : Occupant) : Occupant :=
          if keyOf o.real == key then { o with aff := aff, role := defaultRole aff (s1.mutedKey name key) } else o
        let room' := { room with occupants := stay.map fresh }
        let code := if new == .outcast then 301 else 321
        .ok (s1.putLeft room',
          gone.flatMap (fun o => announceRemoved rj stay o aff code actor reason) ++
          announce rj room' (room'.occupants.filter (fun o => keyOf o.real == key)))

/-- The role that `from_` acts with. An admin or an owner who is not in the room is a moderator here:
the affiliation is the power, and the person need not sit in the room to use it. -/
def Service.actorRole (svc : Service) (room : Room) (name from_ : String) : Role :=
  match room.byReal from_ with
  | some o => o.role
  | none => if (svc.affOf name from_).rank ≥ 2 then .moderator else .visitor

/-- A role change for the occupant `nick`; `new` is `none` for a kick. A role belongs to a session,
but a revoked voice belongs to the account: every session of the account has it. -/
def setRole (svc : Service) (name from_ nick : String) (new : Option Role) (reason : Option String) :
    Except Refusal (Service × List Delivery) :=
  let room := (svc.room? name).getD ⟨name, []⟩
  let actor := svc.affOf name from_
  let me := room.byReal from_
  let actorRole := svc.actorRole room name from_
  if actorRole != .moderator then .error refuseForbidden
  else match room.byNick nick with
  | none => .error refuseNotFound
  | some t =>
    let key := keyOf t.real
    let target := svc.affOfKey name key
    match roleRefusal actorRole actor target t.role (key == keyOf from_) new with
    | some r => .error r
    | none =>
      let rj := svc.roomJid name
      let kept := ((svc.entry? name key).map (·.aff)).getD .unaffiliated
      match new with
      | none =>
        let room' := leaveRoom room t.real
        .ok (svc.putLeft room', announceRemoved rj room'.occupants t target 307 (me.map (·.nick)) reason)
      | some .visitor =>
        if svc.aclFull name key then .error refuseFull
        else
          let room' := { room with occupants := room.occupants.map (fun o =>
            if keyOf o.real == key then { o with role := .visitor } else o) }
          .ok ((svc.setEntry name key kept true).put room',
            announce rj room' (room'.occupants.filter (fun o => keyOf o.real == key)))
      | some r =>
        let hit (o : Occupant) : Bool := o.real == t.real || (keyOf o.real == key && o.role == .visitor)
        let room' := { room with occupants := room.occupants.map (fun o =>
          if hit o then { o with role := if o.real == t.real then r else .participant } else o) }
        .ok ((svc.setEntry name key kept false).put room', announce rj room' (room'.occupants.filter hit))

/-- One `<item/>` of a set, parsed. -/
inductive Change where
  | role (nick : String) (new : Option Role) (reason : Option String)
  | aff (key : String) (new : Affiliation) (reason : Option String)
  deriving Inhabited

private def textOf (ns : List Node) : String :=
  String.join (ns.filterMap (fun n => match n with | .text t => some t | _ => none))

/-- The `<reason/>` of an item, at most 512 characters. -/
private def reasonOf (kids : List Node) : Option String :=
  kids.findSome? (fun n => match n with
    | .element "reason" _ ks => some (String.ofList ((textOf ks).toList.take 512))
    | _ => none)

def parseChange (room : Room) : Node → Except Refusal Change
  | .element "item" attrs kids =>
    let reason := reasonOf kids
    match findAttr attrs "affiliation", findAttr attrs "role" with
    | some a, none =>
      match Affiliation.ofText? a with
      | none => .error refuseBadRequest
      | some new =>
        match findAttr attrs "jid", findAttr attrs "nick" with
        | some j, _ =>
          match Jid.parse j with
          | some ⟨some l, d, _⟩ => .ok (.aff (keyOf (l ++ "@" ++ d)) new reason)
          | _ => .error ("modify", "jid-malformed")
        | none, some n =>
          match room.byNick n with
          | some o => .ok (.aff (keyOf o.real) new reason)
          | none => .error refuseNotFound
        | none, none => .error refuseBadRequest
    | none, some r =>
      match findAttr attrs "nick", r with
      | some n, "none" => .ok (.role n none reason)
      | some n, "visitor" => .ok (.role n (some .visitor) reason)
      | some n, "participant" => .ok (.role n (some .participant) reason)
      | some n, "moderator" => .ok (.role n (some .moderator) reason)
      | _, _ => .error refuseBadRequest
    | _, _ => .error refuseBadRequest
  | _ => .error refuseBadRequest

def applyChange (svc : Service) (name from_ : String) : Change → Except Refusal (Service × List Delivery)
  | .role nick new reason => setRole svc name from_ nick new reason
  | .aff key new reason => setAff svc name from_ key new reason

/-- Every item of a set, in order; the first refusal stops the whole request and nothing is kept. -/
def applyItems (svc : Service) (name from_ : String) (items : List Node) :
    Except Refusal (Service × List Delivery) :=
  items.foldl (fun acc n => match acc with
    | .error e => .error e
    | .ok (s, ds) =>
      match parseChange ((s.room? name).getD ⟨name, []⟩) n with
      | .error e => .error e
      | .ok c =>
        match applyChange s name from_ c with
        | .error e => .error e
        | .ok (s', ds') => .ok (s', ds ++ ds')) (.ok (svc, []))

/-- Who may read a list (sections 8.5, 9.2, 9.5, 9.8, 10.5, 10.8): the affiliation lists name bare
JIDs, so only admins read the ban and member lists, and only owners the admin and owner lists. -/
def listRefusal (actor : Affiliation) (actorRole : Role) (asked : Sum Affiliation Role) : Option Refusal :=
  match asked with
  | .inl .owner | .inl .admin => if actor == .owner then none else some refuseForbidden
  | .inl _ => if actor.rank ≥ 2 then none else some refuseForbidden
  | .inr .moderator => if actor.rank ≥ 2 then none else some refuseForbidden
  | .inr _ => if actorRole == .moderator then none else some refuseForbidden

/-- The accounts with this affiliation in a room. -/
def Service.withAff (svc : Service) (name : String) (a : Affiliation) : List String :=
  let kept := (svc.entriesOf name).map (·.jid)
  let listed := (svc.memberLists.filter (·.room == name)).flatMap (·.members.map keyOf)
  ((svc.ownersOf name ++ listed ++ kept).filter (fun k => svc.affOfKey name k == a)).eraseDups

/-- A `<query/>` of the admin or owner namespace: the namespace and the children. -/
def adminQueryOf (st : Stanza) : Option (String × List Node) :=
  st.payload.findSome? (fun n => match n with
    | .element "query" attrs kids =>
      match findAttr attrs "xmlns" with
      | some ns => if ns == nsMucAdmin || ns == nsMucOwner then some (ns, kids) else none
      | none => none
    | _ => none)

/-- The empty form of an instant room (section 10.1.2): the room is open already, so there is
nothing to do. A form with fields is a configuration, which this service does not do. -/
private def isInstantForm (kids : List Node) : Bool :=
  kids.any (fun n => match n with
    | .element "x" attrs ks =>
      findAttr attrs "xmlns" == some nsData && findAttr attrs "type" == some "submit" &&
        !ks.any (fun k => match k with | .element "field" _ _ => true | _ => false)
    | _ => false)

def adminIq (svc : Service) (name from_ : String) (st : Stanza) (ns : String) (kids : List Node) :
    Service × List Delivery :=
  let rj := svc.roomJid name
  let fail (r : Refusal) : Service × List Delivery := (svc, [⟨from_, rj, .error .iq st.id rj r.1 r.2⟩])
  let actor := svc.affOf name from_
  let room := (svc.room? name).getD ⟨name, []⟩
  let actorRole := svc.actorRole room name from_
  let items := kids.filter (fun n => match n with | .element "item" _ _ => true | _ => false)
  if st.type == some "set" && ns == nsMucOwner && items.isEmpty && isInstantForm kids then
    if actor == .owner then (svc, [⟨from_, rj, .iqResult st.id rj []⟩]) else fail refuseForbidden
  else if items.isEmpty then fail ("cancel", "feature-not-implemented")
  else if st.type == some "set" then
    if actor.rank < 2 && actorRole != .moderator then fail refuseForbidden
    else match applyItems svc name from_ items with
      | .error r => fail r
      | .ok (s, ds) => (s, ds ++ [⟨from_, rj, .iqResult st.id rj []⟩])
  else
    let attr (k : String) : Option String := match items with
      | .element _ attrs _ :: _ => findAttr attrs k
      | _ => none
    let answer (ks : List Node) : Service × List Delivery :=
      (svc, [⟨from_, rj, .iqResult st.id rj [.element "query" [⟨"xmlns", ns⟩] ks]⟩])
    match attr "affiliation", attr "role", (attr "affiliation").bind Affiliation.ofText? with
    | some _, none, some a =>
      match listRefusal actor actorRole (.inl a) with
      | some r => fail r
      | none => answer ((svc.withAff name a).map (fun k =>
          .element "item" [⟨"affiliation", a.text⟩, ⟨"jid", k⟩] []))
    | none, some r, _ =>
      let role? : Option Role := match r with
        | "moderator" => some .moderator
        | "participant" => some .participant
        | "visitor" => some .visitor
        | _ => none
      match role? with
      | none => fail refuseBadRequest
      | some want =>
        match listRefusal actor actorRole (.inr want) with
        | some e => fail e
        | none => answer ((room.occupants.filter (·.role == want)).map (fun o =>
            .element "item" [⟨"affiliation", o.aff.text⟩, ⟨"nick", o.nick⟩, ⟨"role", o.role.text⟩] []))
    | _, _, _ => fail refuseBadRequest

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
      | some name, none, .iq =>
        match adminQueryOf st with
        | some (ns, kids) =>
          if ty == some "get" || ty == some "set" then adminIq svc name from_ st ns kids else (svc, [])
        | none => (svc, roomIq svc name from_ st)
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
  let occ (o : String) : List Node :=
    if o.isEmpty then [] else [.element "occupant-id" [⟨"xmlns", Gc3.nsOccupantId⟩, ⟨"id", o⟩] []]
  Wire.render <| match d.body with
  | .presence nick available aff role codes o =>
    .element "presence" (attrs (d.room ++ "/" ++ nick) (if available then [] else [⟨"type", "unavailable"⟩]))
      ([.element "x" [⟨"xmlns", nsMucUser⟩]
        ([.element "item" [⟨"affiliation", aff⟩, ⟨"role", if available then role else "none"⟩] []] ++
         codes.map (fun c => .element "status" [⟨"code", toString c⟩] []))] ++ occ o)
  | .removed nick aff codes actor reason o =>
    .element "presence" (attrs (d.room ++ "/" ++ nick) [⟨"type", "unavailable"⟩])
      ([.element "x" [⟨"xmlns", nsMucUser⟩]
        ([.element "item" [⟨"affiliation", aff⟩, ⟨"role", "none"⟩]
           ((actor.map (fun a => Node.element "actor" [⟨"nick", a⟩] [])).toList ++
            (reason.map (fun r => Node.element "reason" [] [.text r])).toList)] ++
         codes.map (fun c => .element "status" [⟨"code", toString c⟩] []))] ++ occ o)
  | .groupchat nick id payload o =>
    .element "message" (attrs (d.room ++ "/" ++ nick) ([⟨"type", "groupchat"⟩] ++ idAttr id)) (payload ++ occ o)
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
    (hr : svc.room? name = some room) (hm : room.byReal from_ = some me) (hv : me.role ≠ .visitor) :
    (groupchat svc name from_ id p).map (·.to) = room.occupants.map (·.real) := by
  simp [groupchat, hr, hm, hv, List.map_map, Function.comp_def]

/-- 2. No spoofing: every delivery of that message is from the room JID with
the SENDER's own occupant nick, and carries no `muc#user` element of the
sender's making. -/
theorem groupchat_from_sender (svc : Service) (name from_ : String) (id : Option String)
    (p : List Node) (room : Room) (me : Occupant)
    (hr : svc.room? name = some room) (hm : room.byReal from_ = some me) (hv : me.role ≠ .visitor) :
    ∀ d ∈ groupchat svc name from_ id p, d.room = svc.roomJid name ∧ d.body = .groupchat me.nick id (sanitize p) me.occId := by
  intro d hd
  simp [groupchat, hr, hm, hv] at hd
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
theorem joinRoom_nodup (room room' : Room) (nick real occId : String) (aff : Affiliation) (role : Role)
    (hnd : (room.occupants.map (·.nick)).Nodup) (h : joinRoom room nick real occId aff role = some room') :
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

/-- 7. Members only: a join by someone who may not enter changes nothing, and
only the joiner hears of it. -/
theorem join_refused (svc : Service) (name nick from_ : String)
    (h : svc.mayJoin name from_ = false) :
    (join svc name nick from_).1 = svc ∧ ∀ d ∈ (join svc name nick from_).2, d.to = from_ := by
  simp [join, h]

/-- 7b. A nick refused for `from_`: nothing changes, and only `from_` hears of it. -/
theorem join_nickRefused (svc : Service) (name nick from_ : String) (r : String × String)
    (hm : svc.mayJoin name from_ = true) (h : svc.nickRefusal nick from_ = some r) :
    (join svc name nick from_).1 = svc ∧ ∀ d ∈ (join svc name nick from_).2, d.to = from_ := by
  obtain ⟨t, c⟩ := r
  simp [join, hm, h]

/-- A nick reserved for another account is refused. -/
theorem nickRefusal_reserved (svc : Service) (nick from_ owner k : String)
    (hn : nickOk nick = true) (hf : svc.reserved.find? (·.1 == nickKey nick) = some (k, owner))
    (ho : owner ≠ bareOf from_) : svc.nickRefusal nick from_ = some ("cancel", "conflict") := by
  simp [Service.nickRefusal, hn, hf, ho]

/-- Everyone in every room may be there. -/
def Service.sound (svc : Service) : Prop :=
  ∀ r ∈ svc.rooms, ∀ o ∈ r.occupants, svc.mayJoin r.name o.real = true

/-- `put` keeps the member lists, so it keeps `mayJoin`. -/
theorem put_mayJoin (svc : Service) (r : Room) (name from_ : String) :
    (svc.put r).mayJoin name from_ = svc.mayJoin name from_ := rfl

/-- Storing a room whose occupants may be there keeps the service sound. -/
theorem put_sound (svc : Service) (r : Room) (hs : svc.sound)
    (hr : ∀ o ∈ r.occupants, svc.mayJoin r.name o.real = true) : (svc.put r).sound := by
  intro x hx o ho
  rw [put_mayJoin]
  simp only [Service.put] at hx
  split at hx
  · exact hs x ((List.mem_filter.mp hx).1) o ho
  · rcases List.mem_append.mp hx with hx | hx
    · exact hs x ((List.mem_filter.mp hx).1) o ho
    · simp only [List.mem_singleton] at hx
      subst hx
      exact hr o ho

/-! ### Affiliations -/

private theorem find_filter_room (l : List Acl) (name n : String) (h : n ≠ name) :
    (l.filter (·.room != name)).find? (·.room == n) = l.find? (·.room == n) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons]
    by_cases ha : a.room = name
    · have h1 : (a.room != name) = false := by simp [ha]
      have h2 : (a.room == n) = false := by
        simpa using fun e : a.room = n => h (e.symm.trans ha)
      simp only [h1, Bool.false_eq_true, if_false, ih, List.find?_cons, h2]
    · have h1 : (a.room != name) = true := by simpa using ha
      simp only [h1, if_true, List.find?_cons, ih]

private theorem find_filter_room_self (l : List Acl) (name : String) :
    (l.filter (·.room != name)).find? (·.room == name) = none := by
  simp [List.find?_eq_none]

theorem setEntry_acl_other (svc : Service) (name n key : String) (aff : Affiliation) (m : Bool)
    (h : n ≠ name) : (svc.setEntry name key aff m).acl? n = svc.acl? n := by
  simp only [Service.setEntry, Service.acl?]
  split
  · exact find_filter_room _ _ _ h
  · rw [List.find?_append, find_filter_room _ _ _ h]
    cases svc.acls.find? (·.room == n) with
    | some _ => rfl
    | none => simp [Ne.symm h]

theorem setEntry_entriesOf (svc : Service) (name key : String) (aff : Affiliation) (m : Bool) :
    (svc.setEntry name key aff m).entriesOf name = svc.nextEntries name key aff m := by
  simp only [Service.entriesOf, Service.setEntry, Service.acl?]
  split
  · rename_i he
    rw [find_filter_room_self]
    simpa using (List.isEmpty_iff.mp he).symm
  · rw [List.find?_append, find_filter_room_self]
    simp

/-- What an affiliation depends on: `acls` and the configuration. -/
private theorem affOfKey_of_entries (a b : Service) (n k : String)
    (hs : a.serviceOwners = b.serviceOwners) (hr : a.roomOwners = b.roomOwners)
    (hm : a.memberLists = b.memberLists) (he : a.entriesOf n = b.entriesOf n) :
    a.affOfKey n k = b.affOfKey n k := by
  unfold Service.affOfKey Service.configuredOwner Service.listed Service.entry?
  rw [hs, hr, hm, he]

theorem affOfKey_other (svc : Service) (name n key k : String) (aff : Affiliation) (m : Bool)
    (h : n ≠ name) : (svc.setEntry name key aff m).affOfKey n k = svc.affOfKey n k :=
  affOfKey_of_entries _ _ _ _ rfl rfl rfl (by simp only [Service.entriesOf, setEntry_acl_other _ _ _ _ _ _ h])

theorem mayJoin_other (svc : Service) (name n key f : String) (aff : Affiliation) (m : Bool)
    (h : n ≠ name) : (svc.setEntry name key aff m).mayJoin n f = svc.mayJoin n f := by
  simp only [Service.mayJoin, Service.affOf, affOfKey_other _ _ _ _ _ _ _ h]
  rfl

/-- The new entry is what the service reads. -/
theorem setEntry_entry (svc : Service) (name key : String) (aff : Affiliation) (m : Bool)
    (h : aff ≠ .unaffiliated) : (svc.setEntry name key aff m).entry? name key = some ⟨key, aff, m⟩ := by
  simp only [Service.entry?, setEntry_entriesOf, Service.nextEntries]
  have hn : (aff == .unaffiliated) = false := by simpa using h
  simp only [hn, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.find?_append]
  have : ((svc.entriesOf name).filter (·.jid != key)).find? (·.jid == key) = none := by
    simp [List.find?_eq_none]
  rw [this]
  simp

/-- A configured owner is an owner, whatever the kept state says: the state cannot ban one. -/
theorem configured_owner_is_owner (svc : Service) (name key : String)
    (h : svc.configuredOwner name key = true) : svc.affOfKey name key = .owner := by
  simp [Service.affOfKey, h]

/-- A kept affiliation is the account's affiliation. -/
theorem setEntry_aff (svc : Service) (name key : String) (aff : Affiliation) (m : Bool)
    (h : aff ≠ .unaffiliated) (hc : svc.configuredOwner name key = false) :
    (svc.setEntry name key aff m).affOfKey name key = aff := by
  have hc' : (svc.setEntry name key aff m).configuredOwner name key = false := hc
  simp [Service.affOfKey, hc', setEntry_entry _ _ _ _ _ h, h]

/-- 9. An outcast cannot join: nothing changes, and only the outcast hears of it. -/
theorem mayJoin_outcast (svc : Service) (name from_ : String) (h : svc.affOf name from_ = .outcast) :
    svc.mayJoin name from_ = false := by
  simp [Service.mayJoin, h]

theorem outcast_cannot_join (svc : Service) (name nick from_ : String)
    (h : svc.affOf name from_ = .outcast) :
    (join svc name nick from_).1 = svc ∧ ∀ d ∈ (join svc name nick from_).2, d.to = from_ :=
  join_refused svc name nick from_ (mayJoin_outcast svc name from_ h)

/-- 10. A visitor's groupchat message reaches nobody but the sender (an error). -/
theorem groupchat_visitor (svc : Service) (name from_ : String) (id : Option String)
    (p : List Node) (room : Room) (me : Occupant)
    (hr : svc.room? name = some room) (hm : room.byReal from_ = some me) (hv : me.role = .visitor) :
    ∀ d ∈ groupchat svc name from_ id p, d.to = from_ := by
  intro d hd
  simp [groupchat, hr, hm, hv] at hd
  simp [hd]

/-- 11. A moderator below admin cannot kick an admin or an owner, and cannot revoke their voice. -/
theorem roleRefusal_below_admin (ar tr : Role) (a t : Affiliation) (self : Bool)
    (ha : a.rank < 2) (ht : t.rank ≥ 2) :
    roleRefusal ar a t tr self none ≠ none ∧ roleRefusal ar a t tr self (some .visitor) ≠ none := by
  cases a <;> cases t <;> cases ar <;> cases tr <;> cases self <;>
    simp_all [roleRefusal, Affiliation.rank, mayDiscipline]

/-- 11b. Nobody kicks an owner, an owner included. -/
theorem roleRefusal_owner (ar tr : Role) (a : Affiliation) (self : Bool) :
    roleRefusal ar a .owner tr self none ≠ none := by
  cases a <;> cases ar <;> cases tr <;> cases self <;>
    simp_all [roleRefusal, Affiliation.rank, mayDiscipline]

/-- 11c. Only an owner kicks an admin. -/
theorem roleRefusal_admin (ar tr : Role) (a : Affiliation) (self : Bool) (ha : a ≠ .owner) :
    roleRefusal ar a .admin tr self none ≠ none := by
  cases a <;> cases ar <;> cases tr <;> cases self <;>
    simp_all [roleRefusal, Affiliation.rank, mayDiscipline]

/-- 11d. The same at the level of the room: such a kick is refused, and so nothing changes. -/
theorem setRole_kick_refused (svc : Service) (name from_ nick : String) (reason : Option String) (t : Occupant)
    (ht : ((svc.room? name).getD ⟨name, []⟩).byNick nick = some t)
    (ha : (svc.affOf name from_).rank < 2) (hr : (svc.affOf name t.real).rank ≥ 2) :
    ∃ e, setRole svc name from_ nick none reason = .error e := by
  unfold setRole
  simp only [ht]
  generalize svc.actorRole _ name from_ = ar
  split
  · exact ⟨_, rfl⟩
  · cases hrf : roleRefusal ar (svc.affOf name from_) (svc.affOfKey name (keyOf t.real)) t.role
      (keyOf t.real == keyOf from_) none with
    | none => exact absurd hrf (roleRefusal_below_admin ar t.role _ _ _ ha hr).1
    | some r => exact ⟨r, by simp [hrf]⟩

/-- 12. An admin does not grant admin or owner, and does not touch an admin or an owner. -/
theorem admin_cannot_raise (svc : Service) (name a key : String) (new : Affiliation)
    (hn : new.rank ≥ 2) (ha : svc.affOfKey name a ≠ .owner) : svc.affRefusal name a key new ≠ none := by
  simp only [Service.affRefusal]
  split
  · simp
  · have : (decide (new.rank ≥ 2) && (svc.affOfKey name a != .owner)) = true := by simp [hn, ha]
    simp [hn, ha]

theorem admin_cannot_touch (svc : Service) (name a key : String) (new : Affiliation)
    (hc : (svc.affOfKey name key).rank ≥ 2) (ha : svc.affOfKey name a ≠ .owner) :
    svc.affRefusal name a key new ≠ none := by
  simp only [Service.affRefusal]
  split
  · simp
  · split
    · simp
    · simp [hc, ha]

/-- 13. No request changes a configured owner. -/
theorem configured_owner_fixed (svc : Service) (name a key : String) (new : Affiliation)
    (hc : svc.configuredOwner name key = true) (hn : new ≠ .owner) :
    svc.affRefusal name a key new ≠ none := by
  simp only [Service.affRefusal]
  repeat' (first | split | simp [hc, hn])
  all_goals simp_all

/-- 14. Nobody bans themselves. -/
theorem no_self_ban (svc : Service) (name key : String) :
    svc.affRefusal name key key .outcast ≠ none := by
  simp only [Service.affRefusal]
  repeat' split
  all_goals simp_all

private theorem refusal_none_last (svc : Service) (name a key : String) (new : Affiliation)
    (h : svc.affRefusal name a key new = none) :
    ¬ (new != .owner && (svc.ownersOf name).contains key && ((svc.ownersOf name).filter (· != key)).isEmpty) = true := by
  intro hl
  simp only [Service.affRefusal] at h
  repeat' (split at h)
  all_goals simp_all

private theorem refusal_none_configured (svc : Service) (name a key : String) (new : Affiliation)
    (h : svc.affRefusal name a key new = none) (hn : new ≠ .owner) :
    svc.configuredOwner name key = false := by
  cases hc : svc.configuredOwner name key with
  | false => rfl
  | true => exact absurd h (configured_owner_fixed svc name a key new hc hn)

/-- Writing one account keeps every other owner. -/
private theorem mem_owners_setEntry (svc : Service) (name key x : String) (aff : Affiliation) (m : Bool)
    (hx : x ∈ svc.ownersOf name) (hk : x ≠ key) : x ∈ (svc.setEntry name key aff m).ownersOf name := by
  simp only [Service.ownersOf, List.mem_append, setEntry_entriesOf] at hx ⊢
  rcases hx with (h | h) | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · refine Or.inr ?_
    simp only [List.mem_map, List.mem_filter] at h ⊢
    obtain ⟨e, ⟨he, ho⟩, rfl⟩ := h
    refine ⟨e, ⟨?_, ho⟩, rfl⟩
    simp only [Service.nextEntries]
    split
    · exact List.mem_filter.mpr ⟨he, by simpa using hk⟩
    · exact List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨he, by simpa using hk⟩))

private theorem assign_owners (svc : Service) (name a key : String) (new : Affiliation)
    (hr : svc.affRefusal name a key new = none) (ho : svc.ownersOf name ≠ []) :
    (svc.assign name key new).ownersOf name ≠ [] := by
  by_cases hother : ∃ x ∈ svc.ownersOf name, x ≠ key
  · obtain ⟨x, hx, hk⟩ := hother
    exact List.ne_nil_of_mem (mem_owners_setEntry svc name key x _ _ hx hk)
  · have hall : ∀ x ∈ svc.ownersOf name, x = key := by
      intro x hx
      exact Classical.byContradiction fun hk => hother ⟨x, hx, hk⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ ho
    have hkey : key ∈ svc.ownersOf name := hall x hx ▸ hx
    by_cases hn : new = .owner
    · subst hn
      refine List.ne_nil_of_mem (a := key) ?_
      simp only [Service.ownersOf, List.mem_append, Service.assign, setEntry_entriesOf, Service.nextEntries]
      refine Or.inr ?_
      simp [List.mem_map, List.mem_filter, Affiliation.rank]
    · exfalso
      apply refusal_none_last svc name a key new hr
      have he : ((svc.ownersOf name).filter (· != key)).isEmpty = true := by
        rw [List.isEmpty_iff, List.filter_eq_nil_iff]
        intro y hy
        simpa using hall y hy
      simp [hn, hkey, he]

/-- What `putLeft` leaves of the configuration, with an owner configuration. -/
private theorem putLeft_acls (svc : Service) (r : Room) (h : svc.firstOwner = false) :
    svc.putLeft r = svc.put r := by
  simp [Service.putLeft, h]

/-- 15. With an owner configuration, a room that has an owner keeps one: no affiliation change
removes the last. -/
theorem setAff_keeps_owner (svc s' : Service) (name from_ key : String) (new : Affiliation)
    (reason : Option String) (ds : List Delivery) (hf : svc.firstOwner = false)
    (ho : svc.ownersOf name ≠ []) (h : setAff svc name from_ key new reason = .ok (s', ds)) :
    s'.ownersOf name ≠ [] := by
  unfold setAff at h
  split at h
  · cases h
  · rename_i hr
    split at h
    · cases h; exact ho
    · split at h
      · cases h
      · have h1 := assign_owners svc name _ key new hr ho
        split at h
        · cases h; exact h1
        · simp only at h
          cases h
          have hf' : (svc.assign name key new).firstOwner = false := hf
          rw [putLeft_acls _ _ hf']
          exact h1

/-- 16. With an owner configuration, a join gives no affiliation: the first occupant is no owner. -/
theorem join_no_first_owner (svc : Service) (name nick from_ : String) (hf : svc.firstOwner = false) :
    (join svc name nick from_).1.acls = svc.acls := by
  unfold join
  dsimp only
  repeat' split
  all_goals simp_all [Service.put]

theorem join_affOfKey (svc : Service) (name nick from_ n k : String) (hf : svc.firstOwner = false) :
    (join svc name nick from_).1.affOfKey n k = svc.affOfKey n k := by
  have hacl := join_no_first_owner svc name nick from_ hf
  have hcfg : (join svc name nick from_).1.serviceOwners = svc.serviceOwners ∧
      (join svc name nick from_).1.roomOwners = svc.roomOwners ∧
      (join svc name nick from_).1.memberLists = svc.memberLists := by
    unfold join
    dsimp only
    repeat' split
    all_goals simp_all [Service.put]
  refine affOfKey_of_entries _ _ _ _ hcfg.1 hcfg.2.1 hcfg.2.2 ?_
  simp [Service.entriesOf, Service.acl?, hacl]

/-- Only admins and owners read a list with bare JIDs in it. -/
theorem list_jids_admin_only (a : Affiliation) (r : Role) (x : Affiliation)
    (h : listRefusal a r (.inl x) = none) : a.rank ≥ 2 := by
  cases a <;> cases x <;> simp_all [listRefusal, Affiliation.rank]

/-- Storing a room keeps a service sound when the rooms are as before, and every other room's
entrance is as before. -/
theorem put_sound_at (svc s : Service) (r : Room) (hs : svc.sound) (hrooms : s.rooms = svc.rooms)
    (hother : ∀ n f, n ≠ r.name → s.mayJoin n f = svc.mayJoin n f)
    (hr : ∀ o ∈ r.occupants, s.mayJoin r.name o.real = true) : (s.put r).sound := by
  intro x hx o ho
  rw [put_mayJoin]
  simp only [Service.put, hrooms] at hx
  have hold : x ∈ svc.rooms ∧ x.name ≠ r.name → s.mayJoin x.name o.real = true := by
    intro ⟨hm, hn⟩
    rw [hother _ _ hn]
    exact hs x hm o ho
  split at hx
  · have := List.mem_filter.mp hx
    exact hold ⟨this.1, by simpa using this.2⟩
  · rcases List.mem_append.mp hx with hx | hx
    · have := List.mem_filter.mp hx
      exact hold ⟨this.1, by simpa using this.2⟩
    · simp only [List.mem_singleton] at hx
      subst hx
      exact hr o ho

/-- 8. Members only, as an invariant: joining never puts anyone in a room who
may not be there. Leaving only removes occupants. -/
theorem join_sound (svc : Service) (name nick from_ : String) (hs : svc.sound)
    (hroom : ∀ r, svc.room? name = some r → r.name = name) :
    (join svc name nick from_).1.sound := by
  have hget : ∀ o ∈ ((svc.room? name).getD ⟨name, []⟩).occupants, svc.mayJoin name o.real = true := by
    intro o ho
    cases hr : svc.room? name with
    | none => simp [hr] at ho
    | some r =>
      simp only [hr, Option.getD_some] at ho
      have hmem : r ∈ svc.rooms := List.mem_of_find?_eq_some hr
      have := hs r hmem o ho
      rwa [hroom r hr] at this
  have hname : ((svc.room? name).getD ⟨name, []⟩).name = name := by
    cases hr : svc.room? name with
    | none => rfl
    | some r => simpa [hr] using hroom r hr
  unfold join
  dsimp only
  split
  · exact hs
  rename_i hmay
  split
  · exact hs
  split
  · exact hs
  split
  · exact hs
  split
  · exact hs
  rename_i room' hj
  have hj' := hj
  unfold joinRoom at hj'
  split at hj'
  · cases hj'
  cases hj'
  dsimp only
  by_cases hfirst : (((svc.room? name).getD ⟨name, []⟩).occupants.isEmpty && svc.firstOwner &&
      (svc.ownersOf name).isEmpty) = true
  · rw [if_pos hfirst]
    refine put_sound_at svc _ _ hs rfl ?_ ?_
    · intro n f hn
      rw [hname] at hn
      exact mayJoin_other _ _ _ _ _ _ _ hn
    · have hempty : ((svc.room? name).getD ⟨name, []⟩).occupants = [] := by
        simpa using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hfirst).1).1
      intro o ho
      simp only [hempty, List.nil_append, List.mem_singleton] at ho
      subst ho
      rw [hname]
      have hown : (svc.setEntry name (keyOf from_) .owner false).affOfKey name (keyOf from_) = .owner := by
        cases hc : svc.configuredOwner name (keyOf from_) with
        | true => exact configured_owner_is_owner _ _ _ hc
        | false => exact setEntry_aff _ _ _ _ _ (by simp) hc
      simp [Service.mayJoin, Service.affOf, hown]
  · rw [if_neg hfirst]
    refine put_sound_at svc _ _ hs rfl (fun _ _ _ => rfl) ?_
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · rw [hname]; exact hget o ho
    · simp only [List.mem_singleton] at ho
      subst ho
      rw [hname]
      simpa using hmay

private theorem room?_name (svc : Service) (name : String) (r : Room) (h : svc.room? name = some r) :
    r.name = name := by
  simpa using List.find?_some h

private theorem mayJoin_dropAcl (s : Service) (name n f : String) (hn : n ≠ name) :
    ({ s with acls := s.acls.filter (·.room != name) } : Service).mayJoin n f = s.mayJoin n f := by
  have : ({ s with acls := s.acls.filter (·.room != name) } : Service).affOfKey n (keyOf f) = s.affOfKey n (keyOf f) :=
    affOfKey_of_entries _ _ _ _ rfl rfl rfl (by simp [Service.entriesOf, Service.acl?, find_filter_room _ _ _ hn])
  simp only [Service.mayJoin, Service.affOf, this]

private theorem putLeft_sound (svc s : Service) (r : Room) (hs : svc.sound) (hrooms : s.rooms = svc.rooms)
    (hother : ∀ n f, n ≠ r.name → s.mayJoin n f = svc.mayJoin n f)
    (hr : ∀ o ∈ r.occupants, s.mayJoin r.name o.real = true) : (s.putLeft r).sound := by
  have hput := put_sound_at svc s r hs hrooms hother hr
  unfold Service.putLeft
  dsimp only
  split
  · rename_i he
    have hempty : r.occupants = [] := by
      simpa using (Bool.and_eq_true_iff.mp he).1
    intro x hx o ho
    have hx' : x ∈ (s.put r).rooms := hx
    have hn : x.name ≠ r.name := by
      simp only [Service.put, hempty, List.isEmpty_nil, ↓reduceIte, List.mem_filter] at hx'
      simpa using hx'.2
    exact (mayJoin_dropAcl (s.put r) r.name _ _ hn).trans (hput x hx' o ho)
  · exact hput

/-- 17. An affiliation change keeps the service sound: nobody who may not be in a room stays. -/
theorem setAff_sound (svc s' : Service) (name from_ key : String) (new : Affiliation)
    (reason : Option String) (ds : List Delivery) (hs : svc.sound)
    (h : setAff svc name from_ key new reason = .ok (s', ds)) : s'.sound := by
  unfold setAff at h
  split at h
  · cases h
  · split at h
    · cases h; exact hs
    · split at h
      · cases h
      · have hother : ∀ n f, n ≠ name → (svc.assign name key new).mayJoin n f = svc.mayJoin n f :=
          fun n f hn => mayJoin_other _ _ _ _ _ _ _ hn
        split at h
        · rename_i hnone
          cases h
          intro x hx o ho
          have hn : x.name ≠ name := by
            intro he
            have := List.find?_eq_none.mp hnone x hx
            simp [he] at this
          rw [hother _ _ hn]
          exact hs x hx o ho
        · rename_i room hroom
          simp only [List.partition_eq_filter_filter] at h
          cases h
          have hrn := room?_name svc name room hroom
          refine putLeft_sound svc _ _ hs rfl ?_ ?_
          · intro n f hn
            exact hother n f (by simpa [hrn] using hn)
          · intro o ho
            simp only [List.mem_map, List.mem_filter] at ho
            obtain ⟨o', ⟨_, hm⟩, rfl⟩ := ho
            simp only [hrn]
            split <;> simpa using hm

/-- 18. After a ban, with an owner configuration, the banned account is in no seat of that room,
and it cannot join (theorem 9). -/
theorem ban_gone (svc s' : Service) (name from_ key : String) (reason : Option String)
    (ds : List Delivery) (hs : svc.sound) (hf : svc.firstOwner = false)
    (h : setAff svc name from_ key .outcast reason = .ok (s', ds)) :
    s'.affOfKey name key = .outcast ∧ ∀ r ∈ s'.rooms, r.name = name → ∀ o ∈ r.occupants, keyOf o.real ≠ key := by
  have hsound := setAff_sound _ _ _ _ _ _ _ _ hs h
  have haff : s'.affOfKey name key = .outcast := by
    unfold setAff at h
    split at h
    · cases h
    · rename_i hr
      split at h
      · rename_i heq
        cases h
        exact (eq_of_beq heq).symm
      · split at h
        · cases h
        · have hc := refusal_none_configured svc name _ key .outcast hr (by simp)
          have h1 : (svc.assign name key .outcast).affOfKey name key = .outcast :=
            setEntry_aff _ _ _ _ _ (by simp) hc
          split at h
          · cases h; exact h1
          · simp only at h
            cases h
            have hf' : (svc.assign name key .outcast).firstOwner = false := hf
            rw [putLeft_acls _ _ hf']
            exact h1
  refine ⟨haff, ?_⟩
  intro r hr hn o ho hk
  have := hsound r hr o ho
  rw [hn] at this
  simp [Service.mayJoin, Service.affOf, hk, haff] at this

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

-- Members only: Mallory is refused, sees nothing, and cannot make the room;
-- Juliet gets in on any resource.
#guard
  let locked : Service := { svc0 with memberLists := [⟨"bus", ["juliet@example.com"]⟩] }
  let (s1, ds1) := step locked "mallory@example.com/x" (st .presence "bus@conference.example.com/m" none)
  let (s2, _) := step s1 "juliet@example.com/any" (st .presence "bus@conference.example.com/j" none)
  let (s3, ds3) := step s2 "mallory@example.com/x" (st .presence "bus@conference.example.com/m" none)
  let (_, ds4) := step s3 "mallory@example.com/x" (st .message "bus@conference.example.com" (some "groupchat") [body "hi"])
  let (_, items) := step s3 "mallory@example.com/x" (st .iq "conference.example.com" (some "get") [.element "query" [⟨"xmlns", nsDiscoItems⟩] []])
  let (_, info) := step s3 "mallory@example.com/x" (st .iq "bus@conference.example.com" (some "get") [.element "query" [⟨"xmlns", nsDiscoInfo⟩] []])
  let (_, jinfo) := step s3 "juliet@example.com/any" (st .iq "bus@conference.example.com" (some "get") [.element "query" [⟨"xmlns", nsDiscoInfo⟩] []])
  s1.rooms.isEmpty && has (ds1[0]!.render) "registration-required" && has (ds1[0]!.render) "type=\"auth\"" &&
  (s3.room? "bus").map (·.occupants.length) == some 1 && has (ds3[0]!.render) "registration-required" &&
  ds4.map (·.to) == ["mallory@example.com/x"] && has (ds4[0]!.render) "not-acceptable" &&
  !has (items[0]!.render) "bus@" && has (info[0]!.render) "item-not-found" &&
  has (jinfo[0]!.render) "muc_membersonly" && !has (jinfo[0]!.render) "muc_open"

-- A room with no list stays open beside a locked one.
#guard
  let locked : Service := { svc0 with memberLists := [⟨"bus", ["juliet@example.com"]⟩] }
  let (s1, _) := step locked "mallory@example.com/x" (st .presence "tea@conference.example.com/m" none)
  s1.rooms.length == 1

-- A nick that differs only in case is taken.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let (s2, ds) := step s1 "romeo@example.com/orchard" (st .presence "tea@conference.example.com/JUL" none)
  (s2.room? "tea").map (·.occupants.length) == some 1 && has (ds[0]!.render) "conflict"

-- So is one that differs only in width.
#guard nickKey "\uFF41lice" == nickKey "Alice"
#guard
  let locked : Service := { svc0 with reserved := [(nickKey "alice", "alice@example.com")] }
  let (s1, ds) := step locked "mallory@example.com/x" (st .presence "tea@conference.example.com/\uFF41lice" none)
  s1.rooms.isEmpty && has (ds[0]!.render) "conflict"

-- Nicks that cannot be told from another are refused, and the room is unchanged.
#guard
  ["jul ", " jul", "ju  l", "ju\u200Bl", "ju\u00ADl", "jul\u00A0", "ju\u202El", String.ofList (List.replicate 65 'x')].all
    (fun n => !nickOk n)
#guard ["jul", "third witch", "Grüße", "朱丽叶"].all nickOk
#guard
  let (s1, ds) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul " none)
  s1.rooms.isEmpty && has (ds[0]!.render) "not-acceptable"

-- A nick reserved for an account: another account gets `conflict`, in any case;
-- the account itself gets in, on any resource.
#guard
  let locked : Service := { svc0 with reserved := [("foafos", "foafos@example.com")] }
  let (s1, ds1) := step locked "mallory@example.com/x" (st .presence "tea@conference.example.com/foafos" none)
  let (s2, ds2) := step locked "mallory@example.com/x" (st .presence "tea@conference.example.com/Foafos" none)
  let (s3, _) := step locked "foafos@example.com/any" (st .presence "tea@conference.example.com/foafos" none)
  s1.rooms.isEmpty && s2.rooms.isEmpty && has (ds1[0]!.render) "conflict" && has (ds2[0]!.render) "conflict" &&
  (s3.room? "tea").map (·.occupants.length) == some 1

-- A client's subject does not reach the room.
#guard
  let (s1, _) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let subj : Node := .element "subject" [] [.text "new"]
  let (_, ds) := step s1 "juliet@example.com/balcony" (st .message "tea@conference.example.com" (some "groupchat") [body "hi", subj])
  ds.all (fun d => has d.render "<body>hi</body>" && !has d.render "subject")

-- XEP-0421: one id for an account in a room, on any resource and at any join; another account
-- and another room differ; no JID in it; a client's own id does not pass.
#guard
  let svc : Service := { svc0 with idSeed := "seed" }
  let a := svc.occupantId "tea" "juliet@example.com/one"
  a == svc.occupantId "tea" "juliet@example.com/two" && a != svc.occupantId "tea" "romeo@example.com/one" &&
  a != svc.occupantId "cake" "juliet@example.com/one" && !has a "juliet" && !a.isEmpty
#guard
  let svc : Service := { svc0 with idSeed := "seed" }
  let a := svc.occupantId "tea" "juliet@example.com/balcony"
  let (s1, ds) := step svc "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  let forged : Node := .element "occupant-id" [⟨"xmlns", Gc3.nsOccupantId⟩, ⟨"id", "forged"⟩] []
  let (_, ms) := step s1 "juliet@example.com/balcony" (st .message "tea@conference.example.com" (some "groupchat") [body "hi", forged])
  let (_, info) := step s1 "romeo@example.com/x" (st .iq "tea@conference.example.com" (some "get") [.element "query" [⟨"xmlns", nsDiscoInfo⟩] []])
  has (ds[0]!.render) s!"id=\"{a}\"" && has (ms[0]!.render) s!"id=\"{a}\"" && !has (ms[0]!.render) "forged" &&
  has (info[0]!.render) Gc3.nsOccupantId
-- With no key there is no id.
#guard
  let (_, ds) := step svc0 "juliet@example.com/balcony" (st .presence "tea@conference.example.com/jul" none)
  !has (ds[0]!.render) "occupant-id"

-- The room limit holds.
#guard
  let small : Service := { svc0 with maxRooms := 1 }
  let (s1, _) := step small "juliet@example.com/balcony" (st .presence "a@conference.example.com/j" none)
  let (s2, ds) := step s1 "juliet@example.com/balcony" (st .presence "b@conference.example.com/j" none)
  s2.rooms.length == 1 && has (ds[0]!.render) "service-unavailable"

-- With no owner configuration: the first occupant is owner and moderator, as before.
private def seat (s : Service) (who nick : String) : Service :=
  (step s who (st .presence s!"tea@conference.example.com/{nick}" none)).1
private def admin (ns : String) (ty : String) (kids : List Node) : Stanza :=
  st .iq "tea@conference.example.com" (some ty) [.element "query" [⟨"xmlns", ns⟩] kids]
private def item (attrs : List (String × String)) (kids : List Node := []) : Node :=
  .element "item" (attrs.map (fun (a, b) => ⟨a, b⟩)) kids
private def J := "juliet@example.com/balcony"
private def Ro := "romeo@example.com/orchard"
private def M := "mallory@example.com/x"
private def Bo := "boss@example.com/desk"
/-- A server with an owner configuration: boss@ owns every room. -/
private def svcO : Service := { svc0 with firstOwner := false, serviceOwners := ["boss@example.com"] }
private def roleOf (s : Service) (nick : String) : Option Role :=
  ((s.room? "tea").bind (·.byNick nick)).map (·.role)

#guard
  let s := seat (seat svc0 J "jul") Ro "rom"
  roleOf s "jul" == some .moderator && s.affOf "tea" J == .owner && roleOf s "rom" == some .participant

-- With an owner configuration the first occupant is nobody; the configured owner is an owner.
#guard
  let (s, ds) := step svcO M (st .presence "tea@conference.example.com/m" none)
  s.affOf "tea" M == .unaffiliated && roleOf s "m" == some .participant && s.acls.isEmpty &&
  has (ds[0]!.render) "affiliation=\"none\"" &&
  (let s2 := seat s Bo "boss"; s2.affOf "tea" Bo == .owner && roleOf s2 "boss" == some .moderator)

-- An empty owner configuration still ends first-occupant ownership.
#guard
  let s := seat { svc0 with firstOwner := false } J "jul"
  s.affOf "tea" J == .unaffiliated && roleOf s "jul" == some .participant

-- A per-room owner owns that room only.
#guard
  let c : Service := { svc0 with firstOwner := false, roomOwners := [⟨"tea", ["juliet@example.com"]⟩] }
  c.affOf "tea" J == .owner && c.affOf "cake" J == .unaffiliated

-- Kick: 307 and 110 with actor and reason to the person, 307 to the others, the result last.
#guard
  let s := seat (seat svcO Bo "boss") Ro "rom"
  let (s1, ds) := step s Bo (admin nsMucAdmin "set" [item [("nick", "rom"), ("role", "none")] [.element "reason" [] [.text "a<b"]]])
  roleOf s1 "rom" == none && ds.map (·.to) == [Ro, Bo, Bo] &&
  has (ds[0]!.render) "code=\"307\"" && has (ds[0]!.render) "code=\"110\"" && has (ds[0]!.render) "<actor nick=\"boss\"" &&
  has (ds[0]!.render) "a&lt;b" && has (ds[1]!.render) "code=\"307\"" && !has (ds[1]!.render) "code=\"110\"" &&
  !has (ds[1]!.render) "actor" && has (ds[2]!.render) "type=\"result\"" &&
  -- Kicked is not banned.
  roleOf (seat s1 Ro "rom") "rom" == some .participant

-- A participant cannot kick; a moderator cannot kick an owner, or an admin.
#guard
  let s0 := seat (seat (seat svcO Bo "boss") Ro "rom") M "m"
  let (s1, d1) := step s0 M (admin nsMucAdmin "set" [item [("nick", "rom"), ("role", "none")]])
  let (s2, _) := step s0 Bo (admin nsMucAdmin "set" [item [("nick", "rom"), ("role", "moderator")]])
  let (s3, d3) := step s2 Ro (admin nsMucAdmin "set" [item [("nick", "boss"), ("role", "none")]])
  let (s4, d4) := step s2 Ro (admin nsMucAdmin "set" [item [("nick", "boss"), ("role", "visitor")]])
  let (_, d5) := step s2 Ro (admin nsMucAdmin "set" [item [("nick", "rom"), ("role", "none")]])
  let (s6, d6) := step s2 Ro (admin nsMucAdmin "set" [item [("nick", "m"), ("role", "none")]])
  roleOf s1 "rom" == some .participant && has (d1[0]!.render) "forbidden" && d1.map (·.to) == [M] &&
  roleOf s3 "boss" == some .moderator && has (d3[0]!.render) "not-allowed" &&
  roleOf s4 "boss" == some .moderator && has (d4[0]!.render) "not-allowed" &&
  has (d5[0]!.render) "conflict" && roleOf s6 "m" == none && d6.length == 4

-- Voice: a visitor cannot send; the mute stays across a new join; a moderator gives it back.
#guard
  let s0 := seat (seat svcO Bo "boss") Ro "rom"
  let (s1, d1) := step s0 Bo (admin nsMucAdmin "set" [item [("nick", "rom"), ("role", "visitor")]])
  let (_, g) := step s1 Ro (st .message "tea@conference.example.com" (some "groupchat") [body "hi"])
  let (s2, _) := step s1 Ro (st .presence "tea@conference.example.com/rom" (some "unavailable"))
  let s3 := seat s2 Ro "rom"
  let (s4, _) := step s3 Bo (admin nsMucAdmin "set" [item [("nick", "rom"), ("role", "participant")]])
  let (_, g2) := step s4 Ro (st .message "tea@conference.example.com" (some "groupchat") [body "hi"])
  roleOf s1 "rom" == some .visitor && has (d1[0]!.render) "role=\"visitor\"" &&
  g.map (·.to) == [Ro] && has (g[0]!.render) "forbidden" &&
  roleOf s3 "rom" == some .visitor && roleOf s4 "rom" == some .participant && g2.length == 2 && s4.acls.isEmpty

-- Ban: every session of the account goes, 301; it cannot return; the list names it; unban works.
#guard
  let s0 := seat (seat (seat svcO Bo "boss") Ro "rom") "romeo@example.com/phone" "rom2"
  let (s1, ds) := step s0 Bo (admin nsMucAdmin "set" [item [("jid", "Romeo@example.com/any"), ("affiliation", "outcast")]])
  let (s2, dj) := step s1 Ro (st .presence "tea@conference.example.com/rom" none)
  let (_, dl) := step s1 Bo (admin nsMucAdmin "get" [item [("affiliation", "outcast")]])
  let (s3, _) := step s1 Bo (admin nsMucAdmin "set" [item [("jid", "romeo@example.com"), ("affiliation", "none")]])
  roleOf s1 "rom" == none && roleOf s1 "rom2" == none && (s1.affOf "tea" Ro == .outcast) &&
  has (ds[0]!.render) "code=\"301\"" && has (ds[0]!.render) "affiliation=\"outcast\"" &&
  roleOf s2 "rom" == none && has (dj[0]!.render) "forbidden" && dj.map (·.to) == [Ro] &&
  has (dl[0]!.render) "jid=\"romeo@example.com\"" &&
  s3.acls.isEmpty && roleOf (seat s3 Ro "rom") "rom" == some .participant

-- A ban by nick; a ban outlives an empty room.
#guard
  let s0 := seat (seat svcO Bo "boss") Ro "rom"
  let (s1, _) := step s0 Bo (admin nsMucAdmin "set" [item [("nick", "rom"), ("affiliation", "outcast")]])
  let (s2, _) := leaveAll s1 Bo
  s2.rooms.isEmpty && s2.affOf "tea" Ro == .outcast && (seat s2 Ro "rom").rooms.isEmpty

-- With no owner configuration a room's bans go with the room, and its owner too.
#guard
  let s0 := seat (seat svc0 J "jul") Ro "rom"
  let (s1, _) := step s0 J (admin nsMucAdmin "set" [item [("nick", "rom"), ("affiliation", "outcast")]])
  let (s2, _) := leaveAll s1 J
  s1.affOf "tea" Ro == .outcast && s2.acls.isEmpty && s2.affOf "tea" J == .unaffiliated &&
  (seat s2 Ro "rom").affOf "tea" Ro == .owner

-- The privilege table of affiliations.
#guard
  let s0 := seat svcO Ro "rom"
  let bo (s : Service) (j a : String) := step s Bo (admin nsMucAdmin "set" [item [("jid", j), ("affiliation", a)]])
  let (s1, _) := bo s0 "juliet@example.com" "admin"
  let jd (s : Service) (j a : String) := step s J (admin nsMucAdmin "set" [item [("jid", j), ("affiliation", a)]])
  -- An admin: member and ban, yes; admin or owner, no; an admin or an owner as target, no.
  let (s2, _) := jd s1 "romeo@example.com" "member"
  let (_, e1) := jd s1 "mallory@example.com" "admin"
  let (_, e2) := jd s1 "mallory@example.com" "owner"
  let (_, e3) := jd s1 "boss@example.com" "outcast"
  let (_, e4) := jd s1 "juliet@example.com" "outcast"
  -- A person with no affiliation: nothing.
  let (_, e5) := step s1 Ro (admin nsMucAdmin "set" [item [("jid", "mallory@example.com"), ("affiliation", "outcast")]])
  -- The configured owner cannot be changed by another owner or by himself.
  let (s3, _) := bo s1 "juliet@example.com" "owner"
  let (_, e6) := jd s3 "boss@example.com" "none"
  let (_, e7) := bo s3 "boss@example.com" "outcast"
  s1.affOf "tea" J == .admin && s2.affOf "tea" Ro == .member &&
  has (e1[0]!.render) "forbidden" && has (e2[0]!.render) "forbidden" && has (e3[0]!.render) "not-allowed" &&
  has (e4[0]!.render) "not-allowed" && has (e5[0]!.render) "forbidden" && has (e6[0]!.render) "not-allowed" &&
  has (e7[0]!.render) "conflict"

-- The last owner: refused with `conflict`. With two, one can go.
#guard
  let c : Service := { svc0 with firstOwner := false, acls := [⟨"tea", [⟨"juliet@example.com", .owner, false⟩]⟩] }
  let (s1, e) := step c J (admin nsMucAdmin "set" [item [("jid", "juliet@example.com"), ("affiliation", "none")]])
  let (s2, _) := step c J (admin nsMucAdmin "set" [item [("jid", "romeo@example.com"), ("affiliation", "owner")]])
  let (s3, _) := step s2 Ro (admin nsMucAdmin "set" [item [("jid", "juliet@example.com"), ("affiliation", "none")]])
  has (e[0]!.render) "conflict" && s1.affOf "tea" J == .owner && s2.affOf "tea" Ro == .owner &&
  s3.affOf "tea" J == .unaffiliated && s3.affOf "tea" Ro == .owner

-- A promotion reaches the presence of the occupant: admin brings the moderator role.
#guard
  let s0 := seat (seat svcO Bo "boss") Ro "rom"
  let (s1, ds) := step s0 Bo (admin nsMucAdmin "set" [item [("jid", "romeo@example.com"), ("affiliation", "admin")]])
  roleOf s1 "rom" == some .moderator && ds.length == 3 && has (ds[0]!.render) "affiliation=\"admin\"" &&
  has (ds[0]!.render) "role=\"moderator\""

-- Members only: an added member gets in, 321 removes a revoked one, a listed one stays listed.
#guard
  let c : Service := { svcO with memberLists := [⟨"tea", ["juliet@example.com"]⟩] }
  let s0 := seat c Bo "boss"
  let (s1, _) := step s0 Bo (admin nsMucAdmin "set" [item [("jid", "romeo@example.com"), ("affiliation", "member")]])
  let s2 := seat s1 Ro "rom"
  let (s3, ds) := step s2 Bo (admin nsMucAdmin "set" [item [("jid", "romeo@example.com"), ("affiliation", "none")]])
  let (_, e) := step s3 Bo (admin nsMucAdmin "set" [item [("jid", "juliet@example.com"), ("affiliation", "none")]])
  let (s4, _) := step s3 Bo (admin nsMucAdmin "set" [item [("jid", "juliet@example.com"), ("affiliation", "outcast")]])
  let (_, l) := step s3 Bo (admin nsMucAdmin "get" [item [("affiliation", "member")]])
  roleOf s2 "rom" == some .participant && roleOf s3 "rom" == none && has (ds[0]!.render) "code=\"321\"" &&
  has (e[0]!.render) "not-allowed" && !s4.mayJoin "tea" J && has (l[0]!.render) "juliet@example.com"

-- A request is done in full or not at all.
#guard
  let s0 := seat (seat svcO Bo "boss") Ro "rom"
  let (s1, ds) := step s0 Bo (admin nsMucAdmin "set"
    [item [("jid", "mallory@example.com"), ("affiliation", "outcast")], item [("nick", "nobody"), ("role", "none")]])
  s1.acls.isEmpty && ds.map (·.to) == [Bo] && has (ds[0]!.render) "item-not-found"

-- The lists: who may read, and what they show. A moderator's lists have nicks, not JIDs.
#guard
  let s0 := seat (seat svcO Bo "boss") Ro "rom"
  let (_, o1) := step s0 Bo (admin nsMucAdmin "get" [item [("affiliation", "owner")]])
  let (_, o2) := step s0 Bo (admin nsMucOwner "get" [item [("affiliation", "owner")]])
  let (_, o3) := step s0 Ro (admin nsMucAdmin "get" [item [("affiliation", "owner")]])
  let (_, o4) := step s0 Ro (admin nsMucAdmin "get" [item [("affiliation", "outcast")]])
  let (_, v) := step s0 Bo (admin nsMucAdmin "get" [item [("role", "participant")]])
  let (s1, _) := step s0 Bo (admin nsMucAdmin "set" [item [("jid", "romeo@example.com"), ("affiliation", "admin")]])
  let (_, o5) := step s1 Ro (admin nsMucAdmin "get" [item [("affiliation", "owner")]])
  let (_, o6) := step s1 Ro (admin nsMucAdmin "get" [item [("affiliation", "outcast")]])
  has (o1[0]!.render) "jid=\"boss@example.com\"" && has (o2[0]!.render) nsMucOwner &&
  has (o3[0]!.render) "forbidden" && has (o4[0]!.render) "forbidden" &&
  has (v[0]!.render) "nick=\"rom\"" && !has (v[0]!.render) "romeo@" &&
  has (o5[0]!.render) "forbidden" && has (o6[0]!.render) "type=\"result\""

-- The form of an instant room: an owner only; a form with fields is not done.
#guard
  let s0 := seat (seat svcO Bo "boss") Ro "rom"
  let form (ks : List Node) : Node := .element "x" [⟨"xmlns", nsData⟩, ⟨"type", "submit"⟩] ks
  let (_, a) := step s0 Bo (admin nsMucOwner "set" [form []])
  let (_, b) := step s0 Ro (admin nsMucOwner "set" [form []])
  let (_, c) := step s0 Bo (admin nsMucOwner "set" [form [.element "field" [] []]])
  has (a[0]!.render) "type=\"result\"" && has (b[0]!.render) "forbidden" && has (c[0]!.render) "feature-not-implemented"

-- Bounds on the kept state.
#guard
  let c : Service := { svcO with maxAclEntries := 1 }
  let (s1, _) := step c Bo (admin nsMucAdmin "set" [item [("jid", "a@example.com"), ("affiliation", "outcast")]])
  let (s2, e) := step s1 Bo (admin nsMucAdmin "set" [item [("jid", "b@example.com"), ("affiliation", "outcast")]])
  (s2.entriesOf "tea").length == 1 && has (e[0]!.render) "resource-constraint"

-- Bad items.
#guard
  let s0 := seat svcO Bo "boss"
  let t (kids : List Node) := ((step s0 Bo (admin nsMucAdmin "set" kids)).2)[0]!.render
  has (t [item [("nick", "boss"), ("role", "king")]]) "bad-request" &&
  has (t [item [("jid", "example.com"), ("affiliation", "outcast")]]) "jid-malformed" &&
  has (t [item [("jid", "a@example.com"), ("affiliation", "king")]]) "bad-request" &&
  has (t [item [("jid", "a@example.com"), ("affiliation", "member"), ("role", "none")]]) "bad-request" &&
  has (t [item []]) "bad-request" && has (t []) "feature-not-implemented"

end L4Factoidal.XMPP.Muc
