/-
L4Factoidal.XMPP.Mix — XEP-0369 Mediated Information eXchange, MIX-CORE
(https://xmpp.org/extensions/xep-0369.html), with joins through the user's own server as
XEP-0405 MIX-PAM (https://xmpp.org/extensions/xep-0405.html), as a total function:

  step : Service → (from : full JID) → Stanza → Service × List Delivery

A MIX participant is an ACCOUNT (a bare JID), not a session: membership survives
disconnects, and a channel message goes to each participant's bare JID, where the server
may hold it for an offline account like any message (`Delivery.held`). An IQ answer goes
to the one session that asked (`held = false`, performed as `Out.routeFull`).

Covered:
  XEP-0369 7.3.2   create a channel (IQ set `<create/>` to the service); the creator owns it
  XEP-0405 5.1     join through the user's server: `<client-join/>` in an IQ to the user's own
                   bare JID; the answer carries the participant id. `<client-leave/>` leaves.
                   Joining twice is one participant.
  XEP-0369 7.1.2   a groupchat message from a participant to every participant's bare JID,
                   from the channel, with `<mix><nick/></mix>`; from anyone else `not-acceptable`
  XEP-0369 6.1     disco#info and disco#items on the service, disco#info on a channel

The channel is JID-hidden: `<mix/>` never carries `<jid>`, and `Body` has no field for a
real JID. A direct `<join/>` to a channel is refused `not-allowed` (MIX-PAM servers proxy
joins). Not covered, and answered `feature-not-implemented`: PubSub nodes and their
subscriptions (a join's `<subscribe/>` elements are echoed back as given; no node is served),
channel presence, MAM, nick registration, private messages, destruction, administration.
Channels are in memory; nothing persists across a restart. `maxChannels` and
`maxParticipants` bound the state.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XMPP.Core
import L4Factoidal.XMPP.Wire

namespace L4Factoidal.XMPP.Mix

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP (Jid)
open L4Factoidal.XMPP.Core (Stanza StanzaKind findAttr)

def nsCore : String := "urn:xmpp:mix:core:1"
def nsPam : String := "urn:xmpp:mix:pam:2"
def nsDiscoInfo : String := "http://jabber.org/protocol/disco#info"
def nsDiscoItems : String := "http://jabber.org/protocol/disco#items"
def nsStanzas : String := "urn:ietf:params:xml:ns:xmpp-stanzas"

/-- The bare form of a JID text. -/
def bareOf (s : String) : String :=
  match Jid.parse s with
  | some j => Jid.render { j with resourcepart := none }
  | none => s

/-! ## State -/

structure Participant where
  /-- The participant's account. Used only as a delivery address. -/
  bare : String
  nick : String
  /-- The stable participant id the join answered with. -/
  id : String
  deriving Repr, DecidableEq, Inhabited

structure Channel where
  name : String
  owner : String
  participants : List Participant
  nextId : Nat := 1
  deriving Repr, DecidableEq, Inhabited

structure Service where
  domain : String
  channels : List Channel := []
  maxChannels : Nat := 64
  maxParticipants : Nat := 256
  deriving Repr, Inhabited

def Channel.byBare (c : Channel) (bare : String) : Option Participant := c.participants.find? (·.bare == bare)
def Service.channel? (svc : Service) (name : String) : Option Channel := svc.channels.find? (·.name == name)
def Service.channelJid (svc : Service) (name : String) : String := name ++ "@" ++ svc.domain
def Service.put (svc : Service) (c : Channel) : Service :=
  { svc with channels := svc.channels.filter (·.name != c.name) ++ [c] }

/-! ## Deliveries -/

inductive Body where
  /-- A channel message (XEP-0369 section 7.1.2), from the channel's bare JID. -/
  | message (nick : String) (id : Option String) (payload : List Node)
  | iqResult (id : Option String) (fromAddr : Option String) (children : List Node)
  | error (kind : StanzaKind) (id : Option String) (fromAddr : String) (errType cond : String)
  deriving Inhabited

structure Delivery where
  /-- A bare JID when `held`, else the asking session's full JID. -/
  to : String
  /-- A channel message to an account: the server may hold it for an offline account. -/
  held : Bool
  /-- The channel JID or the service domain. -/
  channel : String
  body : Body
  deriving Inhabited

/-- A client's payload minus any `<mix/>` element in the MIX-CORE namespace: only the
channel says who sent a message, so a sender cannot forge a nick. -/
def sanitize (payload : List Node) : List Node :=
  payload.filter (fun n => match n with
    | .element _ attrs _ => findAttr attrs "xmlns" != some nsCore
    | _ => true)

private def child (ns tag : String) (ns' : List Node) : Option Node :=
  ns'.find? (fun n => match n with
    | .element t attrs _ => t == tag && findAttr attrs "xmlns" == some ns
    | _ => false)

private def childrenOf : Node → List Node
  | .element _ _ cs => cs
  | _ => []

private def attrOf (n : Node) (name : String) : Option String :=
  match n with
  | .element _ attrs _ => findAttr attrs name
  | _ => none

private def textOf (n : Node) : String :=
  String.join ((childrenOf n).filterMap (fun c => match c with | .text t => some t | _ => none))

/-! ## Channels: the pure operations the theorems are about -/

/-- Join `bare` with `nick`. Already a participant: unchanged, the same id.
`none`: another participant holds the nick. -/
def joinChannel (c : Channel) (bare nick : String) : Option (Channel × Participant) :=
  match c.byBare bare with
  | some p => some (c, p)
  | none =>
    if c.participants.any (·.nick == nick) then none
    else
      let p : Participant := ⟨bare, nick, "p" ++ toString c.nextId⟩
      some ({ c with participants := c.participants ++ [p], nextId := c.nextId + 1 }, p)

def leaveChannel (c : Channel) (bare : String) : Channel :=
  { c with participants := c.participants.filter (·.bare != bare) }

/-- XEP-0369 section 7.1.2: a channel message. -/
def message (svc : Service) (name from_ : String) (id : Option String) (payload : List Node) :
    List Delivery :=
  let cj := svc.channelJid name
  match svc.channel? name with
  | none => [⟨from_, false, cj, .error .message id cj "cancel" "item-not-found"⟩]
  | some c =>
    match c.byBare (bareOf from_) with
    | none => [⟨from_, false, cj, .error .message id cj "modify" "not-acceptable"⟩]
    | some me => c.participants.map (fun p => ⟨p.bare, true, cj, .message me.nick id (sanitize payload)⟩)

/-- XEP-0369 section 7.3.2: create a channel. -/
def create (svc : Service) (from_ : String) (st : Stanza) (name : String) : Service × List Delivery :=
  let fail (cond : String) : Service × List Delivery := (svc, [⟨from_, false, svc.domain, .error .iq st.id svc.domain "cancel" cond⟩])
  match Jid.parse (name ++ "@" ++ svc.domain) with
  | none => fail "bad-request"
  | some _ =>
    if (svc.channel? name).isSome then fail "conflict"
    else if svc.channels.length ≥ svc.maxChannels then fail "resource-constraint"
    else
      ({ svc with channels := svc.channels ++ [⟨name, bareOf from_, [], 1⟩] },
       [⟨from_, false, svc.domain, .iqResult st.id (some svc.domain)
          [.element "create" [⟨"xmlns", nsCore⟩, ⟨"channel", name⟩] []]⟩])

/-- XEP-0405 section 5.1: join through the user's own server. -/
def pamJoin (svc : Service) (from_ : String) (st : Stanza) (cj : String) (join : Node) : Service × List Delivery :=
  let fail (cond : String) : Service × List Delivery := (svc, [⟨from_, false, cj, .error .iq st.id cj "cancel" cond⟩])
  match Jid.parse cj with
  | some j =>
    if j.domainpart != svc.domain || j.resourcepart.isSome then fail "item-not-found"
    else
      let name := j.localpart.getD ""
      match svc.channel? name with
      | none => fail "item-not-found"
      | some c =>
        let bare := bareOf from_
        -- `<nick/>` inherits the MIX-CORE namespace from `<join/>`, so it is found by tag.
        let nickEl := (childrenOf join).find? (fun n => match n with | .element "nick" _ _ => true | _ => false)
        let nick := match nickEl with
          | some n => if (textOf n).isEmpty then (Jid.parse bare).bind (·.localpart) |>.getD bare else textOf n
          | none => ((Jid.parse bare).bind (·.localpart)).getD bare
        if (c.byBare bare).isNone && c.participants.length ≥ svc.maxParticipants then fail "resource-constraint"
        else
          match joinChannel c bare nick with
          | none => fail "conflict"
          | some (c', p) =>
            let subs := (childrenOf join).filter (fun n => match n with | .element "subscribe" _ _ => true | _ => false)
            (svc.put c',
             [⟨from_, false, cj, .iqResult st.id none
               [.element "client-join" [⟨"xmlns", nsPam⟩]
                 [.element "join" [⟨"xmlns", nsCore⟩, ⟨"id", p.id⟩]
                   (subs ++ [.element "nick" [] [.text p.nick]])]]⟩])
  | none => fail "item-not-found"

/-- XEP-0405 section 5.2: leave through the user's own server. -/
def pamLeave (svc : Service) (from_ : String) (st : Stanza) (cj : String) : Service × List Delivery :=
  let name := ((Jid.parse cj).bind (·.localpart)).getD ""
  match svc.channel? name with
  | none => (svc, [⟨from_, false, cj, .error .iq st.id cj "cancel" "item-not-found"⟩])
  | some c =>
    (svc.put (leaveChannel c (bareOf from_)),
     [⟨from_, false, cj, .iqResult st.id none
       [.element "client-leave" [⟨"xmlns", nsPam⟩] [.element "leave" [⟨"xmlns", nsCore⟩] []]]⟩])

private def feature (v : String) : Node := .element "feature" [⟨"var", v⟩] []

def serviceIq (svc : Service) (from_ : String) (st : Stanza) : Service × List Delivery :=
  let ty := st.type.getD "get"
  let none_ : Service × List Delivery := (svc, [])
  if ty == "result" || ty == "error" then none_
  else if ty == "set" then
    match child nsCore "create" st.payload with
    | some c =>
      match attrOf c "channel" with
      | some name => create svc from_ st name
      | none => (svc, [⟨from_, false, svc.domain, .error .iq st.id svc.domain "modify" "bad-request"⟩])
    | none => (svc, [⟨from_, false, svc.domain, .error .iq st.id svc.domain "cancel" "feature-not-implemented"⟩])
  else if (child nsDiscoInfo "query" st.payload).isSome then
    (svc, [⟨from_, false, svc.domain, .iqResult st.id (some svc.domain) [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
      [.element "identity" [⟨"category", "conference"⟩, ⟨"type", "mix"⟩, ⟨"name", "Factoidal MIX"⟩] [],
       feature nsCore, feature (nsCore ++ "#searchable"), feature (nsCore ++ "#create-channel"), feature nsDiscoInfo,
       feature nsDiscoItems]]⟩])
  else if (child nsDiscoItems "query" st.payload).isSome then
    (svc, [⟨from_, false, svc.domain, .iqResult st.id (some svc.domain) [.element "query" [⟨"xmlns", nsDiscoItems⟩]
      (svc.channels.map (fun c => .element "item" [⟨"jid", svc.channelJid c.name⟩] []))]⟩])
  else (svc, [⟨from_, false, svc.domain, .error .iq st.id svc.domain "cancel" "feature-not-implemented"⟩])

def channelIq (svc : Service) (name from_ : String) (st : Stanza) : List Delivery :=
  let cj := svc.channelJid name
  let ty := st.type.getD "get"
  if ty == "result" || ty == "error" then []
  else if (child nsCore "join" st.payload).isSome then
    -- MIX-PAM: joins come through the user's own server.
    [⟨from_, false, cj, .error .iq st.id cj "cancel" "not-allowed"⟩]
  else if ty == "get" && (child nsDiscoInfo "query" st.payload).isSome then
    match svc.channel? name with
    | none => [⟨from_, false, cj, .error .iq st.id cj "cancel" "item-not-found"⟩]
    | some _ =>
      [⟨from_, false, cj, .iqResult st.id (some cj) [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
        [.element "identity" [⟨"category", "conference"⟩, ⟨"type", "mix"⟩, ⟨"name", name⟩] [], feature nsCore]]⟩]
  else [⟨from_, false, cj, .error .iq st.id cj "cancel" "feature-not-implemented"⟩]

/-- Is this IQ a MIX-PAM request (`<client-join/>` or `<client-leave/>`)? `Server.step`
hands such an IQ to the user's own bare JID to this service. -/
def isPam (st : Stanza) : Bool :=
  st.kind == .iq && ((child nsPam "client-join" st.payload).isSome || (child nsPam "client-leave" st.payload).isSome)

/-! ## The dispatch -/

def step (svc : Service) (from_ : String) (st : Stanza) : Service × List Delivery :=
  if isPam st then
    if st.type != some "set" then (svc, [])
    else
      match child nsPam "client-join" st.payload, child nsPam "client-leave" st.payload with
      | some cjn, _ =>
        match attrOf cjn "channel", child nsCore "join" (childrenOf cjn) with
        | some cj, some j => pamJoin svc from_ st cj j
        | _, _ => (svc, [⟨from_, false, svc.domain, .error .iq st.id svc.domain "modify" "bad-request"⟩])
      | none, some cl =>
        match attrOf cl "channel" with
        | some cj => pamLeave svc from_ st cj
        | none => (svc, [⟨from_, false, svc.domain, .error .iq st.id svc.domain "modify" "bad-request"⟩])
      | none, none => (svc, [])
  else
  match st.to with
  | none => (svc, [])
  | some to =>
    if to.domainpart != svc.domain then (svc, [])
    else
      let ty := st.type
      match to.localpart, to.resourcepart, st.kind with
      | none, _, .iq => serviceIq svc from_ st
      | none, _, _ => (svc, [])
      | some name, none, .message =>
        if ty == some "groupchat" then (svc, message svc name from_ st.id st.payload)
        else if ty == some "error" then (svc, [])
        else (svc, [⟨from_, false, svc.channelJid name, .error .message st.id (svc.channelJid name) "modify" "bad-request"⟩])
      | some name, none, .iq => (svc, channelIq svc name from_ st)
      | some _, _, .presence => (svc, [])
      | some name, _, kind =>
        if ty == some "error" || ty == some "result" then (svc, [])
        else (svc, [⟨from_, false, svc.channelJid name, .error kind st.id (svc.channelJid name) "cancel" "feature-not-implemented"⟩])

/-! ## Rendering -/

def Delivery.render (d : Delivery) : String :=
  let idAttr (id : Option String) : List Attribute := (id.map (Attribute.mk "id")).toList
  Wire.render <| match d.body with
  | .message nick id payload =>
    .element "message" ([⟨"from", d.channel⟩, ⟨"to", d.to⟩, ⟨"type", "groupchat"⟩] ++ idAttr id)
      (payload ++ [.element "mix" [⟨"xmlns", nsCore⟩] [.element "nick" [] [.text nick]]])
  | .iqResult id fromAddr children =>
    .element "iq" ((fromAddr.map (Attribute.mk "from")).toList ++ [⟨"to", d.to⟩, ⟨"type", "result"⟩] ++ idAttr id) children
  | .error kind id fromAddr errType cond =>
    .element kind.tagName ([⟨"from", fromAddr⟩, ⟨"to", d.to⟩, ⟨"type", "error"⟩] ++ idAttr id)
      [.element "error" [⟨"type", errType⟩] [.element cond [⟨"xmlns", nsStanzas⟩] []]]

/-! ## Theorems -/

/-- Fan-out: a participant's message goes to exactly the participants' accounts, each once,
and every copy may be held for an offline account. -/
theorem message_recipients (svc : Service) (name from_ : String) (id : Option String) (p : List Node)
    (c : Channel) (me : Participant) (hc : svc.channel? name = some c) (hm : c.byBare (bareOf from_) = some me) :
    (message svc name from_ id p).map (·.to) = c.participants.map (·.bare) ∧
    ∀ d ∈ message svc name from_ id p, d.held = true := by
  constructor
  · simp [message, hc, hm, List.map_map, Function.comp_def]
  · intro d hd
    simp [message, hc, hm] at hd
    obtain ⟨_, _, rfl⟩ := hd
    rfl

/-- No spoofing: every copy is from the channel, with the SENDER's own nick, and carries no
client-made `<mix/>` element. -/
theorem message_from_sender (svc : Service) (name from_ : String) (id : Option String) (p : List Node)
    (c : Channel) (me : Participant) (hc : svc.channel? name = some c) (hm : c.byBare (bareOf from_) = some me) :
    ∀ d ∈ message svc name from_ id p, d.channel = svc.channelJid name ∧ d.body = .message me.nick id (sanitize p) := by
  intro d hd
  simp [message, hc, hm] at hd
  obtain ⟨_, _, rfl⟩ := hd
  exact ⟨rfl, rfl⟩

/-- A message from someone who is not a participant reaches nobody but the sender. -/
theorem message_nonparticipant (svc : Service) (name from_ : String) (id : Option String) (p : List Node)
    (h : ∀ c, svc.channel? name = some c → c.byBare (bareOf from_) = none) :
    ∀ d ∈ message svc name from_ id p, d.to = from_ ∧ d.held = false := by
  intro d hd
  unfold message at hd
  cases hc : svc.channel? name with
  | none => simp [hc] at hd; simp [hd]
  | some c => simp [hc, h c hc] at hd; simp [hd]

/-- Joining keeps one entry per account: participants' bare JIDs stay distinct. -/
theorem joinChannel_bares_nodup (c c' : Channel) (bare nick : String) (p : Participant)
    (hnd : (c.participants.map (·.bare)).Nodup) (h : joinChannel c bare nick = some (c', p)) :
    (c'.participants.map (·.bare)).Nodup := by
  unfold joinChannel at h
  cases hb : c.byBare bare with
  | some q => simp [hb] at h; obtain ⟨rfl, _⟩ := h; exact hnd
  | none =>
    simp only [hb] at h
    split at h
    · cases h
    · cases h
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
      intro a ha b hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro heq
      subst heq
      simp only [List.mem_map] at ha
      obtain ⟨o, ho, hob⟩ := ha
      have : c.byBare o.bare ≠ none := by
        unfold Channel.byBare
        intro hn
        have := List.find?_eq_none.mp hn o ho
        simp at this
      rw [hob] at this
      exact this hb

/-- Joining keeps nicks distinct. -/
theorem joinChannel_nicks_nodup (c c' : Channel) (bare nick : String) (p : Participant)
    (hnd : (c.participants.map (·.nick)).Nodup) (h : joinChannel c bare nick = some (c', p)) :
    (c'.participants.map (·.nick)).Nodup := by
  unfold joinChannel at h
  cases hb : c.byBare bare with
  | some q => simp [hb] at h; obtain ⟨rfl, _⟩ := h; exact hnd
  | none =>
    simp only [hb] at h
    split at h
    · cases h
    · rename_i hany
      cases h
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
      intro a ha b hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      intro heq
      subst heq
      apply hany
      simp only [List.any_eq_true, beq_iff_eq]
      simp only [List.mem_map] at ha
      obtain ⟨o, ho, rfl⟩ := ha
      exact ⟨o, ho, rfl⟩

/-- Joining again is no change. -/
theorem joinChannel_again (c : Channel) (bare nick : String) (p : Participant)
    (h : c.byBare bare = some p) : joinChannel c bare nick = some (c, p) := by
  simp [joinChannel, h]

/-- Leaving removes the participant. -/
theorem leaveChannel_gone (c : Channel) (bare : String) :
    ∀ p ∈ (leaveChannel c bare).participants, p.bare ≠ bare := by
  intro p hp
  simp [leaveChannel, List.mem_filter] at hp
  exact hp.2

/-! ## Checks -/

private def svc0 : Service := { domain := "mix.example.com" }
private def st (kind : StanzaKind) (to : Option String) (ty : Option String) (payload : List Node := []) : Stanza :=
  { kind, id := some "x1", from_ := none, to := to.bind Jid.parse, type := ty, payload }
private def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
private def createIq (name : String) : Stanza :=
  st .iq (some "mix.example.com") (some "set") [.element "create" [⟨"xmlns", nsCore⟩, ⟨"channel", name⟩] []]
private def joinIq (cj : String) (nick : Option String) : Stanza :=
  st .iq none (some "set") [.element "client-join" [⟨"xmlns", nsPam⟩, ⟨"channel", cj⟩]
    [.element "join" [⟨"xmlns", nsCore⟩]
      ([.element "subscribe" [⟨"node", "urn:xmpp:mix:nodes:messages"⟩] []] ++
       (nick.map (fun n => .element "nick" [] [.text n])).toList)]]
private def body (t : String) : Node := .element "body" [] [.text t]

private def twoIn : Service :=
  let (s1, _) := step svc0 "hag66@example.com/a" (createIq "coven")
  let (s2, _) := step s1 "hag66@example.com/a" (joinIq "coven@mix.example.com" (some "third witch"))
  (step s2 "hecate@example.com/x" (joinIq "coven@mix.example.com" none)).1

-- Create, then join through PAM: the answer carries a participant id and the nick.
#guard
  let (s1, d1) := step svc0 "hag66@example.com/a" (createIq "coven")
  let (s2, d2) := step s1 "hag66@example.com/a" (joinIq "coven@mix.example.com" (some "third witch"))
  has d1[0]!.render "channel=\"coven\"" && has d2[0]!.render "id=\"p1\"" &&
  has d2[0]!.render "<nick>third witch</nick>" && has d2[0]!.render "urn:xmpp:mix:nodes:messages" &&
  d2[0]!.to == "hag66@example.com/a" && !d2[0]!.held &&
  (s2.channel? "coven").map (·.participants.length) == some 1

-- Joining again from another resource of the same account: one participant, the same id.
#guard
  let (s3, d3) := step twoIn "hag66@example.com/b" (joinIq "coven@mix.example.com" (some "third witch"))
  (s3.channel? "coven").map (·.participants.length) == some 2 && has d3[0]!.render "id=\"p1\""

-- A message goes to both ACCOUNTS (held), from the channel, with the sender's nick and no JID;
-- a forged <mix/> is dropped.
#guard
  let forged : Node := .element "mix" [⟨"xmlns", nsCore⟩] [.element "nick" [] [.text "hecate"]]
  let (_, ds) := step twoIn "hag66@example.com/a" (st .message (some "coven@mix.example.com") (some "groupchat") [body "harpier cries", forged])
  ds.map (·.to) == ["hag66@example.com", "hecate@example.com"] && ds.all (·.held) &&
  ds.all (fun d => has d.render "from=\"coven@mix.example.com\"" && has d.render "<nick>third witch</nick>" &&
    !has d.render "<nick>hecate</nick>" && !has d.render "<jid>")

-- A non-participant: not-acceptable, to the sender only, never held.
#guard
  let (_, ds) := step twoIn "mallory@example.com/x" (st .message (some "coven@mix.example.com") (some "groupchat") [body "spam"])
  ds.map (·.to) == ["mallory@example.com/x"] && !ds[0]!.held && has ds[0]!.render "not-acceptable"

-- The nick is taken by another account: conflict.
#guard
  let (s3, ds) := step twoIn "mallory@example.com/x" (joinIq "coven@mix.example.com" (some "third witch"))
  (s3.channel? "coven").map (·.participants.length) == some 2 && has ds[0]!.render "conflict"

-- Joining a channel that does not exist; a direct join to the channel; a duplicate create.
#guard
  let (_, a) := step svc0 "hag66@example.com/a" (joinIq "nowhere@mix.example.com" none)
  let (_, b) := step twoIn "hag66@example.com/a" (st .iq (some "coven@mix.example.com") (some "set") [.element "join" [⟨"xmlns", nsCore⟩] []])
  let (_, c) := step twoIn "x@example.com/y" (createIq "coven")
  has a[0]!.render "item-not-found" && has b[0]!.render "not-allowed" && has c[0]!.render "conflict"

-- Leave through PAM; the channel stays (MIX channels are not temporary).
#guard
  let (s3, ds) := step twoIn "hecate@example.com/x" (st .iq none (some "set")
    [.element "client-leave" [⟨"xmlns", nsPam⟩, ⟨"channel", "coven@mix.example.com"⟩] [.element "leave" [⟨"xmlns", nsCore⟩] []]])
  (s3.channel? "coven").map (·.participants.map (·.bare)) == some ["hag66@example.com"] && has ds[0]!.render "client-leave"

-- Disco on the service lists the channel.
#guard
  let (_, ds) := step twoIn "x@example.com/y" (st .iq (some "mix.example.com") (some "get") [.element "query" [⟨"xmlns", nsDiscoItems⟩] []])
  has ds[0]!.render "jid=\"coven@mix.example.com\""

end L4Factoidal.XMPP.Mix
