/-
L4Factoidal.WebDAV.State — the server's state (`DavState`: dead properties,
locks, the lock counter) as a JSON text, and back.
https://github.com/danbri/factoidal/issues/1078

The WebDAV handle keeps this text in the file `CONFIGDIR/.webdav-state.json`
(`stateFileName`): it reads the file at start and names a new text to write
after each request that changes the state. The host only reads and writes
the file. Design record: docs/designissues/2026-10-27-webdav.md
§ "State across a restart".

The form (version 1):

    {"format":"factoidal-webdav-state","version":1,"serial":N,
     "props":[{"key":"/m/a.txt","props":[{"ns":"urn:x"|null,"local":"colour",
                                         "value":DEADVALUE}]}],
     "locks":[{"token":"urn:uuid:…","root":{"segs":["m","a.txt"],"slash":false},
               "infinite":B,"exclusive":B,"owner":DEADVALUE|null,
               "timeout":N,"expires":N}]}

    DEADVALUE = {"node":[EVENT,…],"bindings":[[PREFIX,NAMESPACE],…]}
    EVENT = ["e",TAG,[[NAME,VALUE],…],CHILDREN] | ["t",TEXT] | ["c",COMMENT]
          | ["d",CDATA] | ["p",TARGET,DATA]

An XML node is a flat list of events in document order: an element gives
its tag, its attributes as written and the number of its children, and its
children follow. `nodeEvents` writes the list with one loop over a stack of
sibling lists; `nodeOfEvents` reads it with one loop over a stack of open
elements. Neither recurses over the depth of the value, so a deep property
value is written and read in fixed stack.

A text that is not JSON, has another `format`, another `version`, or a
member of the wrong type is refused with a message; the handle stops the
start with it (`stateOfText`). Nothing is dropped silently.
-/
import L4Factoidal.WebDAV.Server
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.WebDAV

open L4Factoidal.XML
open L4Factoidal.JSON

deriving instance DecidableEq for Lock
deriving instance DecidableEq for DavState

/-- The state file, relative to CONFIGDIR. A name that starts with `.` is
never a mount file (`isMountFile`). -/
def stateFileName : String := ".webdav-state.json"

def stateFormat : String := "factoidal-webdav-state"

/-- The version this engine writes and the only one it reads. -/
def stateVersion : Nat := 1

/-! ## XML nodes as events -/

def attrsJson (attrs : List Attribute) : Json :=
  .array (attrs.map (fun a => .array [.string a.name, .string a.value]))

/-- The events of the nodes on a stack of sibling lists, appended to `acc`
in document order. One loop: each step takes one node, and pushes an
element's children as a new sibling list. -/
def nodeEventsGo : List (List Node) → Array Json → Array Json
  | [], acc => acc
  | [] :: st, acc => nodeEventsGo st acc
  | (n :: ns) :: st, acc =>
    match n with
    | .element tag attrs kids =>
      nodeEventsGo (kids :: ns :: st)
        (acc.push (.array [.string "e", .string tag, attrsJson attrs, .number (toString kids.length)]))
    | .text s => nodeEventsGo (ns :: st) (acc.push (.array [.string "t", .string s]))
    | .comment s => nodeEventsGo (ns :: st) (acc.push (.array [.string "c", .string s]))
    | .cdata s => nodeEventsGo (ns :: st) (acc.push (.array [.string "d", .string s]))
    | .pi t d => nodeEventsGo (ns :: st) (acc.push (.array [.string "p", .string t, .string d]))
termination_by st => sizeOf st

def nodeEvents (n : Node) : Json := .array (nodeEventsGo [[n]] #[]).toList

/-- An element whose children are still being read. -/
structure OpenEl where
  tag : String
  attrs : List Attribute
  left : Nat
  /-- The children read, last first. -/
  kids : List Node

/-- Give a complete node to the innermost open element; close each element
that is then complete. `.inr n`: the outermost node is complete. -/
def deliverNode : List OpenEl → Node → List OpenEl ⊕ Node
  | [], n => .inr n
  | f :: fs, n =>
    if f.left ≤ 1 then deliverNode fs (.element f.tag f.attrs (n :: f.kids).reverse)
    else .inl ({ f with left := f.left - 1, kids := n :: f.kids } :: fs)

def natOf? : Json → Option Nat
  | .number s => s.toNat?
  | _ => none

def attrOf? : Json → Option Attribute
  | .array [.string n, .string v] => some { name := n, value := v }
  | _ => none

/-- One event: an element's tag, attributes and child count, or a node with
no children. -/
def eventOf : Json → Except String ((String × List Attribute × Nat) ⊕ Node)
  | .array [.string "e", .string tag, .array as, c] =>
    match as.mapM attrOf?, natOf? c with
    | some attrs, some k => .ok (.inl (tag, attrs, k))
    | _, _ => .error "an element event has a malformed attribute list or child count"
  | .array [.string "t", .string s] => .ok (.inr (.text s))
  | .array [.string "c", .string s] => .ok (.inr (.comment s))
  | .array [.string "d", .string s] => .ok (.inr (.cdata s))
  | .array [.string "p", .string t, .string d] => .ok (.inr (.pi t d))
  | _ => .error "an XML node event is malformed"

/-- Read events into one node. One loop over the events. -/
def nodeOfEventsGo : List Json → List OpenEl → Except String Node
  | [], _ => .error "the XML node events end before the node does"
  | e :: es, st =>
    match eventOf e with
    | .error m => .error m
    | .ok ev =>
      let step : List OpenEl ⊕ Node :=
        match ev with
        | .inl (tag, attrs, 0) => deliverNode st (.element tag attrs [])
        | .inl (tag, attrs, k) => .inl ({ tag, attrs, left := k, kids := [] } :: st)
        | .inr n => deliverNode st n
      match step with
      | .inl st' => nodeOfEventsGo es st'
      | .inr n => if es.isEmpty then .ok n else .error "XML node events follow the end of the node"

def nodeOfEvents (j : Json) : Except String Node :=
  match j with
  | .array es => nodeOfEventsGo es []
  | _ => .error "an XML node is not an array of events"

/-! ## The state -/

def pairsJson (ps : List (String × String)) : Json :=
  .array (ps.map (fun (a, b) => .array [.string a, .string b]))

def pairOf? : Json → Option (String × String)
  | .array [.string a, .string b] => some (a, b)
  | _ => none

def deadValueJson (v : DeadValue) : Json :=
  .object [("node", nodeEvents v.raw), ("bindings", pairsJson v.bindings)]

def deadValueOf (j : Json) : Except String DeadValue := do
  let raw ← nodeOfEvents ((j.field? "node").getD .null)
  match (j.getArray? "bindings").bind (·.mapM pairOf?) with
  | some bindings => pure { raw, bindings }
  | none => throw "a property value has no well-formed \"bindings\""

def deadPropJson (d : DeadProp) : Json :=
  .object [ ("ns", match d.name.namespace_ with | some u => .string u | none => .null)
          , ("local", .string d.name.localPart), ("value", deadValueJson d.value) ]

def deadPropOf (j : Json) : Except String DeadProp := do
  let ns ← match j.field? "ns" with
    | some .null => pure none
    | some (.string u) => pure (some u)
    | _ => throw "a dead property has no well-formed \"ns\""
  let localPart ← (j.getString? "local").elim (throw "a dead property has no \"local\"") pure
  let value ← deadValueOf ((j.field? "value").getD .null)
  pure { name := { namespace_ := ns, localPart }, value }

def lockJson (l : Lock) : Json :=
  .object [ ("token", .string l.token)
          , ("root", .object [("segs", .array (l.root.segs.map Json.string)), ("slash", .bool l.root.slash)])
          , ("infinite", .bool l.infinite), ("exclusive", .bool l.exclusive)
          , ("owner", match l.owner with | some o => deadValueJson o | none => .null)
          , ("timeout", .number (toString l.timeout)), ("expires", .number (toString l.expires)) ]

def natField (j : Json) (key what : String) : Except String Nat :=
  ((j.field? key).bind natOf?).elim (.error s!"{what} has no natural number \"{key}\"") .ok

def boolField (j : Json) (key what : String) : Except String Bool :=
  (j.getBool? key).elim (.error s!"{what} has no boolean \"{key}\"") .ok

def lockOf (j : Json) : Except String Lock := do
  let token ← (j.getString? "token").elim (throw "a lock has no \"token\"") pure
  let r := (j.field? "root").getD .null
  let segs ← ((r.getArray? "segs").bind (·.mapM Json.asString?)).elim
    (throw s!"the lock {token} has no well-formed \"root\"") pure
  let slash ← boolField r "slash" s!"the root of lock {token}"
  let infinite ← boolField j "infinite" s!"the lock {token}"
  let exclusive ← boolField j "exclusive" s!"the lock {token}"
  let owner ← match j.field? "owner" with
    | some .null => pure none
    | some o => (deadValueOf o).map some
    | none => throw s!"the lock {token} has no \"owner\""
  let timeout ← natField j "timeout" s!"the lock {token}"
  let expires ← natField j "expires" s!"the lock {token}"
  pure { token, root := { segs, slash }, infinite, exclusive, owner, timeout, expires }

def stateJson (st : DavState) : Json :=
  .object [ ("format", .string stateFormat), ("version", .number (toString stateVersion))
          , ("serial", .number (toString st.serial))
          , ("props", .array (st.props.map (fun (k, ps) =>
              .object [("key", .string k), ("props", .array (ps.map deadPropJson))])))
          , ("locks", .array (st.locks.map lockJson)) ]

/-- The text the handle writes to the state file. -/
def stateText (st : DavState) : String := (stateJson st).toString

def propsEntryOf (j : Json) : Except String (String × List DeadProp) := do
  let k ← (j.getString? "key").elim (throw "a property entry has no \"key\"") pure
  let ps ← (j.getArray? "props").elim (throw s!"the property entry {k} has no \"props\"") pure
  let ds ← ps.mapM deadPropOf
  pure (k, ds)

def stateOfJson (j : Json) : Except String DavState := do
  if j.getString? "format" != some stateFormat then
    throw s!"\"format\" is not \"{stateFormat}\""
  let v ← natField j "version" "the state"
  if v != stateVersion then
    throw s!"format version {v} is not known (this engine reads version {stateVersion})"
  let serial ← natField j "serial" "the state"
  let props ← ((j.getArray? "props").elim (throw "the state has no \"props\" array") pure) >>= (·.mapM propsEntryOf)
  let locks ← ((j.getArray? "locks").elim (throw "the state has no \"locks\" array") pure) >>= (·.mapM lockOf)
  pure { props, locks, serial }

/-- Read a state file's text. -/
def stateOfText (t : String) : Except String DavState :=
  match parseJson t with
  | .error e => .error s!"not JSON: {toString e}"
  | .ok j => stateOfJson j

/-- The state a server starts from: the locks that have not expired at
`now` (RFC 4918 §6.6). -/
def stateAtStart (st : DavState) (now : Nat) : DavState :=
  { st with locks := st.locks.filter (·.expires > now) }

/-! ## Checks -/

def roundTrips (st : DavState) : Bool :=
  match stateOfText (stateText st) with
  | .ok st' => st' == st
  | .error _ => false

private def sampleValue : DeadValue :=
  { raw := .element "Z:colour" [{ name := "xml:lang", value := "en" }]
      [.text "gr\"een\n", .element "Z:b" [] [], .cdata "<x>", .comment " c ", .pi "t" "d",
       .element "Z:c" [{ name := "a", value := "1&2" }] [.element "Z:d" [] [.text "é"]]]
    bindings := [("Z", "http://ns.example/"), ("", "urn:default")] }

private def sampleState : DavState :=
  { props := [ ("/local/a.txt", [{ name := { namespace_ := some "http://ns.example/", localPart := "colour" }, value := sampleValue },
                                 { name := { namespace_ := none, localPart := "plain" }, value := { raw := .element "plain" [] [] } }])
             , ("/local/dir", []) ]
    locks := [ { token := "urn:uuid:ffffffff-ffff-4fff-bfff-ffffffffffff", root := { segs := ["local", "a.txt"] },
                 infinite := false, exclusive := true, owner := some { raw := .element "D:owner" [] [.text "me"] },
                 timeout := 3600, expires := 1700003600 }
             , { token := "urn:uuid:00000000-0000-4000-8000-000000000000", root := { segs := ["local", "dir"], slash := true },
                 infinite := true, exclusive := false, timeout := 60, expires := 1700000060 } ]
    serial := 7 }

#guard roundTrips {}
#guard roundTrips sampleState
#guard (match nodeOfEvents (nodeEvents sampleValue.raw) with | .ok n => n == sampleValue.raw | .error _ => false)
#guard (stateAtStart sampleState 1700000100).locks.length == 1

-- Refusals: not JSON, another format, another version, a malformed member.
#guard (stateOfText "{").toOption.isNone
#guard (stateOfText "{\"format\":\"x\",\"version\":1,\"serial\":0,\"props\":[],\"locks\":[]}").toOption.isNone
#guard (match stateOfText "{\"format\":\"factoidal-webdav-state\",\"version\":2,\"serial\":0,\"props\":[],\"locks\":[]}" with
        | .error m => m == "format version 2 is not known (this engine reads version 1)" | .ok _ => false)
#guard (stateOfText "{\"format\":\"factoidal-webdav-state\",\"version\":1,\"serial\":0,\"props\":[],\"locks\":[{}]}").toOption.isNone
#guard (stateOfText "{\"format\":\"factoidal-webdav-state\",\"version\":1,\"serial\":0,\"props\":[],\"locks\":[]}").toOption.isSome
-- Events: a child count larger than the children, and events after the node.
#guard (nodeOfEvents (.array [.array [.string "e", .string "a", .array [], .number "2"], .array [.string "t", .string "x"]])).toOption.isNone
#guard (nodeOfEvents (.array [.array [.string "t", .string "x"], .array [.string "t", .string "y"]])).toOption.isNone

end L4Factoidal.WebDAV
