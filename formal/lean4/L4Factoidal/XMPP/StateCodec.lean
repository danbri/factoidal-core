/-
L4Factoidal.XMPP.StateCodec — the text forms in which `xmpp-serve` keeps its state in an LWS
storage (issue https://github.com/danbri/factoidal/issues/1237): the stanzas held for one
account, one MIX channel, one GC3 group. Each has a decoder and a ROUND-TRIP theorem, so a
restart restores exactly what was written, and what the live state no longer holds is not in
what is written.

The framing is the one of `OWL.CertNames` (each character of a field is preceded by `+`, a
bare `;` ends a field), copied here with its proofs because `OWL.CertNames` imports all of `Std`,
which the wasm build does not link (`initialize_Std`, measured 2026-11-03). Numbers are decimal,
from `LWS.Snapshot` (`decimal?`, `decimal_repr`), which is in the wasm build.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.LWS.Snapshot
import L4Factoidal.XMPP.Mix
import L4Factoidal.XMPP.Gc3

namespace L4Factoidal.XMPP.StateCodec

open L4Factoidal.LWS (decimal? decimal_repr)

/-! ## Field framing (from `OWL.CertNames`) -/

def frame : List Char → List Char
  | [] => [';']
  | c :: cs => '+' :: c :: frame cs

def frameAcc : List Char → List Char → List Char
  | [], acc => acc.reverse ++ [';']
  | c :: cs, acc => frameAcc cs (c :: '+' :: acc)

def frameTR (cs : List Char) : List Char := frameAcc cs []

theorem frameAcc_eq (cs acc : List Char) : frameAcc cs acc = acc.reverse ++ frame cs := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih => simp [frameAcc, frame, ih, List.reverse_cons, List.append_assoc]

@[csimp] theorem frame_eq_frameTR : @frame = @frameTR := by
  funext cs
  simp [frameTR, frameAcc_eq]

def fields (ss : List String) : List Char := ss.flatMap (fun s => frame s.toList)

def readFields : List Char → List Char → List String → Option (List String)
  | [], [], acc => some acc.reverse
  | [], _ :: _, _ => none
  | ';' :: rest, chars, acc => readFields rest [] (String.ofList chars.reverse :: acc)
  | '+' :: c :: rest, chars, acc => readFields rest (c :: chars) acc
  | _ :: _, _, _ => none

theorem readFields_frame (cs rest chars : List Char) (acc : List String) :
    readFields (frame cs ++ rest) chars acc =
      readFields rest [] (String.ofList (chars.reverse ++ cs) :: acc) := by
  induction cs generalizing chars with
  | nil => simp [frame, readFields]
  | cons c cs ih => simp [frame, readFields, ih, List.reverse_cons, List.append_assoc]

theorem readFields_fields (ss acc : List String) :
    readFields (fields ss) [] acc = some (acc.reverse ++ ss) := by
  induction ss generalizing acc with
  | nil => simp [fields, readFields]
  | cons s ss ih =>
      simp only [fields, List.flatMap_cons]
      rw [readFields_frame]
      simp only [List.reverse_nil, List.nil_append, String.ofList_toList]
      change readFields (fields ss) [] (s :: acc) = some (acc.reverse ++ s :: ss)
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- Decode the framed fields of a text. -/
def fieldsOf (s : String) : Option (List String) := readFields s.toList [] []

def textOf (ss : List String) : String := String.ofList (fields ss)

theorem fieldsOf_textOf (ss : List String) : fieldsOf (textOf ss) = some ss := by
  simp [fieldsOf, textOf, String.toList_ofList, readFields_fields]

/-! ## Held stanzas for one account -/

def encodeHeld (q : List String) : String := textOf q
def decodeHeld (s : String) : Option (List String) := fieldsOf s

theorem decodeHeld_encodeHeld (q : List String) : decodeHeld (encodeHeld q) = some q :=
  fieldsOf_textOf q

/-! ## A MIX channel -/

def partFields (ps : List Mix.Participant) : List String := ps.flatMap (fun p => [p.bare, p.nick, p.id])

/-- Tail-recursive (the tail-recursion gate). -/
def readParts : List String → List Mix.Participant → Option (List Mix.Participant)
  | [], acc => some acc.reverse
  | a :: b :: c :: rest, acc => readParts rest (⟨a, b, c⟩ :: acc)
  | _, _ => none

theorem readParts_partFields (ps acc : List Mix.Participant) :
    readParts (partFields ps) acc = some (acc.reverse ++ ps) := by
  induction ps generalizing acc with
  | nil => simp [partFields, readParts]
  | cons p ps ih =>
    simp only [partFields, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [readParts, ih]
    simp

def encodeChannel (c : Mix.Channel) : String :=
  textOf ([c.name, c.owner, c.nextId.repr] ++ partFields c.participants)

def decodeChannel (s : String) : Option Mix.Channel :=
  match fieldsOf s with
  | some (name :: owner :: n :: rest) =>
    match decimal? n, readParts rest [] with
    | some k, some ps => some ⟨name, owner, ps, k⟩
    | _, _ => none
  | _ => none

theorem decodeChannel_encodeChannel (c : Mix.Channel) : decodeChannel (encodeChannel c) = some c := by
  simp only [decodeChannel, encodeChannel, fieldsOf_textOf, List.cons_append, List.nil_append,
    decimal_repr, readParts_partFields, List.reverse_nil, List.nil_append]

/-! ## A GC3 group -/

def affText : Gc3.Affiliation → String
  | .owner => "owner"
  | .member => "member"

def affOf : String → Option Gc3.Affiliation
  | "owner" => some .owner
  | "member" => some .member
  | _ => none

theorem affOf_affText (a : Gc3.Affiliation) : affOf (affText a) = some a := by
  cases a <;> rfl

def boolText (b : Bool) : String := if b then "1" else "0"

def boolOf : String → Option Bool
  | "1" => some true
  | "0" => some false
  | _ => none

theorem boolOf_boolText (b : Bool) : boolOf (boolText b) = some b := by
  cases b <;> rfl

def memberFields (ms : List Gc3.Member) : List String :=
  ms.flatMap (fun m => [m.bare, m.nick, m.id, affText m.affiliation, boolText m.presence])

/-- Tail-recursive (the tail-recursion gate). -/
def readMembers : List String → List Gc3.Member → Option (List Gc3.Member)
  | [], acc => some acc.reverse
  | a :: b :: c :: d :: e :: rest, acc =>
    match affOf d, boolOf e with
    | some aff, some pr => readMembers rest (⟨a, b, c, aff, pr⟩ :: acc)
    | _, _ => none
  | _, _ => none

theorem readMembers_memberFields (ms acc : List Gc3.Member) :
    readMembers (memberFields ms) acc = some (acc.reverse ++ ms) := by
  induction ms generalizing acc with
  | nil => simp [memberFields, readMembers]
  | cons m ms ih =>
    simp only [memberFields, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [readMembers, affOf_affText, boolOf_boolText]
    simp only []
    rw [ih]
    simp

def encodeGroup (g : Gc3.Group) : String :=
  textOf ([g.name, g.nextId.repr] ++ memberFields g.members)

def decodeGroup (s : String) : Option Gc3.Group :=
  match fieldsOf s with
  | some (name :: n :: rest) =>
    match decimal? n, readMembers rest [] with
    | some k, some ms => some ⟨name, ms, k⟩
    | _, _ => none
  | _ => none

theorem decodeGroup_encodeGroup (g : Gc3.Group) : decodeGroup (encodeGroup g) = some g := by
  simp only [decodeGroup, encodeGroup, fieldsOf_textOf, List.cons_append, List.nil_append,
    decimal_repr, readMembers_memberFields, List.reverse_nil, List.nil_append]

/-! ## Where each item is kept

One resource per item, under `/xmpp/<kind>/<name in hex>`, so a change rewrites one small
resource, and the name (an account, a channel, a group) needs no escaping. -/

def hexOf (s : String) : String :=
  String.join (s.toUTF8.toList.map (fun b =>
    let h := "0123456789abcdef".toList
    String.ofList [h[b.toNat / 16]!, h[b.toNat % 16]!]))

private def nibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else none

/-- Tail-recursive (the tail-recursion gate). -/
def bytesOfHex : List Char → List UInt8 → Option (List UInt8)
  | [], acc => some acc.reverse
  | a :: b :: rest, acc =>
    match nibble a, nibble b with
    | some x, some y => bytesOfHex rest ((x * 16 + y).toUInt8 :: acc)
    | _, _ => none
  | _, _ => none

def nameOfHex (h : String) : Option String :=
  (bytesOfHex h.toList []).bind (fun bs => String.fromUTF8? ⟨bs.toArray⟩)

def pathOf (kind name : String) : String := "/xmpp/" ++ kind ++ "/" ++ hexOf name

/-! ## Checks -/

#guard decodeHeld (encodeHeld ["<message/>", "a;b+c", ""]) == some ["<message/>", "a;b+c", ""]
#guard (decodeChannel (encodeChannel ⟨"coven", "hag66@example.com", [⟨"hag66@example.com", "third; witch", "p1"⟩], 2⟩)).map (·.participants.map (·.nick)) == some ["third; witch"]
#guard (decodeGroup (encodeGroup ⟨"tea", [⟨"j@x", "jul", "p1", .owner, true⟩, ⟨"r@x", "rom", "p2", .member, false⟩], 3⟩)).map (fun g => (g.nextId, g.members.map (·.presence))) == some (3, [true, false])
#guard nameOfHex (hexOf "juliet@example.com") == some "juliet@example.com"
#guard nameOfHex (hexOf "Grüße/../x") == some "Grüße/../x"
#guard pathOf "held" "r@x" == "/xmpp/held/72407"   ++ "8"
#guard decodeChannel "garbage" == none

end L4Factoidal.XMPP.StateCodec
