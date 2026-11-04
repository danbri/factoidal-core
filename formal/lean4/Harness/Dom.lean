/-
Harness.Dom — `l4dom`: the DOM arena (`L4Factoidal/DOM/`) driven by a script of
DOM operations (https://github.com/danbri/factoidal/issues/1167, milestone 6).

  l4dom ops FILE     run each script of FILE; print one result line per
                     operation, then the dump of every root that a handle names

The scripts come from `tests/dom/diff.mjs`, which runs the same operations in
jsdom and compares the output line by line. Script format, one operation per
line; a string argument is `=` followed by the hex of its UTF-8 bytes; a node
argument is a handle number, `-` for null:

  script                start a script
  html =S               parse S with the Lean HTML parser; handles 0.. are the
                        Document and its descendants in tree order
  el =S | text =S | comment =S | frag | pi =T =S | doctype =S
                        create a node of the Document; a new handle on success
  append P C | insert P C R | replace P N O | removechild P C | remove C
  move P C R            P.moveBefore(C, R)
  settext N =S | gettext N | normalize N | clone N 0|1 | equal A B | contains A B
  content T             the template contents of T (a new handle), or null
  setattr E =Q =V | byid N =S
  end                   print `final`, the dumps of the roots, and check the
                        tree invariant (`wellFormed`; a failure exits 1)

A result line is `ok`, `ok VALUE` or `err NAME` (the DOMException name).
-/
import L4Factoidal.DOM.OfHtml
import Harness.DomDump

namespace Harness.Dom

open L4Factoidal.DOM

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else 0

/-- `=HEX` to the string of those UTF-8 bytes. -/
def unhex (s : String) : String := Id.run do
  let cs := (s.toList.drop 1).toArray
  let mut b : ByteArray := ByteArray.empty
  for i in [0:cs.size / 2] do
    b := b.push (UInt8.ofNat (hexVal cs[2 * i]! * 16 + hexVal cs[2 * i + 1]!))
  return (String.fromUTF8? b).getD ""

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex (s : String) : String := Id.run do
  let mut out := "="
  for b in s.toUTF8 do
    out := out.push (hexDigit (b.toNat / 16)) |>.push (hexDigit (b.toNat % 16))
  return out

structure St where
  d : Dom := {}
  hs : Array NodeId := #[]
  out : Array String := #[]
  bad : Nat := 0

def St.h (st : St) (s : String) : Option NodeId := if s == "-" then none else st.hs[s.toNat!]?
def St.hn (st : St) (s : String) : NodeId := (st.h s).getD 0
def St.say (st : St) (l : String) : St := { st with out := st.out.push l }

def withErr (st : St) (r : Res Unit) : St :=
  match r with
  | (d, .ok ()) => { st with d }.say "ok"
  | (d, .error e) => { st with d }.say ("err " ++ e.name)

def withNew (st : St) (r : Res NodeId) : St :=
  match r with
  | (d, .ok n) => { st with d, hs := st.hs.push n }.say "ok"
  | (d, .error e) => { st with d }.say ("err " ++ e.name)

def ok (r : Dom × NodeId) : Res NodeId := (r.1, .ok r.2)
def done (d : Dom) : Res Unit := (d, .ok ())

def finish (st : St) : St := Id.run do
  let mut st := st.say "final"
  let mut seen : Array NodeId := #[]
  for i in [0:st.hs.size] do
    let n := st.hs[i]!
    if (st.d.get n).parent.isNone && !seen.contains n then
      seen := seen.push n
      st := st.say s!"root {i}"
      for l in DomDump.dump st.d n do st := st.say l
  if !st.d.wellFormed then
    st := { st with bad := st.bad + 1 }
    st := st.say "NOT WELL-FORMED"
  return st

/-- One operation. The arena is taken out of the state first, and every
operation gives it back (`Res`), so it is not shared while an operation changes
it: `Array.modify` then works in place. Measured 2026-11-01: with the old state
alive, every change copied the whole arena, and 80,000 appends took 44 s. -/
def step (st0 : St) (ws : List String) : St :=
  let doc : NodeId := 0
  let d := st0.d
  let st := { st0 with d := {} }
  match ws with
  | ["script"] => { st with hs := #[] }.say "script"
  | ["html", s] =>
    let d := parseHtmlDocument (unhex s)
    { st with d, hs := d.treeOrder 0 true }
  | ["el", s] => withNew st (d.createElement doc (unhex s))
  | ["text", s] => withNew st (ok (d.createTextNode doc (unhex s)))
  | ["comment", s] => withNew st (ok (d.createComment doc (unhex s)))
  | ["frag"] => withNew st (ok (d.createDocumentFragment doc))
  | ["doctype", s] => withNew st (d.createDocumentType doc (unhex s) "" "")
  | ["pi", t, s] => withNew st (d.createProcessingInstruction doc (unhex t) (unhex s))
  | ["append", p, c] => withErr st (d.appendChild (st.hn p) (st.hn c))
  | ["insert", p, c, r] => withErr st (d.insertBefore (st.hn p) (st.hn c) (st.h r))
  | ["replace", p, n, o] => withErr st (d.replace (st.hn o) (st.hn n) (st.hn p))
  | ["removechild", p, c] => withErr st (d.preRemove (st.hn c) (st.hn p))
  | ["remove", c] => withErr st (done (d.removeSelf (st.hn c)))
  | ["move", p, c, r] => withErr st (d.move (st.hn c) (st.hn p) (st.h r))
  | ["settext", n, s] => withErr st (done (d.setTextContent (st.hn n) (unhex s)))
  | ["gettext", n] =>
    { st with d }.say (match d.textContent (st.hn n) with
      | some s => "ok " ++ hex s
      | none => "ok null")
  | ["normalize", n] => withErr st (done (d.normalize (st.hn n)))
  | ["clone", n, deep] => withNew st (ok (d.cloneNode (st.hn n) (deep == "1")))
  | ["equal", a, b] => { st with d }.say s!"ok {d.isEqualNode (st.hn a) (st.hn b)}"
  | ["contains", a, b] => { st with d }.say s!"ok {d.contains (st.hn a) (st.h b)}"
  | ["content", t] =>
    match (d.get (st.hn t)).content with
    | some c => { st with d, hs := st.hs.push c }.say "ok"
    | none => { st with d }.say "ok null"
  | ["setattr", e, q, v] => withErr st (d.setAttribute (st.hn e) (unhex q) (unhex v))
  | ["byid", n, s] =>
    { st with d }.say (match d.getElementById (st.hn n) (unhex s) with
      | some k => match st.hs.findIdx? (· == k) with
        | some i => s!"ok {i}"
        | none => "ok unnamed"
      | none => "ok null")
  | ["end"] => finish { st with d }
  | _ => { st with d }.say ("unknown " ++ " ".intercalate ws)

end Harness.Dom

open Harness.Dom in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["ops", file] =>
    let txt ← IO.FS.readFile file
    let mut st : St := {}
    for l in txt.splitOn "\n" do
      if l.isEmpty then continue
      st := step st (l.splitOn " ")
      if st.out.size > 4096 then
        for o in st.out do IO.println o
        st := { st with out := #[] }
    for o in st.out do IO.println o
    pure (if st.bad == 0 then 0 else 1)
  | _ =>
    IO.eprintln "usage: l4dom ops FILE"
    pure 2
