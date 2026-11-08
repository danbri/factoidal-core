import L4Factoidal.WasmVM.Hosts.Dom
import L4Factoidal.DOM.OfHtml

/-!
# Compacted page commands replay to the same arena

`Hosts.Dom.addCommand` keeps one write per attribute and per character data: a write
takes the place of the last write of the same one since the last command that reads
them (`cloneNode`, `normalize`). These checks record each command of a sequence as the
host does (the arena after the command is `Command.apply`), and compare the replay of
the compacted list with the replay of the whole sequence, node by node.
-/
namespace L4Factoidal.WasmVM.Tests.DomCommands
open L4Factoidal.WasmVM.Hosts.Dom L4Factoidal.DOM

/-- Record `c` as the host does; a command the arena refuses is skipped, as the host
records nothing for it. -/
def record (s : State) (c : Command) : State :=
  match c.apply s.dom with
  | .ok d => (addCommand s c d).1
  | .error _ => s

def replay (d : Dom) (cs : List Command) : Option Dom :=
  cs.foldlM (fun d c => (c.apply d).toOption) d

def same (a b : Option Dom) : Bool :=
  match a, b with
  | some a, some b => toString (repr a.nodes) == toString (repr b.nodes)
  | _, _ => false

/-- The compacted replay equals the whole replay; the answer also gives the list's size. -/
def check (html : String) (cs : List Command) : Bool × Nat :=
  let d := parseHtmlDocument html
  let s := cs.foldl record ({ dom := d } : State)
  (same (replay d s.commands.toList) (replay d cs) && same (some s.dom) (replay d s.commands.toList),
   s.commands.size)

def page := "<!doctype html><body><svg><circle id=a cx=1></circle><circle id=b></circle></svg><p id=t>x</p></body>"

def dom0 := parseHtmlDocument page
def A := (dom0.getElementById 0 "a").getD 0
def B := (dom0.getElementById 0 "b").getD 0
def P := (dom0.getElementById 0 "t").getD 0
def T := ((dom0.get P).kids[0]?).getD 0
def N := dom0.size
#guard A != 0 && B != 0 && P != 0 && T != 0

def frames (n : Nat) : List Command :=
  (List.range n).flatMap fun i =>
    [.setAttribute A "transform" s!"translate({i} 0)", .setAttribute B "transform" s!"translate(0 {i})",
     .setTextContent T s!"frame {i}"]

-- 300 frames of three writes: three commands.
#guard check page (frames 300) == (true, 3)
-- A new attribute keeps its place: `fill` after `transform`, as first written.
#guard check page (frames 2 ++ [.setAttribute A "fill" "red"] ++ frames 2 ++ [.setAttribute A "fill" "blue"]) == (true, 4)
-- Names that may be one attribute: `Fill` and `fill` on an HTML element are one attribute.
#guard (check page [.setAttribute P "title" "a", .setAttribute P "TITLE" "b", .setAttribute P "title" "c"]).1
-- A removal between two writes keeps all three.
#guard check page [.setAttribute A "fill" "a", .removeAttribute A "fill", .setAttribute A "fill" "b"] == (true, 3)
-- A clone reads the attribute: the write before it stays before it.
#guard check page [.setAttribute A "fill" "a", .cloneNode A false N, .setAttribute A "fill" "b"] == (true, 3)
-- Text data written, a node made, written again: the node numbers do not move.
#guard check page [.setTextContent T "a", .createElement "b" N, .setTextContent T "c", .appendChild P N] == (true, 3)
-- `textContent` of an element makes a node each time: never compacted.
#guard check page [.setTextContent P "a", .setTextContent P "b"] == (true, 2)
-- A namespaced write may be the same attribute: no write moves past it.
#guard check page [.setAttribute A "x" "1", .setAttributeNS A "" "x" "2", .setAttribute A "x" "3"] == (true, 3)
#guard check page [.setAttribute A "x" "1", .removeAttributeNS A "" "x", .setAttribute A "x" "3"] == (true, 3)
-- Normalize reads the data.
#guard check page [.setTextContent T "", .normalize P, .setTextContent T "z"] == (true, 3)

end L4Factoidal.WasmVM.Tests.DomCommands
