/-! Session history and the key table of the browser. The host keeps the value
between calls and loads the URL that Lean returns. It makes no history decision. -/
namespace WebHistory

def maxEntries : Nat := 100

structure History where
  entries : Array String := #[]
  index : Nat := 0
  deriving BEq, Repr

def History.current (h : History) : Option String := h.entries[h.index]?
def History.canBack (h : History) : Bool := h.index > 0
def History.canForward (h : History) : Bool := h.index+1 < h.entries.size

/-- A new page removes the forward entries. The same URL again changes nothing,
and over the limit the oldest entry goes. -/
def History.push (h : History) (url : String) : History :=
  if h.current == some url then h else
  let kept := (h.entries.extract 0 (h.index+1)).push url
  let kept := kept.extract (kept.size-maxEntries) kept.size
  {entries:=kept,index:=kept.size-1}

def History.back (h : History) : History := if h.canBack then {h with index:=h.index-1} else h
def History.forward (h : History) : History := if h.canForward then {h with index:=h.index+1} else h

/-- Command numbers of the window. Menus and keys both send them. -/
def backCommand : Nat := 6
def forwardCommand : Nat := 7
def reloadCommand : Nat := 8

/-- The history after a command, and the URL to load. A command at the end of the
list loads nothing. Reload keeps the index. -/
def apply (command : Nat) (h : History) : History × Option String :=
  if command == backCommand then (h.back,if h.canBack then h.back.current else none)
  else if command == forwardCommand then (h.forward,if h.canForward then h.forward.current else none)
  else if command == reloadCommand then (h,h.current)
  else (h,none)

/-- Platform, modifier, key, command. On macOS AppKit matches the same keys through
the menu, so that host does not read this table. A host with no menu reads it. -/
def keyTable : List (String × String × String × Nat) :=
  [("mac","command","ArrowLeft",backCommand),("mac","command","ArrowRight",forwardCommand),
   ("mac","command","[",backCommand),("mac","command","]",forwardCommand),
   ("mac","command","=",1),("mac","command","+",1),("mac","command","-",2),("mac","command","_",2),
   ("mac","command","0",3),("mac","command","c",4),("mac","command","a",5),("mac","command","r",reloadCommand),
   ("other","alt","ArrowLeft",backCommand),("other","alt","ArrowRight",forwardCommand),
   ("other","control","=",1),("other","control","+",1),("other","control","-",2),("other","control","_",2),
   ("other","control","0",3),("other","control","c",4),("other","control","a",5),("other","control","r",reloadCommand)]

def keyCommand (platform modifier key : String) : Option Nat :=
  (keyTable.find? (fun (p,m,k,_) => p == platform && m == modifier && k == key)).map (·.2.2.2)

private def three : History := ((({} : History).push "a").push "b").push "c"
#guard three.entries == #["a","b","c"] && three.index == 2
#guard three.current == some "c" && three.canBack && !three.canForward
#guard (apply backCommand three).2 == some "b" && (apply backCommand three).1.index == 1
#guard ((apply backCommand three).1.canForward)
#guard (apply forwardCommand three).2 == none && (apply forwardCommand three).1 == three
-- A new page after going back removes the forward entries.
#guard (three.back.back.push "d").entries == #["a","d"]
#guard !(three.back.push "d").canForward
-- Reload keeps the place in the list, and loads the entry there.
#guard (apply reloadCommand three.back).1 == three.back && (apply reloadCommand three.back).2 == some "b"
#guard three.push "c" == three
#guard (apply backCommand ({} : History)).2 == none && (apply reloadCommand ({} : History)).2 == none
#guard ((List.range 150).foldl (fun h i => h.push (toString i)) ({} : History)).entries.size == maxEntries
#guard ((List.range 150).foldl (fun h i => h.push (toString i)) ({} : History)).current == some "149"
#guard keyCommand "mac" "command" "ArrowLeft" == some 6 && keyCommand "mac" "command" "]" == some 7
#guard keyCommand "other" "alt" "ArrowRight" == some 7 && keyCommand "other" "command" "ArrowLeft" == none

end WebHistory
