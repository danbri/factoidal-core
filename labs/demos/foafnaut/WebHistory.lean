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

/-- Command numbers of the tab, find, scroll and stop commands (issue 1268). -/
def newTabCommand : Nat := 10
def closeTabCommand : Nat := 11
def reopenTabCommand : Nat := 20
/-- Tab 1 to 8 is 21 to 28; 29 is the last tab, as Command-9 in the common browsers. -/
def selectTabCommand (n : Nat) : Nat := 20+n
def lastTabCommand : Nat := 29
def nextTabCommand : Nat := 30
def previousTabCommand : Nat := 31
def findCommand : Nat := 32
def pageDownCommand : Nat := 33
def pageUpCommand : Nat := 34
def topCommand : Nat := 35
def bottomCommand : Nat := 36
def lineDownCommand : Nat := 37
def lineUpCommand : Nat := 38
def stopCommand : Nat := 39
/-- The console tab (`foafnaut:console`): Option-Command-J, as Safari and Chrome on macOS;
Control-Alt-J elsewhere (Control-Shift-J belongs to the host browser on the Hub). -/
def consoleCommand : Nat := 40
/-- About Foafnaut (the app menu): `about:foafnaut` in a new tab (issue 416). -/
def aboutCommand : Nat := 41
/-- Find Next and Find Previous: Command-G and Shift-Command-G, as the common browsers. -/
def findNextCommand : Nat := 42
def findPreviousCommand : Nat := 43
/-- File > Open File… (Command-O) and Save Page As… (Command-S), on a host with files. -/
def openFileCommand : Nat := 44
def savePageCommand : Nat := 45

/-- Keys that the common desktop browsers (Safari, Chrome, Firefox, Edge) share, for
one platform: `primary` is Command on macOS and Control elsewhere. -/
private def shared (p primary : String) : List (String × String × String × Nat) :=
  [(p,primary,"=",1),(p,primary,"+",1),(p,primary,"-",2),(p,primary,"_",2),(p,"shift+"++primary,"+",1),(p,"shift+"++primary,"_",2),
   (p,primary,"0",3),(p,primary,"c",4),(p,primary,"a",5),(p,primary,"r",reloadCommand),
   (p,"shift+"++primary,"r",reloadCommand),
   (p,primary,"x",15),(p,primary,"v",14),(p,primary,"z",16),(p,"shift+"++primary,"z",17),
   (p,primary,"p",18),(p,primary,"l",9),(p,primary,"t",newTabCommand),(p,primary,"w",closeTabCommand),
   (p,"shift+"++primary,"t",reopenTabCommand),(p,primary,"f",findCommand),
   (p,primary,"g",findNextCommand),(p,"shift+"++primary,"g",findPreviousCommand)] ++
  ((List.range 8).map fun i => (p,primary,toString (i+1),selectTabCommand (i+1))) ++
  [(p,primary,"9",lastTabCommand),
   (p,"control","Tab",nextTabCommand),(p,"shift+control","Tab",previousTabCommand),
   (p,"","Space",pageDownCommand),(p,"shift","Space",pageUpCommand),
   (p,"","PageDown",pageDownCommand),(p,"","PageUp",pageUpCommand),
   (p,"","Home",topCommand),(p,"","End",bottomCommand),
   (p,"","ArrowDown",lineDownCommand),(p,"","ArrowUp",lineUpCommand),
   (p,"","Escape",stopCommand)]

/-- Platform, modifier, key, command. Key names are those of `KeyboardEvent.key`
(UI Events KeyboardEvent key Values), with "Space" for " ". A modifier is "" or the
names "shift", "control", "alt", "command" joined by "+" in that order
(`modifierName`). On macOS AppKit matches the keys with Command through the menu, and
sends the others (`pageKey`) to this table. A host with no menu reads it all. -/
def keyTable : List (String × String × String × Nat) :=
  [("mac","command","ArrowLeft",backCommand),("mac","command","ArrowRight",forwardCommand),
   ("mac","command","[",backCommand),("mac","command","]",forwardCommand),
   -- Safari and Chrome: Shift-Command-[ and ] change tab; Command-Up and Down go to the ends.
   ("mac","shift+command","{",previousTabCommand),("mac","shift+command","}",nextTabCommand),
   ("mac","command","ArrowUp",topCommand),("mac","command","ArrowDown",bottomCommand),
   ("mac","command",".",stopCommand),("mac","alt+command","j",consoleCommand),
   ("mac","command","o",openFileCommand),("mac","command","s",savePageCommand)] ++ shared "mac" "command" ++
  [("other","alt","ArrowLeft",backCommand),("other","alt","ArrowRight",forwardCommand),
   ("other","control","y",17),("other","","F5",reloadCommand),("other","control","F5",reloadCommand),
   ("other","control","PageDown",nextTabCommand),("other","control","PageUp",previousTabCommand),
   ("other","control","Home",topCommand),("other","control","End",bottomCommand),
   ("other","control+alt","j",consoleCommand)] ++ shared "other" "control"

/-- The modifier name of `keyTable` for the bits that the window library sends:
1 Shift, 2 Command, 4 Option (alt), 8 Control. -/
def modifierName (bits : Nat) : String :=
  "+".intercalate ((if bits % 2 == 1 then ["shift"] else []) ++ (if bits / 8 % 2 == 1 then ["control"] else []) ++
    (if bits / 4 % 2 == 1 then ["alt"] else []) ++ (if bits / 2 % 2 == 1 then ["command"] else []))

/-- `KeyboardEvent.key` names of the macOS virtual key codes that the table uses. -/
def macKeyName : Nat → Option String
  | 49 => some "Space" | 116 => some "PageUp" | 121 => some "PageDown" | 115 => some "Home"
  | 119 => some "End" | 125 => some "ArrowDown" | 126 => some "ArrowUp" | 123 => some "ArrowLeft"
  | 124 => some "ArrowRight" | 53 => some "Escape" | 48 => some "Tab" | 96 => some "F5"
  | _ => none

/-- The tab that a tab command shows, of `count` tabs with `active` shown. Command-1 to
8 past the last tab do nothing; Command-9 is the last tab; next and previous wrap. -/
def tabTarget (command active count : Nat) : Option Nat :=
  if count == 0 then none
  else if command == lastTabCommand then some (count-1)
  else if command > reopenTabCommand && command < lastTabCommand then
    if command-reopenTabCommand-1 < count then some (command-reopenTabCommand-1) else none
  else if command == nextTabCommand then some ((active+1) % count)
  else if command == previousTabCommand then some ((active+count-1) % count)
  else none

/-- The scroll after a scroll command, in backing pixels: a page is four fifths of the
view, a line is `line`, and the result is between 0 and `limit`. -/
def scrollTarget (command scroll view limit line : Nat) : Option Nat :=
  let page := view*4/5
  let scroll := min scroll limit
  if command == pageDownCommand then some (min limit (scroll+page))
  else if command == pageUpCommand then some (scroll-min scroll page)
  else if command == topCommand then some 0
  else if command == bottomCommand then some limit
  else if command == lineDownCommand then some (min limit (scroll+line))
  else if command == lineUpCommand then some (scroll-min scroll line)
  else none

/-- Command numbers of the edit and print commands (issue 1268). -/
def copyCommand : Nat := 4
def selectAllCommand : Nat := 5
def pasteCommand : Nat := 14
def cutCommand : Nat := 15
def undoCommand : Nat := 16
def redoCommand : Nat := 17
def printCommand : Nat := 18

def keyCommand (platform modifier key : String) : Option Nat :=
  (keyTable.find? (fun (p,m,k,_) => p == platform && m == modifier && k == key)).map (·.2.2.2)

/-- A key that the macOS menu did not take: the key code and modifier bits of the window library. -/
def pageKey (code bits : Nat) : Option Nat :=
  (macKeyName code).bind (keyCommand "mac" (modifierName bits))

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
-- The graph page is an entry like any other: back from it loads the page before it,
-- forward loads it again (issue 1268).
private def toGraph : History := (({} : History).push "file:///pages/index.html").push "foafnaut:graph"
#guard toGraph.canBack && (apply backCommand toGraph).2 == some "file:///pages/index.html"
#guard (apply forwardCommand (apply backCommand toGraph).1).2 == some "foafnaut:graph"
#guard keyCommand "mac" "command" "ArrowLeft" == some 6 && keyCommand "mac" "command" "]" == some 7
#guard keyCommand "mac" "command" "x" == some cutCommand && keyCommand "mac" "shift+command" "z" == some redoCommand
#guard keyCommand "other" "control" "p" == some printCommand && keyCommand "other" "control" "y" == some redoCommand
#guard keyCommand "other" "alt" "ArrowRight" == some 7 && keyCommand "other" "command" "ArrowLeft" == none
-- The cross-browser keys (issue 1268): reload, tabs, find, scrolling and stop.
#guard keyCommand "mac" "command" "r" == some reloadCommand && keyCommand "mac" "shift+command" "r" == some reloadCommand
#guard keyCommand "other" "" "F5" == some reloadCommand && keyCommand "mac" "" "F5" == none
#guard keyCommand "mac" "shift+command" "t" == some reopenTabCommand && keyCommand "other" "shift+control" "t" == some reopenTabCommand
#guard (List.range 8).all fun i => keyCommand "mac" "command" (toString (i+1)) == some (21+i) && keyCommand "other" "control" (toString (i+1)) == some (21+i)
#guard keyCommand "mac" "command" "9" == some lastTabCommand
#guard keyCommand "mac" "control" "Tab" == some nextTabCommand && keyCommand "other" "shift+control" "Tab" == some previousTabCommand
#guard keyCommand "mac" "shift+command" "}" == some nextTabCommand && keyCommand "other" "control" "PageUp" == some previousTabCommand
#guard keyCommand "mac" "command" "f" == some findCommand && keyCommand "other" "control" "f" == some findCommand
#guard keyCommand "mac" "command" "g" == some findNextCommand && keyCommand "mac" "shift+command" "g" == some findPreviousCommand
#guard keyCommand "mac" "command" "o" == some openFileCommand && keyCommand "other" "control" "o" == none
#guard keyCommand "mac" "" "Space" == some pageDownCommand && keyCommand "other" "shift" "Space" == some pageUpCommand
#guard keyCommand "mac" "" "Home" == some topCommand && keyCommand "mac" "command" "ArrowDown" == some bottomCommand
#guard keyCommand "other" "" "Escape" == some stopCommand && keyCommand "mac" "command" "." == some stopCommand
-- One command for each platform, modifier and key: the first match is the only match.
#guard (keyTable.map fun (p,m,k,_) => (p,m,k)).eraseDups.length == keyTable.length
#guard keyCommand "mac" "alt+command" "j" == some consoleCommand && keyCommand "other" "control+alt" "j" == some consoleCommand
#guard modifierName 0 == "" && modifierName 1 == "shift" && modifierName 3 == "shift+command" && modifierName 9 == "shift+control"
#guard pageKey 49 0 == some pageDownCommand && pageKey 49 1 == some pageUpCommand && pageKey 126 2 == some topCommand
#guard pageKey 53 0 == some stopCommand && pageKey 48 8 == some nextTabCommand && pageKey 0 0 == none
#guard tabTarget lastTabCommand 0 5 == some 4 && tabTarget (selectTabCommand 2) 0 5 == some 1
#guard tabTarget (selectTabCommand 6) 0 5 == none && tabTarget nextTabCommand 4 5 == some 0
#guard tabTarget previousTabCommand 0 5 == some 4 && tabTarget nextTabCommand 0 0 == none && tabTarget 5 0 3 == none
#guard scrollTarget pageDownCommand 0 1000 500 80 == some 500 && scrollTarget pageDownCommand 0 1000 5000 80 == some 800
#guard scrollTarget pageUpCommand 300 1000 5000 80 == some 0 && scrollTarget bottomCommand 10 1000 5000 80 == some 5000
#guard scrollTarget topCommand 900 1000 5000 80 == some 0 && scrollTarget lineUpCommand 900 1000 5000 80 == some 820
#guard scrollTarget lineDownCommand 4990 1000 5000 80 == some 5000 && scrollTarget stopCommand 0 1 1 1 == none

end WebHistory
