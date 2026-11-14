/-
L4Factoidal.HTML.Sanitizer — HTML sanitization (HTML §8.6): a sanitizer's configuration and
the algorithms on it, the decisions of what a configuration keeps of parsed markup, and the
built-in constants.

Specification: HTML §8.6.2 "The Sanitizer interface" (the constructor's "configure" and
"canonicalize the configuration", `get()`, and the modifier methods), §8.6.3.1 (a valid
configuration), §8.6.4 "Sanitization algorithms" ("get a sanitizer config from options",
"contains a javascript: URL", "get the sanitizer action for an element name", "check if a
sanitizer config allows an attribute", "remove an element", "remove an attribute", "remove
unsafe", "compare sanitizer items") and §8.6.5 "Sanitization constants" (the built-in safe
baseline and safe default configurations, the navigating and animating URL attribute lists,
the non-replaceable elements).

The page's `Sanitizer` object holds its configuration as the text of `configWire` and asks
here for every method (`answer`, node_query 192); the markup of `setHTML`, `parseHTML` and
the methods that take a `sanitizer` option is parsed and then sanitized here (`plan`,
node_query 193) before a script can see it.

Safety does not rest on the configuration, and it does not rest on the walk. The standard
makes the safe methods safe by changing the configuration ("remove unsafe"); `removeUnsafe`
does that, and the decisions `actionFor` and `keepsAttribute` also refuse the baseline when
`safe` is set, whatever the configuration says. After the walk the tree is read again
(`conforms`), and a root whose content does not conform is emptied: so what a safe method
gives a page holds no baseline element, no event handler content attribute and no script
URL (`safe_output`, proved for every arena and configuration).

Limits: the standard sanitizes while parsing; this sanitizes the parsed fragment, which
differs where the parser would have moved a node the sanitizer removes (adoption agency,
foster parenting). `get()` sorts by code points, not UTF-16 code units.
-/
import L4Factoidal.DOM.Fragment
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.HTML.Sanitizer
open L4Factoidal.DOM

/-- A canonical element or attribute name: a local name and a namespace (`none`: null). -/
structure Name where
  name : String
  ns : Option String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An entry of `elements` (SanitizerElementNamespaceWithAttributes). -/
structure ElemRule where
  el : Name
  attributes : Option (List Name) := none
  removeAttributes : Option (List Name) := none
  deriving Repr, BEq, Inhabited

/-- A SanitizerConfig; `none` is a member that does not exist. -/
structure Config where
  elements : Option (List ElemRule) := none
  removeElements : Option (List Name) := none
  replaceWithChildren : Option (List Name) := none
  pis : Option (List String) := none
  removePis : Option (List String) := none
  attributes : Option (List Name) := none
  removeAttributes : Option (List Name) := none
  comments : Option Bool := none
  dataAttributes : Option Bool := none
  javascriptURLs : Option Bool := none
  deriving Repr, BEq, Inhabited

def html (n : String) : Name := { name := n, ns := some htmlNS }
def svg (n : String) : Name := { name := n, ns := some svgNS }
def mathml (n : String) : Name := { name := n, ns := some mathmlNS }
def attrName (n : String) : Name := { name := n, ns := none }

/-! ## Constants (§8.6.5) -/

/-- The built-in safe baseline configuration's `removeElements`: the HTML elements marked
Unsafe, `frame`, and the SVG `script` and `use` elements. -/
def baselineElements : List Name :=
  [html "base", html "embed", html "frame", html "iframe", html "object", html "script", svg "script", svg "use"]

/-- The event handler content attributes that "remove unsafe" writes into a configuration:
those of GlobalEventHandlers, WindowEventHandlers and DocumentAndElementEventHandlers. -/
def handlerNames : List String :=
  ["abort", "afterprint", "auxclick", "beforeinput", "beforematch", "beforeprint", "beforetoggle", "beforeunload",
   "blur", "cancel", "canplay", "canplaythrough", "change", "click", "close", "command", "contextlost",
   "contextmenu", "contextrestored", "copy", "cuechange", "cut", "dblclick", "drag", "dragend", "dragenter",
   "dragleave", "dragover", "dragstart", "drop", "durationchange", "emptied", "ended", "error", "focus",
   "formdata", "hashchange", "input", "invalid", "keydown", "keypress", "keyup", "languagechange", "load",
   "loadeddata", "loadedmetadata", "loadstart", "message", "messageerror", "mousedown", "mouseenter",
   "mouseleave", "mousemove", "mouseout", "mouseover", "mouseup", "offline", "online", "pagehide",
   "pagereveal", "pageshow", "pageswap", "paste", "pause", "play", "playing", "popstate", "progress",
   "ratechange", "rejectionhandled", "reset", "resize", "scroll", "scrollend", "securitypolicyviolation",
   "seeked", "seeking", "select", "slotchange", "stalled", "storage", "submit", "suspend", "timeupdate",
   "toggle", "unhandledrejection", "unload", "volumechange", "waiting", "webkitanimationend",
   "webkitanimationiteration", "webkitanimationstart", "webkittransitionend", "wheel"].map ("on" ++ ·)

/-- An event handler content attribute, read widely: no namespace, and a name that starts
with "on" and goes on. Every name of `handlerNames` is one (tested), and so is the handler
attribute of an event that a later standard adds. -/
def isEventHandler (a : Name) : Bool := a.ns.isNone && a.name.startsWith "on" && a.name.length > 2

/-- "Contains a javascript: URL": the value parses as a URL with no base, and its scheme is
`javascript`. -/
def javascriptURL (v : String) : Bool :=
  match L4Factoidal.WHATWG.URL.parseUrl v none with
  | some u => u.scheme == "javascript"
  | none => false

/-- The built-in navigating URL attributes list: the element and attribute pairs whose
value a click or a submission navigates to. -/
def navigating (el attr : Name) : Bool :=
  (attr.ns.isNone &&
    ((el == html "a" && attr.name == "href") || (el == html "area" && attr.name == "href") ||
     (el == html "base" && attr.name == "href") ||
     (el == html "form" && attr.name == "action") || (el == html "input" && attr.name == "formaction") ||
     (el == html "button" && attr.name == "formaction") || (el == svg "a" && attr.name == "href"))) ||
  (el == svg "a" && attr.name == "href" && attr.ns == some xlinkNS)

/-- The built-in animating URL attributes list: `attributeName` of the SVG animation elements
that can animate a link's target. -/
def animating (el attr : Name) : Bool :=
  attr.ns.isNone && attr.name == "attributeName" &&
    (el == svg "animate" || el == svg "animateTransform" || el == svg "set")

/-- The built-in non-replaceable elements list. -/
def nonReplaceable : List Name := [html "html", svg "svg", mathml "math"]

/-- A custom data attribute: no namespace and a name that starts with "data-". -/
def isDataAttribute (a : Name) : Bool := a.ns.isNone && a.name.startsWith "data-"

/-! ## Decisions (§8.6.4) -/

/-- A sanitizer action. -/
inductive Action where
  | keep | remove | unwrap
  deriving Repr, DecidableEq, Inhabited

/-- "Get the sanitizer action for an element name". -/
def elementAction (c : Config) (el : Name) : Action :=
  if (c.replaceWithChildren.getD []).contains el then .unwrap
  else match c.elements with
    | some rules => if rules.any (·.el == el) then .keep else .remove
    | none => if (c.removeElements.getD []).contains el then .remove else .keep

/-- The action the walk takes: with `safe`, a baseline element is removed before the
configuration is read. -/
def actionFor (c : Config) (safe : Bool) (el : Name) : Action :=
  if safe && baselineElements.contains el then .remove else elementAction c el

/-- An attribute whose value makes a click, a submission or an animation run script: a
`javascript:` URL in an attribute of the navigating URL attributes list or in `href` of a
MathML element, or an SVG animation of a link's target (the last three steps of "check if a
sanitizer config allows an attribute"). -/
def scriptURL (el attr : Name) (value : String) : Bool :=
  (navigating el attr && javascriptURL value) ||
  (el.ns == some mathmlNS && attr.name == "href" && (attr.ns.isNone || attr.ns == some xlinkNS) && javascriptURL value) ||
  (animating el attr && (value == "href" || value == "xlink:href"))

/-- "Check if a sanitizer config allows an attribute", with `jsURLs` for the
configuration's `javascriptURLs`. -/
def allowsAttribute (c : Config) (jsURLs : Bool) (el attr : Name) (value : String) : Bool :=
  let rule := c.elements.bind fun rules => rules.find? (·.el == el)
  let localRemove := (rule.bind (·.removeAttributes)).getD []
  let localAllow := rule.bind (·.attributes)
  let byLists :=
    if localRemove.contains attr then false
    else match c.attributes with
      | some allowed =>
        allowed.contains attr || (localAllow.getD []).contains attr ||
          (attr.name.startsWith "data-" && attr.ns.isNone && c.dataAttributes == some true)
      | none =>
        match localAllow with
        | some la => la.contains attr
        | none => !(c.removeAttributes.getD []).contains attr
  byLists && (jsURLs || !scriptURL el attr value)

/-- Whether the walk keeps an attribute: with `safe`, an event handler content attribute
never stays and `javascript:` URLs are refused whatever the configuration says. -/
def keepsAttribute (c : Config) (safe : Bool) (el attr : Name) (value : String) : Bool :=
  allowsAttribute c (!safe && c.javascriptURLs == some true) el attr value && !(safe && isEventHandler attr)

/-- "Check if a sanitizer config allows processing instruction target". -/
def allowsPI (c : Config) (target : String) : Bool :=
  match c.pis with
  | some l => l.contains target
  | none => !(c.removePis.getD []).contains target

/-! ## The walk -/

def nameOfNode (x : Node) : Name := { name := x.lname, ns := x.ns }
def nameOfAttr (a : Attr) : Name := { name := a.lname, ns := a.ns }

/-- A change the sanitizer makes to the parsed tree. -/
inductive Step where
  /-- Remove the node (and its subtree) from its parent. -/
  | remove (node : NodeId)
  /-- Put the element's children in its place, and remove it. -/
  | unwrap (node : NodeId)
  /-- Remove an attribute. -/
  | dropAttr (node : NodeId) (ns : Option String) (lname : String)
  deriving Repr, BEq, Inhabited

/-- The steps for the nodes of `work` and their descendants, in tree order. The children of
an element that is replaced come next, so each is decided as a child of the place it moves
to; a removed node's subtree is not looked at. Every round takes one node, so the fuel of
`plan` (the arena's size) is enough. -/
def planGo (c : Config) (safe : Bool) (d : Dom) : Nat → List NodeId → Array Step → Array Step
  | 0, _, out => out
  | _, [], out => out
  | fuel + 1, n :: rest, out =>
    let x := d.get n
    match x.type with
    | .comment => planGo c safe d fuel rest (if c.comments == some true then out else out.push (.remove n))
    | .pi => planGo c safe d fuel rest (if allowsPI c x.lname then out else out.push (.remove n))
    | .element =>
      let el := nameOfNode x
      match actionFor c safe el with
      | .remove => planGo c safe d fuel rest (out.push (.remove n))
      | .unwrap => planGo c safe d fuel (x.kids.toList ++ rest) (out.push (.unwrap n))
      | .keep =>
        let drops := x.attrs.filterMap fun a =>
          if keepsAttribute c safe el (nameOfAttr a) a.value then none else some (Step.dropAttr n a.ns a.lname)
        let inner := (match x.content with | some t => (d.get t).kids.toList | none => []) ++
          (match x.shadow with | some s => (d.get s).kids.toList | none => [])
        planGo c safe d fuel (x.kids.toList ++ inner ++ rest) (out ++ drops)
    | _ => planGo c safe d fuel rest out

/-- The steps that sanitize the children of `root` (a fragment or a document) with the
prepared configuration `c`; `safe` for `setHTML` and `parseHTML`. -/
def plan (d : Dom) (root : NodeId) (c : Config) (safe : Bool) : Array Step :=
  planGo c safe d (d.size + 1) (d.get root).kids.toList #[]

/-- One step on the arena (the page host runs the same steps as recorded commands). -/
def Step.run (d : Dom) : Step → Dom
  | .remove n => d.remove n
  | .unwrap n =>
    match (d.get n).parent with
    | none => d
    | some p =>
      let kids := (d.get n).kids
      let d := d.setNode p fun pn =>
        { pn with kids := pn.kids.foldl (fun out k => if k == n then out ++ kids else out.push k) #[] }
      let d := kids.foldl (fun d k => d.setNode k fun x => { x with parent := some p }) d
      d.setNode n fun x => { x with parent := none, kids := #[] }
  | .dropAttr n ns l => d.setNode n fun x => { x with attrs := x.attrs.filter fun a => !(a.ns == ns && a.lname == l) }

def sanitize (d : Dom) (root : NodeId) (c : Config) (safe : Bool) : Dom :=
  (plan d root c safe).foldl Step.run d

/-! ## The check after the walk

The walk is not trusted for safety. After it, `conforms` reads the tree again and answers
whether every node below the root is one the configuration keeps; `sanitizeChecked` empties
the root when it is not. So what a safe method inserts conforms by construction, whatever
the walk and the commands that ran its steps did (`sanitizeChecked_conforms`). -/

/-- The nodes directly below a node, as a page can reach them: its children, the children
of its template contents, and the children of its shadow root. -/
def below (d : Dom) (n : NodeId) : List NodeId :=
  let x := d.get n
  x.kids.toList ++ (match x.content with | some t => (d.get t).kids.toList | none => []) ++
    (match x.shadow with | some s => (d.get s).kids.toList | none => [])

/-- A node that the configuration keeps as it is: an element with the action "keep" whose
attributes are all kept, a comment or a processing instruction that is allowed, or any
other node. -/
def nodeConforms (c : Config) (safe : Bool) (x : Node) : Bool :=
  match x.type with
  | .element =>
    actionFor c safe (nameOfNode x) == .keep &&
      x.attrs.toList.all fun a => keepsAttribute c safe (nameOfNode x) (nameOfAttr a) a.value
  | .comment => c.comments == some true
  | .pi => allowsPI c x.lname
  | _ => true

/-- Whether the nodes of `work` and everything below them conform. One node a round; when
the fuel ends with nodes left the answer is false, so a true answer has read every node. -/
def conformsGo (c : Config) (safe : Bool) (d : Dom) : Nat → List NodeId → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | fuel + 1, n :: rest =>
    if nodeConforms c safe (d.get n) then conformsGo c safe d fuel (below d n ++ rest) else false

/-- Whether everything below `root` conforms to the configuration. -/
def conforms (d : Dom) (root : NodeId) (c : Config) (safe : Bool) : Bool :=
  conformsGo c safe d (d.size + 1) (below d root)

/-- `root` with nothing below it. -/
def emptied (d : Dom) (root : NodeId) : Dom :=
  d.setNode root fun x => { x with kids := #[], content := none, shadow := none }

/-- Sanitize, check, and empty the root when the check fails. -/
def sanitizeChecked (d : Dom) (root : NodeId) (c : Config) (safe : Bool) : Dom :=
  let d' := sanitize d root c safe
  if conforms d' root c safe then d' else emptied d' root

/-- `m` is `n` or below it, through children, template contents and shadow roots. -/
inductive Reach (d : Dom) : NodeId → NodeId → Prop where
  | here (n : NodeId) : Reach d n n
  | down {n k m : NodeId} : k ∈ below d n → Reach d k m → Reach d n m

/-! ## Configurations (§8.6.2, §8.6.3) -/

/-- "Canonicalize the configuration": the members that default. (The names are canonical
already: the page converts the dictionary and gives each name its namespace.) -/
def canonicalize (c : Config) (permissive : Bool) : Config :=
  let c := if c.elements.isNone && c.removeElements.isNone then { c with removeElements := some [] } else c
  let c := if c.attributes.isNone && c.removeAttributes.isNone then { c with removeAttributes := some [] } else c
  let c := if c.pis.isNone && c.removePis.isNone then
    (if permissive then { c with removePis := some [] } else { c with pis := some [] }) else c
  let c := { c with elements := c.elements.map fun (rules : List ElemRule) => rules.map fun (r : ElemRule) =>
    if r.attributes.isNone && r.removeAttributes.isNone then { r with removeAttributes := some [] } else r }
  let c := if c.comments.isNone then { c with comments := some permissive } else c
  let c := if c.attributes.isSome && c.dataAttributes.isNone then { c with dataAttributes := some permissive } else c
  if c.javascriptURLs.isNone then { c with javascriptURLs := some permissive } else c

def hasDuplicates {α : Type} [BEq α] : List α → Bool
  | [] => false
  | x :: xs => xs.contains x || hasDuplicates xs

def intersects {α : Type} [BEq α] (a b : List α) : Bool := a.any b.contains

/-- A canonical configuration is valid (§8.6.3.1). -/
def valid (c : Config) : Bool :=
  let els := (c.elements.getD []).map (·.el)
  let replace := c.replaceWithChildren.getD []
  !(c.elements.isSome && c.removeElements.isSome) &&
  !(c.pis.isSome && c.removePis.isSome) &&
  !(c.attributes.isSome && c.removeAttributes.isSome) &&
  !hasDuplicates els && !hasDuplicates (c.removeElements.getD []) && !hasDuplicates replace &&
  !hasDuplicates (c.pis.getD []) && !hasDuplicates (c.removePis.getD []) &&
  !hasDuplicates (c.attributes.getD []) && !hasDuplicates (c.removeAttributes.getD []) &&
  !intersects replace nonReplaceable &&
  !intersects els replace && !intersects (c.removeElements.getD []) replace &&
  (match c.attributes with
   | some allowed =>
     (c.elements.getD []).all (fun r =>
       !hasDuplicates (r.attributes.getD []) && !hasDuplicates (r.removeAttributes.getD []) &&
       !intersects allowed (r.attributes.getD []) &&
       (r.removeAttributes.getD []).all allowed.contains &&
       !(c.dataAttributes == some true && (r.attributes.getD []).any isDataAttribute)) &&
     !(c.dataAttributes == some true && allowed.any isDataAttribute)
   | none =>
     (c.elements.getD []).all (fun r =>
       !(r.attributes.isSome && r.removeAttributes.isSome) &&
       !hasDuplicates (r.attributes.getD []) && !hasDuplicates (r.removeAttributes.getD []) &&
       !intersects (c.removeAttributes.getD []) (r.attributes.getD []) &&
       !intersects (c.removeAttributes.getD []) (r.removeAttributes.getD [])) &&
     c.dataAttributes.isNone)

def dedupe {α : Type} [BEq α] (l : List α) : List α :=
  l.foldl (fun out x => if out.contains x then out else out ++ [x]) []

/-- Remove `x` from an optional list: the list, and whether it changed. -/
def without {α : Type} [BEq α] (l : Option (List α)) (x : α) : Option (List α) × Bool :=
  match l with
  | none => (none, false)
  | some xs => (some (xs.filter (· != x)), xs.contains x)

/-- "Remove an element" from a configuration. -/
def removeElement (c : Config) (el : Name) : Config × Bool :=
  let (replace, modified) := without c.replaceWithChildren el
  let c := { c with replaceWithChildren := replace }
  match c.elements with
  | some rules =>
    if rules.any (·.el == el) then ({ c with elements := some (rules.filter (·.el != el)) }, true) else (c, modified)
  | none =>
    let removed := c.removeElements.getD []
    if removed.contains el then (c, modified) else ({ c with removeElements := some (removed ++ [el]) }, true)

/-- "Remove an attribute" from a configuration. -/
def removeAttribute (c : Config) (attr : Name) : Config × Bool :=
  match c.attributes with
  | some allowed =>
    let inRules := (c.elements.getD []).any fun r => (r.attributes.getD []).contains attr
    let rules := c.elements.map fun (rules : List ElemRule) => rules.map fun (r : ElemRule) =>
      { r with attributes := r.attributes.map (·.filter (· != attr)),
               removeAttributes := r.removeAttributes.map (·.filter (· != attr)) }
    ({ c with attributes := some (allowed.filter (· != attr)), elements := rules }, allowed.contains attr || inRules)
  | none =>
    let removed := c.removeAttributes.getD []
    if removed.contains attr then (c, false) else
    let rules := c.elements.map fun (rules : List ElemRule) => rules.map fun (r : ElemRule) =>
      { r with attributes := r.attributes.map (·.filter (· != attr)),
               removeAttributes := r.removeAttributes.map (·.filter (· != attr)) }
    ({ c with elements := rules, removeAttributes := some (removed ++ [attr]) }, true)

/-- The last step of "remove unsafe": `javascriptURLs` is not true afterwards; `r` is
whether anything changed before. -/
def noJavascriptURLs (c : Config) (r : Bool) : Config × Bool :=
  if c.javascriptURLs == some true then ({ c with javascriptURLs := some false }, true) else (c, r)

/-- The list steps of "remove unsafe": every baseline element and every event handler
content attribute is removed from the configuration; whether anything changed. -/
def removeUnsafeLists (c : Config) : Config × Bool :=
  let r1 := baselineElements.foldl
    (fun (acc : Config × Bool) el => let m := removeElement acc.1 el; (m.1, acc.2 || m.2)) (c, false)
  handlerNames.foldl
    (fun (acc : Config × Bool) a => let m := removeAttribute acc.1 (attrName a); (m.1, acc.2 || m.2)) r1

/-- "Remove unsafe": the baseline elements and the event handler content attributes are
removed from the configuration, and `javascriptURLs` is false. -/
def removeUnsafe (c : Config) : Config × Bool :=
  noJavascriptURLs (removeUnsafeLists c).1 (removeUnsafeLists c).2

/-- `allowElement(element)`. -/
def allowElement (c : Config) (e : ElemRule) : Config × Bool :=
  let e := if e.attributes.isNone && e.removeAttributes.isNone then { e with removeAttributes := some [] } else e
  match c.elements with
  | some rules =>
    let (replace, modified) := without c.replaceWithChildren e.el
    let c := { c with replaceWithChildren := replace }
    let e := match c.attributes with
      | some allowed =>
        let e := { e with attributes := e.attributes.map fun l =>
          let l := (dedupe l).filter (!allowed.contains ·)
          if c.dataAttributes == some true then l.filter (!isDataAttribute ·) else l }
        { e with removeAttributes := e.removeAttributes.map fun l => (dedupe l).filter allowed.contains }
      | none =>
        let globalRemove := c.removeAttributes.getD []
        let e := match e.attributes with
          | some l =>
            let l := (dedupe l).filter (!(e.removeAttributes.getD []).contains ·)
            { e with attributes := some (l.filter (!globalRemove.contains ·)), removeAttributes := none }
          | none => e
        { e with removeAttributes := e.removeAttributes.map fun l => (dedupe l).filter (!globalRemove.contains ·) }
    match rules.find? (·.el == e.el) with
    | none => ({ c with elements := some (rules ++ [e]) }, true)
    | some current =>
      if current == e then (c, modified)
      else ({ c with elements := some (rules.filter (·.el != e.el) ++ [e]) }, true)
  | none =>
    if e.attributes.isSome || !(e.removeAttributes.getD []).isEmpty then (c, false) else
    let (replace, modified) := without c.replaceWithChildren e.el
    let c := { c with replaceWithChildren := replace }
    let removed := c.removeElements.getD []
    if !removed.contains e.el then (c, modified)
    else ({ c with removeElements := some (removed.filter (· != e.el)) }, true)

/-- `replaceElementWithChildren(element)`. -/
def replaceElementWithChildren (c : Config) (el : Name) : Config × Bool :=
  if nonReplaceable.contains el then (c, false) else
  let inRules := (c.elements.getD []).any (·.el == el)
  let c := { c with elements := c.elements.map fun (rules : List ElemRule) => rules.filter (·.el != el) }
  let (removed, m2) := without c.removeElements el
  let c := { c with removeElements := removed }
  let replace := c.replaceWithChildren.getD []
  if replace.contains el then (c, inRules || m2) else ({ c with replaceWithChildren := some (replace ++ [el]) }, true)

/-- `allowAttribute(attribute)`. -/
def allowAttribute (c : Config) (attr : Name) : Config × Bool :=
  match c.attributes with
  | some allowed =>
    if c.dataAttributes == some true && isDataAttribute attr then (c, false)
    else if allowed.contains attr then (c, false)
    else
      let rules := c.elements.map fun (rules : List ElemRule) => rules.map fun (r : ElemRule) =>
        { r with attributes := r.attributes.map (·.filter (· != attr)) }
      ({ c with elements := rules, attributes := some (allowed ++ [attr]) }, true)
  | none =>
    let removed := c.removeAttributes.getD []
    if !removed.contains attr then (c, false)
    else ({ c with removeAttributes := some (removed.filter (· != attr)) }, true)

/-- `setComments(allow)`. -/
def setComments (c : Config) (allow : Bool) : Config × Bool :=
  if c.comments == some allow then (c, false) else ({ c with comments := some allow }, true)

/-- `setDataAttributes(allow)`. -/
def setDataAttributes (c : Config) (allow : Bool) : Config × Bool :=
  match c.attributes with
  | none => (c, false)
  | some allowed =>
    if c.dataAttributes == some allow then (c, false) else
    let c := if allow then
      { c with elements := c.elements.map fun (rules : List ElemRule) => rules.map fun (r : ElemRule) =>
                 { r with attributes := r.attributes.map (·.filter (!isDataAttribute ·)) },
               attributes := some (allowed.filter (!isDataAttribute ·)) }
      else c
    ({ c with dataAttributes := some allow }, true)

/-- `setJavascriptURLs(allow)`. -/
def setJavascriptURLs (c : Config) (allow : Bool) : Config × Bool :=
  if c.javascriptURLs == some allow then (c, false) else ({ c with javascriptURLs := some allow }, true)

/-- `allowProcessingInstruction(pi)`. -/
def allowPI (c : Config) (target : String) : Config × Bool :=
  match c.pis with
  | some l => if l.contains target then (c, false) else ({ c with pis := some (l ++ [target]) }, true)
  | none =>
    let removed := c.removePis.getD []
    if removed.contains target then ({ c with removePis := some (removed.filter (· != target)) }, true) else (c, false)

/-- `removeProcessingInstruction(pi)`. -/
def removePI (c : Config) (target : String) : Config × Bool :=
  match c.pis with
  | some l => if l.contains target then ({ c with pis := some (l.filter (· != target)) }, true) else (c, false)
  | none =>
    let removed := c.removePis.getD []
    if removed.contains target then (c, false) else ({ c with removePis := some (removed ++ [target]) }, true)

/-- "Compare sanitizer items": null namespace first, then by namespace, then by name. -/
def nameLt (a b : Name) : Bool :=
  match a.ns, b.ns with
  | none, some _ => true
  | some _, none => false
  | none, none => a.name < b.name
  | some x, some y => x < y || (x == y && a.name < b.name)

def sortNames (l : List Name) : List Name := l.mergeSort fun a b => !nameLt b a

/-- The configuration as `get()` answers it: every list sorted. -/
def sorted (c : Config) : Config :=
  { c with
    elements := c.elements.map fun rules =>
      (rules.map fun r => { r with attributes := r.attributes.map sortNames, removeAttributes := r.removeAttributes.map sortNames }).mergeSort
        fun a b => !nameLt b.el a.el,
    removeElements := c.removeElements.map sortNames,
    replaceWithChildren := c.replaceWithChildren.map sortNames,
    pis := c.pis.map (·.mergeSort fun a b => !(b < a)),
    removePis := c.removePis.map (·.mergeSort fun a b => !(b < a)),
    attributes := c.attributes.map sortNames,
    removeAttributes := c.removeAttributes.map sortNames }

/-! ## The built-in safe default configuration -/

/-- The built-in safe default configuration's elements: a line for each (`h` HTML, `m`
MathML, `s` SVG; then its own attributes), and `*` with the attributes allowed on every
element. -/
def defaultTable : String := "m a href,hreflang,type
m math
m merror
m mfrac
m mi
m mmultiscripts
m mn
m mo fence,form,largeop,lspace,maxsize,minsize,movablelimits,rspace,separator,stretchy,symmetric
m mover accent
m mpadded depth,height,lspace,voffset,width
m mphantom
m mprescripts
m mroot
m mrow
m ms
m mspace depth,height,width
m msqrt
m mstyle
m msub
m msubsup
m msup
m mtable
m mtd columnspan,rowspan
m mtext
m mtr
m munder accentunder
m munderover accent,accentunder
m semantics
h a href,hreflang,type
h abbr
h address
h article
h aside
h b
h bdi
h bdo
h blockquote cite
h body
h br
h caption
h cite
h code
h col span
h colgroup span
h data value
h dd
h del cite,datetime
h dfn
h div
h dl
h dt
h em
h figcaption
h figure
h footer
h h1
h h2
h h3
h h4
h h5
h h6
h head
h header
h hgroup
h hr
h html
h i
h ins cite,datetime
h kbd
h li value
h main
h mark
h menu
h nav
h ol reversed,start,type
h p
h pre
h q
h rp
h rt
h ruby
h s
h samp
h search
h section
h small
h span
h strong
h sub
h sup
h table
h tbody
h td colspan,headers,rowspan
h tfoot
h th abbr,colspan,headers,rowspan,scope
h thead
h time datetime
h title
h tr
h u
h ul
h var
h wbr
s a href,hreflang,type
s circle cx,cy,pathLength,r
s defs
s desc
s ellipse cx,cy,pathLength,rx,ry
s foreignObject height,width,x,y
s g
s line pathLength,x1,x2,y1,y2
s marker markerHeight,markerUnits,markerWidth,orient,preserveAspectRatio,refX,refY,viewBox
s metadata
s path d,pathLength
s polygon pathLength,points
s polyline pathLength,points
s rect height,pathLength,rx,ry,width,x,y
s svg height,preserveAspectRatio,viewBox,width,x,y
s text dx,dy,lengthAdjust,rotate,textLength,x,y
s textPath lengthAdjust,method,path,side,spacing,startOffset,textLength
s title
s tspan dx,dy,lengthAdjust,rotate,textLength,x,y
* alignment-baseline,baseline-shift,clip-path,clip-rule,color,color-interpolation,cursor,dir,direction,display,displaystyle,dominant-baseline,fill,fill-opacity,fill-rule,font-family,font-size,font-size-adjust,font-stretch,font-style,font-variant,font-weight,lang,letter-spacing,marker-end,marker-mid,marker-start,mathbackground,mathcolor,mathsize,opacity,paint-order,pointer-events,scriptlevel,shape-rendering,stop-color,stop-opacity,stroke,stroke-dasharray,stroke-dashoffset,stroke-linecap,stroke-linejoin,stroke-miterlimit,stroke-opacity,stroke-width,text-anchor,text-decoration,text-overflow,text-rendering,title,transform,transform-origin,unicode-bidi,vector-effect,visibility,white-space,word-spacing,writing-mode"

def nsOfLetter (l : String) : Option String :=
  if l == "h" then some htmlNS else if l == "m" then some mathmlNS else if l == "s" then some svgNS else none

def attrNames (s : String) : List Name := (s.splitOn ",").filter (· != "") |>.map attrName

/-- The configuration that `defaultTable` writes: no processing instructions, comments,
data attributes or `javascript:` URLs. -/
def defaultConfig : Config :=
  let lines := (defaultTable.splitOn "\n").map fun l => l.splitOn " "
  { elements := some (lines.filterMap fun
      | [l, name] => if l == "*" then none else some { el := { name, ns := nsOfLetter l }, attributes := some [] }
      | [l, name, attrs] => if l == "*" then none else some { el := { name, ns := nsOfLetter l }, attributes := some (attrNames attrs) }
      | _ => none),
    attributes := some ((lines.filterMap fun
      | ["*", attrs] => some (attrNames attrs)
      | _ => none).flatten),
    pis := some [], comments := some false, dataAttributes := some false, javascriptURLs := some false }

/-! ## Wire forms

A configuration is ten fields separated by U+0001: `elements`, `removeElements`,
`replaceWithChildrenElements`, `processingInstructions`, `removeProcessingInstructions`,
`attributes`, `removeAttributes` (each "0" for a member that does not exist, else "1" and
the items separated by U+0002), `comments`, `dataAttributes`, `javascriptURLs` ("" for a
member that does not exist, else "1" or "0"). A name is the local name, U+0005, the
namespace ("" for null). An entry of `elements` is its name, U+0003, its `attributes`,
U+0003, its `removeAttributes` (each "0", or "1" and the names separated by U+0004). A
processing instruction is U+0005 and its target. In a name, a namespace and a target, a
character below U+0008 is written as U+0007 and the character 64 above it, so the
separators and U+0000 never occur inside one. -/

def esc (s : String) : String :=
  String.ofList (s.toList.flatMap fun c => if c.toNat < 8 then ['\x07', Char.ofNat (c.toNat + 64)] else [c])

def unesc (s : String) : String :=
  let r := s.toList.foldl (fun (acc : List Char × Bool) c =>
    if acc.2 then (Char.ofNat (c.toNat - 64) :: acc.1, false)
    else if c == '\x07' then (acc.1, true) else (c :: acc.1, false)) ([], false)
  String.ofList r.1.reverse

def nameWire (n : Name) : String := esc n.name ++ "\x05" ++ esc (n.ns.getD "")

def parseName (s : String) : Name :=
  match s.splitOn "\x05" with
  | [n, ns] => { name := unesc n, ns := if ns.isEmpty then none else some (unesc ns) }
  | _ => { name := unesc s, ns := none }

def optList (sep : String) (item : String → String) (l : Option (List String)) : String :=
  match l with
  | none => "0"
  | some xs => "1" ++ sep.intercalate (xs.map item)

def parseOptList (sep : String) (s : String) : Option (List String) :=
  if s.startsWith "1" then
    let body := (s.drop 1).toString
    some (if body.isEmpty then [] else body.splitOn sep)
  else none

def namesWire (sep : String) (l : Option (List Name)) : String := optList sep id (l.map (·.map nameWire))
def parseNames (sep : String) (s : String) : Option (List Name) := (parseOptList sep s).map (·.map parseName)

def ruleWire (r : ElemRule) : String :=
  "\x03".intercalate [nameWire r.el, namesWire "\x04" r.attributes, namesWire "\x04" r.removeAttributes]

def parseRule (s : String) : ElemRule :=
  match s.splitOn "\x03" with
  | [n, a, r] => { el := parseName n, attributes := parseNames "\x04" a, removeAttributes := parseNames "\x04" r }
  | _ => { el := parseName s }

def boolWire (b : Option Bool) : String := match b with | none => "" | some true => "1" | some false => "0"
def parseBool (s : String) : Option Bool := if s == "1" then some true else if s == "0" then some false else none

def piWire (l : Option (List String)) : String := optList "\x02" (fun t => "\x05" ++ esc t) l
def parsePis (s : String) : Option (List String) := (parseOptList "\x02" s).map (·.map fun t => unesc (t.drop 1).toString)

def configWire (c : Config) : String :=
  "\x01".intercalate [
    optList "\x02" id (c.elements.map (·.map ruleWire)), namesWire "\x02" c.removeElements,
    namesWire "\x02" c.replaceWithChildren, piWire c.pis, piWire c.removePis,
    namesWire "\x02" c.attributes, namesWire "\x02" c.removeAttributes,
    boolWire c.comments, boolWire c.dataAttributes, boolWire c.javascriptURLs]

/-- The configuration of a wire text; "default" is the built-in safe default configuration. -/
def parseConfig (s : String) : Config :=
  if s == "default" then defaultConfig else
  match s.splitOn "\x01" with
  | [els, removeEls, replace, pis, removePis, attrs, removeAttrs, comments, data, js] =>
    { elements := (parseOptList "\x02" els).map (·.map parseRule), removeElements := parseNames "\x02" removeEls,
      replaceWithChildren := parseNames "\x02" replace, pis := parsePis pis, removePis := parsePis removePis,
      attributes := parseNames "\x02" attrs, removeAttributes := parseNames "\x02" removeAttrs,
      comments := parseBool comments, dataAttributes := parseBool data, javascriptURLs := parseBool js }
  | _ => {}

/-- "Get a sanitizer config from options" for a configuration that exists: configure it
(`none` for a configuration that is not valid: a TypeError), and with `safe` remove what is
unsafe. -/
def prepare (c : Config) (safe : Bool) : Option Config :=
  let c := canonicalize c (!safe)
  if !valid c then none else some (if safe then (removeUnsafe c).1 else c)

/-- node_query 192: the methods of a `Sanitizer` and the preparation of a configuration.
`q` is the method, U+0000, the configuration, and for most U+0000 and an argument:
"default"; "new" (argument "1" for permissive defaults): "K" and the configured
configuration, or "E" when it is not valid; "prepare" (argument "1" for the safe methods):
the same after `prepare`; "get": the sorted configuration; and the modifiers, which answer
"1" or "0" (the method's result) and the configuration after it. -/
def answer (q : String) : String :=
  let result := fun (r : Config × Bool) => (if r.2 then "1" else "0") ++ configWire r.1
  match q.splitOn "\x00" with
  | ["default"] => configWire defaultConfig
  | ["get", w] => configWire (sorted (parseConfig w))
  | ["removeUnsafe", w] => result (removeUnsafe (parseConfig w))
  | [m, w, arg] =>
    let c := parseConfig w
    if m == "new" then
      let c := canonicalize c (arg == "1")
      if valid c then "K" ++ configWire c else "E"
    else if m == "prepare" then
      match prepare c (arg == "1") with
      | some c => "K" ++ configWire c
      | none => "E"
    else if m == "allowElement" then result (allowElement c (parseRule arg))
    else if m == "removeElement" then result (removeElement c (parseName arg))
    else if m == "replaceElementWithChildren" then result (replaceElementWithChildren c (parseName arg))
    else if m == "allowAttribute" then result (allowAttribute c (parseName arg))
    else if m == "removeAttribute" then result (removeAttribute c (parseName arg))
    else if m == "allowProcessingInstruction" then result (allowPI c (unesc arg))
    else if m == "removeProcessingInstruction" then result (removePI c (unesc arg))
    else if m == "setComments" then result (setComments c (arg == "1"))
    else if m == "setDataAttributes" then result (setDataAttributes c (arg == "1"))
    else if m == "setJavascriptURLs" then result (setJavascriptURLs c (arg == "1"))
    else ""
  | _ => ""

/-! ## What is proved -/

/-- Safety (kind: a policy decision refuses what it must). Says: with `safe`, a baseline
element (`script`, `iframe`, `frame`, `object`, `embed`, `base`, SVG `script` and `use`) is
removed whatever the configuration: no allow-list and no replace-with-children entry keeps
it or its children. Does not say: that the walk applies the decision to every node
(tested), nor anything about elements outside the baseline. -/
theorem safe_removes_baseline (c : Config) (el : Name) (h : baselineElements.contains el = true) :
    actionFor c true el = .remove := by
  simp [actionFor, h]

/-- Safety. Says: with `safe`, an event handler content attribute never stays, on any
element and under any configuration. -/
theorem safe_removes_handlers (c : Config) (el attr : Name) (value : String) (h : isEventHandler attr = true) :
    keepsAttribute c true el attr value = false := by
  simp [keepsAttribute, h]

/-- Safety. Says: with `safe`, an attribute whose value is a script URL (`scriptURL`: a
`javascript:` URL in a navigating attribute or a MathML `href`, or an SVG animation of a
link's target) never stays, even under a configuration whose `javascriptURLs` is true. Does
not say: that `javascriptURL` recognises every string a browser would navigate to as script
(it is the URL parser's answer for the scheme). -/
theorem safe_removes_script_urls (c : Config) (el attr : Name) (value : String)
    (h : scriptURL el attr value = true) : keepsAttribute c true el attr value = false := by
  simp [keepsAttribute, allowsAttribute, h]

/-- Says: the same holds in the unsafe methods for a configuration whose `javascriptURLs`
is not true. -/
theorem no_script_urls (c : Config) (el attr : Name) (value : String)
    (hc : c.javascriptURLs ≠ some true) (h : scriptURL el attr value = true) :
    keepsAttribute c false el attr value = false := by
  simp [keepsAttribute, allowsAttribute, hc, h]

/-- Says: a `javascript:` URL in an attribute of the navigating URL attributes list is a
script URL. -/
theorem navigating_javascript_scriptURL (el attr : Name) (value : String)
    (hn : navigating el attr = true) (hj : javascriptURL value = true) : scriptURL el attr value = true := by
  simp [scriptURL, hn, hj]

/-- Says: an element that the configuration replaces with its children is not kept (the
baseline may remove it first). -/
theorem unwrap_not_kept (c : Config) (safe : Bool) (el : Name)
    (h : (c.replaceWithChildren.getD []).contains el = true) : actionFor c safe el ≠ .keep := by
  unfold actionFor elementAction
  split <;> simp_all

/-- Says: `setJavascriptURLs` leaves the configuration with the value asked for, and
answers whether it changed. -/
theorem setJavascriptURLs_sets (c : Config) (allow : Bool) :
    (setJavascriptURLs c allow).1.javascriptURLs = some allow := by
  unfold setJavascriptURLs
  split
  · rename_i h; simpa using h
  · rfl

/-- Says: after "remove unsafe" a configuration does not allow `javascript:` URLs, if it
said anything about them (a configured configuration always does). -/
theorem removeUnsafe_javascriptURLs (c : Config) : (removeUnsafe c).1.javascriptURLs ≠ some true := by
  have key : ∀ (c : Config) (r : Bool), (noJavascriptURLs c r).1.javascriptURLs ≠ some true := by
    intro c r
    unfold noJavascriptURLs
    split
    · simp
    · rename_i h; simpa using h
  unfold removeUnsafe
  exact key _ _

/-! ### The output of the checked sanitizer -/

/-- Says: when `conformsGo` answers true, every node of the work list, and every node below
one (`Reach`), conforms. There is no assumption on the arena: a tree too deep or too large
for the fuel answers false. -/
theorem conformsGo_sound (c : Config) (safe : Bool) (d : Dom) :
    ∀ (fuel : Nat) (work : List NodeId), conformsGo c safe d fuel work = true →
      ∀ n, n ∈ work → ∀ m, Reach d n m → nodeConforms c safe (d.get m) = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro work h n hn
    cases work with
    | nil => cases hn
    | cons w ws => simp [conformsGo] at h
  | succ fuel ih =>
    intro work h n hn m hr
    cases work with
    | nil => cases hn
    | cons w ws =>
      simp only [conformsGo] at h
      split at h
      · rename_i hw
        cases hn with
        | head =>
          cases hr with
          | here => exact hw
          | down hk hr' => exact ih _ h _ (List.mem_append_left _ hk) m hr'
        | tail _ hn' => exact ih _ h n (List.mem_append_right _ hn') m hr
      · cases h

/-- Says: when `conforms` answers true, every node below the root conforms. -/
theorem conforms_sound (d : Dom) (root : NodeId) (c : Config) (safe : Bool) (h : conforms d root c safe = true)
    (k : NodeId) (hk : k ∈ below d root) (m : NodeId) (hr : Reach d k m) :
    nodeConforms c safe (d.get m) = true :=
  conformsGo_sound c safe d _ _ h k hk m hr

/-- Says: an emptied root has nothing below it. -/
theorem below_emptied (d : Dom) (root : NodeId) : below (emptied d root) root = [] := by
  have hk : ((emptied d root).get root).kids = #[] ∧ ((emptied d root).get root).content = none ∧
      ((emptied d root).get root).shadow = none := by
    unfold emptied Dom.get Dom.setNode
    by_cases h : root < d.nodes.size
    · simp [Array.getD, h, Array.getElem_modify]
    · simp [Array.getD, h]
      exact ⟨rfl, rfl, rfl⟩
  unfold below
  simp [hk.1, hk.2.1, hk.2.2]

/-- Safety of the output (kind: a policy decision refuses what it must). Says: what
`sanitizeChecked` leaves below the root conforms to the configuration, for every arena, root
and configuration: either the walk's result passed the check, or the root is empty. Does not
say: that the check never fails on the walk's result (then the page would get nothing; tested),
nor that the page host's recorded commands build the same arena as `sanitize` (the host runs
`conforms` on the arena it has, and empties the root when it fails). -/
theorem sanitizeChecked_conforms (d : Dom) (root : NodeId) (c : Config) (safe : Bool) :
    conforms (sanitizeChecked d root c safe) root c safe = true := by
  unfold sanitizeChecked
  simp only
  split
  · assumption
  · simp [conforms, below_emptied, conformsGo]

/-- Safety, the statement a page relies on. Says: in the output of a safe method, under any
configuration (the default one too), no element at or below a child of the root is a
baseline element (`script`, `iframe`, `frame`, `object`, `embed`, `base`, SVG `script`, SVG
`use`), none has an event handler content attribute, and none has an attribute whose value
is a script URL. -/
theorem safe_output (d : Dom) (root : NodeId) (c : Config) (k m : NodeId)
    (hk : k ∈ below (sanitizeChecked d root c true) root) (hr : Reach (sanitizeChecked d root c true) k m)
    (he : ((sanitizeChecked d root c true).get m).type = .element) :
    let x := (sanitizeChecked d root c true).get m
    baselineElements.contains (nameOfNode x) = false ∧
      ∀ a, a ∈ x.attrs.toList →
        isEventHandler (nameOfAttr a) = false ∧ scriptURL (nameOfNode x) (nameOfAttr a) a.value = false := by
  intro x
  have h := conforms_sound _ root c true (sanitizeChecked_conforms d root c true) k hk m hr
  have hx : nodeConforms c true x = true := h
  have he' : x.type = .element := he
  unfold nodeConforms at hx
  rw [he'] at hx
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hx
  refine ⟨?_, ?_⟩
  · cases hb : baselineElements.contains (nameOfNode x) with
    | false => rfl
    | true => rw [safe_removes_baseline c _ hb] at hx; exact absurd hx.1 (by decide)
  · intro a ha
    have hkeep := hx.2 a ha
    refine ⟨?_, ?_⟩
    · cases hh : isEventHandler (nameOfAttr a) with
      | false => rfl
      | true => rw [safe_removes_handlers c _ _ _ hh] at hkeep; cases hkeep
    · cases hs : scriptURL (nameOfNode x) (nameOfAttr a) a.value with
      | false => rfl
      | true => rw [safe_removes_script_urls c _ _ _ hs] at hkeep; cases hkeep

/-! ## Tests -/

#guard handlerNames.all fun a => isEventHandler (attrName a)
#guard (defaultConfig.elements.getD []).length == 122 && (defaultConfig.attributes.getD []).length == 58
#guard valid defaultConfig && valid (canonicalize {} true) && valid (canonicalize {} false)
#guard elementAction defaultConfig (html "p") == .keep && elementAction defaultConfig (html "script") == .remove
#guard elementAction defaultConfig (html "img") == .remove && elementAction (canonicalize {} true) (html "script") == .keep
#guard actionFor (canonicalize {} true) true (html "script") == .remove &&
  actionFor { replaceWithChildren := some [html "script"] } true (html "script") == .remove
#guard elementAction { replaceWithChildren := some [html "b"] } (html "b") == .unwrap
#guard javascriptURL "javascript:alert(1)" && javascriptURL "  JavaScript:alert(1)" && !javascriptURL "data:text/html,x" && !javascriptURL "nothing"
#guard keepsAttribute defaultConfig true (html "a") (attrName "href") "https://example.com/" &&
  !keepsAttribute defaultConfig true (html "a") (attrName "href") "javascript:alert(1)" &&
  !keepsAttribute defaultConfig true (html "a") (attrName "onclick") "x" &&
  !keepsAttribute defaultConfig true (html "p") (attrName "href") "x" &&
  keepsAttribute defaultConfig true (html "p") (attrName "title") "x"
#guard keepsAttribute (canonicalize {} true) false (html "a") (attrName "onclick") "x" &&
  !keepsAttribute (canonicalize {} true) true (html "a") (attrName "onclick") "x"
#guard keepsAttribute (canonicalize {} true) false (html "a") (attrName "href") "javascript:alert(1)" &&
  !keepsAttribute (canonicalize { javascriptURLs := some false } true) false (html "a") (attrName "href") "javascript:alert(1)" &&
  !keepsAttribute (canonicalize {} true) true (html "a") (attrName "href") "javascript:alert(1)"
#guard !keepsAttribute (canonicalize {} false) false (svg "animate") (attrName "attributeName") "href" &&
  keepsAttribute (canonicalize {} false) false (svg "animateMotion") (attrName "attributeName") "href"
-- the configuration's defaults (sanitizer-config.html)
#guard (canonicalize {} true).comments == some true && (canonicalize {} false).comments == some false
#guard (canonicalize { attributes := some [] } true).dataAttributes == some true && (canonicalize {} true).dataAttributes == none
-- validity
#guard !valid (canonicalize { elements := some [], removeElements := some [] } true)
#guard !valid (canonicalize { attributes := some [], removeAttributes := some [] } true)
#guard !valid (canonicalize { pis := some [], removePis := some [] } true)
#guard !valid (canonicalize { elements := some [{ el := html "abc" }, { el := html "abc" }] } true)
#guard !valid (canonicalize { replaceWithChildren := some [html "html"] } true)
#guard !valid (canonicalize { removeAttributes := some [], dataAttributes := some true } true)
#guard !valid (canonicalize { elements := some [{ el := html "div" }], replaceWithChildren := some [html "div"] } true)
-- the modifiers (sanitizer-config.html "Test elements addition" and the tests after it)
private def afterAll (c : Config) (fs : List (Config → Config × Bool)) : Config := fs.foldl (fun c f => (f c).1) c
#guard ((afterAll (canonicalize { elements := some [{ el := html "div" }, { el := html "p" }] } true)
    [(allowElement · { el := html "bla" }), (removeElement · (html "div")), (replaceElementWithChildren · (html "p"))]).elements.getD []) ==
  [{ el := html "bla", removeAttributes := some [] }]
#guard (afterAll (canonicalize { removeElements := some [html "div", html "p"] } true)
    [(removeElement · (html "bla")), (replaceElementWithChildren · (html "div")), (allowElement · { el := html "p" })]).removeElements ==
  some [html "bla"]
#guard (afterAll (canonicalize { attributes := some [attrName "href", attrName "src"] } true)
    [(allowAttribute · (attrName "id")), (removeAttribute · { name := "href", ns := some "x" }), (removeAttribute · (attrName "href")),
     (removeAttribute · (attrName "src"))]).attributes == some [attrName "id"]
#guard (afterAll (canonicalize { elements := some [{ el := html "div", attributes := some [attrName "href", attrName "src"] }] } true)
    [(allowElement · { el := html "div", attributes := some [attrName "class"] })]).elements ==
  some [{ el := html "div", attributes := some [attrName "class"] }]
#guard (removeUnsafe (canonicalize {} true)).1.removeElements == some baselineElements &&
  ((removeUnsafe (canonicalize {} true)).1.removeAttributes.getD []).length == handlerNames.length &&
  (removeUnsafe (canonicalize {} true)).2 && !(removeUnsafe defaultConfig).2
#guard (setJavascriptURLs defaultConfig false).2 == false && (setJavascriptURLs defaultConfig true).2
-- sorting and the wire
#guard sortNames [html "b", attrName "z", html "a", svg "a"] == [attrName "z", html "a", html "b", svg "a"]
#guard parseConfig (configWire defaultConfig) == defaultConfig
#guard parseConfig (configWire (canonicalize { elements := some [{ el := { name := "a\x02b\x00", ns := some "n\x05" }, attributes := some [attrName ""] }], pis := some ["", "t"] } true)) ==
  canonicalize { elements := some [{ el := { name := "a\x02b\x00", ns := some "n\x05" }, attributes := some [attrName ""] }], pis := some ["", "t"] } true
#guard unesc (esc "a\x00\x01\x07b") == "a\x00\x01\x07b" && !(esc "a\x00\x01\x07b").contains '\x00'
#guard answer ("new\x00" ++ configWire {} ++ "\x001") == "K" ++ configWire (canonicalize {} true)
#guard answer ("new\x00" ++ configWire { elements := some [], removeElements := some [] } ++ "\x001") == "E"
#guard answer ("setComments\x00" ++ configWire defaultConfig ++ "\x001") == "1" ++ configWire { defaultConfig with comments := some true }

private def sanitized (src : String) (c : Config) (safe : Bool) : String :=
  let d : Dom := { nodes := #[{ type := .document }] }
  let (d, frag) := L4Factoidal.DOM.Fragment.parseInto d 0 htmlNS "div" src (shadow := true)
  match prepare c safe with
  | some c =>
    -- the walk's result passes the check, so the checked sanitizer gives the same tree
    if conforms (sanitize d frag c safe) frag c safe then
      L4Factoidal.DOM.Fragment.serialize (sanitizeChecked d frag c safe) frag false
    else "does not conform"
  | none => "invalid"

#guard sanitized "<p onclick=x>a<script>b</script><b>c</b><!--d--></p>" defaultConfig true == "<p>a<b>c</b></p>"
#guard sanitized "<a href='javascript:alert(1)' title=t>x</a><iframe></iframe>" defaultConfig true == "<a title=\"t\">x</a>"
#guard sanitized "<div><span>a<i>b</i></span></div>" { replaceWithChildren := some [html "span"] } false == "<div>a<i>b</i></div>"
#guard sanitized "<p>a</p><img src=x><template><script>1</script><b>t</b></template>" { removeElements := some [html "img"] } true ==
  "<p>a</p><template><b>t</b></template>"
#guard sanitized "<span>html;</span><p>forbidden</p>" { removeElements := some [html "p"] } false == "<span>html;</span>"
#guard sanitized "<b><i>x</i></b><!--c-->" { replaceWithChildren := some [html "b", html "i"] } false == "x<!--c-->"
#guard sanitized "<script>1</script><p onclick=x>y</p>" {} false == "<script>1</script><p onclick=\"x\">y</p>"
#guard sanitized "<p>x</p>" { elements := some [], removeElements := some [] } false == "invalid"

#guard sanitized "<div><template shadowrootmode=open><script>1</script><i onclick=x>s</i></template><svg><use href='#a'/><a href='javascript:1'>t</a></svg></div>" {} true ==
  "<div><svg><a>t</a></svg></div>"
-- the check alone: a tree the walk has not seen does not conform, and an emptied root does
private def parsed (src : String) : Dom × NodeId :=
  L4Factoidal.DOM.Fragment.parseInto { nodes := #[{ type := .document }] } 0 htmlNS "div" src (shadow := true)
#guard !conforms (parsed "<p><script>1</script></p>").1 (parsed "<p><script>1</script></p>").2 (removeUnsafe (canonicalize {} false)).1 true
#guard !conforms (parsed "<p onclick=x></p>").1 (parsed "<p onclick=x></p>").2 (removeUnsafe (canonicalize {} false)).1 true
#guard conforms (emptied (parsed "<p onclick=x></p>").1 (parsed "<p onclick=x></p>").2) (parsed "<p onclick=x></p>").2 defaultConfig true
#guard conforms (parsed "<p title=t>a<b>c</b></p>").1 (parsed "<p title=t>a<b>c</b></p>").2 defaultConfig true

end L4Factoidal.HTML.Sanitizer
