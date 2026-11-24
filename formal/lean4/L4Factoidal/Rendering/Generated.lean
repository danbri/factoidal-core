import L4Factoidal.Rendering.Style
import L4Factoidal.Unicode.RegexPropData

/-! Generated content: the boxes of `::before` and `::after` (CSS 2.1 §12.1; CSS
Pseudo-Elements 4 §4.1).

A pseudo-element is laid out as a child of its originating element: first for `::before`,
last for `::after`. So the layout needs no rule of its own for them: `derive` gives the
tree two more nodes for each one, an element named `::before` or `::after` and a text node
in it, at the end of the node array, and the cascade and the layout run on that tree.

- **No node of the page changes its number** (`derive_keeps`): the page's nodes keep their
  type, name, attributes, data and parent, so every answer by node number stands.
- **Selectors never see the added nodes**: rules match on the page's own tree. A rule
  whose selector ends in a pseudo-element is matched on the originating element
  (`CSS.Rule.before`, `CSS.Rule.after`) and applies to the added element, which inherits
  from the originating element as a child does.
- **A pseudo-element exists only with `content`** (§12.2): one is added only where a rule
  with a `content` declaration matches, and after the cascade the one whose `content`
  computes to `none` or `normal` is `display: none`; the others get their text
  (`Content.text`).
- **Bound** (`derive_size_le`): the tree grows by at most four nodes for each node of the
  page, whatever the sheet says.
- **A page with no such rule pays one pass over its rules** (`used`), and its styles are
  those of `CSS.computeFor` (`styled_unused`). -/
namespace L4Factoidal.Rendering.Generated
open DOM CSS

/-- One pseudo-element to make: its originating element, and which of the two. -/
structure Spot where
  owner : Nat
  before : Bool
  deriving Repr, BEq

/-- The local name of the added element. No parser makes an element of this name. -/
def Spot.name (s : Spot) : String := if s.before then "::before" else "::after"

/-- `d` with the pseudo-element of `s`: an element at `d.size`, child of the originating
element (first or last), and an empty text node at `d.size + 1` in it. -/
def addSpot (d : Dom) (s : Spot) : Dom :=
  let pe := d.size
  let doc := (d.get s.owner).doc
  let element : DOM.Node := {type := .element, ns := some htmlNS, lname := s.name, parent := some s.owner, kids := #[pe+1], doc}
  let text : DOM.Node := {type := .text, parent := some pe, doc}
  {nodes := ((d.nodes.push element).push text).modify s.owner fun n =>
    {n with kids := if s.before then #[pe] ++ n.kids else n.kids.push pe}}

/-- The page's tree with every pseudo-element of `spots`, in that order: the k-th at
`dom.size + 2*k`, its text node next to it. -/
def derive (dom : Dom) (spots : List Spot) : Dom := spots.foldl addSpot dom

/-- The pseudo-elements a page wants, in node order: `wants id` says whether node `id` has
a `::before` and whether it has an `::after`. -/
def spots (size : Nat) (wants : Nat → Bool × Bool) : List Spot :=
  (List.range size).flatMap fun id =>
    (if (wants id).1 then [⟨id,true⟩] else []) ++ (if (wants id).2 then [⟨id,false⟩] else [])

theorem addSpot_size (d : Dom) (s : Spot) : (addSpot d s).size = d.size + 2 := by
  simp [addSpot, Dom.size]

theorem derive_size (dom : Dom) (spots : List Spot) : (derive dom spots).size = dom.size + 2 * spots.length := by
  unfold derive
  induction spots generalizing dom with
  | nil => simp
  | cons s rest ih => rw [List.foldl_cons, ih, addSpot_size, List.length_cons]; omega

private theorem flatMap_length_le {α β : Type} (f : α → List β) (k : Nat) (h : ∀ a, (f a).length ≤ k) :
    ∀ l : List α, (l.flatMap f).length ≤ k * l.length
  | [] => by simp
  | a :: l => by
    have step := flatMap_length_le f k h l
    have one := h a
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [Nat.mul_succ]
    omega

/-- At most two pseudo-elements a node. -/
theorem spots_length_le (size : Nat) (wants : Nat → Bool × Bool) : (spots size wants).length ≤ 2 * size := by
  unfold spots
  have h := flatMap_length_le (fun id => (if (wants id).1 then [(⟨id,true⟩ : Spot)] else []) ++
      (if (wants id).2 then [⟨id,false⟩] else [])) 2
    (by intro a; cases (wants a).1 <;> cases (wants a).2 <;> simp) (List.range size)
  simpa using h

/-- **The derived tree is at most five times the page's**, whatever the sheet says. -/
theorem derive_size_le (dom : Dom) (wants : Nat → Bool × Bool) :
    (derive dom (spots dom.size wants)).size ≤ 5 * dom.size := by
  rw [derive_size]
  have h := spots_length_le dom.size wants
  omega

/-- What `addSpot` keeps of a node of `d`: everything but its list of children. -/
def sameNode (a b : DOM.Node) : Prop :=
  a.type = b.type ∧ a.ns = b.ns ∧ a.lname = b.lname ∧ a.attrs = b.attrs ∧ a.data = b.data ∧ a.parent = b.parent

theorem sameNode_refl (a : DOM.Node) : sameNode a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sameNode_trans {a b c : DOM.Node} (h : sameNode a b) (g : sameNode b c) : sameNode a c :=
  ⟨h.1.trans g.1, h.2.1.trans g.2.1, h.2.2.1.trans g.2.2.1, h.2.2.2.1.trans g.2.2.2.1,
   h.2.2.2.2.1.trans g.2.2.2.2.1, h.2.2.2.2.2.trans g.2.2.2.2.2⟩

theorem addSpot_keeps (d : Dom) (s : Spot) (id : Nat) (h : id < d.size) :
    sameNode ((addSpot d s).get id) (d.get id) := by
  have h' : id < d.nodes.size := h
  unfold addSpot Dom.get
  simp only [Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_modify]
  by_cases own : s.owner = id
  · subst own
    simp [Array.getElem?_push, h', Nat.ne_of_lt h', Nat.ne_of_lt (Nat.lt_succ_of_lt h'), sameNode]
  · simp [own, Array.getElem?_push, h', Nat.ne_of_lt h', Nat.ne_of_lt (Nat.lt_succ_of_lt h'), sameNode]

/-- **The page's nodes keep their numbers and all but their child lists.** -/
theorem derive_keeps (dom : Dom) (spots : List Spot) (id : Nat) (h : id < dom.size) :
    sameNode ((derive dom spots).get id) (dom.get id) := by
  unfold derive
  induction spots generalizing dom with
  | nil => exact sameNode_refl _
  | cons s rest ih =>
    rw [List.foldl_cons]
    exact sameNode_trans (ih (addSpot dom s) (by rw [addSpot_size]; omega)) (addSpot_keeps dom s id h)

/-- The rules for one of the two pseudo-elements, as rules of the originating element. -/
def rulesOf (before : Bool) (rules : List Rule) : List Rule :=
  rules.filterMap fun r =>
    let sels := if before then r.before else r.after
    if sels.isEmpty then none else some {r with selectors := sels, before := [], after := []}

/-- A rule that can make a pseudo-element: it has a `content` declaration. -/
def makesContent (r : Rule) : Bool := r.declarations.any (·.property == "content")

/-- Whether a sheet can make a pseudo-element at all: a `::before` or `::after` with
`content`, or a `::first-letter`. -/
def used (rules : List Rule) : Bool :=
  rules.any fun r => ((!r.before.isEmpty || !r.after.isEmpty) && makesContent r) || !r.firstLetter.isEmpty

/-- Elements that have no pseudo-elements here: replaced elements and controls, whose
content is not their children. -/
def bare : List String :=
  ["img", "br", "hr", "input", "textarea", "select", "canvas", "video", "audio", "iframe", "embed", "object",
   "svg", "math", "head", "style", "script", "title", "meta", "link", "template", "base", "col", "colgroup"]

/-- `l` with the first counter named `name` (the innermost) changed by `f`. -/
def bumpFirst (name : String) (f : Int → Int) : List (String × Int × Nat) → List (String × Int × Nat)
  | [] => []
  | (n, v, o) :: rest => if n == name then (n, f v, o) :: rest else (n, v, o) :: bumpFirst name f rest

private def bumpFirstGo (name : String) (f : Int → Int) :
    List (String × Int × Nat) → List (String × Int × Nat) → List (String × Int × Nat)
  | [], acc => acc.reverse
  | (n, v, o) :: rest, acc =>
    if n == name then acc.reverseAux ((n, f v, o) :: rest)
    else bumpFirstGo name f rest ((n, v, o) :: acc)

private theorem bumpFirstGo_eq (name : String) (f : Int → Int)
    (xs acc : List (String × Int × Nat)) :
    bumpFirstGo name f xs acc = acc.reverse ++ bumpFirst name f xs := by
  induction xs generalizing acc with
  | nil => simp [bumpFirstGo, bumpFirst]
  | cons x rest ih =>
    obtain ⟨n, v, o⟩ := x
    by_cases h : (n == name) = true <;>
      simp [bumpFirstGo, bumpFirst, h, ih, List.append_assoc]

def bumpFirstLoop (name : String) (f : Int → Int) (xs : List (String × Int × Nat)) :=
  bumpFirstGo name f xs []

@[csimp] theorem bumpFirst_eq_loop : @bumpFirst = @bumpFirstLoop := by
  funext name f xs
  simp [bumpFirstLoop, bumpFirstGo_eq]

#print axioms bumpFirst_eq_loop

/-- The `list-item` counter of HTML lists (HTML §15.3.8, CSS Lists 3 §4.5): whether `k` is an
`ol` with the `reversed` attribute. -/
def reversedList (d : Dom) (k : Nat) : Bool :=
  let n := d.get k
  n.type == .element && n.lname == "ol" && hasAttribute n "reversed"

/-- The increments of element `k`: its `counter-increment`, and for an `li` that does not name
`list-item` there, `list-item` by 1 (by -1 in a reversed `ol`). -/
def incrementsOf (d : Dom) (styles : Array Computed) (k : Nat) : List (String × Int) :=
  let n := d.get k
  let own := ((styles[k]?).getD {}).pos.counterIncrement
  if n.type == .element && n.lname == "li" && !own.any (·.1 == "list-item") then
    let step : Int := if (n.parent.map (reversedList d)).getD false then -1 else 1
    own ++ [("list-item", step)]
  else own

/-- The sets of element `k`: its `counter-set`, and for an `li` with an integer `value`
attribute that does not name `list-item` there, `list-item` to that value. -/
def setsOf (d : Dom) (styles : Array Computed) (k : Nat) : List (String × Int) :=
  let n := d.get k
  let own := ((styles[k]?).getD {}).pos.counterSet
  if n.type == .element && n.lname == "li" && !own.any (·.1 == "list-item") then
    match (attrValue n "value").trim.toInt? with
    | some v => own ++ [("list-item", v)]
    | none => own
  else own

/-- The resets of element `k`, with `true` for a `reversed(name)` with no integer: its
`counter-reset`, and for an `ol`, `ul` or `menu` that does not name `list-item` there,
`list-item` (HTML §15.3.8): to `start - 1` (`start + 1` when reversed; no `start` attribute:
0, or the reversed start). -/
def resetsOf (d : Dom) (styles : Array Computed) (k : Nat) : List (String × Int × Bool) :=
  let n := d.get k
  let s := (styles[k]?).getD {}
  let own := s.pos.counterReset.map fun (m, v) => (m, v, s.pos.counterReversed.contains m)
  if n.type == .element && (n.lname == "ol" || n.lname == "ul" || n.lname == "menu") &&
      !own.any (·.1 == "list-item") then
    let rev := reversedList d k
    match (if n.lname == "ol" then (attrValue n "start").trim.toInt? else none) with
    | some v => own ++ [("list-item", if rev then v + 1 else v - 1, false)]
    | none => own ++ [("list-item", 0, rev)]
  else own

/-- The start of a `reversed(name)` counter that element `k` resets with no integer (CSS
Lists 3 §4.4.2): minus the sum of the increments of `name` in its scope (`k`, its
descendants, its later siblings and theirs), minus the last of them, so that the last
element that increments shows minus its increment. The subtrees of other elements that reset
`name` (they count their own) and elements that make no box are left out. At most
`d.size + 1` steps. -/
def reversedStart (d : Dom) (styles : Array Computed) (makesBox : Nat → Bool) (k : Nat) (name : String) : Int := Id.run do
  let later := match (d.get k).parent with
    | some p => ((d.get p).kids.toList.dropWhile (· != k))
    | none => [k]
  let mut pending := later
  let mut sum : Int := 0
  let mut last : Int := 0
  for _ in [0:d.size + 1] do
    match pending with
    | [] => pure ()
    | j :: rest =>
      pending := rest
      let n := d.get j
      let s := (styles[j]?).getD {}
      if n.type == .element && s.display != .none && makesBox j then
        if j != k && (resetsOf d styles j).any (·.1 == name) then pure ()
        else
          for (m, v) in incrementsOf d styles j do
            if m == name then
              sum := sum + v
              last := v
          pending := n.kids.toList ++ pending
  return -(sum + last)

/-- The counters in scope at each node where `record` holds (CSS 2.1 §12.4.1): `d` is walked
in tree order (a `::before` is its element's first child, an `::after` its last). An element
that makes a box (`makesBox`, and not `display: none`) applies its `counter-reset` (a new
counter), then `counter-increment` and `counter-set` (to the innermost counter of the name,
or to a new one at 0 when none is in scope). A counter's scope is the element's parent: it
ends when the parent ends. Each entry: name, value, the node whose end ends it; innermost
first. At most `2 * d.size + 2` steps. -/
def counterScopes (d : Dom) (styles : Array Computed) (makesBox record : Nat → Bool) :
    Array (List (String × Int × Nat)) := Id.run do
  let mut out : Array (List (String × Int × Nat)) := Array.replicate d.size []
  let mut inst : List (String × Int × Nat) := []
  let mut stack : List (Bool × Nat) := [(true, 0)]
  for _ in [0:2 * d.size + 2] do
    match stack with
    | [] => pure ()
    | (enter, k) :: rest =>
      stack := rest
      if !enter then
        inst := inst.filter (·.2.2 != k)
      else
        let n := d.get k
        let s := (styles[k]?).getD {}
        let skip := n.type == .element && (s.display == .none || !makesBox k)
        if !skip && (n.type == .element || n.type == .document || n.type == .fragment) then
          if n.type == .element then
            let owner := n.parent.getD 0
            for (name, v, rev) in resetsOf d styles k do
              let v := if rev then reversedStart d styles makesBox k name else v
              inst := (name, v, owner) :: inst
            for (name, v) in incrementsOf d styles k do
              inst := if inst.any (·.1 == name) then bumpFirst name (· + v) inst else (name, v, owner) :: inst
            for (name, v) in setsOf d styles k do
              inst := if inst.any (·.1 == name) then bumpFirst name (fun _ => v) inst else (name, v, owner) :: inst
            if record k then out := out.set! k inst
          stack := n.kids.toList.map ((true, ·)) ++ [(false, k)] ++ stack
  return out

/-- After the cascade: each pseudo-element whose `content` makes a box gets its text; the
others are `display: none`. `base` is the size of the page's tree; `owners` the spots in
the order `derive` added them. -/
def fill (base : Nat) (owners : Array Spot) (dom : Dom) (styles : Array Computed) : Dom × Array Computed := Id.run do
  let partsOf := fun (k : Nat) => match (styles[k]?).bind (·.pos.content) with
    | some value => match Content.read value with
      | some (.parts ps) => some ps
      | _ => none
    | none => none
  -- counters only when a box shows one (most pages: none)
  let counting := owners.size > 0 && (List.range owners.size).any fun i =>
    ((partsOf (base + 2*i)).getD []).any fun p => match p with
      | .counter .. | .counters .. => true
      | _ => false
  let scopes := if counting then
      counterScopes dom styles (fun k => k < base || (k - base) % 2 == 1 || (partsOf k).isSome) (· ≥ base)
    else #[]
  let mut dom := dom
  let mut styles := styles
  for h : i in [:owners.size] do
    let pe := base + 2*i
    match partsOf pe with
    | some ps =>
      let values := fun (name : String) =>
        (((scopes[pe]?).getD []).filter (·.1 == name)).reverse.map (·.2.1)
      let text := Content.text (attrValue (dom.get owners[i].owner)) (Content.withCounters values ps)
      dom := {nodes := dom.nodes.modify (pe+1) fun n => {n with data := text}}
    | none => styles := styles.modify pe fun s => {s with display := .none}
  return (dom,styles)

/-- The buckets of author rules alone (`RuleIndex.build` has the user agent's too): the
user agent's rules for an element are not rules for its pseudo-elements. -/
def authorIndex (rules : List Rule) : RuleIndex := Id.run do
  let entries := (rules.map fun r => (1,r)).toArray
  let mut b : RuleIndexB := {}
  for h : i in [:entries.size] do
    for sel in entries[i].2.selectors do
      b := b.add sel.bucket i
  return b.finish entries

/-- The buckets of a rule list, built once and then asked for each element: of a page
with no shadow tree, or of one with shadow trees (with the node tree the selectors read). -/
inductive Index where
  | empty
  | flat (ix : RuleIndex)
  | scoped (ix : ScopedIndex) (ts : TreeScope) (authorOnly : Bool)

/-- The buckets of the author rules `rules`. -/
def Index.author (treeScope : Option TreeScope) (rules : List Rule) : Index :=
  if rules.isEmpty then .empty else
  match treeScope with
  | some ts => .scoped (ScopedIndex.build rules) ts true
  | none => .flat (authorIndex rules)

/-- The buckets of `rules` and the user agent's: what `CSS.computeAll` and
`CSS.computeAllIn` match the page's elements with. -/
def Index.all (treeScope : Option TreeScope) (rules : List Rule) : Index :=
  match treeScope with
  | some ts => .scoped (ScopedIndex.build rules) ts false
  | none => .flat (RuleIndex.build rules)

/-- The rules of the index that match element `id` of the page's tree. -/
def Index.matched (ix : Index) (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) (id : Nat) : List Match :=
  match ix with
  | .empty => []
  | .flat ix => ix.matched keys dom id state
  | .scoped ix ts authorOnly =>
    let ms := ix.matched keys ts id state
    if authorOnly then ms.filter (·.1 != 0) else ms

/-- The tree to lay out and the styles of its nodes: the page's tree with its
pseudo-elements, or the page's tree itself and `CSS.computeFor` when the sheet makes none.
`dom` is the tree that is laid out (the flat tree on a page with shadow trees, whose node
tree `treeScope` holds for the selectors).

Cost: a sheet with no pseudo-element rule that has `content` pays one pass over its rules.
Else each element looks once in the buckets of the rules that have `content` (not of the
rules that only style a pseudo-element, such as `*::before{box-sizing:border-box}`), and
the rest is paid for each pseudo-element made. -/
def styledParts (treeScope : Option TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Dom × Array Computed) := do
  -- as `computeFor` does (`CSS.forDocument`): `:has()` and the structural pseudo-classes
  -- worked out once for the document
  let rules := forTree treeScope dom rules
  let tree := match treeScope with
    | some ts => ts.tree
    | none => dom
  let ks := ElemKeys.of tree
  let keys := ks.get tree
  let before := rulesOf true rules
  let after := rulesOf false rules
  let makesBefore := Index.author treeScope (before.filter makesContent)
  let makesAfter := Index.author treeScope (after.filter makesContent)
  -- one look in the buckets for most elements: the rules that make either
  let makesAny := Index.author treeScope (before.filter makesContent ++ after.filter makesContent)
  let wants := fun (id : Nat) =>
    if (makesAny.matched keys dom state id).isEmpty then (false,false) else
    let n := tree.get id
    if n.type != .element || n.ns == some svgNS || bare.contains n.lname then (false,false)
    else (!(makesBefore.matched keys dom state id).isEmpty,!(makesAfter.matched keys dom state id).isEmpty)
  let plan := spots dom.size wants
  -- the rules of the page's own elements
  let own := Index.all treeScope rules
  -- (with the animated values of the element state after the rules of each element, as
  -- `computeFor` has them: `CSS.withAnimated`; a generated box has none)
  if plan.isEmpty then return (dom, ← computeAllWith (withAnimated state (own.matched keys dom state)) dom textScale)
  let owners := plan.toArray
  let derived := derive dom plan
  let beforeOf := Index.author treeScope before
  let afterOf := Index.author treeScope after
  let matchesOf := fun (id : Nat) =>
    if id < dom.size then own.matched keys dom state id
    else if (id - dom.size) % 2 == 1 then []
    else match owners[(id - dom.size) / 2]? with
      | some s => (if s.before then beforeOf else afterOf).matched keys dom state s.owner
      | none => []
  let styles ← computeAllWith (withAnimated state matchesOf) derived textScale
  return fill dom.size owners derived styles

/-! ### `::first-letter` (CSS Pseudo-Elements 4 §2.3; CSS 2.1 §5.12.2)

After the cascade, the first letter of each element that a `::first-letter` rule matches
is put in an element of its own, named `::first-letter`, with the rules of the
pseudo-element; it inherits from the parent of the text it is cut from.

- **The first letter**: the first letter or digit (General_Category L or N) of the first
  text of the element's first line, with the marks that follow it (M), and the
  punctuation (Ps, Pe, Pi, Pf, Po) before and after it. White space before it is dropped.
- **Where it is looked for**: the element's children in tree order, into inline elements
  and block children (and its `::before` text); not into floats, absolutely positioned
  boxes, `display: none`, or atomic boxes (an inline block, a table, a replaced element,
  `br`), where the first line has no first letter here.
- **Only block containers** have one: `block`, `inline-block`, `table-cell`,
  `table-caption`.
- **Nodes**: the page's nodes keep their numbers. The text node the letter is cut from
  loses the letter from its data; the element and its text node are added at the end.
- **Not done**: a first letter in `::marker`, the text scale applied to a size the rule
  sets (a size the letter inherits is scaled), a letter run of a digraph, `initial-letter`. -/

private def hexValue (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55 else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87 else 0)) 0

/-- The code points of General_Category values, as sorted ranges. -/
def categoryRanges (names : List String) : Array (Nat × Nat) :=
  let rs := names.flatMap fun k => match L4Factoidal.Unicode.RegexPropData.gc.find? (·.1 == k) with
    | some (_, t) => if t.isEmpty then [] else (t.splitOn ",").map fun e => match e.splitOn "-" with
        | [a, b] => (hexValue a, hexValue b)
        | _ => (hexValue e, hexValue e)
    | none => []
  rs.toArray.qsort (fun a b => a.1 < b.1)

/-- Whether `c` is in the sorted ranges `rs`: a binary search, at most 64 steps. -/
def inRanges (rs : Array (Nat × Nat)) (c : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := rs.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      let (a, b) := rs[mid]!
      if c < a then hi := mid
      else if c > b then lo := mid + 1
      else return true
  return false

def punctuationRanges : Array (Nat × Nat) := categoryRanges ["Ps", "Pe", "Pi", "Pf", "Po"]
def letterRanges : Array (Nat × Nat) := categoryRanges ["Lu", "Ll", "Lt", "Lm", "Lo", "Nd", "Nl", "No"]
def markRanges : Array (Nat × Nat) := categoryRanges ["Mn", "Mc", "Me"]

/-- The first letter of a text, as the character offsets of its start and end; the
white space before it is not in it. `none`: the text is white space only (look further);
`some none`: the text starts with something that is not a first letter (look no further). -/
def firstLetterRange (text : String) : Option (Option (Nat × Nat)) := Id.run do
  let cs := text.toList.toArray
  let space := fun (c : Char) => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'
  let mut i := 0
  for _ in [0:cs.size] do
    if i < cs.size && space cs[i]! then i := i + 1
  if i ≥ cs.size then return none
  let start := i
  let punct := fun (k : Nat) => k < cs.size && inRanges punctuationRanges cs[k]!.toNat
  for _ in [0:cs.size] do
    if punct i then i := i + 1
  if !(i < cs.size && inRanges letterRanges cs[i]!.toNat) then return some none
  i := i + 1
  for _ in [0:cs.size] do
    if i < cs.size && inRanges markRanges cs[i]!.toNat then i := i + 1
  for _ in [0:cs.size] do
    if punct i then i := i + 1
  return some (some (start, i))

#guard firstLetterRange "  Test" == some (some (2, 3))
#guard firstLetterRange ")T)est" == some (some (0, 3))
#guard firstLetterRange "“A” b" == some (some (0, 3))
#guard firstLetterRange "éx" == some (some (0, 2))
#guard firstLetterRange "   " == none
#guard firstLetterRange "-x" == some none
#guard firstLetterRange "42" == some (some (0, 1))

/-- The text node of an element's first letter, and the letter's character offsets in it,
by the styles of the laid out tree. Children in tree order, depth first, as the first
line would hold them; at most `d.size` steps. -/
def firstLetterText (d : Dom) (styles : Array Computed) (owner : Nat) : Option (Nat × Nat × Nat) := Id.run do
  -- `none` in the list ends a block child: a first letter is not after a block (CSS Pseudo 4 §2.3).
  let mut pending : List (Option Nat) := (d.get owner).kids.toList.map some
  let within (c lo hi : Nat) : Bool := lo <= c && c <= hi
  -- Letters of the cursive scripts join their neighbours; a split would break the shaping
  -- (CSS Text 3 §7.3), so they take no first letter here.
  let cursive (c : Nat) : Bool :=
    within c 0x0600 0x077F || within c 0x07C0 0x07FF || within c 0x0840 0x08FF || within c 0xFB50 0xFDFF ||
    within c 0xFE70 0xFEFE || within c 0x1800 0x18AF || within c 0x1E900 0x1E95F
  for _ in [0:2 * d.size + 2] do
    match pending with
    | [] => return none
    | none :: _ => return none
    | some k :: rest =>
      pending := rest
      let n := d.get k
      if n.type == .text then
        match firstLetterRange n.data with
        | none => pure ()
        | some none => return none
        | some (some (a, b)) =>
          let cs := n.data.toList.toArray
          let ps := n.parent.bind (styles[·]?) |>.getD {}
          -- A preserved line feed before the letter puts it on a later line.
          if (ps.preformatted || ps.preserveSegmentBreaks) && (cs.extract 0 a).any (· == '\n') then return none
          if (cs.extract a b).any (fun c => cursive c.toNat && inRanges letterRanges c.toNat) then return none
          return some (k, a, b)
      else if n.type == .element then
        let s := (styles[k]?).getD {}
        if s.display == .none || s.pos.float != .none || s.pos.position == .absolute || s.pos.position == .fixed then pure ()
        else if bare.contains n.lname || n.ns == some svgNS then return none
        else if s.display == .inline then pending := n.kids.toList.map some ++ pending
        else if s.display == .block then pending := n.kids.toList.map some ++ [none]
        else return none
  return none

/-- The elements that have a first letter, then their letters made elements: `matchesOf id`
are the `::first-letter` rules that match page element `id` (`base` elements). -/
def addFirstLetters (base : Nat) (matchesOf : Nat → List Match) (d : Dom) (styles : Array Computed) :
    Except String (Dom × Array Computed) := do
  let mut d := d
  let mut styles := styles
  for id in [0:base] do
    let ms := matchesOf id
    if ms.isEmpty then continue
    let display := ((styles[id]?).map (·.display)).getD .none
    if !(display == .block || display == .inlineBlock || display == .tableCell || display == .tableCaption) then continue
    match firstLetterText d styles id with
    | none => pure ()
    | some (t, a, b) =>
      let text := d.get t
      let some p := text.parent | continue
      let cs := text.data.toList
      let letter := String.ofList ((cs.drop a).take (b - a))
      let rest := String.ofList (cs.drop b)
      let pe := d.size
      let element : DOM.Node :=
        {type := .element, ns := some htmlNS, lname := "::first-letter", parent := some p, kids := #[pe+1], doc := text.doc}
      let letterNode : DOM.Node := {type := .text, parent := some pe, data := letter, doc := text.doc}
      let nodes := ((d.nodes.push element).push letterNode).modify t fun n => {n with data := rest}
      d := {nodes := nodes.modify p fun n => {n with kids := n.kids.flatMap fun k => if k == t then #[pe, t] else #[k]}}
      let parentStyle := (styles[p]?).getD {}
      let own ← styleOfNode (fun x => if x == pe then ms else []) d pe parentStyle
      let inner ← styleOfNode (fun _ => []) d (pe+1) own
      styles := (styles.push own).push inner
  return (d, styles)

/-- The tree to lay out and the styles of its nodes: `styledParts`, then the first letters
(`addFirstLetters`) when a rule has `::first-letter`. -/
def styled (treeScope : Option TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Dom × Array Computed) := do
  if !used rules then return (dom, ← computeFor treeScope dom rules textScale state)
  let (d, styles) ← styledParts treeScope dom rules textScale state
  if !(rules.any (!·.firstLetter.isEmpty)) then return (d, styles)
  let rules := forTree treeScope dom rules
  let tree := match treeScope with
    | some ts => ts.tree
    | none => dom
  let keys := (ElemKeys.of tree).get tree
  let letters := Index.author treeScope (rules.filterMap fun r =>
    if r.firstLetter.isEmpty then none else some {r with selectors := r.firstLetter, before := [], after := [], firstLetter := []})
  addFirstLetters dom.size (fun id => letters.matched keys dom state id) d styles

/-- **A sheet with no pseudo-element rule that has `content` changes nothing**: the tree
is the page's and the styles are those of `CSS.computeFor`. -/
theorem styled_unused (treeScope : Option TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float)
    (state : ElementState) (h : used rules = false) :
    styled treeScope dom rules textScale state = (computeFor treeScope dom rules textScale state).map fun s => (dom,s) := by
  unfold styled
  simp only [h, Bool.not_false, ↓reduceIte]
  cases computeFor treeScope dom rules textScale state <;> rfl

/-! ### `display: contents` (CSS Display 3 §2.5)

An element with `display: contents` makes no box: its children are laid out as children of
its parent. In the tree that is laid out, the child list of each node has such a child
replaced by that child's own children; the element stays in the node array (its number,
its parent link and its own child list stand: selectors, inheritance and the links of an
anchor follow them), out of reach of the layout. -/

/-- One level: each child that is a `contents` element replaced by its children. -/
def contentsPass (dom : Dom) (contents : Nat → Bool) : Dom :=
  {nodes := dom.nodes.map fun n =>
    if n.kids.any contents then {n with kids := n.kids.flatMap fun k => if contents k then (dom.get k).kids else #[k]}
    else n}

/-- Levels until no child list holds a `contents` element; `fuel` bounds the nesting. -/
def contentsLoop (contents : Nat → Bool) : Nat → Dom → Dom
  | 0, dom => dom
  | fuel+1, dom =>
    if dom.nodes.any (fun n => n.kids.any contents) then contentsLoop contents fuel (contentsPass dom contents) else dom

/-- The tree to lay out with no `display: contents` element in a child list. A page with
none pays one pass over its styles. Nesting deeper than 64 is left as it is (the layout
refuses that depth anyway). -/
def flattenContents (dom : Dom) (styles : Array Computed) : Dom :=
  if !(styles.any fun s => s.pos.contents) then dom
  else contentsLoop (fun k => ((styles[k]?).map (·.pos.contents)).getD false && (dom.get k).type == .element) 64 dom

theorem contentsPass_size (dom : Dom) (contents : Nat → Bool) : (contentsPass dom contents).size = dom.size := by
  simp [contentsPass, Dom.size]

theorem contentsPass_keeps (dom : Dom) (contents : Nat → Bool) (id : Nat) :
    sameNode ((contentsPass dom contents).get id) (dom.get id) := by
  unfold contentsPass Dom.get
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases dom.nodes[id]? with
  | none => exact sameNode_refl _
  | some n =>
    simp only [Option.map_some, Option.getD_some]
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact sameNode_refl _

theorem contentsLoop_size (contents : Nat → Bool) (fuel : Nat) (dom : Dom) :
    (contentsLoop contents fuel dom).size = dom.size := by
  induction fuel generalizing dom with
  | zero => rfl
  | succ fuel ih =>
    unfold contentsLoop
    split
    · rw [ih, contentsPass_size]
    · rfl

theorem contentsLoop_keeps (contents : Nat → Bool) (fuel : Nat) (dom : Dom) (id : Nat) :
    sameNode ((contentsLoop contents fuel dom).get id) (dom.get id) := by
  induction fuel generalizing dom with
  | zero => exact sameNode_refl _
  | succ fuel ih =>
    unfold contentsLoop
    split
    · exact sameNode_trans (ih _) (contentsPass_keeps dom contents id)
    · exact sameNode_refl _

/-- **The nodes keep their numbers and all but their child lists**, and the tree has as
many nodes as before. -/
theorem flattenContents_keeps (dom : Dom) (styles : Array Computed) (id : Nat) :
    (flattenContents dom styles).size = dom.size ∧ sameNode ((flattenContents dom styles).get id) (dom.get id) := by
  unfold flattenContents
  split
  · exact ⟨rfl, sameNode_refl _⟩
  · exact ⟨contentsLoop_size .., contentsLoop_keeps ..⟩

/-- **A page with no `display: contents` is laid out on its own tree.** -/
theorem flattenContents_unused (dom : Dom) (styles : Array Computed)
    (h : (styles.any fun s => s.pos.contents) = false) : flattenContents dom styles = dom := by
  simp [flattenContents, h]

end L4Factoidal.Rendering.Generated
