import L4Factoidal.Rendering.Style

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

/-- Whether a sheet can make a pseudo-element at all. -/
def used (rules : List Rule) : Bool :=
  rules.any fun r => (!r.before.isEmpty || !r.after.isEmpty) && makesContent r

/-- Elements that have no pseudo-elements here: replaced elements and controls, whose
content is not their children. -/
def bare : List String :=
  ["img", "br", "hr", "input", "textarea", "select", "canvas", "video", "audio", "iframe", "embed", "object",
   "svg", "math", "head", "style", "script", "title", "meta", "link", "template", "base", "col", "colgroup"]

/-- After the cascade: each pseudo-element whose `content` makes a box gets its text; the
others are `display: none`. `base` is the size of the page's tree; `owners` the spots in
the order `derive` added them. -/
def fill (base : Nat) (owners : Array Spot) (dom : Dom) (styles : Array Computed) : Dom × Array Computed := Id.run do
  let mut dom := dom
  let mut styles := styles
  for h : i in [:owners.size] do
    let pe := base + 2*i
    let parts := match (styles[pe]?).bind (·.pos.content) with
      | some value => match Content.read value with
        | some (.parts ps) => some ps
        | _ => none
      | none => none
    match parts with
    | some ps =>
      let text := Content.text (attrValue (dom.get owners[i].owner)) ps
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
def styled (treeScope : Option TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Dom × Array Computed) := do
  if !used rules then return (dom, ← computeFor treeScope dom rules textScale state)
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
