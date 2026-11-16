/-
L4Factoidal.HTML.AccessibleTree — the accessibility tree of a document: what assistive
technology (a screen reader, a switch device, a test driver) is given in place of the
pixels. One entry per exposed node, in tree order, with its depth:

- the role (`AccessibleRole.computedRole`: WAI-ARIA 1.2 §7.1 and HTML-AAM §4),
- the accessible name and description (Accessible Name and Description Computation 1.2 §4.3),
- states and properties (WAI-ARIA 1.2 §6: checked, expanded, disabled, level, the value of
  a range, live region properties, and the others of `props`),
- whether it can take the focus, and its border box when the layout gives one.

What is left out (WAI-ARIA 1.2 §7.1 "Excluding elements from the accessibility tree",
HTML-AAM §3):

- **pruned**, with its whole subtree: `aria-hidden="true"`, `inert`, an element that makes
  no box (`display: none`, which is also `hidden`, `script`, `style`, `head`...), a hidden
  `input`, comments, doctypes;
- **skipped**, its children taking its place: an element with no role, with the role
  `generic` or `none` and nothing that makes it of interest (no focus, no global ARIA
  attribute), an element with `visibility: hidden` (a child may be visible again), text of
  white space only;
- the descendants of a role whose children are presentational (WAI-ARIA 1.2 §5.2.8:
  `button`, `checkbox`, `image`...): the role's name speaks for them.

The tree is a function of the document and of `Env`, the three facts of the layout it
reads. It costs nothing when nobody asks for it: no other module calls it.

Bounds (page-controlled input): the walk is at most `maxDepth` deep (content nested deeper
is left out), visits each node at most once (`seen`), and a name or description in the tree
is at most `maxText` characters.

Proved below (`tree_*`): every entry is a node of the document; no node has two entries;
every entry is reached from the root by a path on which no node is pruned, so nothing of a
pruned subtree is in the tree; every entry is the function `entry` of its node (its role is
the computed role of that node); the depth bound. Proved of the name: the order of the
first steps (`aria-labelledby` before `aria-label` before the host language) and that a
node being computed for an `aria-labelledby` does not follow `aria-labelledby` again (the
cycle guard). Not proved: that every exposed node of the document has an entry (tested).
-/
import L4Factoidal.HTML.AccessibleRole
import L4Factoidal.JSON.Serialize
import Std.Data.HashSet
import Std.Data.HashMap

namespace L4Factoidal.HTML.AccessibleTree
open L4Factoidal.DOM L4Factoidal.DOM.Forms L4Factoidal.HTML.AccessibleRole

/-- A border box in CSS px of the page (rounded). -/
structure Rect where
  x : Int
  y : Int
  w : Nat
  h : Nat
  deriving Repr, BEq, DecidableEq

/-- What the tree reads of the layout. -/
structure Env where
  /-- `false`: the element makes no box (`display: none`). -/
  rendered : NodeId → Bool := fun _ => true
  /-- `false`: `visibility` is `hidden` or `collapse`. -/
  visible : NodeId → Bool := fun _ => true
  /-- The border box of an element that has one. -/
  box : NodeId → Option Rect := fun _ => none

/-- The elements HTML's own style sheet gives no box, read from the markup. -/
def markupUnrendered (d : Dom) (k : NodeId) : Bool :=
  let x := d.get k
  x.type == .element && ((attr? d k "hidden").isSome ||
    (x.ns == some htmlNS && ["script", "style", "template", "noscript", "head", "title", "meta", "link", "base",
      "datalist", "param", "source", "track"].contains x.lname))

/-- The layout facts of a document with no layout: the markup's. -/
def Env.ofMarkup (d : Dom) : Env := { rendered := fun k => !markupUnrendered d k }

/-- The smallest rectangle that holds both. -/
def Rect.union (a b : Rect) : Rect :=
  let x := min a.x b.x
  let y := min a.y b.y
  let right := max (a.x + Int.ofNat a.w) (b.x + Int.ofNat b.w)
  let bottom := max (a.y + Int.ofNat a.h) (b.y + Int.ofNat b.h)
  ⟨x, y, (right - x).toNat, (bottom - y).toNat⟩

/-- `env` with the boxes of a layout: an element's box is the union of its boxes (an inline
element on two lines has two). The index is made once, when the first box is asked for. -/
def Env.withBoxes (env : Env) (boxes : Array (NodeId × Rect)) : Env :=
  let index : Thunk (Std.HashMap NodeId Rect) := Thunk.mk fun _ =>
    boxes.foldl (fun m (k, r) => match m.get? k with
      | some old => m.insert k (old.union r)
      | none => m.insert k r) {}
  { env with box := fun k => index.get.get? k }

/-- Most levels of the tree walk. -/
def maxDepth : Nat := 512
/-- Most characters of a name or a description in the tree. -/
def maxText : Nat := 2000

/-- A node that is left out with its whole subtree. -/
def pruned (d : Dom) (env : Env) (k : NodeId) : Bool :=
  let x := d.get k
  match x.type with
  | .text | .cdata | .document | .fragment => false
  | .element =>
    (attr? d k "aria-hidden").map asciiLower == some "true" || (attr? d k "inert").isSome ||
    !env.rendered k || (isHtml d k ["input"] && inputType d k == "hidden")
  | _ => true

/-- Roles whose children are presentational (WAI-ARIA 1.2 §5.2.8). -/
def childrenPresentational : List String :=
  ["button", "checkbox", "image", "math", "menuitemcheckbox", "menuitemradio", "meter", "option",
   "progressbar", "radio", "scrollbar", "separator", "slider", "switch", "tab"]

/-- Roles that take no name from the author (WAI-ARIA 1.2 §5.2.8.6 "name prohibited"); the
tree gives them none, their text is in their children. -/
def nameProhibited : List String :=
  ["caption", "code", "deletion", "emphasis", "insertion", "paragraph", "none", "strong",
   "subscript", "superscript", "definition", "term", "time", "mark", ""]

inductive Kind where
  | skip | leaf | node
  deriving Repr, BEq, DecidableEq

def whitespaceOnly (s : String) : Bool := s.all isAsciiWs

def hasGlobalAria (d : Dom) (k : NodeId) : Bool :=
  (d.get k).attrs.any fun a => a.ns.isNone && globalAria.contains a.lname

/-- What the walk does with a node that is not pruned. -/
def kind (d : Dom) (env : Env) (k : NodeId) : Kind :=
  let x := d.get k
  match x.type with
  | .text | .cdata =>
    if whitespaceOnly x.data then .skip
    else match x.parent with
      | some p => if env.visible p then .leaf else .skip
      | none => .leaf
  | .element =>
    if !env.visible k then .skip else
    let role := computedRole d k
    if childrenPresentational.contains role then .leaf
    else if role == "" || role == "generic" || role == "none" then
      (if focusable d k || hasGlobalAria d k then .node else .skip)
    else .node
  | _ => .skip

def clip (s : String) : String := if s.length ≤ maxText then s else (s.take maxText).toString

/-- The accessible description (Accessible Name and Description Computation 1.2 §4.3.2,
"description"): the nodes `aria-describedby` names, else `aria-description`, else the
`title` when it is not the name. -/
def accessibleDescription (d : Dom) (k : NodeId) (name : String) : String :=
  let refs := match attr? d k "aria-describedby" with
    | some ids => collapse (" ".intercalate ((tokens' ids).filterMap fun id =>
        (byIdIn d k id).map fun j => textAlternative d (d.size + 1) j true true))
    | none => ""
  if !refs.isEmpty then refs else
  let own := collapse ((attr? d k "aria-description").getD "")
  if !own.isEmpty then own else
  let title := collapse ((attr? d k "title").getD "")
  if title == name then "" else title

/-- The name in the tree: the document's `title` for the root element, none for a role
that takes none, else the accessible name. -/
def treeName (d : Dom) (k : NodeId) (role : String) : String :=
  if nameProhibited.contains role then ""
  else
    let own := accessibleName d k
    if own.isEmpty && isHtml d k ["html"] then
      match (d.treeOrder k).find? (isHtml d · ["title"]) with
      | some t => collapse ((d.textContent t).getD "")
      | none => ""
    else own

def triState (v : Option String) : Option String :=
  match v.map asciiLower with
  | some "true" => some "true"
  | some "false" => some "false"
  | some "mixed" => some "mixed"
  | _ => none

/-- An ARIA attribute given as it is, under the name `key`. -/
def pass (d : Dom) (k : NodeId) (name key : String) : List (String × String) :=
  match attr? d k name with
  | some v => let v := collapse v; if v.isEmpty then [] else [(key, v)]
  | none => []

def rangeRoles : List String := ["slider", "spinbutton", "progressbar", "meter", "scrollbar", "separator"]
def checkRoles : List String := ["checkbox", "radio", "switch", "menuitemcheckbox", "menuitemradio"]

/-- The live region of a role (WAI-ARIA 1.2 §5.3.5: the implicit `aria-live`). -/
def implicitLive (role : String) : Option String :=
  if role == "alert" then some "assertive"
  else if role == "status" || role == "log" then some "polite"
  else if role == "timer" || role == "marquee" then some "off"
  else none

/-- The states and properties of an element with the role `role` (WAI-ARIA 1.2 §6.6, and
HTML-AAM §4 for the states that HTML attributes and form controls give). -/
def props (d : Dom) (k : NodeId) (role : String) : List (String × String) :=
  let x := d.get k
  let bool := fun (b : Bool) => if b then "true" else "false"
  let level : List (String × String) :=
    if role != "heading" then [] else
    match (attr? d k "aria-level").bind (·.trimAscii.toString.toNat?) with
    | some n => if n > 0 then [("level", toString n)] else [("level", "2")]
    | none =>
      let n := if isHtml d k ["h1"] then 1 else if isHtml d k ["h2"] then 2 else if isHtml d k ["h3"] then 3
        else if isHtml d k ["h4"] then 4 else if isHtml d k ["h5"] then 5 else if isHtml d k ["h6"] then 6 else 2
      [("level", toString n)]
  let checked : List (String × String) :=
    if !checkRoles.contains role then [] else
    if isHtml d k ["input"] then [("checked", bool (checkedness d k))]
    else [("checked", (triState (attr? d k "aria-checked")).getD "false")]
  let pressed : List (String × String) := match triState (attr? d k "aria-pressed") with
    | some v => if role == "button" then [("pressed", v)] else []
    | none => []
  let expanded : List (String × String) :=
    if isDetailsSummary d k then
      [("expanded", bool (match x.parent with | some p => (attr? d p "open").isSome | none => false))]
    else match triState (attr? d k "aria-expanded") with
      | some "mixed" | none => []
      | some v => [("expanded", v)]
  let selected : List (String × String) :=
    if isHtml d k ["option"] then [("selected", bool (attr? d k "selected").isSome)]
    else match triState (attr? d k "aria-selected") with
      | some "mixed" | none => []
      | some v => [("selected", v)]
  let disabled := disabledControl d k ||
    (isHtml d k ["option", "optgroup"] && (attr? d k "disabled").isSome) ||
    (attr? d k "aria-disabled").map asciiLower == some "true"
  let flag := fun (native : Bool) (aria key : String) =>
    if native || (attr? d k aria).map asciiLower == some "true" then [(key, "true")] else []
  let control := isHtml d k ["input", "select", "textarea"]
  let invalid : List (String × String) := match (attr? d k "aria-invalid").map asciiLower with
    | some "false" | some "" | none => []
    | some v => [("invalid", v)]
  let range : List (String × String) :=
    if !rangeRoles.contains role then [] else
    let one := fun (aria native key : String) => match attr? d k aria with
      | some v => [(key, collapse v)]
      | none => if isHtml d k ["input", "progress", "meter"] then
          (match attr? d k native with | some v => [(key, collapse v)] | none => []) else []
    one "aria-valuenow" "value" "valuenow" ++ one "aria-valuemin" "min" "valuemin" ++
      one "aria-valuemax" "max" "valuemax" ++ pass d k "aria-valuetext" "valuetext"
  let value : List (String × String) :=
    if isHtml d k ["input"] && ["textbox", "searchbox", "combobox", "spinbutton"].contains role then
      (match attr? d k "value" with | some v => [("value", clip v)] | none => [])
    else if isHtml d k ["textarea"] then [("value", clip ((d.textContent k).getD ""))]
    else []
  let live : List (String × String) := match (attr? d k "aria-live").map asciiLower with
    | some v => if v == "polite" || v == "assertive" || v == "off" then [("live", v)] else []
    | none => match implicitLive role with | some v => [("live", v)] | none => []
  let atomic : List (String × String) := match triState (attr? d k "aria-atomic") with
    | some "true" => [("atomic", "true")]
    | some _ => []
    | none => if role == "alert" || role == "status" then [("atomic", "true")] else []
  let url : List (String × String) := if role == "link" then pass d k "href" "url" else []
  level ++ checked ++ pressed ++ expanded ++ selected ++
    (if disabled then [("disabled", "true")] else []) ++
    flag (control && (attr? d k "required").isSome) "aria-required" "required" ++
    flag (control && (attr? d k "readonly").isSome) "aria-readonly" "readonly" ++
    invalid ++ range ++ value ++ live ++ atomic ++
    flag false "aria-busy" "busy" ++ flag (isHtml d k ["select"] && (attr? d k "multiple").isSome) "aria-multiselectable" "multiselectable" ++
    flag (isHtml d k ["textarea"]) "aria-multiline" "multiline" ++ flag false "aria-modal" "modal" ++
    pass d k "aria-orientation" "orientation" ++ pass d k "aria-haspopup" "haspopup" ++
    pass d k "aria-current" "current" ++ pass d k "aria-sort" "sort" ++
    pass d k "aria-relevant" "relevant" ++ pass d k "aria-posinset" "posinset" ++
    pass d k "aria-setsize" "setsize" ++ pass d k "aria-roledescription" "roledescription" ++
    pass d k "aria-keyshortcuts" "keyshortcuts" ++ pass d k "aria-placeholder" "placeholder" ++
    (if isHtml d k ["input", "textarea"] then pass d k "placeholder" "placeholder" else []) ++
    url ++ (if x.states &&& 8 != 0 then [("focused", "true")] else [])

/-- One node of the accessibility tree. -/
structure Entry where
  /-- Its level in the tree: 0 for the root, one more than its parent's. -/
  depth : Nat
  /-- The node of the document. -/
  id : NodeId
  /-- The computed role; `text` for a text node. -/
  role : String
  name : String := ""
  description : String := ""
  /-- The local name of the element; "" for text. -/
  tag : String := ""
  props : List (String × String) := []
  focusable : Bool := false
  box : Option Rect := none
  deriving Repr, BEq

/-- The entry of node `k` at `depth`. -/
def entry (d : Dom) (env : Env) (depth : Nat) (k : NodeId) : Entry :=
  let x := d.get k
  if x.type != .element then
    { depth, id := k, role := "text", name := clip (collapse x.data),
      box := x.parent.bind env.box }
  else
    let role := computedRole d k
    let name := clip (treeName d k role)
    { depth, id := k, role, name,
      description := clip (accessibleDescription d k name),
      tag := x.lname, props := props d k role, focusable := focusable d k && !disabledControl d k,
      box := env.box k }

/-- The state of the walk: the nodes visited, and the entries made, the last one first. -/
structure St where
  seen : Std.HashSet NodeId := {}
  out : List Entry := []

/-- The walk from node `k` at `depth`: `fuel` levels at most. A node is visited once. -/
def walk (d : Dom) (env : Env) : Nat → Nat → NodeId → St → St
  | 0, _, _, st => st
  | fuel + 1, depth, k, st =>
    if st.seen.contains k = true then st
    else if k < d.size then
      if pruned d env k = true then st
      else match kind d env k with
        | .skip => (d.get k).kids.toList.foldl (fun st c => walk d env fuel depth c st)
            { seen := st.seen.insert k, out := st.out }
        | .leaf => { seen := st.seen.insert k, out := entry d env depth k :: st.out }
        | .node => (d.get k).kids.toList.foldl (fun st c => walk d env fuel (depth + 1) c st)
            { seen := st.seen.insert k, out := entry d env depth k :: st.out }
    else st

/-- The accessibility tree of the document under `root`, in tree order. -/
def tree (d : Dom) (env : Env) (root : NodeId := 0) : List Entry :=
  (walk d env maxDepth 0 root {}).out.reverse

/-! ## What is proved -/

/-- `j` is reached from `k` by a path of children on which no node is pruned (`k` and `j`
included). -/
inductive Reach (d : Dom) (env : Env) : NodeId → NodeId → Prop
  | here (k : NodeId) : pruned d env k = false → Reach d env k k
  | step (k c j : NodeId) : pruned d env k = false → c ∈ (d.get k).kids.toList →
      Reach d env c j → Reach d env k j

/-- Says: the end of such a path is not pruned. -/
theorem Reach.not_pruned {d : Dom} {env : Env} : ∀ {k j : NodeId}, Reach d env k j → pruned d env j = false
  | _, _, .here _ h => h
  | _, _, .step _ _ _ _ _ h => Reach.not_pruned h

/-- Says: the start of such a path is not pruned. -/
theorem Reach.start_not_pruned {d : Dom} {env : Env} : ∀ {k j : NodeId}, Reach d env k j → pruned d env k = false
  | _, _, .here _ h => h
  | _, _, .step _ _ _ h _ _ => h

/-- The invariant of the walk: every entry made is visited, is the entry of a node of the
document that satisfies `P`, at a depth below `bound`; no two entries are of one node. -/
def Inv (d : Dom) (env : Env) (P : NodeId → Prop) (bound : Nat) (st : St) : Prop :=
  (∀ e ∈ st.out, st.seen.contains e.id = true ∧ P e.id ∧ e.id < d.size ∧
    e = entry d env e.depth e.id ∧ e.depth < bound) ∧
  (st.out.map (·.id)).Nodup

theorem foldl_inv {α β : Type} (f : β → α → β) (I : β → Prop) (l : List α)
    (h : ∀ b a, a ∈ l → I b → I (f b a)) : ∀ b, I b → I (l.foldl f b) := by
  induction l with
  | nil => intro b hb; exact hb
  | cons a rest ih =>
    intro b hb
    simp only [List.foldl_cons]
    exact ih (fun b' a' ha' => h b' a' (List.mem_cons_of_mem _ ha')) _ (h b a List.mem_cons_self hb)

theorem entry_id (d : Dom) (env : Env) (depth : Nat) (k : NodeId) : (entry d env depth k).id = k := by
  simp only [entry]; split <;> rfl

theorem entry_depth (d : Dom) (env : Env) (depth : Nat) (k : NodeId) : (entry d env depth k).depth = depth := by
  simp only [entry]; split <;> rfl

/-- The step of the walk that makes an entry keeps the invariant. -/
theorem inv_push (d : Dom) (env : Env) (P : NodeId → Prop) (bound depth : Nat) (k : NodeId) (st : St)
    (hinv : Inv d env P bound st) (hseen : st.seen.contains k = false) (hk : k < d.size) (hP : P k)
    (hd : depth < bound) :
    Inv d env P bound { seen := st.seen.insert k, out := entry d env depth k :: st.out } := by
  unfold Inv at hinv ⊢
  obtain ⟨hall, hnd⟩ := hinv
  refine ⟨?_, ?_⟩
  · intro e he
    have he' : e = entry d env depth k ∨ e ∈ st.out := List.mem_cons.mp he
    rcases he' with heq | he'
    · subst heq
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show (st.seen.insert k).contains (entry d env depth k).id = true
        rw [entry_id]; exact Std.HashSet.contains_insert_self
      · rw [entry_id]; exact hP
      · rw [entry_id]; exact hk
      · rw [entry_id, entry_depth]
      · rw [entry_depth]; exact hd
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hall e he'
      refine ⟨?_, h2, h3, h4, h5⟩
      show (st.seen.insert k).contains e.id = true
      rw [Std.HashSet.contains_insert, h1, Bool.or_true]
  · show (List.map (·.id) (entry d env depth k :: st.out)).Nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hnd⟩
    intro hmem
    obtain ⟨e, he, hid⟩ := List.mem_map.mp hmem
    have hid' : e.id = k := by rw [← entry_id d env depth k]; exact hid
    have h1 := (hall e he).1
    rw [hid', hseen] at h1
    exact absurd h1 (by decide)

/-- The step of the walk that visits a node and makes no entry keeps the invariant. -/
theorem inv_visit (d : Dom) (env : Env) (P : NodeId → Prop) (bound : Nat) (k : NodeId) (st : St)
    (hinv : Inv d env P bound st) : Inv d env P bound { seen := st.seen.insert k, out := st.out } := by
  unfold Inv at hinv ⊢
  obtain ⟨hall, hnd⟩ := hinv
  refine ⟨?_, hnd⟩
  intro e he
  obtain ⟨h1, h2, h3, h4, h5⟩ := hall e he
  refine ⟨?_, h2, h3, h4, h5⟩
  show (st.seen.insert k).contains e.id = true
  rw [Std.HashSet.contains_insert, h1, Bool.or_true]

theorem inv_empty (d : Dom) (env : Env) (P : NodeId → Prop) (bound : Nat) : Inv d env P bound {} := by
  unfold Inv
  refine ⟨?_, ?_⟩
  · intro e he
    have he' : e ∈ ([] : List Entry) := he
    exact absurd he' (List.not_mem_nil)
  · show (List.map (·.id) ([] : List Entry)).Nodup
    exact List.nodup_nil

/-- The walk keeps the invariant, for any property `P` that holds of every node reached
from `k` by an unpruned path. -/
theorem walk_inv (d : Dom) (env : Env) (P : NodeId → Prop) (bound : Nat) :
    ∀ (fuel depth : Nat) (k : NodeId) (st : St), (∀ j, Reach d env k j → P j) → depth + fuel ≤ bound →
      Inv d env P bound st → Inv d env P bound (walk d env fuel depth k st) := by
  intro fuel
  induction fuel with
  | zero => intro depth k st _ _ hinv; simpa only [walk] using hinv
  | succ fuel ih =>
    intro depth k st hP hb hinv
    simp only [walk]
    split
    · exact hinv
    · rename_i hns
      have hseen : st.seen.contains k = false := Bool.eq_false_iff.mpr hns
      split
      · rename_i hk
        split
        · exact hinv
        · rename_i hnp
          have hpr : pruned d env k = false := Bool.eq_false_iff.mpr hnp
          have hkids : ∀ c ∈ (d.get k).kids.toList, ∀ j, Reach d env c j → P j :=
            fun c hc j hr => hP j (Reach.step k c j hpr hc hr)
          split
          · exact foldl_inv _ (Inv d env P bound) _
              (fun b c hc hb' => ih depth c b (hkids c hc) (by omega) hb') _ (inv_visit d env P bound k st hinv)
          · exact inv_push d env P bound depth k st hinv hseen hk (hP k (Reach.here k hpr)) (by omega)
          · exact foldl_inv _ (Inv d env P bound) _
              (fun b c hc hb' => ih (depth + 1) c b (hkids c hc) (by omega) hb') _
              (inv_push d env P bound depth k st hinv hseen hk (hP k (Reach.here k hpr)) (by omega))
      · exact hinv

/-- Everything the invariant says of the finished tree. -/
theorem tree_spec (d : Dom) (env : Env) (root : NodeId) :
    (∀ e ∈ tree d env root, Reach d env root e.id ∧ e.id < d.size ∧ e = entry d env e.depth e.id ∧
      e.depth < maxDepth + 1) ∧ ((tree d env root).map (·.id)).Nodup := by
  have h := walk_inv d env (Reach d env root) (maxDepth + 1) maxDepth 0 root {} (fun _ h => h) (by omega)
    (inv_empty d env _ _)
  unfold Inv at h
  obtain ⟨hall, hnd⟩ := h
  refine ⟨fun e he => ?_, ?_⟩
  · have he' : e ∈ (walk d env maxDepth 0 root {}).out.reverse := he
    obtain ⟨_, h2, h3, h4, h5⟩ := hall e (List.mem_reverse.mp he')
    exact ⟨h2, h3, h4, h5⟩
  · show (List.map (·.id) (walk d env maxDepth 0 root {}).out.reverse).Nodup
    rw [List.map_reverse]
    exact List.nodup_reverse.mpr hnd

/-- Says: every entry of the tree is reached from the root by a path of children on which
no node is pruned. So nothing of a pruned subtree is in the tree: not the pruned node
(`Reach.not_pruned`), and no node below it by this path. -/
theorem tree_reach (d : Dom) (env : Env) (root : NodeId) (e : Entry) (h : e ∈ tree d env root) :
    Reach d env root e.id :=
  ((tree_spec d env root).1 e h).1

/-- Says: no entry of the tree is of a pruned node (`aria-hidden`, `inert`, no box, a
hidden input, a comment). -/
theorem tree_not_pruned (d : Dom) (env : Env) (root : NodeId) (e : Entry) (h : e ∈ tree d env root) :
    pruned d env e.id = false :=
  (tree_reach d env root e h).not_pruned

/-- Says: the tree of a pruned root is empty. -/
theorem tree_pruned_root (d : Dom) (env : Env) (root : NodeId) (h : pruned d env root = true) :
    tree d env root = [] := by
  cases hl : tree d env root with
  | nil => rfl
  | cons e rest =>
    have hr := (tree_reach d env root e (by rw [hl]; exact List.mem_cons_self)).start_not_pruned
    rw [h] at hr
    exact absurd hr (by decide)

/-- Says: every entry is of a node of the document. -/
theorem tree_id_lt (d : Dom) (env : Env) (root : NodeId) (e : Entry) (h : e ∈ tree d env root) :
    e.id < d.size :=
  ((tree_spec d env root).1 e h).2.1

/-- Says: every entry is the function `entry` of its node: its role, name, description,
states and box are those of that node of the document, and of no other. -/
theorem tree_entry (d : Dom) (env : Env) (root : NodeId) (e : Entry) (h : e ∈ tree d env root) :
    e = entry d env e.depth e.id :=
  ((tree_spec d env root).1 e h).2.2.1

/-- Says: the role of an element's entry is its computed role. -/
theorem tree_role (d : Dom) (env : Env) (root : NodeId) (e : Entry) (h : e ∈ tree d env root)
    (he : (d.get e.id).type = .element) : e.role = computedRole d e.id := by
  have h1 : e.role = (entry d env e.depth e.id).role := congrArg Entry.role (tree_entry d env root e h)
  rw [h1]
  simp [entry, he]

/-- Says: no node of the document has two entries. -/
theorem tree_nodup (d : Dom) (env : Env) (root : NodeId) : ((tree d env root).map (·.id)).Nodup :=
  (tree_spec d env root).2

/-- Says: no entry is deeper than `maxDepth`. -/
theorem tree_depth (d : Dom) (env : Env) (root : NodeId) (e : Entry) (h : e ∈ tree d env root) :
    e.depth ≤ maxDepth :=
  Nat.lt_succ_iff.mp ((tree_spec d env root).1 e h).2.2.2

/-! ### The order of the name's steps (Accessible Name and Description Computation 1.2 §4.3.2) -/

/-- Says (step 2B before 2D and later): the text of the nodes that `aria-labelledby` names,
when there is some, is the text alternative, whatever `aria-label`, the host language or
the content give. -/
theorem labelledby_first (d : Dom) (k : NodeId) (fuel : Nat) (content : Bool) (ids : String)
    (he : (d.get k).type = .element) (hh : hiddenEl d k = false)
    (hl : attr? d k "aria-labelledby" = some ids)
    (hne : (collapse (" ".intercalate ((tokens' ids).filterMap fun id =>
        (byIdIn d k id).map fun j => textAlternative d fuel j true true))).isEmpty = false) :
    textAlternative d (fuel + 1) k false content =
      collapse (" ".intercalate ((tokens' ids).filterMap fun id =>
        (byIdIn d k id).map fun j => textAlternative d fuel j true true)) := by
  rw [textAlternative]
  simp [he, hh, hl, hne]

/-- Says (step 2D before 2E and later): with no `aria-labelledby`, a non-empty `aria-label`
is the text alternative of an element whose name is not being taken from the content of
an ancestor. -/
theorem aria_label_second (d : Dom) (k : NodeId) (fuel : Nat) (v : String)
    (he : (d.get k).type = .element) (hh : hiddenEl d k = false)
    (hl : attr? d k "aria-labelledby" = none) (hv : attr? d k "aria-label" = some v)
    (hne : v.trimAscii.toString.isEmpty = false) :
    textAlternative d (fuel + 1) k false false = v.trimAscii.toString := by
  rw [textAlternative]
  simp [he, hh, hl, hv, hne]

/-- Says (the cycle guard, step 2B's "the current node is not already part of an
`aria-labelledby` traversal"): a node computed for an `aria-labelledby` does not follow its
own `aria-labelledby`: its text alternative is the same whatever that attribute names. Two
elements that name each other therefore end: the depth of `aria-labelledby` is one. -/
theorem labelledby_once (d : Dom) (k : NodeId) (fuel : Nat) (content : Bool)
    (he : (d.get k).type = .element) :
    textAlternative d (fuel + 1) k true content =
      (match (if content then embeddedValue d k else none) with
       | some v => v
       | none =>
        let label := (attr? d k "aria-label").map (·.trimAscii.toString) |>.getD ""
        if !label.isEmpty then label else
        let native := hostLabel d fuel k
        if !native.isEmpty then native else
        let fromContent := childrenText d fuel (d.get k).kids.toList
        if !fromContent.isEmpty then fromContent else
        let title := (attr? d k "title").getD ""
        if !title.trimAscii.toString.isEmpty then title else
        let ph := (attr? d k "placeholder").getD ""
        if !ph.trimAscii.toString.isEmpty then ph else (attr? d k "aria-placeholder").getD "") := by
  rw [textAlternative]
  simp [he]

/-! ## The tree as JSON, for a host -/

open L4Factoidal.JSON in
/-- One entry: `id`, `depth`, `role`, and what is not empty of `name`, `description`, `tag`,
`props` (an object), `focusable`, `box` (`[x, y, width, height]`). -/
def Entry.json (e : Entry) : Json :=
  let num := fun (n : Nat) => Json.number (toString n)
  let int := fun (n : Int) => Json.number (toString n)
  .object ([("id", num e.id), ("depth", num e.depth), ("role", .string e.role)] ++
    (if e.name.isEmpty then [] else [("name", .string e.name)]) ++
    (if e.description.isEmpty then [] else [("description", .string e.description)]) ++
    (if e.tag.isEmpty then [] else [("tag", .string e.tag)]) ++
    (if e.props.isEmpty then [] else [("props", .object (e.props.map fun (p, v) => (p, .string v)))]) ++
    (if e.focusable then [("focusable", .bool true)] else []) ++
    (match e.box with
     | some r => [("box", .array [int r.x, int r.y, num r.w, num r.h])]
     | none => []))

open L4Factoidal.JSON in
/-- The tree: `{"nodes": [...]}` in tree order; a host makes the nesting from `depth`. -/
def json (entries : List Entry) : Json := .object [("nodes", .array (entries.map Entry.json))]

/-! ## The tree as a page, for a person (the "Accessibility tree" view) -/

def escapeHtml (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
    else if c == '"' then "&quot;" else String.singleton c)

/-- One line of the view: the role, the name in quotes, then the rest. -/
def Entry.line (e : Entry) : String :=
  let more := (if e.tag.isEmpty then [] else ["<" ++ e.tag ++ ">"]) ++
    (if e.description.isEmpty then [] else ["description: " ++ e.description]) ++
    e.props.map (fun (p, v) => p ++ ": " ++ v) ++ (if e.focusable then ["focusable"] else []) ++
    (match e.box with
     | some r => [s!"box {r.x},{r.y} {r.w}x{r.h}"]
     | none => [])
  "<li style=\"margin-left:" ++ toString (e.depth * 20) ++ "px\"><b>" ++ escapeHtml e.role ++ "</b>" ++
    (if e.name.isEmpty then "" else " <q>" ++ escapeHtml e.name ++ "</q>") ++
    (if more.isEmpty then "" else " <small>" ++ escapeHtml (", ".intercalate more) ++ "</small>") ++ "</li>"

/-- The view page of a tree: an HTML document, one line an entry, indented by depth. -/
def viewPage (about : String) (entries : List Entry) : String :=
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>Accessibility tree</title>" ++
  "<style>body{font-family:sans-serif;margin:16px}ul{list-style:none;padding:0}li{padding:2px 0}" ++
  "small{color:#555}q{color:#053}</style></head><body><h1>Accessibility tree</h1><p>What the built-in engine gives assistive technology for <code>" ++
  escapeHtml about ++ "</code>: " ++ toString entries.length ++ " nodes. Each line is a role, the accessible name, then the element, " ++
  "description, states and border box.</p><ul>" ++ String.join (entries.map Entry.line) ++ "</ul></body></html>"

/-! ## Tests -/

private def treeOf (html : String) : List Entry :=
  let d := DOM.parseHtmlDocument html
  tree d (Env.ofMarkup d)

private def shape (html : String) : List (Nat × String × String) :=
  (treeOf html).map fun e => (e.depth, e.role, e.name)

#guard shape "<title>T</title><h1>Hi</h1><p>One <a href=x>link</a></p>" ==
  [(0, "document", "T"), (1, "heading", "Hi"), (2, "text", "Hi"), (1, "paragraph", ""), (2, "text", "One"),
   (2, "link", "link"), (3, "text", "link")]
-- pruned: aria-hidden, hidden, inert, script, a hidden input; with their subtrees
#guard shape "<div aria-hidden=true><button>a</button></div><p hidden>b</p><div inert><a href=x>c</a></div><script>d</script><input type=hidden><button>e</button>" ==
  [(0, "document", ""), (1, "button", "e")]
-- skipped: generic containers; their children take their place
#guard shape "<div><span><button>a</button></span></div>" == [(0, "document", ""), (1, "button", "a")]
-- a generic that can take the focus, or has a global ARIA attribute, stays
#guard shape "<div tabindex=0>x</div><div aria-label=y>z</div>" ==
  [(0, "document", ""), (1, "generic", ""), (2, "text", "x"), (1, "generic", "y"), (2, "text", "z")]
-- children presentational: no entries below a button or an image
#guard shape "<button><b>Save</b> <img alt=disk></button><img alt=cat>" ==
  [(0, "document", ""), (1, "button", "Save disk"), (1, "image", "cat")]
#guard (treeOf "<h3>x</h3><input type=checkbox checked><details open><summary>s</summary>t</details><button disabled>b</button>").map
    (fun e => (e.role, e.props, e.focusable)) ==
  [("document", [], false), ("heading", [("level", "3")], false), ("text", [], false),
   ("checkbox", [("checked", "true")], true), ("group", [], false), ("", [("expanded", "true")], true), ("text", [], false),
   ("text", [], false), ("button", [("disabled", "true")], false)]
#guard (treeOf "<div role=alert>Saved</div><div role=slider aria-valuenow=3 aria-valuemin=0 aria-valuemax=9 tabindex=0></div><progress value=2 max=4></progress>").map
    (fun e => (e.role, e.props)) ==
  [("document", []), ("alert", [("live", "assertive"), ("atomic", "true")]), ("text", []),
   ("slider", [("valuenow", "3"), ("valuemin", "0"), ("valuemax", "9")]),
   ("progressbar", [("valuenow", "2"), ("valuemax", "4")])]
#guard (treeOf "<span id=d>More help</span><input aria-describedby=d title=tip aria-label=n><button title=t>t</button><a href=u title=why>x</a>").map
    (fun e => (e.role, e.name, e.description)) ==
  [("document", "", ""), ("text", "More help", ""), ("textbox", "n", "More help"), ("button", "t", ""), ("link", "x", "why"),
   ("text", "x", "")]
-- the layout's facts: no box prunes, `visibility: hidden` skips the node and keeps a visible child
#guard (let d := DOM.parseHtmlDocument "<nav><a href=x>one</a></nav><main><p>two</p></main>"
  let nav := ((List.range d.size).find? fun i => (d.get i).lname == "nav").getD 0
  let main := ((List.range d.size).find? fun i => (d.get i).lname == "main").getD 0
  (tree d { rendered := fun k => k != nav, visible := fun k => k != main }).map (fun e => (e.depth, e.role))) ==
  [(0, "document"), (1, "paragraph"), (2, "text")]
#guard (let d := DOM.parseHtmlDocument "<button>a</button>"
  let b := ((List.range d.size).find? fun i => (d.get i).lname == "button").getD 0
  (tree d ((Env.ofMarkup d).withBoxes #[(b, ⟨10, 20, 30, 10⟩), (b, ⟨5, 30, 10, 10⟩)])).map (·.box)) ==
  [none, some ⟨5, 20, 35, 20⟩]
#guard (json [{ depth := 1, id := 4, role := "button", name := "a", tag := "button", focusable := true,
    props := [("pressed", "true")], box := some ⟨1, -2, 3, 4⟩ }]).toString ==
  "{\"nodes\":[{\"id\":4,\"depth\":1,\"role\":\"button\",\"name\":\"a\",\"tag\":\"button\",\"props\":{\"pressed\":\"true\"},\"focusable\":true,\"box\":[1,-2,3,4]}]}"
#guard ((viewPage "x" (treeOf "<button>a&lt;</button>")).splitOn "<li").length == 3

end L4Factoidal.HTML.AccessibleTree
