/-
L4Factoidal.XForms.Model — the XForms 1.1 processing model as pure
functions: `step : Model → Event → Model × List Output`.

Parts (XForms 1.1 section in brackets):
  * the form: the host document flattened to a table of elements, with
    the XForms and XML Events attributes read off it;
  * instance data [3.3.2] as XPath 1.0 data model documents, with node
    replacement by address;
  * binds [3.3.4, 6.1]: nested `bind` elements with `nodeset`
    expressions and the model item properties `type`, `readonly`,
    `required`, `relevant`, `calculate`, `constraint`;
  * rebuild, recalculate, revalidate, refresh [4.3.1 to 4.3.4]: the
    dependency graph over `calculate` nodes is built from the read sets
    of evaluation and ordered by `DepGraph.topoSort`;
  * the view model [8, 9]: one record per form control instance (value,
    label, bound node, relevant / readonly / required / valid), with
    `group`, `switch` / `case` and `repeat`;
  * events [4] and actions [10]: a work list processed by a loop with
    fuel. `dispatch` puts the event's handlers in front of the rest of
    the running action, so delivery is synchronous without a stack
    frame per event. The outermost handler ends with the deferred
    update [10];
  * outputs: messages, the log of dispatched events, fatal errors,
    `load` requests, focus changes.

Not done here (reported as `Output.unsupported`, never as a result):
submission [11]; `insert` / `delete` of attribute nodes; schema-defined
types; `itemset` / `copy`; the effect of `insert` and `delete` on
repeat indexes [9.3.6].
-/
import L4Factoidal.XForms.Eval
import L4Factoidal.XForms.DepGraph
import L4Factoidal.XML.Parser
import L4Factoidal.XSD.Lexical

namespace L4Factoidal.XForms.Engine

open L4Factoidal.XML
open L4Factoidal.XPath
open L4Factoidal.XPath.Full

def xfNs : String := "http://www.w3.org/2002/xforms"
def evNs : String := "http://www.w3.org/2001/xml-events"
def xsNs : String := "http://www.w3.org/2001/XMLSchema"

def nsLookup (sc : List (String × String)) (p : String) : String :=
  ((sc.find? (·.1 == p)).map (·.2)).getD ""

/-! ## The form: a table of the host document's elements -/

structure El where
  idx : Nat := 0
  parent : Option Nat := none
  /-- The local name of an XForms element; empty for any other element. -/
  name : String := ""
  tag : String := ""
  /-- Attributes as written, XML Events attributes as `ev:<local name>`. -/
  attrs : List (String × String) := []
  kids : List Nat := []
  /-- Namespace declarations in scope (nearest first). -/
  ns : List (String × String) := []
  text : String := ""
  node : Node := .text ""
deriving Inhabited

def El.attr (e : El) (n : String) : Option String := (e.attrs.find? (·.1 == n)).map (·.2)

abbrev FB := StateM (Array El)

/-- Flatten the host document. The first argument bounds the element
    nesting depth. -/
def flatten : Nat → Option Nat → List (String × String) → Node → FB (Option Nat)
  | 0, _, _, _ => pure none
  | f + 1, par, sc, n =>
    match n with
    | .element tag attrs kids => do
      let sc' := attrs.foldl (fun s a =>
        if a.name == "xmlns" then ("", a.value) :: s
        else if a.name.startsWith "xmlns:" then (String.ofList (a.name.toList.drop 6), a.value) :: s
        else s) sc
      let isXF := nsLookup sc' (prefixOf tag) == xfNs
      let attrs' := attrs.filterMap (fun a =>
        if a.name == "xmlns" || a.name.startsWith "xmlns:" then none
        else if prefixOf a.name != "" && nsLookup sc' (prefixOf a.name) == evNs then
          some ("ev:" ++ localOf a.name, a.value)
        else some (a.name, a.value))
      let i ← modifyGet (fun (arr : Array El) => (arr.size, arr.push
        { idx := arr.size, parent := par, name := if isXF then localOf tag else "", tag := tag,
          attrs := attrs', ns := sc', text := nodeText n, node := n }))
      let ks ← kids.foldlM (fun (acc : List Nat) k => do
        match ← flatten f (some i) sc' k with
        | some j => pure (j :: acc)
        | none => pure acc) []
      modify (fun arr => if h : i < arr.size then arr.set i { arr[i] with kids := ks.reverse } else arr)
      pure (some i)
    | _ => pure none

structure Form where
  els : Array El := #[]
deriving Inhabited

def Form.ofNode (n : Node) : Form :=
  { els := (Id.run ((flatten 512 none [] n).run #[])).2 }

def Form.el (fm : Form) (i : Nat) : El := fm.els[i]?.getD default

def Form.byId (fm : Form) (id : String) : Option Nat :=
  (fm.els.toList.find? (fun e => e.attr "id" == some id)).map (·.idx)

def Form.kidsNamed (fm : Form) (e : El) (n : String) : List El :=
  (e.kids.map fm.el).filter (·.name == n)

def Form.ancestorsGo (fm : Form) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, i, acc =>
    match (fm.el i).parent with
    | none => acc
    | some p => fm.ancestorsGo f p (p :: acc)

/-- The ancestors of element `i`, outermost first. -/
def Form.ancestors (fm : Form) (i : Nat) : List Nat := fm.ancestorsGo fm.els.size i []

def Form.models (fm : Form) : List Nat :=
  (fm.els.toList.filter (·.name == "model")).map (·.idx)

/-- Namespace bindings for XPath name tests: an unprefixed name has no
    namespace in XPath 1.0, so the default namespace is left out. -/
def xpNs (el : El) : List (String × String) := el.ns.filter (·.1 != "")

/-! ## Instance data -/

/-- Apply `f` to the child list of the node at a child-index path. -/
def modKids : List Nat → (List Node → List Node) → List Node → List Node
  | [], f, kids => f kids
  | i :: rest, f, kids => kids.zipIdx.map (fun (n, j) =>
      if j == i then
        match n with
        | .element t a cs => Node.element t a (modKids rest f cs)
        | o => o
      else n)

/-- Set the string value of the node at an address: an attribute, or an
    element with no element children (XForms 1.1 §10.2). -/
def setNodeValue (d : Doc) (l : Loc) (v : String) : Doc :=
  match l.slot with
  | some (true, ai) =>
    (match l.path.reverse with
     | [] => d
     | last :: revInit => modKids revInit.reverse (fun kids => kids.zipIdx.map (fun (n, j) =>
         if j == last then
           match n with
           | .element t a cs => Node.element t (a.zipIdx.map (fun (atr, k) =>
               if k == ai then { atr with value := v } else atr)) cs
           | o => o
         else n)) d)
  | _ =>
    modKids l.path (fun kids =>
      if kids.any isElem then kids else (if v == "" then [] else [Node.text v])) d

structure Inst where
  id : String := ""
  model : Nat := 0
  el : Nat := 0
  doc : Doc := []
  orig : Doc := []
deriving Inhabited

/-- The root element of an inline instance, carrying the namespace
    declarations that were in scope in the host document. -/
def inlineRoot (e : El) : Option Node :=
  match e.node with
  | .element _ _ kids =>
    (kids.find? isElem).map (fun r =>
      match r with
      | .element t a cs =>
        let have' := a.map (·.name)
        let seen := e.ns.foldl (fun (acc : List (String × String)) p =>
          if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
        let extra := seen.filterMap (fun (p, u) =>
          let nm := if p == "" then "xmlns" else "xmlns:" ++ p
          if have'.contains nm || p == "xml" then none else some ({ name := nm, value := u } : Attribute))
        Node.element t (a ++ extra) cs
      | o => o)
  | _ => none

/-- Load the instances of every model (§3.3.2: `src` wins over inline
    content, inline content over `resource`). The second component
    lists the links that could not be read. -/
def loadInstances (fm : Form) (res : List (String × String)) : List Inst × List (Nat × String) :=
  let fetch (uri : String) : Option Doc :=
    match res.find? (·.1 == uri) with
    | none => none
    | some (_, content) =>
      match parseXML content with
      | .ok d => some d.children
      | .error _ => none
  fm.models.foldl (fun (acc : List Inst × List (Nat × String)) mi =>
    let mel := fm.el mi
    let rootCount := fun (e : El) => match e.node with
      | .element _ _ kids => (kids.filter isElem).length
      | _ => 0
    let badInline := ((fm.kidsNamed mel "instance").filter (fun e =>
      (e.attr "src").isNone && rootCount e > 1)).map (fun e => (mi, "#" ++ (e.attr "id").getD "instance"))
    let schemaErrs := badInline ++ match mel.attr "schema" with
      | none => []
      | some s => ((splitWs s).filter (fun u => !u.startsWith "#" && !(res.any (·.1 == u)))).map (fun u => (mi, u))
    (fm.kidsNamed mel "instance").foldl (fun (acc : List Inst × List (Nat × String)) e =>
      let id := (e.attr "id").getD ""
      let mk (d : Doc) : Inst := { id := id, model := mi, el := e.idx, doc := d, orig := d }
      match e.attr "src" with
      | some uri =>
        (match fetch uri with
         | some d => (acc.1 ++ [mk d], acc.2)
         | none => (acc.1 ++ [mk []], acc.2 ++ [(mi, uri)]))
      | none =>
        match inlineRoot e with
        | some r => (acc.1 ++ [mk [r]], acc.2)
        | none =>
          match e.attr "resource" with
          | some uri =>
            (match fetch uri with
             | some d => (acc.1 ++ [mk d], acc.2)
             | none => (acc.1 ++ [mk []], acc.2 ++ [(mi, uri)]))
          | none => (acc.1 ++ [mk []], acc.2)) (acc.1, acc.2 ++ schemaErrs)) ([], [])

/-! ## Model item properties -/

structure Mips where
  readonly : Bool := false
  relevant : Bool := true
  required : Bool := false
  constraint : Bool := true
  typeOk : Bool := true
  hasCalc : Bool := false
deriving Inhabited

def emailOk (v : String) : Bool :=
  match v.splitOn "@" with
  | [a, b] => !a.isEmpty && !b.isEmpty && !v.toList.any Char.isWhitespace &&
      !b.startsWith "." && !b.endsWith "." && !a.startsWith "." && !a.endsWith "."
  | _ => false

/-- The `type` model item property (§6.1.1) for the XML Schema built-in
    types and the XForms datatypes (§5.2). A type this function does
    not know counts as satisfied. -/
def typeValid (ns : List (String × String)) (q : String) (v : String) : Bool :=
  let uri := nsLookup ns (prefixOf q)
  let l := localOf q
  if uri == xsNs then (XSD.validLexicalFor .xsd10 l v).getD true
  else if uri == xfNs then
    if l == "listItem" then v != "" && !v.toList.any Char.isWhitespace
    else if l == "listItems" then true
    else if l == "dayTimeDuration" then
      (match parseDur v with
       | some d => d.y == 0 && d.mo == 0
       | none => false)
    else if l == "yearMonthDuration" then
      (match parseDur v with
       | some d => d.d == 0 && d.h == 0 && d.mi == 0 && !d.inTime
       | none => false)
    else if l == "email" then emailOk v
    else if l == "card-number" then
      v.toList.all Char.isDigit && v.length ≥ 12 && v.length ≤ 19
    else v == "" || (XSD.validLexicalFor .xsd10 l v).getD true
  else true

/-- Is the type one `typeValid` decides? -/
def typeKnown (ns : List (String × String)) (q : String) : Bool :=
  let uri := nsLookup ns (prefixOf q)
  if uri == xsNs then (XSD.validLexicalFor .xsd10 (localOf q) "").isSome
  else if uri == xfNs then
    ["listItem", "listItems", "dayTimeDuration", "yearMonthDuration", "email", "card-number"].contains (localOf q)
      || (XSD.validLexicalFor .xsd10 (localOf q) "").isSome
  else false

/-! ## The model state -/

/-- One node selected by one `bind` element. -/
structure BN where
  bind : Nat := 0
  loc : Loc := default
  pos : Nat := 1
  size : Nat := 1
deriving Inhabited

/-- The evaluation context of an element: node, position, size, model. -/
structure Cx where
  item : Option Item := none
  pos : Nat := 1
  size : Nat := 1
  model : Nat := 0
deriving Inhabited

/-- One form control instance of the view model. `iter` gives the
    repeat item it sits in (repeat element, position), outermost first. -/
structure Ctl where
  el : Nat := 0
  iter : List (Nat × Nat) := []
  kind : String := ""
  id : String := ""
  label : String := ""
  bound : Option Loc := none
  value : String := ""
  relevant : Bool := true
  readonly : Bool := false
  required : Bool := false
  valid : Bool := true
deriving Inhabited

inductive Output where
  | message (level : String) (text : String)
  /-- An event was dispatched to the element with this id (or tag). -/
  | event (name : String) (target : String)
  | fatal (name : String) (detail : String)
  | load (uri : String) (show' : String)
  | focus (id : String)
  | unsupported (what : String)
deriving Repr, Inhabited, BEq

inductive Work where
  | dispatch (name : String) (target : Nat) (iter : List (Nat × Nat)) (info : List (String × Value))
  | action (el : Nat) (iter : List (Nat × Nat)) (info : List (String × Value))
  | body (el : Nat) (iter : List (Nat × Nat)) (info : List (String × Value))
  | dflt (name : String) (target : Nat) (iter : List (Nat × Nat)) (info : List (String × Value))
  | endOuter
  | uiInit
deriving Inhabited

def Work.isEndOuter : Work → Bool
  | .endOuter => true
  | _ => false

structure Flags where
  models : List Nat := []
  rebuild : Bool := false
  recalc : Bool := false
  revalidate : Bool := false
  refresh : Bool := false
deriving Inhabited

structure Model where
  form : Form := {}
  insts : List Inst := []
  resources : List (String × String) := []
  bns : List BN := []
  bindNodes : List (Nat × List Loc) := []
  calcOrder : List BN := []
  mips : List (Loc × Mips) := []
  indexes : List (String × Nat) := []
  cases : List (Nat × Nat) := []
  snap : List Ctl := []
  out : List Output := []
  work : List Work := []
  flags : Flags := {}
  halted : Bool := false
  /-- The control that has the focus. -/
  focus : Option Nat := none
  now : String := "1970-01-01T00:00:00Z"
  tz : Int := 0
deriving Inhabited

/-- An input to the engine. -/
inductive Event where
  /-- Initialise the form (§4.2). -/
  | init
  /-- The user activates a control (DOMActivate). -/
  | activate (el : Nat) (iter : List (Nat × Nat))
  /-- The user changes the value of a control. -/
  | setValue (el : Nat) (iter : List (Nat × Nat)) (value : String)
  /-- Dispatch a named event to an element. -/
  | dispatch (name : String) (el : Nat)

def Model.ofForm (fm : Form) (res : List (String × String)) (now : String) (tz : Int) : Model :=
  { form := fm, resources := res, now := now, tz := tz }

def Model.docAt (m : Model) (k : Nat) : Doc := ((m.insts[k - 2]?).map (·.doc)).getD []

def Model.item? (m : Model) (l : Loc) : Option Item := itemAt (m.docAt l.doc) l

def Model.firstModel (m : Model) : Nat := m.form.models.head?.getD 0

def Model.env (m : Model) (modelEl : Nat) (ns : List (String × String)) (cur : Option Item)
    (info : List (String × Value)) : Env :=
  let mine := m.insts.zipIdx.filter (fun (i, _) => i.model == modelEl)
  { docs := m.insts.map (·.doc), instIds := mine.map (fun (i, k) => (i.id, k)),
    defaultInst := mine.head?.map (·.2), nsctx := ns,
    -- §7.7.5: every repeat has an index; one that `setindex` has not moved is at its `startindex` (default 1)
    indexes := (m.form.els.toList.filter (·.name == "repeat")).filterMap (fun e =>
      (e.attr "id").map (fun id => (id, ((m.indexes.find? (·.1 == id)).map (·.2)).getD
        (((e.attr "startindex").bind String.toNat?).getD 1)))),
    current := cur,
    eventInfo := info, now := m.now, tz := m.tz }

def Model.defaultRoot (m : Model) (modelEl : Nat) : Option Item :=
  let env := m.env modelEl [] none []
  env.defaultInst.bind (instRoot env)

/-- The model an element belongs to: an enclosing `model`, a `model`
    attribute, the model of a referenced `bind`, else the first model. -/
def Model.modelOf (m : Model) (e : Nat) : Nat :=
  let chain := (m.form.ancestors e ++ [e]).reverse
  let found := chain.findSome? (fun i =>
    let el := m.form.el i
    if el.name == "model" then some i
    else match el.attr "model" with
      | some id => m.form.byId id
      | none =>
        match el.attr "bind" with
        | some id => (m.form.byId id).bind (fun b =>
            (m.form.ancestors b).reverse.find? (fun a => (m.form.el a).name == "model"))
        | none => none)
  found.getD m.firstModel

def Model.setValue (m : Model) (l : Loc) (v : String) : Model :=
  { m with insts := m.insts.zipIdx.map (fun (i, k) =>
      if k + 2 == l.doc then { i with doc := setNodeValue i.doc l v } else i) }

def Model.editDoc (m : Model) (docNo : Nat) (f : Doc → Doc) : Model :=
  { m with insts := m.insts.zipIdx.map (fun (i, k) =>
      if k + 2 == docNo then { i with doc := f i.doc } else i) }

/-! ## Rebuild and recalculate (§4.3.1, §4.3.2) -/

/-- Evaluate the `bind` elements: a work list of (bind, context node,
    position, size). Tail recursive; the first argument bounds the
    number of (bind, node) pairs visited. -/
def Model.bindLoop (m : Model) : Nat → List (Nat × Option Item × Nat × Nat) → List BN →
    Except String (List BN)
  | 0, _, acc => .ok acc.reverse
  | _ + 1, [], acc => .ok acc.reverse
  | f + 1, (b, cx, pos, size) :: rest, acc =>
    let el := m.form.el b
    match cx with
    | none => m.bindLoop f rest acc
    | some it =>
      let nsr : Except String (List Item) :=
        match el.attr "nodeset" with
        | none => .ok [it]
        | some src =>
          match evalStr (m.env (m.modelOf b) (xpNs el) (some it) []) it pos size src with
          | .ok (.nodes ns, _) => .ok ns
          | .ok _ => .error s!"bind nodeset '{src}' is not a node-set"
          | .error e => .error e
      match nsr with
      | .error e => .error e
      | .ok ns =>
        let n := ns.length
        let here := ns.zipIdx.map (fun (x, i) => ({ bind := b, loc := x.loc, pos := i + 1, size := n } : BN))
        let kids := (m.form.kidsNamed el "bind").map (·.idx)
        let more := ns.zipIdx.flatMap (fun (x, i) => kids.map (fun k => (k, some x, i + 1, n)))
        m.bindLoop f (more ++ rest) (here.reverse ++ acc)

/-- Evaluate one model item property expression of a bind node. -/
def Model.evalBN (m : Model) (bn : BN) (attr : String) : Except String (Value × List Loc) :=
  let el := m.form.el bn.bind
  match el.attr attr, m.item? bn.loc with
  | some src, some it =>
    evalStr (m.env (m.modelOf bn.bind) (xpNs el) (some it) []) it bn.pos bn.size src
  | _, _ => .ok (.bool true, [])

/-- Rebuild: evaluate the binds, take the read set of every `calculate`
    and order the calculated nodes with `DepGraph.topoSort`. A node's
    reference to itself is not a dependency (§4.3.2). A cycle is an
    error (the caller raises `xforms-compute-exception`). -/
def Model.rebuild (m : Model) : Except String Model := do
  let starts := m.form.models.flatMap (fun mi =>
    (m.form.kidsNamed (m.form.el mi) "bind").map (fun b => (b.idx, m.defaultRoot mi, 1, 1)))
  let bns ← m.bindLoop 100000 starts []
  let bindEls := (bns.map (·.bind)).eraseDups
  let bindNodes := bindEls.map (fun b => (b, (bns.filter (·.bind == b)).map (·.loc)))
  let m1 := { m with bns := bns, bindNodes := bindNodes }
  let calcs := bns.filter (fun bn => ((m.form.el bn.bind).attr "calculate").isSome)
  let table ← calcs.mapM (fun bn => do
    let r ← m1.evalBN bn "calculate"
    pure (bn.loc, r.2))
  let calcLocs := (calcs.map (·.loc)).eraseDups
  let deps := fun (l : Loc) =>
    (((table.find? (·.1 == l)).map (·.2)).getD []).filter (fun u => u != l && calcLocs.contains u)
  match DepGraph.topoSort deps calcLocs with
  | none => .error "the calculate expressions depend on each other in a cycle"
  | some order =>
    pure { m1 with calcOrder := order.filterMap (fun l => calcs.find? (·.loc == l)) }

/-- Recalculate: the `calculate` expressions in dependency order, then
    the other model item properties of every bind node (the validity
    parts are what §4.3.3 revalidate reads). -/
def Model.recalc (m : Model) : Except String Model := do
  let m1 ← m.calcOrder.foldlM (fun (m : Model) bn => do
    let r ← m.evalBN bn "calculate"
    pure (m.setValue bn.loc r.1.toStr)) m
  let mips ← m1.bns.foldlM (fun (acc : List (Loc × Mips)) bn => do
    let el := m1.form.el bn.bind
    let b (a : String) (dflt : Bool) : Except String Bool :=
      match el.attr a with
      | none => .ok dflt
      | some _ => (m1.evalBN bn a).map (fun r => r.1.toBool)
    let ro ← b "readonly" false
    let rel ← b "relevant" true
    let req ← b "required" false
    let con ← b "constraint" true
    let sv := ((m1.item? bn.loc).map (·.stringValue)).getD ""
    let tyOk := match el.attr "type" with
      | none => true
      | some q => typeValid el.ns q sv
    let old : Mips := ((acc.find? (·.1 == bn.loc)).map (·.2)).getD {}
    let merged : Mips :=
      { readonly := old.readonly || ro, relevant := old.relevant && rel,
        required := old.required || req, constraint := old.constraint && con,
        typeOk := old.typeOk && tyOk, hasCalc := old.hasCalc || (el.attr "calculate").isSome }
    pure ((bn.loc, merged) :: acc.filter (fun p => p.1 != bn.loc))) []
  let unknown := m1.bns.filterMap (fun bn =>
    let el := m1.form.el bn.bind
    (el.attr "type").bind (fun q => if typeKnown el.ns q then none else some q))
  let m2 := match unknown.head? with
    | some q => { m1 with out := Output.unsupported s!"type '{q}' is not a built-in type (schema-defined types are not implemented)" :: m1.out }
    | none => m1
  pure { m2 with mips := mips }

def Model.own (m : Model) (l : Loc) : Mips := ((m.mips.find? (·.1 == l)).map (·.2)).getD {}

/-- The element ancestors of an address and the address itself. -/
def locChain (l : Loc) : List Loc :=
  (List.range l.path.length).map (fun k => ({ path := l.path.take (k + 1), doc := l.doc } : Loc)) ++
    (if l.slot.isSome then [l] else [])

/-- §6.1.4: a node is relevant when it and all its ancestors are. -/
def Model.relevantAt (m : Model) (l : Loc) : Bool := (locChain l).all (fun a => (m.own a).relevant)

/-- §6.1.2: a node is readonly when it or an ancestor is, or it has a `calculate`. -/
def Model.readonlyAt (m : Model) (l : Loc) : Bool :=
  (locChain l).any (fun a => (m.own a).readonly) || (m.own l).hasCalc

/-- §4.3.3: valid when the constraint holds, the type is satisfied and
    a required node is not empty. -/
def Model.validAt (m : Model) (l : Loc) : Bool :=
  let o := m.own l
  let v := ((m.item? l).map (·.stringValue)).getD ""
  o.constraint && o.typeOk && (!o.required || v != "")

/-! ## Evaluation contexts and bindings (§7.2) -/

def Model.evalCx (m : Model) (el : El) (cx : Cx) (src : String)
    (info : List (String × Value) := []) (inScope : Option Item := none) : Except String Value :=
  match cx.item with
  | none => .ok (.nodes [])
  | some it =>
    let env := m.env cx.model (xpNs el) (some it) info
    (evalStr { env with context := inScope.orElse (fun _ => some it) } it cx.pos cx.size src).map (·.1)

def Model.switchModel (m : Model) (el : El) (cx : Cx) : Cx :=
  match el.attr "model" with
  | some id =>
    (match m.form.byId id with
     | some mi => { item := m.defaultRoot mi, model := mi }
     | none => cx)
  | none => cx

/-- The node-set of an element's binding attributes (`bind`, else `ref`
    or `nodeset`); `none` when it has none. -/
def Model.nodes (m : Model) (el : El) (cx : Cx) : Except String (Option (List Item)) :=
  let modelOk := match el.attr "model" with
    | none => true
    | some id => ((m.form.byId id).map (fun i => (m.form.el i).name == "model")).getD false
  if !modelOk then .error s!"the model attribute '{(el.attr "model").getD ""}' does not name a model" else
  match el.attr "bind" with
  | some id =>
    (match m.form.byId id with
     | none => .error s!"no bind element with id '{id}'"
     | some b =>
       if (m.form.el b).name != "bind" then .error s!"'{id}' is not a bind element"
       else .ok (some ((((m.bindNodes.find? (·.1 == b)).map (·.2)).getD []).filterMap m.item?)))
  | none =>
    match (el.attr "ref").orElse (fun _ => el.attr "nodeset") with
    | none => .ok none
    | some src =>
      match m.evalCx el cx src with
      | .ok (.nodes ns) => .ok (some ns)
      | .ok _ => .error s!"binding expression '{src}' is not a node-set"
      | .error e => .error e

def Model.indexOf (m : Model) (el : El) : Nat :=
  ((el.attr "id").bind (fun id => (m.indexes.find? (·.1 == id)).map (·.2))).getD
    (((el.attr "startindex").bind String.toNat?).getD 1)

/-- The in-scope evaluation context of element `e` (§7.2): the default
    instance of its model, narrowed by each enclosing binding element;
    inside a `repeat` the item is the one named by `iter`, else the
    repeat's index. -/
def Model.cxOf (m : Model) (e : Nat) (iter : List (Nat × Nat)) : Except String Cx := do
  let m0 := m.firstModel
  let start : Cx := { item := m.defaultRoot m0, model := m0 }
  (m.form.ancestors e).foldlM (fun (cx : Cx) a => do
    let el := m.form.el a
    if el.name == "" then pure cx
    else if el.name == "model" then pure { item := m.defaultRoot a, model := a }
    else
      let cx1 := m.switchModel el cx
      match ← m.nodes el cx1 with
      | none => pure cx1
      | some ns =>
        if el.name == "repeat" || el.name == "itemset" then
          let p := ((iter.find? (·.1 == a)).map (·.2)).getD (m.indexOf el)
          pure { cx1 with item := ns[p - 1]?, pos := p, size := ns.length }
        else pure { cx1 with item := ns.head?, pos := 1, size := 1 }) start

/-- The context of an element and the first node of its own binding. -/
def Model.single (m : Model) (el : El) (iter : List (Nat × Nat)) :
    Except String (Cx × Option (List Item)) := do
  let cx0 ← m.cxOf el.idx iter
  let cx := m.switchModel el cx0
  let ns ← m.nodes el cx
  pure (cx, ns)

/-! ## The view model (§8, §9) -/

def controlKinds : List String :=
  ["input", "secret", "textarea", "output", "upload", "range", "trigger", "submit", "select", "select1"]

def Model.selectedCase (m : Model) (sw : El) : Option Nat :=
  match m.cases.find? (·.1 == sw.idx) with
  | some (_, c) => some c
  | none =>
    let cs := m.form.kidsNamed sw "case"
    ((cs.find? (fun c => c.attr "selected" == some "true")).orElse (fun _ => cs.head?)).map (·.idx)

def Model.caseSelected (m : Model) (c : El) : Bool :=
  match c.parent with
  | some p => m.selectedCase (m.form.el p) == some c.idx
  | none => true

def Model.ctlOf (m : Model) (el : El) (iter : List (Nat × Nat)) (cx : Cx)
    (ns? : Option (List Item)) (rel : Bool) : Except String Ctl := do
  let bound := ns?.bind (·.head?)
  let cxB : Cx := match bound with
    | some x => { cx with item := some x, pos := 1, size := 1 }
    | none => cx
  -- §8.1.5: on `output` a node binding takes precedence over `value`
  let value ← match el.name == "output" && ns?.isNone, el.attr "value" with
    | true, some src => (m.evalCx el cx src).map Value.toStr
    | _, _ => pure ((bound.map (·.stringValue)).getD "")
  let label ← match (m.form.kidsNamed el "label").head? with
    | none => pure ""
    | some l =>
      match ← m.nodes l cxB with
      | some ns => pure ((ns.head?.map (·.stringValue)).getD "")
      | none =>
        -- §8.2.1: a `src` link gives the label text when it can be read
        match (l.attr "src").bind (fun u => (m.resources.find? (·.1 == u)).map (·.2)) with
        | some t => pure (normalizeSpaceStr t)
        | none => pure (normalizeSpaceStr l.text)
  let relevant := rel && (match ns? with
    | none => true
    | some [] => false
    | some (x :: _) => m.relevantAt x.loc)
  pure { el := el.idx, iter := iter, kind := el.name, id := (el.attr "id").getD "", label := label,
         bound := bound.map (·.loc), value := value, relevant := relevant,
         readonly := (bound.map (fun x => m.readonlyAt x.loc)).getD false,
         required := (bound.map (fun x => (m.own x.loc).required)).getD false,
         valid := (bound.map (fun x => m.validAt x.loc)).getD true }

/-- Walk the user interface: a work list of (element, repeat items,
    context, inherited relevance). Tail recursive; the first argument
    bounds the number of elements visited. -/
def Model.viewLoop (m : Model) : Nat → List (Nat × List (Nat × Nat) × Cx × Bool) → List Ctl →
    Except String (List Ctl)
  | 0, _, acc => .ok acc.reverse
  | _ + 1, [], acc => .ok acc.reverse
  | f + 1, (e, iter, cx0, rel) :: rest, acc =>
    let el := m.form.el e
    if el.name == "" then
      m.viewLoop f (el.kids.map (fun k => (k, iter, cx0, rel)) ++ rest) acc
    else
      let cx := m.switchModel el cx0
      match m.nodes el cx with
      | .error err => .error err
      | .ok ns? =>
        if el.name == "repeat" then
          let ns := ns?.getD []
          let items := ns.zipIdx.flatMap (fun (x, i) =>
            el.kids.map (fun k => (k, iter ++ [(e, i + 1)],
              ({ cx with item := some x, pos := i + 1, size := ns.length } : Cx),
              rel && m.relevantAt x.loc)))
          m.viewLoop f (items ++ rest) acc
        else if el.name == "group" || el.name == "switch" || el.name == "case" then
          let (cx', rel') := match ns? with
            | none => (cx, rel)
            | some [] => (({ cx with item := none } : Cx), false)
            | some (x :: _) => (({ cx with item := some x, pos := 1, size := 1 } : Cx),
                                rel && m.relevantAt x.loc)
          let rel'' := if el.name == "case" then rel' && m.caseSelected el else rel'
          m.viewLoop f (el.kids.map (fun k => (k, iter, cx', rel'')) ++ rest) acc
        else if controlKinds.contains el.name then
          match m.ctlOf el iter cx ns? rel with
          | .error err => .error err
          | .ok c => m.viewLoop f rest (c :: acc)
        else m.viewLoop f rest acc

/-- The view model: every form control instance in document order. -/
def Model.view (m : Model) : Except String (List Ctl) :=
  let m0 := m.firstModel
  m.viewLoop 1000000 [(0, [], { item := m.defaultRoot m0, model := m0 }, true)] []

/-! ## Events and actions (§4, §10) -/

def Model.emit (m : Model) (o : Output) : Model := { m with out := o :: m.out }

def Model.push (m : Model) (ws : List Work) : Model := { m with work := ws ++ m.work }

def Model.raise (m : Model) (exc : String) (target : Nat) (detail : String) : Model :=
  m.push [.dispatch exc target [] [("error-message", .str detail)]]

def Model.flag (m : Model) (modelEl : Nat) (rb rc rv rf : Bool) : Model :=
  { m with flags :=
      { models := if m.flags.models.contains modelEl then m.flags.models else m.flags.models ++ [modelEl],
        rebuild := m.flags.rebuild || rb, recalc := m.flags.recalc || rc,
        revalidate := m.flags.revalidate || rv, refresh := m.flags.refresh || rf } }

/-- The handlers of an event at a target, in delivery order (target
    first, then each ancestor: the bubbling phase), and whether one of
    them cancels the default action. -/
def Model.handlers (m : Model) (name : String) (target : Nat) : List Nat × Bool :=
  let path := target :: (m.form.ancestors target).reverse
  let tid := ((m.form.el target).attr "id").getD ""
  let hs := m.form.els.toList.filter (fun h => h.attr "ev:event" == some name &&
    (match h.attr "ev:target" with
     | some t => t == tid
     | none => true))
  let obs (h : El) : Option Nat :=
    match h.attr "ev:observer" with
    | some id => m.form.byId id
    | none => h.parent
  let ordered := path.flatMap (fun p => (hs.filter (fun h => obs h == some p)).map (·.idx))
  (ordered, ordered.any (fun h => (m.form.el h).attr "ev:defaultAction" == some "cancel"))

/-- Refresh (§4.3.4): compute the view model, mark the notification
    events against the previous view, keep the new view. -/
def Model.refresh (m : Model) (target : Nat) : Model :=
  match m.view with
  | .error e => m.raise "xforms-binding-exception" target e
  | .ok v =>
    let evs := v.flatMap (fun c =>
      match c.bound, m.snap.find? (fun o => o.el == c.el && o.iter == c.iter) with
      | some _, some o =>
        -- §8.1.1: a control that becomes relevant is told its whole state
        let changed := c.value != o.value || !o.relevant
        let w (n : String) := Work.dispatch n c.el c.iter []
        if !c.relevant then (if o.relevant then [w "xforms-disabled"] else [])
        else
          (if changed then [w "xforms-enabled"] else []) ++
          (if changed then [w "xforms-value-changed"] else []) ++
          (if changed || c.valid != o.valid then
            [w (if c.valid then "xforms-valid" else "xforms-invalid")] else []) ++
          (if changed || c.readonly != o.readonly then
            [w (if c.readonly then "xforms-readonly" else "xforms-readwrite")] else []) ++
          (if changed || c.required != o.required then
            [w (if c.required then "xforms-required" else "xforms-optional")] else [])
      | _, _ => [])
    ({ m with snap := v }).push evs

/-- The value of a child element such as `name`, `targetid`, `case`,
    `control`, `resource`: its `value` expression, else its text. -/
def Model.childValue (m : Model) (el : El) (child : String) (iter : List (Nat × Nat))
    (info : List (String × Value)) : Except String (Option String) :=
  match (m.form.kidsNamed el child).head? with
  | none => .ok none
  | some c =>
    match c.attr "value" with
    | some src => do
      let cx ← m.cxOf c.idx iter
      let v ← m.evalCx c cx src info
      pure (some v.toStr)
    | none => .ok (some (normalizeSpaceStr c.text))

/-- The text of an element with `output` children evaluated in place
    (the content of `message`, §10.16). -/
def Model.mixedText (m : Model) (el : El) (iter : List (Nat × Nat))
    (info : List (String × Value)) : Except String String := do
  let kids := match el.node with
    | .element _ _ ks => ks
    | _ => []
  let r ← kids.foldlM (fun (acc : String × Nat) k => do
    match k with
    | .element .. =>
      let c := m.form.el ((el.kids[acc.2]?).getD 0)
      if c.name == "output" then
        let (cx, ns) ← m.single c iter
        let v ← match ns, c.attr "value" with
          | some l, _ => pure ((l.head?.map (·.stringValue)).getD "")
          | none, some src => (m.evalCx c cx src info).map Value.toStr
          | none, none => pure ""
        pure (acc.1 ++ v, acc.2 + 1)
      else pure (acc.1 ++ c.text, acc.2 + 1)
    | .text t => pure (acc.1 ++ t, acc.2)
    | .cdata t => pure (acc.1 ++ t, acc.2)
    | _ => pure acc) ("", 0)
  pure (normalizeSpaceStr r.1)

def Model.afterEdit (m : Model) (ev : String) (docNo : Nat)
    (info : List (String × Value) := []) : Model :=
  match m.insts[docNo - 2]? with
  | none => m
  | some i => (m.flag i.model true true true true).push [.dispatch ev i.el [] info]

/-- `insert` (§10.3), for element nodes. -/
def Model.doInsert (m : Model) (el : El) (iter : List (Nat × Nat))
    (info : List (String × Value)) : Except String Model := do
  let cx0 ← m.cxOf el.idx iter
  let cx1 := m.switchModel el cx0
  let cx ← match el.attr "context" with
    | none => pure cx1
    | some src =>
      match ← m.evalCx el cx1 src info with
      | .nodes (x :: _) => pure { cx1 with item := some x, pos := 1, size := 1 }
      | _ => pure { cx1 with item := none }
  match cx.item with
  | none => pure m
  | some ctxNode =>
    let ns := (← m.nodes el cx).getD []
    -- the origin node-set (all its element nodes are cloned, in order); default: the last node
    let origin ← match el.attr "origin" with
      | none => pure ns.getLast?.toList
      | some src =>
        match ← m.evalCx el cx src info with
        | .nodes xs => pure xs
        | _ => pure []
    let clones := origin.filterMap (fun x => match x with
      | .tree _ n => some n
      | _ => none)
    match clones with
    | _ :: _ =>
      let size := ns.length
      if size == 0 then
        -- no node-set: the clone becomes the first child of the context node
        if (el.attr "context").isNone then pure m
        else
          let m' := m.editDoc ctxNode.loc.doc (modKids ctxNode.loc.path (fun kids => clones ++ kids))
          let inserted := (List.range clones.length).filterMap (fun i =>
            m'.item? { path := ctxNode.loc.path ++ [i], doc := ctxNode.loc.doc })
          pure (m'.afterEdit "xforms-insert" ctxNode.loc.doc
            [("inserted-nodes", .nodes inserted), ("origin-nodes", .nodes origin),
             ("insert-location-node", .nodes [ctxNode]), ("position", .str "after")])
      else
        let atIdx ← match el.attr "at" with
          | none => pure size
          | some src => do
            let v ← m.evalCx el { cx with item := ns.head?, pos := 1, size := size } src info
            match numFloor? (Num.roundN v.toNum) with
            | some k => pure (if k < 1 then 1 else if k > Int.ofNat size then size else k.toNat)
            | none => pure size
        let before := el.attr "position" == some "before"
        match ns[atIdx - 1]? with
        | some tgt =>
          let p := tgt.loc.path
          let ci := p.getLast?.getD 0
          let j := if before then ci else ci + 1
          -- §10.3: when the insert location is the root element of an instance, the
          -- first cloned node replaces it
          let isRoot := p.length ≤ 1
          let m' := if isRoot then
              m.editDoc tgt.loc.doc (fun kids => kids.take ci ++ clones.take 1 ++ kids.drop (ci + 1))
            else m.editDoc tgt.loc.doc (modKids p.dropLast
              (fun kids => kids.take j ++ clones ++ kids.drop j))
          let inserted := (List.range (if isRoot then 1 else clones.length)).filterMap (fun i =>
            m'.item? { path := p.dropLast ++ [(if isRoot then ci else j) + i], doc := tgt.loc.doc })
          pure (m'.afterEdit "xforms-insert" tgt.loc.doc
            [("inserted-nodes", .nodes inserted), ("origin-nodes", .nodes origin),
             ("insert-location-node", .nodes [tgt]),
             ("position", .str (if before then "before" else "after"))])
        | none => pure m
    | [] => pure m

/-- `delete` (§10.4), for element, text and other child nodes; the
    root element of an instance is never deleted. -/
def Model.doDelete (m : Model) (el : El) (iter : List (Nat × Nat))
    (info : List (String × Value)) : Except String Model := do
  let cx0 ← m.cxOf el.idx iter
  let cx1 := m.switchModel el cx0
  let cx ← match el.attr "context" with
    | none => pure cx1
    | some src =>
      match ← m.evalCx el cx1 src info with
      | .nodes (x :: _) => pure { cx1 with item := some x, pos := 1, size := 1 }
      | _ => pure { cx1 with item := none }
  let ns := (← m.nodes el cx).getD []
  let size := ns.length
  let targets ← match el.attr "at" with
    | none => pure ns
    | some src => do
      let v ← m.evalCx el { cx with item := ns.head?, pos := 1, size := size } src info
      match numFloor? (Num.roundN v.toNum) with
      | some k =>
        let k' := if k < 1 then 1 else if k > Int.ofNat size then size else k.toNat
        pure (ns[k' - 1]?).toList
      -- §10.4: a NaN location is the last node
      | none => pure (ns[size - 1]?).toList
  let dels := targets.filter (fun t => match t with
    | .tree l _ => l.path.length > 1
    | _ => false)
  match dels.head? with
  | none => pure m
  | some first =>
    let m' := dels.reverse.foldl (fun (m : Model) t =>
      m.editDoc t.loc.doc (modKids t.loc.path.dropLast
        (fun kids => kids.eraseIdx (t.loc.path.getLast?.getD 0)))) m
    pure (m'.afterEdit "xforms-delete" first.loc.doc [("deleted-nodes", .nodes dels)])

/-- Run one action element (§10). -/
def Model.runBody (m : Model) (el : El) (iter : List (Nat × Nat))
    (info : List (String × Value)) : Except String Model := do
  let modelEl := match el.attr "model" with
    | some id => (m.form.byId id).getD (m.modelOf el.idx)
    | none => m.modelOf el.idx
  if el.name == "action" then
    pure (m.push (((el.kids.map m.form.el).filter (·.name != "")).map
      (fun k => Work.action k.idx iter info)))
  else if el.name == "setvalue" then
    let (cx, ns) ← m.single el iter
    match ns.bind (·.head?) with
    | none => pure m
    | some node =>
      let v ← match el.attr "value" with
        | some src =>
          (m.evalCx el { cx with item := some node, pos := 1, size := 1 } src info cx.item).map Value.toStr
        | none => pure el.text
      pure ((m.setValue node.loc v).flag cx.model false true true true)
  else if el.name == "message" then
    let (_, ns) ← m.single el iter
    let text ← match ns with
      | some l => pure ((l.head?.map (·.stringValue)).getD "")
      | none => m.mixedText el iter info
    pure (m.emit (.message ((el.attr "level").getD "modal") text))
  else if el.name == "dispatch" then
    -- §10.8: a child element takes precedence over the attribute of the same name
    let name := (← m.childValue el "name" iter info).orElse (fun _ => el.attr "name")
    let tgt := (← m.childValue el "targetid" iter info).orElse (fun _ =>
      (el.attr "targetid").orElse (fun _ => el.attr "target"))
    let delay := (← m.childValue el "delay" iter info).orElse (fun _ => el.attr "delay")
    match name, tgt.bind m.form.byId with
    | some n, some t =>
      let d := Work.dispatch n t iter []
      if ((delay.bind String.toNat?).getD 0) > 0 then pure { m with work := m.work ++ [d] }
      else pure (m.push [d])
    | _, _ => pure m
  else if el.name == "rebuild" then
    pure ({ m with flags := { m.flags with rebuild := false } }.push [.dispatch "xforms-rebuild" modelEl [] []])
  else if el.name == "recalculate" then
    pure ({ m with flags := { m.flags with recalc := false } }.push [.dispatch "xforms-recalculate" modelEl [] []])
  else if el.name == "revalidate" then
    pure ({ m with flags := { m.flags with revalidate := false } }.push [.dispatch "xforms-revalidate" modelEl [] []])
  else if el.name == "refresh" then
    pure ({ m with flags := { m.flags with refresh := false } }.push [.dispatch "xforms-refresh" modelEl [] []])
  else if el.name == "reset" then
    pure (m.push [.dispatch "xforms-reset" modelEl [] []])
  else if el.name == "toggle" then
    let cid := (← m.childValue el "case" iter info).orElse (fun _ => el.attr "case")
    match cid.bind m.form.byId with
    | none => pure m
    | some c =>
      let cel := m.form.el c
      match cel.parent with
      | none => pure m
      | some sw =>
        let old := m.selectedCase (m.form.el sw)
        if old == some c then pure m
        else
          let m' := { m with cases := (sw, c) :: m.cases.filter (·.1 != sw) }
          pure ((m'.flag modelEl false false false true).push
            ((old.map (fun o => Work.dispatch "xforms-deselect" o iter [])).toList ++
              [.dispatch "xforms-select" c iter []]))
  else if el.name == "setindex" then
    match (el.attr "repeat").bind (fun id => (m.form.byId id).map (fun r => (id, r))), el.attr "index" with
    | some (id, r), some src =>
      let cx ← m.cxOf el.idx iter
      let v ← m.evalCx el cx src info
      let (_, rns) ← m.single (m.form.el r) iter
      let size := (rns.getD []).length
      match numFloor? (Num.roundN v.toNum) with
      | none => pure m
      | some k =>
        let (k', ev) :=
          if k < 1 then ((if size == 0 then 0 else 1), ["xforms-scroll-first"])
          else if k > Int.ofNat size then (size, ["xforms-scroll-last"])
          else (k.toNat, [])
        let m' := { m with indexes := (id, k') :: m.indexes.filter (·.1 != id) }
        pure ((m'.flag modelEl true true true true).push (ev.map (fun n => Work.dispatch n r iter [])))
    | _, _ => pure m
  else if el.name == "setfocus" then
    let cid := (← m.childValue el "control" iter info).orElse (fun _ => el.attr "control")
    match cid.bind m.form.byId with
    | some c => pure (m.push [.dispatch "xforms-focus" c iter []])
    | none => pure m
  else if el.name == "insert" then m.doInsert el iter info
  else if el.name == "delete" then m.doDelete el iter info
  else if el.name == "load" then
    let uri := (← m.childValue el "resource" iter info).orElse (fun _ => el.attr "resource")
    let (_, ns) ← m.single el iter
    let uri := uri.getD (((ns.bind (·.head?)).map (·.stringValue)).getD "")
    pure (m.emit (.load uri ((el.attr "show").getD "replace")))
  else if el.name == "send" then
    pure (m.emit (.unsupported "send: submission is not implemented"))
  else pure m

/-- The default action of an event. -/
def Model.default (m : Model) (name : String) (target : Nat) (iter : List (Nat × Nat))
    (info : List (String × Value)) : Model :=
  let tel := m.form.el target
  if name == "xforms-model-construct" then
    (match m.rebuild >>= Model.recalc with
     | .ok m' => m'
     | .error e => m.raise "xforms-compute-exception" target e)
  else if name == "xforms-rebuild" then
    (match m.rebuild with
     | .ok m' => m'
     | .error e => m.raise "xforms-compute-exception" target e)
  else if name == "xforms-recalculate" then
    (match m.recalc with
     | .ok m' => m'
     | .error e => m.raise "xforms-compute-exception" target e)
  else if name == "xforms-refresh" then m.refresh target
  else if name == "xforms-reset" then
    let m' := { m with insts := m.insts.map (fun (i : Inst) => if i.model == target then { i with doc := i.orig } else i) }
    m'.push [.dispatch "xforms-rebuild" target [] [], .dispatch "xforms-recalculate" target [] [],
             .dispatch "xforms-revalidate" target [] [], .dispatch "xforms-refresh" target [] []]
  else if name.endsWith "-exception" then
    let detail := ((info.find? (·.1 == "error-message")).map (·.2.toStr)).getD
      (((info.find? (·.1 == "resource-uri")).map (·.2.toStr)).getD "")
    { (m.emit (.fatal name detail)) with halted := true, work := [] }
  else if name == "xforms-focus" then
    -- §4.3.7: focus moves; the control that had it gets DOMFocusOut, the new one DOMFocusIn
    let m' := { (m.emit (.focus ((tel.attr "id").getD tel.tag))) with focus := some target }
    if m.focus == some target then m'
    else m'.push ((m.focus.map (fun o => Work.dispatch "DOMFocusOut" o [] [])).toList ++
                  [Work.dispatch "DOMFocusIn" target iter []])
  else if name == "xforms-help" || name == "xforms-hint" then
    let child := if name == "xforms-help" then "help" else "hint"
    (match (m.form.kidsNamed tel child).head? with
     | none => m
     | some h =>
       let text := match (m.cxOf h.idx iter).bind (fun cx => m.nodes h (m.switchModel h cx)) with
         | .ok (some ns) => (ns.head?.map (·.stringValue)).getD ""
         | _ => normalizeSpaceStr h.text
       m.emit (.message (if name == "xforms-help" then "modeless" else "ephemeral") text))
  else if name == "DOMActivate" && tel.name == "submit" then
    m.emit (.unsupported "submit: submission is not implemented")
  else if name == "xforms-submit" then
    m.emit (.unsupported "xforms-submit: submission is not implemented")
  else m

/-- Process one work item. -/
def Model.exec (m : Model) (w : Work) : Model :=
  match w with
  | .dispatch name target iter info =>
    let (hs, cancel) := m.handlers name target
    let tel := m.form.el target
    let m := m.emit (.event name ((tel.attr "id").getD tel.tag))
    let outer := !(m.work.any Work.isEndOuter)
    let acts := hs.map (fun h => Work.action h iter info)
    let acts := if outer && !acts.isEmpty then acts ++ [Work.endOuter] else acts
    m.push (acts ++ (if cancel then [] else [Work.dflt name target iter info]))
  | .action a iter info =>
    let el := m.form.el a
    let cond (attr : String) : Except String Bool :=
      match el.attr attr with
      | none => .ok true
      | some src => do
        let cx ← m.cxOf a iter
        (m.evalCx el cx src info).map Value.toBool
    (match cond "if", cond "while" with
     | .ok true, .ok true =>
       if (el.attr "while").isSome then m.push [.body a iter info, .action a iter info]
       else m.push [.body a iter info]
     | .ok _, .ok _ => m
     | .error e, _ => m.raise "xforms-binding-exception" (m.modelOf a) e
     | _, .error e => m.raise "xforms-binding-exception" (m.modelOf a) e)
  | .body a iter info =>
    (match m.runBody (m.form.el a) iter info with
     | .ok m' => m'
     | .error e => m.raise "xforms-binding-exception" (m.modelOf a) e)
  | .dflt name target iter info => m.default name target iter info
  | .endOuter =>
    -- the deferred update of the outermost action handler (§10)
    let fl := m.flags
    let m := { m with flags := {} }
    m.push (fl.models.flatMap (fun mi =>
      (if fl.rebuild then [Work.dispatch "xforms-rebuild" mi [] []] else []) ++
      (if fl.recalc then [Work.dispatch "xforms-recalculate" mi [] []] else []) ++
      (if fl.revalidate then [Work.dispatch "xforms-revalidate" mi [] []] else []) ++
      (if fl.refresh then [Work.dispatch "xforms-refresh" mi [] []] else [])))
  | .uiInit =>
    (match m.view with
     | .ok v => { m with snap := v }
     | .error e => m.raise "xforms-binding-exception" m.firstModel e)

/-- The event loop: one work item per step, tail recursive, bounded by
    the first argument. -/
def Model.run : Nat → Model → Model
  | 0, m => m
  | f + 1, m =>
    if m.halted then m else
    match m.work with
    | [] => m
    | w :: rest => Model.run f (({ m with work := rest }).exec w)

/-- The names of the XForms functions `Eval.callFn` provides. -/
def xformsFunctions : List String :=
  ["instance", "current", "context", "id", "index", "boolean-from-string", "is-card-number", "if",
   "choose", "avg", "min", "max", "count-non-empty", "power", "random", "compare", "property",
   "digest", "hmac", "now", "local-date", "local-dateTime", "days-from-date", "days-to-date",
   "seconds-from-dateTime", "seconds-to-dateTime", "adjust-dateTime-to-timezone", "seconds",
   "months", "event"]

/-- The work of initialisation (§4.2): load the instances, then
    `xforms-model-construct` to every model, `xforms-model-construct-done`
    to every model, the first view, `xforms-ready` to every model. -/
def Model.initWork (m : Model) : Model :=
  let (insts, errs) := loadInstances m.form m.resources
  let models := m.form.models
  let versionBad (mi : Nat) : Bool :=
    match (m.form.el mi).attr "version" with
    | none => false
    | some v =>
      let ts := splitWs v
      !ts.isEmpty && !ts.any (fun t => t == "1.0" || t == "1.1")
  let d (n : String) (mi : Nat) := Work.dispatch n mi [] []
  -- §7.12: every function named by `functions` must be available
  let functionsBad (mi : Nat) : Bool :=
    match (m.form.el mi).attr "functions" with
    | none => false
    | some v => (splitWs v).any (fun f => !(xformsFunctions.contains (localOf f)))
  { m with insts := insts, work :=
      errs.map (fun (mi, uri) => Work.dispatch "xforms-link-exception" mi [] [("resource-uri", .str uri)]) ++
      (models.filter versionBad).map (d "xforms-version-exception") ++
      (models.filter functionsBad).map (d "xforms-compute-exception") ++
      models.map (d "xforms-model-construct") ++ models.map (d "xforms-model-construct-done") ++
      [Work.uiInit] ++ models.map (d "xforms-ready") }

/-- One step of the engine: an input event, processed to quiescence. -/
def step (m : Model) (e : Event) : Model × List Output :=
  let m0 := { m with out := [] }
  let m1 := match e with
    | .init => m0.initWork
    | .activate el iter => { m0 with work := [.dispatch "DOMActivate" el iter []] }
    | .setValue el iter v =>
      (match (m0.snap.find? (fun c => c.el == el && c.iter == iter)).bind (·.bound) with
       | none => m0
       | some l =>
         let mi := (m0.insts[l.doc - 2]?.map (·.model)).getD m0.firstModel
         { (m0.setValue l v) with work :=
             [.dispatch "xforms-recalculate" mi [] [], .dispatch "xforms-revalidate" mi [] [],
              .dispatch "xforms-refresh" mi [] []] })
    | .dispatch name el => { m0 with work := [.dispatch name el [] []] }
  let m2 := Model.run 200000 m1
  (m2, m2.out.reverse)

end L4Factoidal.XForms.Engine
