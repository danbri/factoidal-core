/-
L4Factoidal.XQuery4.Runtime — the evaluation of the XQuery 4.0
constructs that XPath 4.0 does not have
(https://qt4cg.org/specifications/xquery-40/xquery-40.html, qtspecs
commit b4723ff52fd9d4fabf2b4cd33bd44f21939c512c).

The XQuery 4.0 parser (`XQuery4.Grammar`) puts each such construct in
the tree as `Expr.ext tag es ts qs ss`. `XPath4.eval` gives an `ext`
node to `evalExt`, with a callback `XCb` back into the evaluator, so
this file adds no recursion of its own over expressions: every nested
evaluation goes through `XCb.eval`, which spends the evaluator's fuel.

Implemented here:

* node constructors (§4.12): element, attribute, text, comment,
  processing-instruction, document and namespace nodes, direct and
  computed, with the content-sequence rules of §4.12.1.3 (adjacent
  atomic values joined by a space, document nodes replaced by their
  children, adjacent text merged, attributes before other content,
  duplicate attribute names refused). A constructed node is a new
  runtime document (`NodeRef.rt`); its subtree is copied by index
  arithmetic, in one loop, from the source document;
* the FLWOR clauses that a nested XPath `for`/`let` cannot express
  (§4.13): `for ... allowing empty`, `count`, `order by`, `group by`,
  `window` (tumbling and sliding), over a list of tuples, where a
  tuple is the dynamic context with its variable bindings;
* `try`/`catch` with the `err:` variables, and `finally` (§4.20);
* `typeswitch` (§4.19.2) and `switch` (§4.19.1);
* user-defined functions of the prolog (§5.18): the evaluator asks
  `callUser?` when a static call names no built-in function.

Not implemented: node identity is derived from the content, the
constructor's offset in the query text and the bindings in scope, so
two evaluations of one constructor with equal content in the same
bindings give the same identity
(https://github.com/danbri/factoidal/issues/1101); schema validation
(`validate`, XQST0075).
-/
import L4Factoidal.XPath4.Ext

namespace L4Factoidal.XQuery4

open L4Factoidal.XPath4
open L4Factoidal.XSD

/-- The callbacks into the evaluator that an `ext` node uses. -/
structure XCb where
  eval : Env → Expr → M Seq
  apply : Env → Item → List Seq → M Seq

/-! ## User-defined functions and the static part of the bindings -/

/-- The marker binding that separates the local variables (in front)
    from the prolog's global variables and functions (behind it). -/
def staticKey : QN := { uri := "#xq", loc := "static" }

/-- The binding name under which the prolog keeps a declaration of
    function `q` that accepts `lo` to `hi` arguments (4.0 default
    parameter values). -/
def fnKey (q : QN) (lo hi : Nat) : QN :=
  { uri := "#xqf", loc := q.eqn ++ "#" ++ toString lo ++ "-" ++ toString hi }

/-- The bindings a function body sees: everything from the first
    marker on (the globals and the functions); all bindings when there
    is no marker. -/
def staticVars (vs : List (QN × Seq)) : List (QN × Seq) :=
  match vs.dropWhile (fun (q, _) => !(q == staticKey)) with
  | [] => vs
  | r => r

/-- Is any declaration of `q` there (for the error code)? -/
def userAny (e : Env) (q : QN) : Bool :=
  e.vars.any (fun (v, _) => v.uri == "#xqf" && v.loc.startsWith (q.eqn ++ "#"))

/-- The declaration of `q` that accepts `k` arguments: its function
    item (of the full arity, closure = the static bindings of `e`, so
    the body sees the globals and every function, itself included),
    the number of required parameters, and one focus function per
    optional parameter, which computes the default value in the focus
    of the call. -/
def userDecl? (e : Env) (q0 : QN) (k : Nat) : Option (Item × Nat × List Item) :=
  -- 4.0: an unprefixed call with no `fn` function finds a function in
  -- no namespace
  let q := if q0.uri == nsFN && q0.pfx == "" && userAny e { q0 with uri := "" } then { q0 with uri := "" } else q0
  let pre := q.eqn ++ "#"
  let hit := e.vars.find? (fun (v, _) =>
    v.uri == "#xqf" && v.loc.startsWith pre &&
    (match ((v.loc.drop pre.length).toString.splitOn "-").map String.toNat? with
     | [some lo, some hi] => lo ≤ k && k ≤ hi
     | _ => false))
  match hit with
  | some (v, .fn (.inline ps r b f _) :: dflts) =>
    let lo := match ((v.loc.drop pre.length).toString.splitOn "-").map String.toNat? with
      | [some lo, _] => lo | _ => ps.length
    let sv := staticVars e.vars
    let withCl (d : Item) : Item := match d with
      | .fn (.inline ps' r' b' f' _) => .fn (.inline ps' r' b' f' sv)
      | x => x
    some (.fn (.inline ps r b f sv), lo, dflts.map withCl)
  | _ => none

/-- The callbacks into the evaluator for a user function call. -/
structure CallCb where
  eval : Expr → M Seq
  apply : Item → List Seq → M Seq

/-- A static call `q(args, kw)` of a function declared in the prolog
    (XQuery 4.0 §4.5.1): positional arguments, then keyword arguments
    by parameter name, then defaults in the focus of the call; a
    placeholder `?` makes a partial application. `none` when no
    declaration accepts the call. -/
def callUser? (cb : CallCb) (e : Env) (q : QN) (args : List (Option Expr))
    (kw : List (String × Option Expr)) : Option (M Seq) :=
  match userDecl? e q (args.length + kw.length) with
  | none => none
  | some (fi, lo, dflts) => some do
    let ps := match fi with | .fn (.inline ps _ _ _ _) => ps | _ => []
    let m := ps.length
    let mut slots : Array (Option (Option Expr)) := Array.replicate m none
    for (a, i) in args.zip (List.range args.length) do
      slots := slots.set! i (some a)
    for (nm, a) in kw do
      match ps.findIdx? (fun (v, _) => v.loc == nm) with
      | some i =>
        if (slots.getD i none).isSome then err "XPST0017" ("argument " ++ nm ++ " given twice")
        slots := slots.set! i (some a)
      | none => err "XPST0017" ("no parameter named " ++ nm ++ " in " ++ q.show)
    let ctxArg : Seq := e.ctx.getD []
    let mut fixed : Array (Option Seq) := #[]
    let mut isPartial := false
    for (sl, i) in slots.toList.zip (List.range m) do
      match sl with
      | some (some x) => fixed := fixed.push (some (← cb.eval x))
      | some none => fixed := fixed.push none; isPartial := true
      | none =>
        if i < lo then err "XPST0017" ("missing argument $" ++ ((ps.getD i default).1.show) ++ " of " ++ q.show)
        match dflts[i - lo]? with
        | some d => fixed := fixed.push (some (← cb.apply d [ctxArg]))
        | none => err "XPST0017" ("missing argument of " ++ q.show)
    if isPartial then pure [.fn (.papp fi fixed.toList)]
    else cb.apply fi (fixed.toList.map (·.getD []))

/-- A named function reference `q#k` to a declared function: the
    defaults of the omitted parameters are computed now, in the focus
    of the reference. -/
def refUser? (applyF : Item → List Seq → M Seq) (e : Env) (q : QN) (k : Nat) : Option (M Seq) :=
  match userDecl? e q k with
  | none => none
  | some (fi, lo, dflts) => some do
    let m := match fi with | .fn (.inline ps _ _ _ _) => ps.length | _ => k
    if k == m then return [fi]
    let mut fixed : List (Option Seq) := List.replicate k none
    for i in [k:m] do
      match dflts[i - lo]? with
      | some d => fixed := fixed ++ [some (← applyF d [e.ctx.getD []])]
      | none => err "XPST0017" ("missing argument of " ++ q.show)
    pure [.fn (.papp fi fixed)]

/-! ## Encodings of names in `ext` nodes -/

/-- The absent name (an optional variable that is not there). -/
def noName : QN := { uri := "#none", loc := "" }
def isNoName (q : QN) : Bool := q.uri == "#none"

/-- Bind a variable (as `XPath4.Env.bind`, which comes later). -/
def bindV (e : Env) (q : QN) (s : Seq) : Env := { e with vars := (q, s) :: e.vars }

/-- A static namespace binding, carried in `qs` as `{pfx, uri}`. -/
def nsBinding (p u : String) : QN := { uri := u, loc := "", pfx := p }

/-! ## Building constructed nodes -/

/-- The identity of a constructed node: a runtime document number from
    the constructor's static id, the content and the bindings. -/
def itemSig (i : Item) : String :=
  match i with
  | .atom a => a.str
  | .node n => toString n.doc ++ ":" ++ toString n.idx
  | .map _ => "m" | .arr _ => "a" | .fn _ => "f" | .jnode .. => "j"

def envSalt (e : Env) : String :=
  let vs := (e.vars.take 12).map (fun (q, s) => q.loc ++ "=" ++ String.intercalate "," ((s.take 4).map itemSig))
  toString e.pos ++ "|" ++ String.intercalate ";" vs ++ "|" ++
    (match e.ctx with | some s => String.intercalate "," ((s.take 2).map itemSig) | none => "")

def newDocId (tag : String) (e : Env) (content : String) (ss : List String := []) : Nat :=
  runtimeDocId ("xq-" ++ tag) (envSalt e ++ "\x00" ++ content ++ "\x00" ++
    String.intercalate "," (ss.filter (·.startsWith "#at")))

/-- A piece of element or document content after §4.12.1.3. -/
inductive Piece where
  | text (s : String)
  | node (n : NodeRef)

/-- Copy the subtree of `src` (in `env`) to the end of `out`, with
    parent `par`. A subtree is the index range `[src.idx, last]`, so
    the copy is one loop with an index offset. `inh` are namespace
    bindings to add to every copied element (copy-namespaces inherit). -/
def copyInto (env : Env) (src : NodeRef) (par : Option Nat) (inh : List (String × String))
    (out : Array NRec) (preserve : Bool := true) : Array NRec × Nat := Id.run do
  let d := env.doc src
  let r0 := d.get src.idx
  let lo := src.idx
  let hi := if r0.kind == .element || r0.kind == .document then r0.last else lo
  let base := out.size
  let shift (i : Nat) : Nat := base + (i - lo)
  let mut o := out
  for k in [0:hi + 1 - lo] do
    let i := lo + k
    let r := d.get i
    let parent := if i == lo then par else r.parent.map shift
    -- copy-namespaces no-preserve: only the bindings the names use
    let own := if preserve || r.kind != .element then r.inscope else
      let used := (if r.name.uri != "" then [(r.name.pfx, r.name.uri)] else []) ++
        r.attrs.toList.filterMap (fun a => let ra := d.get a
          if ra.name.uri != "" && ra.name.pfx != "" then some (ra.name.pfx, ra.name.uri) else none)
      used ++ [("xml", nsXML)]
    let inscope := if r.kind == .element && !inh.isEmpty then
        own ++ inh.filter (fun (p, _) => (own.lookup p).isNone)
      else own
    o := o.push { r with parent, inscope,
                         children := r.children.map shift, attrs := r.attrs.map shift,
                         last := shift (if r.kind == .element || r.kind == .document then r.last else i) }
  (o, base)

/-- The content sequence of a constructor, piece by piece (§4.12.1.3):
    `parts` are the values of the content expressions in order; within
    one part, adjacent atomic values are joined by a space. Arrays are
    flattened; a map or function is `XQTY0105`; a document node gives
    its children. Attribute nodes come first, in `attrs`. -/
def contentPieces (env : Env) (parts : List Seq) (forDoc : Bool) :
    M (List NodeRef × List Piece) := do
  let mut attrs : Array NodeRef := #[]
  let mut ps : Array Piece := #[]
  let mut seenOther := false
  for part in parts do
    let mut atoms : Option String := none
    let flat : Seq := part.flatMap (fun i => match i with
      | .arr ms => ms.flatten
      | x => [x])
    for i in flat do
      match i with
      | .atom a =>
          atoms := some (match atoms with | some s => s ++ " " ++ a.str | none => a.str)
      | .arr _ => err "XQTY0105" "an array in element content"
      | .map _ => err "XQTY0105" "a map in element content"
      | .fn _ => err "XQTY0105" "a function item in element content"
      | .jnode .. => err "XQTY0105" "a JNode in element content"
      | .node n =>
        if let some s := atoms then
          ps := ps.push (.text s); seenOther := true; atoms := none
        let r := env.nrec n
        match r.kind with
        | .attribute =>
            if forDoc then err "XPTY0004" "an attribute node in document content"
            if seenOther then err "XQTY0024" "an attribute node after other content"
            attrs := attrs.push n
        | .namespace =>
            if forDoc then err "XPTY0004" "a namespace node in document content"
            if seenOther then err "XQTY0024" "a namespace node after other content"
            attrs := attrs.push n
        | .document =>
            for c in r.children do
              let cr := (env.doc n).get c
              if cr.kind == .text then ps := ps.push (.text cr.value)
              else ps := ps.push (.node (n.at c))
            seenOther := true
        | .text => ps := ps.push (.text r.value); seenOther := true
        | _ => ps := ps.push (.node n); seenOther := true
    if let some s := atoms then
      ps := ps.push (.text s); seenOther := true
  -- merge adjacent text, drop empty text
  let mut merged : Array Piece := #[]
  for p in ps do
    match p, merged.back? with
    | .text a, some (.text b) => merged := merged.pop.push (.text (b ++ a))
    | x, _ => merged := merged.push x
  let res := merged.toList.filter (fun p => match p with | .text s => s != "" | _ => true)
  pure (attrs.toList, res)

/-- Push the children pieces under `par`; returns the new array and the
    child indices. -/
def pushPieces (env : Env) (par : Nat) (inh : List (String × String)) (ps : List Piece)
    (out : Array NRec) (preserve : Bool := true) : Array NRec × Array Nat := Id.run do
  let mut o := out
  let mut cs : Array Nat := #[]
  for p in ps do
    match p with
    | .text s =>
        let i := o.size
        o := o.push { kind := .text, value := s, parent := some par, last := i }
        cs := cs.push i
    | .node n =>
        let (o', i) := copyInto env n (some par) inh o preserve
        o := o'
        cs := cs.push i
  (o, cs)

def isXmlnsName (q : QN) : Bool :=
  q.uri == "http://www.w3.org/2000/xmlns/" || q.pfx == "xmlns" || (q.uri == "" && q.pfx == "" && q.loc == "xmlns")

/-- A fresh prefix for a namespace an attribute needs. -/
def freshPrefix (used : List (String × String)) : String := Id.run do
  let mut k := 0
  for _ in [0:used.length + 2] do
    if (used.lookup ("ns" ++ toString k)).isNone then break
    k := k + 1
  "ns" ++ toString k

/-- Build an element node: name, namespace declarations, content. -/
def buildElement (env : Env) (id : Nat) (name : QN) (decls : List (String × String))
    (parts : List Seq) (preserve inherit : Bool := true) : M Seq := do
  if isXmlnsName name then err "XQDY0096" "the element name is in the xmlns namespace"
  if name.pfx == "xml" && name.uri != nsXML then err "XQDY0096" "prefix xml bound to another namespace"
  if name.uri == nsXML && name.pfx != "xml" && name.pfx != "" then err "XQDY0096" "the xml namespace with another prefix"
  let (ats, ps) ← contentPieces env parts false
  -- in-scope namespaces: declarations, the element name, the attribute names
  let mut scope : List (String × String) := decls
  let mut name := name
  if name.uri != "" then
    match scope.lookup name.pfx with
    | some u => if u != name.uri then
        if name.pfx == "" then scope := ("", name.uri) :: scope.filter (·.1 != "")
        else
          let p := freshPrefix scope
          name := { name with pfx := p }
          scope := (p, name.uri) :: scope
    | none => if name.pfx != "xml" then scope := (name.pfx, name.uri) :: scope
  else if name.pfx == "" && (scope.lookup "").isSome && scope.lookup "" != some "" then
    -- an unprefixed name in no namespace undeclares the default namespace
    scope := ("", "") :: scope.filter (·.1 != "")
  let mut atRecs : Array NRec := #[]
  let mut seen : List QN := []
  for a in ats do
    let r := env.nrec a
    if r.kind == .namespace then
      let p := r.name.loc
      match scope.lookup p with
      | some u => if u != r.value then err "XQDY0102" ("namespace prefix " ++ p ++ " bound twice")
      | none => scope := (p, r.value) :: scope
      continue
    if seen.any (· == r.name) then err "XQDY0025" ("duplicate attribute " ++ r.name.show)
    seen := r.name :: seen
    let mut an := r.name
    if an.uri != "" && an.uri != nsXML then
      if an.pfx == "" || (scope.lookup an.pfx).any (· != an.uri) then
        -- reuse a prefix bound to the namespace, or make one
        match scope.find? (fun (p, u) => u == an.uri && p != "") with
        | some (p, _) => an := { an with pfx := p }
        | none =>
          let p := if an.pfx == "" || (scope.lookup an.pfx).isSome then freshPrefix scope else an.pfx
          an := { an with pfx := p }
          scope := (p, an.uri) :: scope
      else if (scope.lookup an.pfx).isNone then scope := (an.pfx, an.uri) :: scope
    atRecs := atRecs.push { r with name := an, parent := some 0 }
  if (scope.lookup "xml").isNone then scope := scope ++ [("xml", nsXML)]
  scope := scope.filter (fun (p, u) => !(p == "" && u == ""))
  let mut out : Array NRec := #[{ kind := .element, name, inscope := scope }]
  let mut aIdx : Array Nat := #[]
  for r in atRecs do
    let i := out.size
    out := out.push { r with last := i }
    aIdx := aIdx.push i
  let inh := if inherit then scope.filter (fun (p, _) => p != "xml") else []
  let (o2, cs) := pushPieces env 0 inh ps out preserve
  let o3 := o2.set! 0 { (o2.getD 0 default) with children := cs, attrs := aIdx, last := o2.size - 1 }
  let doc : Doc := { nodes := o3, baseUri := env.baseUri }
  pure [.node { doc := id, idx := 0, rt := some doc }]

def buildDocument (env : Env) (id : Nat) (parts : List Seq) : M Seq := do
  let (_, ps) ← contentPieces env parts true
  let out : Array NRec := #[{ kind := .document }]
  let (out, cs) := pushPieces env 0 [] ps out
  let out := out.set! 0 { (out.getD 0 default) with children := cs, last := out.size - 1 }
  pure [.node { doc := id, idx := 0, rt := some { nodes := out, baseUri := env.baseUri, uri := "" } }]

def leafNode (env : Env) (id : Nat) (r : NRec) : Seq :=
  [.node { doc := id, idx := 0, rt := some { nodes := #[{ r with last := 0 }], baseUri := env.baseUri } }]

/-- The string of a computed constructor's content: atomized, joined
    by a space. -/
def contentString (env : Env) (s : Seq) : M String := do
  let as ← env.atomize s
  pure (String.intercalate " " (as.map Atomic.str))

/-- Resolve a computed node name (§4.12.3.1): an `xs:QName`, or a
    string or untyped value that is a lexical QName, resolved with the
    static namespaces `sns`. -/
def nameOf (env : Env) (s : Seq) (sns : List (String × String)) (isAttr : Bool) : M QN := do
  let as ← env.atomize s
  match as with
  | [a] =>
    match a.v with
    | .qn q => pure q
    | .str lex =>
      if !(a.isStringLike || a.ty == .untyped) then err "XPTY0004" "a computed name must be a QName or a string"
      let lex := lex.trimAscii.toString
      if lex.startsWith "Q{" then
        match lex.splitOn "}" with
        | [u, l] => if isNCName l then pure { uri := (u.drop 2).toString, loc := l } else err "XQDY0074" ("invalid name " ++ lex)
        | _ => err "XQDY0074" ("invalid name " ++ lex)
      else
      match parseQNameLex lex with
      | some (p, l) =>
        if p == "" then pure { uri := if isAttr then "" else (sns.lookup "").getD "", loc := l }
        else if p == "xml" then pure { uri := nsXML, loc := l, pfx := p }
        else if p == "xmlns" then pure { uri := "http://www.w3.org/2000/xmlns/", loc := l, pfx := p }
        else match sns.lookup p with
          | some u => pure { uri := u, loc := l, pfx := p }
          | none => match defaultNs.lookup p with
            | some u => pure { uri := u, loc := l, pfx := p }
            | none => err "XQDY0074" ("undeclared prefix " ++ p)
      | none => err "XQDY0074" ("invalid name " ++ lex)
    | _ => err "XPTY0004" "a computed name must be a QName or a string"
  | [] => err "XPTY0004" "a computed name is empty"
  | _ => err "XPTY0004" "a computed name has more than one item"

def sNs (qs : List QN) : List (String × String) := qs.map (fun q => (q.pfx, q.uri))

/-! ## FLWOR tuple streams -/

/-- Atomize an order or group key: at most one value; untyped to
    string. -/
def keyOf (env : Env) (s : Seq) : M (Option Atomic) := do
  match ← env.atomize s with
  | [] => pure none
  | [a] => pure (some (if a.ty == .untyped then Atomic.ofStr a.str else a))
  | _ => err "XPTY0004" "an order or group key has more than one item"

def isNaNA (a : Atomic) : Bool := (a.num?.map (fun n => n.rank ≥ 2 && n.toFloat.isNaN)).getD false

/-- Compare two order keys (§4.13.9): `lt` when `a` sorts first. The
    empty key and NaN come first with `emptyLeast`. -/
def keyCmp (tz : Int) (emptyLeast : Bool) (a b : Option Atomic) : Ordering :=
  let rank (x : Option Atomic) : Nat := match x with
    | none => if emptyLeast then 0 else 3
    | some v => if isNaNA v then (if emptyLeast then 1 else 2) else 5
  match a, b with
  | some x, some y =>
    if isNaNA x || isNaNA y then compare (rank a) (rank b)
    else match atomicCmp x y tz with
      | .ok (some o) => o
      | _ => .eq
  | _, _ =>
    let ra := rank a
    let rb := rank b
    if ra == 5 then (if emptyLeast then .gt else .lt)
    else if rb == 5 then (if emptyLeast then .lt else .gt)
    else compare ra rb

/-- One `order by` key spec: descending, empty least, collation. -/
structure OSpec where
  desc : Bool := false
  emptyLeast : Bool := true

def OSpec.decode (s : String) (dflt : Bool) : OSpec :=
  { desc := s.startsWith "d", emptyLeast := if s.length ≥ 2 then (s.drop 1).startsWith "l" else dflt }

def cmpTuples (tz : Int) (specs : List OSpec) : List (Option Atomic) → List (Option Atomic) → Ordering
  | a :: as, b :: bs =>
    match specs with
    | sp :: rest =>
      let o := keyCmp tz sp.emptyLeast a b
      let o := if sp.desc then o.swap else o
      if o == .eq then cmpTuples tz rest as bs else o
    | [] => .eq
  | _, _ => .eq

/-- `group by` key equality (§4.13.7): deep-equal of the atomized keys,
    NaN equal to NaN; the empty key equals the empty key. -/
def groupKeyEq (a b : Option Atomic) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => deepAtomEq x y
  | _, _ => false

/-- The decoded window clause. -/
structure Win where
  sliding : Bool
  hasEnd : Bool
  only : Bool
  v : QN
  s : QN × QN × QN × QN
  e : QN × QN × QN × QN

def bindOpt (env : Env) (q : QN) (s : Seq) : Env := if isNoName q then env else bindV env q s

def bindWinVars (env : Env) (vs : QN × QN × QN × QN) (items : Array Item) (i : Nat) : Env :=
  let (cur, p, prev, next) := vs
  let atJ (j : Nat) : Seq := if j < items.size then [items[j]!] else []
  let env := bindOpt env cur (atJ i)
  let env := bindOpt env p (sInt (i + 1))
  let env := bindOpt env prev (if i == 0 then [] else atJ (i - 1))
  bindOpt env next (atJ (i + 1))

/-- Evaluate a list of FLWOR clauses over a tuple stream. `bound`
    collects the names the clauses bound so far (for `group by`). -/
def runClauses (cb : XCb) (cs : List Expr) (tuples : List Env) (bound : List QN) :
    M (List Env × List QN) := do
  let mut ts := tuples
  let mut bnd := bound
  for c in cs do
    match c with
    | .ext "c:for" [src] [vt] [v, pv] [kind, allowing] =>
      let mut out : Array Env := #[]
      for t in ts do
        let s ← cb.eval t src
        if kind == "member" then
          match s with
          | [.arr ms] =>
            let mut k := 1
            for m in ms do
              let x ← t.coerce vt m ("$" ++ v.show)
              out := out.push (bindOpt (bindV t v x) pv (sInt k)); k := k + 1
          | _ => err "XPTY0004" "for member needs a single array"
        else
        if s.isEmpty && allowing == "1" then
          out := out.push (bindOpt (bindV t v []) pv (sInt 0))
        else
          let mut k := 1
          for i in s do
            let x ← t.coerce vt [i] ("$" ++ v.show)
            out := out.push (bindOpt (bindV t v x) pv (sInt k)); k := k + 1
      ts := out.toList
      bnd := bnd ++ [v] ++ (if isNoName pv then [] else [pv])
    | .ext "c:forkv" [src] [] [kv, vv, pv] [] =>
      let mut out : Array Env := #[]
      for t in ts do
        match ← cb.eval t src with
        | [.map kvs] =>
          let mut k := 1
          for (key, val) in kvs do
            let t1 := bindOpt (bindOpt t kv [.atom key]) vv val
            out := out.push (bindOpt t1 pv (sInt k)); k := k + 1
        | _ => err "XPTY0004" "for key/value needs a single map"
      ts := out.toList
      bnd := bnd ++ [kv, vv, pv].filter (fun q => !isNoName q)
    | .ext "c:let" [e] [vt] [v] [] =>
      let mut out : Array Env := #[]
      for t in ts do
        let s ← cb.eval t e
        out := out.push (bindV t v (← t.coerce vt s ("$" ++ v.show)))
      ts := out.toList
      bnd := bnd ++ [v]
    | .ext "c:where" [e] [] [] [] =>
      let mut out : Array Env := #[]
      for t in ts do
        if ← ebv (← cb.eval t e) then out := out.push t
      ts := out.toList
    | .ext "c:while" [e] [] [] [] =>
      let mut out : Array Env := #[]
      for t in ts do
        if ← ebv (← cb.eval t e) then out := out.push t else break
      ts := out.toList
    | .ext "c:count" [] [] [v] [] =>
      ts := (ts.zip (List.range ts.length)).map (fun (t, k) => bindV t v (sInt (k + 1)))
      bnd := bnd ++ [v]
    | .ext "c:order" keys [] [] specs =>
      let dflt := specs.headD "l" == "l"
      let sps := (specs.drop 1).map (OSpec.decode · dflt)
      let mut keyed : Array (List (Option Atomic) × Env) := #[]
      for t in ts do
        let mut ks : Array (Option Atomic) := #[]
        for k in keys do ks := ks.push (← keyOf t (← cb.eval t k))
        keyed := keyed.push (ks.toList, t)
      -- the keys at one position must be comparable (XPTY0004)
      for j in [0:keys.length] do
        let vals := keyed.toList.filterMap (fun (ks, _) => (ks.getD j none))
        match vals.find? (fun a => !isNaNA a) with
        | some a0 =>
          for b in vals do
            if !isNaNA b then
              match atomicCmp a0 b (ts.headD {}).tz with
              | .ok (some _) => pure ()
              | _ => err "XPTY0004" "order by keys of incompatible types"
        | none => pure ()
      let tz := (ts.headD {}).tz
      let sorted := keyed.toList.mergeSort (fun x y => cmpTuples tz sps x.1 y.1 != .gt)
      ts := sorted.map (·.2)
    | .ext "c:group" keys [] gvs _ =>
      -- groups in order of first appearance
      let mut groups : Array (List (Option Atomic) × Array Env) := #[]
      for t in ts do
        let mut ks : Array (Option Atomic) := #[]
        for k in keys do ks := ks.push (← keyOf t (← cb.eval t k))
        let kl := ks.toList
        match groups.findIdx? (fun (g, _) => g.length == kl.length && (g.zip kl).all (fun (a, b) => groupKeyEq a b)) with
        | some gi => groups := groups.modify gi (fun (g, ms) => (g, ms.push t))
        | none => groups := groups.push (kl, #[t])
      let others := bnd.filter (fun q => !gvs.any (· == q))
      let mut out : Array Env := #[]
      for (kl, ms) in groups do
        let first := ms.getD 0 {}
        let mut t := first
        for q in others.eraseDups do
          let vals := ms.toList.flatMap (fun m => match m.vars.find? (fun (v, _) => v == q) with
            | some (_, s) => s | none => [])
          t := bindV t q vals
        for (q, k) in gvs.zip kl do
          t := bindV t q (match k with | some a => [.atom a] | none => [])
        out := out.push t
      ts := out.toList
      bnd := bnd ++ gvs
    | .ext "c:window" (src :: sc :: ec) [vt] (v :: s1 :: s2 :: s3 :: s4 :: e1 :: e2 :: e3 :: e4 :: _) [kind, only] =>
      let w : Win := { sliding := kind == "sliding", hasEnd := !ec.isEmpty, only := only == "1",
                       v, s := (s1, s2, s3, s4), e := (e1, e2, e3, e4) }
      let mut out : Array Env := #[]
      for t in ts do
        let items := (← cb.eval t src).toArray
        let n := items.size
        let mut i := 0
        let mut nextFree := 0
        for _ in [0:n] do
          if i ≥ n then break
          let ts1 := bindWinVars t w.s items i
          let startOk ← if !w.sliding && i < nextFree then pure false else ebv (← cb.eval ts1 sc)
          if startOk then
            -- find the end
            let mut endAt : Option Nat := none
            match ec with
            | [ecx] =>
              for j in [i:n] do
                let te := bindWinVars ts1 w.e items j
                if ← ebv (← cb.eval te ecx) then endAt := some j; break
            | _ =>
              -- no end condition (tumbling only): up to the next start
              let mut j := i + 1
              let mut found := false
              for _ in [i+1:n] do
                if ← ebv (← cb.eval (bindWinVars t w.s items j) sc) then found := true; break
                j := j + 1
              endAt := some (if found then j - 1 else n - 1)
            let keep := endAt.isSome || !w.only
            let last := endAt.getD (n - 1)
            if keep then
              let win := (items.extract i (last + 1)).toList
              let win ← t.coerce vt win ("$" ++ v.show)
              let tw := bindWinVars (bindWinVars (bindV t v win) w.s items i) w.e items last
              out := out.push tw
            if !w.sliding then nextFree := last + 1
            if !w.sliding && endAt.isNone && w.only then break
          i := i + 1
      ts := out.toList
      bnd := bnd ++ [v, s1, s2, s3, s4, e1, e2, e3, e4].filter (fun q => !isNoName q)
    | _ => err "XPST0003" "unknown FLWOR clause"
  pure (ts, bnd)

/-! ## try/catch -/

def errUri (e : Err) : String := if e.uri == "" then nsERR else e.uri

/-- The expanded name of an error: a code written `Q{uri}local` (as
    the EXPath modules write theirs) is split; otherwise the code is a
    local name in `errUri e`. -/
def errName (e : Err) : String × String :=
  if e.code.startsWith "Q{" then
    match (e.code.drop 2).toString.splitOn "}" with
    | [u, l] => (u, l)
    | _ => (errUri e, e.code)
  else (errUri e, e.code)

/-- Does a catch name test (`*`, `Q{u}*`, `*:l`, `Q{u}l`) match? -/
def catchMatches (t : String) (e : Err) : Bool :=
  let (u, l) := errName e
  t == "*" ||
  (t.startsWith "*:" && (t.drop 2).toString == l) ||
  (t.endsWith "}*" && t == "Q{" ++ u ++ "}*") ||
  t == "Q{" ++ u ++ "}" ++ l

def errVars (e : Err) : List (QN × Seq) :=
  let n (l : String) : QN := { uri := nsERR, loc := l, pfx := "err" }
  let (eu, el) := errName e
  let code : Seq := single (Atomic.ofQN { uri := eu, loc := el, pfx := if eu == nsERR then "err" else "" })
  [(n "code", code), (n "description", sStr e.msg), (n "value", []), (n "module", []),
   (n "line-number", []), (n "column-number", []), (n "additional", []),
   (n "stack-trace", []),
   (n "map", [.map [(Atomic.ofStr "code", code), (Atomic.ofStr "description", sStr e.msg)]])]

/-! ## The dispatcher -/

def evalExt (cb : XCb) (env : Env) (tag : String) (es : List Expr) (ts : List IType)
    (qs : List QN) (ss : List String) : M Seq := do
  match tag with
  | "elem" =>
    match es with
    | nm :: parts =>
      let sns := sNs qs
      let name ← nameOf env (← cb.eval env nm) sns false
      let name := if name.uri == nsXML && name.pfx == "" then { name with pfx := "xml" } else name
      if ss.headD "" == "c" && (name.pfx == "xmlns" || name.uri == "http://www.w3.org/2000/xmlns/") then
        err "XQDY0096" "the element name is in the xmlns namespace"
      let decls := (ss.drop 1).filterMap (fun d => match d.splitOn "\x00" with
        | [p, u] => some (p, u) | _ => none)
      let mut vals : Array Seq := #[]
      for p in parts do vals := vals.push (← cb.eval env p)
      let id := newDocId "elem" env (name.eqn ++ "|" ++ ss.headD "" ++ "|" ++
        String.intercalate "," (vals.toList.map (fun s => String.intercalate "," (s.map itemSig)))) ss
      buildElement env id name decls vals.toList (!ss.contains "#no-preserve") (!ss.contains "#no-inherit")
    | [] => err "XPST0003" "element constructor without name"
  | "attr" =>
    match es with
    | nm :: parts =>
      let name ← nameOf env (← cb.eval env nm) (sNs qs) true
      let name := if name.uri == nsXML && name.pfx == "" then { name with pfx := "xml" } else name
      if isXmlnsName name then err (if ss.headD "" == "d" then "XQST0071" else "XQDY0044") "an attribute named xmlns"
      if name.pfx == "xml" && name.uri != nsXML then err "XQDY0044" "prefix xml bound to another namespace"
      if name.uri == nsXML && name.pfx != "xml" then err "XQDY0044" "the xml namespace with another prefix"
      let mut v := ""
      for p in parts do v := v ++ (← contentString env (← cb.eval env p))
      let v' := if name == ({ uri := nsXML, loc := "id" } : QN) then normSpace v else v
      let id := newDocId "attr" env (name.eqn ++ "=" ++ v' ++ toString es.length) ss
      pure (leafNode env id { kind := .attribute, name, value := v' })
    | [] => err "XPST0003" "attribute constructor without name"
  | "text" =>
    let s ← cb.eval env (es.headD (.seq []))
    let as ← env.atomize s
    if as.isEmpty then pure [] else
    let v := String.intercalate " " (as.map Atomic.str)
    pure (leafNode env (newDocId "text" env v ss) { kind := .text, value := v })
  | "comment" =>
    let v ← contentString env (← cb.eval env (es.headD (.seq [])))
    if (v.splitOn "--").length > 1 || v.endsWith "-" then err "XQDY0072" "a comment with '--' or a final '-'"
    pure (leafNode env (newDocId "comment" env v ss) { kind := .comment, value := v })
  | "pi" =>
    match es with
    | [tgt, body] =>
      let tv ← env.atomize (← cb.eval env tgt)
      let target ← match tv with
        | [a] =>
          if a.isStringLike || a.ty == .untyped || a.is .ncname then
            let t := a.str.trimAscii.toString
            if isNCName t then pure t else err "XQDY0041" ("invalid processing-instruction target " ++ t)
          else err "XPTY0004" "processing-instruction target must be a string"
        | _ => err "XPTY0004" "processing-instruction target must be one value"
      if target.toLower == "xml" then err "XQDY0064" "processing-instruction target xml"
      let v ← contentString env (← cb.eval env body)
      if (v.splitOn "?>").length > 1 then err "XQDY0026" "processing-instruction content with '?>'"
      let v := String.ofList (v.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r'))
      pure (leafNode env (newDocId "pi" env (target ++ " " ++ v) ss)
        { kind := .pi, name := { uri := "", loc := target }, value := v })
    | _ => err "XPST0003" "bad processing-instruction constructor"
  | "doc" =>
    let s ← cb.eval env (es.headD (.seq []))
    buildDocument env (newDocId "doc" env (String.intercalate "," (s.map itemSig)) ss) [s]
  | "ns" =>
    match es with
    | [px, ux] =>
      let pv ← env.atomize (← cb.eval env px)
      let p ← match pv with
        | [] => pure ""
        | [a] =>
          if a.isStringLike || a.ty == .untyped || a.is .ncname then
            let t := a.str.trimAscii.toString
            if t == "" || isNCName t then pure t else err "XQDY0074" ("invalid namespace prefix " ++ t)
          else err "XPTY0004" "a namespace prefix must be a string"
        | _ => err "XPTY0004" "a namespace prefix must be one value"
      let u ← contentString env (← cb.eval env ux)
      if p == "xmlns" || u == "http://www.w3.org/2000/xmlns/" then err "XQDY0101" "the xmlns namespace"
      if (p == "xml") != (u == nsXML) then err "XQDY0101" "the xml prefix and namespace go together"
      if u == "" then err "XQDY0101" "a namespace node with an empty URI"
      pure (leafNode env (newDocId "ns" env (p ++ "=" ++ u) ss)
        { kind := .namespace, name := { uri := "", loc := p }, value := u })
    | _ => err "XPST0003" "bad namespace constructor"
  | "flwor" =>
    match es.reverse with
    | ret :: rcs =>
      let (tuples, _) ← runClauses cb rcs.reverse [env] []
      let mut out : Array Item := #[]
      for t in tuples do
        for i in ← cb.eval t ret do out := out.push i
      pure out.toList
    | [] => pure []
  | "try" =>
    -- es: body, catch bodies..., [finally]; ss: one name-test list per catch, then "finally"?
    let hasFinally := ss.getLast? == some "#finally"
    let tests := if hasFinally then ss.dropLast else ss
    let body := es.headD (.seq [])
    let handlers := (es.drop 1).take tests.length
    let fin := if hasFinally then es.getLast? else none
    let r := match cb.eval env body with
      | .ok s => Except.ok s
      | .error e =>
        match (tests.zip handlers).find? (fun (t, _) => (t.splitOn "|").any (catchMatches · e)) with
        | some (_, h) => cb.eval { env with vars := errVars e ++ env.vars } h
        | none => .error e
    match fin with
    | some f =>
      let _ ← cb.eval env f
      r
    | none => r
  | "typeswitch" =>
    match es with
    | op :: rest =>
      let v ← cb.eval env op
      let rets := rest
      let k := ts.length
      let mut res : Option Seq := none
      for (t, i) in ts.zip (List.range k) do
        if env.seqMatches v t then
          let q := qs.getD i noName
          res := some (← cb.eval (bindOpt env q v) (rets.getD i (.seq [])))
          break
      match res with
      | some r => pure r
      | none => cb.eval (bindOpt env (qs.getD k noName) v) (rets.getD k (.seq []))
    | [] => pure []
  | "switch" =>
    -- es: operand, default, then per clause its case values and return; ss: case counts
    match es with
    | op :: dflt :: rest =>
      let ov ← env.atomize (← cb.eval env op)
      if ov.length > 1 then err "XPTY0004" "a switch operand of more than one item"
      let ov := ov.map (fun a => if a.ty == .untyped then Atomic.ofStr a.str else a)
      let mut cur := rest
      let mut res : Option Seq := none
      for cnt in ss do
        let n := cnt.toNat?.getD 0
        let cases := cur.take n
        let ret := cur.getD n (.seq [])
        cur := cur.drop (n + 1)
        if res.isSome then continue
        for c in cases do
          let cv ← env.atomize (← cb.eval env c)
          let cv := cv.map (fun a => if a.ty == .untyped then Atomic.ofStr a.str else a)
          let hit := match ov with
            | [] => cv.isEmpty
            | [o] => cv.any (fun x => deepAtomEq o x)
            | _ => false
          if hit then res := some (← cb.eval env ret); break
      match res with
      | some r => pure r
      | none => cb.eval env dflt
    | _ => pure []
  | "seqs" =>
    -- evaluate each operand; yield the last (used for `finally`-like sequencing)
    let mut last : Seq := []
    for e in es do last ← cb.eval env e
    pure last
  | "error" => err (ss.headD "XPST0003") (ss.getD 1 "")
  | _ => err "XPST0003" ("unknown XQuery construct " ++ tag)

end L4Factoidal.XQuery4
