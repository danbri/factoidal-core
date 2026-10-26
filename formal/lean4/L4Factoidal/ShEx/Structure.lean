/-
L4Factoidal.ShEx.Structure — the ShEx 2.1 schema requirements.

Spec: ShEx 2.1 Semantics (http://shex.io/shex-semantics/) §5.7,
"Schema Requirements": structural requirements a schema must meet
beyond the grammar of the abstract syntax. They are "not constraints
expressed by the schema but instead those imposed on the schema", so
a schema that violates one is rejected before any validation.

`structureErrors` returns every violation it finds, as text naming the
label; the empty list means the schema meets the checked requirements:

* §5.7.2 Shape Expression Reference Requirement — a `shapeExprRef`
  names a declared shape expression, and no shape label is in the
  shapeExprRef closure of its own definition;
* §5.7.3 Triple Expression Reference Requirement — a `tripleExprRef`
  (`&label`) names a triple expression in the schema, not a shape
  expression, and no triple expression label is in the tripleExprRef
  closure of its own definition;
* §5.7.4 Negation Requirement — the dependency graph between Shapes
  has no cycle that traverses a NEGATED reference. A reference is
  negated when the target appears under an odd number of `ShapeNot`
  in the shapeExprRef closure of the triple constraint's value, or
  when the triple constraint's predicate is one of the source shape's
  `EXTRA` predicates. An `EXTENDS` reference (ShEx 2.2 shape
  extension) is an edge of the same graph;
* a label is not BOTH a shape expression label and a triple
  expression label (`1ShapeProductionCollision` of the shexTest
  `negativeStructure` suite): ShExJ keeps both kinds of label in one
  space of identifiers, so the reference requirements above could not
  say which one a label means.

## Imports

The reference requirements say a label must appear "in the schema's
shapes map (or an imported schema's map)". This module sees one
document, so when the schema IMPORTs anything an unresolved label is
NOT reported: it may be declared in the imported document. The cycle
and negation checks still run over what is present.

## Termination

Every closure is a fixed-point walk bounded by the number of
declarations or nodes it walks over, so all functions are total
(no `partial def`).

Tracking: https://github.com/danbri/factoidal/issues/698.
-/
import L4Factoidal.ShEx.Schema

namespace L4Factoidal.ShEx.Structure

open L4Factoidal.ShEx

/-! ## Flattening a schema into the graph the requirements talk about -/

/-- The ATOMS of a shape expression at its top level: the Shapes that
    appear in it (by position path) and the shape labels it references,
    each with the parity of the `ShapeNot`s above it (`true` = odd). -/
structure Atoms where
  shapes : List (String × Bool) := []
  refs   : List (String × Bool) := []
deriving Inhabited

def Atoms.append (a b : Atoms) : Atoms :=
  { shapes := a.shapes ++ b.shapes, refs := a.refs ++ b.refs }

/-- A triple constraint, reduced to what the negation requirement
    reads: its predicate and direction, and its value's atoms. -/
structure TcNode where
  predicate : String
  inverse   : Bool
  value     : Atoms
deriving Inhabited

/-- One Shape occurrence. `path` is its position in the schema, which
    is its identity: two Shapes written alike at two places are two
    vertices of the dependency graph. -/
structure ShapeNode where
  path        : String
  extra       : List String
  extendsRefs : List String
  tcs         : List TcNode
  /-- `&label` inclusions written directly in the shape's expression. -/
  includes    : List String
deriving Inhabited

/-- A labelled triple expression: its label, the triple constraints
    written directly in it, and its own `&label` inclusions. -/
structure TeEntry where
  id       : String
  tcs      : List TcNode
  includes : List String
deriving Inhabited

/-- What a walk collects besides its result. -/
structure Acc where
  shapes : List ShapeNode := []
  tes    : List TeEntry := []
deriving Inhabited

def Acc.append (a b : Acc) : Acc :=
  { shapes := a.shapes ++ b.shapes, tes := a.tes ++ b.tes }

/-- A triple expression's direct content. -/
structure TeContent where
  tcs      : List TcNode := []
  includes : List String := []
deriving Inhabited

def TeContent.append (a b : TeContent) : TeContent :=
  { tcs := a.tcs ++ b.tcs, includes := a.includes ++ b.includes }

mutual

def seWalk (path : String) (neg : Bool) : ShapeExpr → Atoms × Acc
  | .ref l          => ({ refs := [(l, neg)] }, {})
  | .shapeAnd es    => seListWalk path neg 0 es
  | .shapeOr es     => seListWalk path neg 0 es
  | .shapeNot e     => seWalk (path ++ "/not") (!neg) e
  | .nodeConstraint _ => ({}, {})
  | .external       => ({}, {})
  | .shape sh       =>
      let (node, acc) := shapeWalk path sh
      ({ shapes := [(path, neg)] }, { acc with shapes := node :: acc.shapes })

def seListWalk (path : String) (neg : Bool) (i : Nat) : List ShapeExpr → Atoms × Acc
  | [] => ({}, {})
  | e :: es =>
      let (a1, c1) := seWalk (path ++ "/" ++ toString i) neg e
      let (a2, c2) := seListWalk path neg (i + 1) es
      (a1.append a2, c1.append c2)

def shapeWalk (path : String) : Shape → ShapeNode × Acc
  | .mk _ extra expr _ _ ext =>
      let (content, acc) := teOptWalk (path ++ "/expr") expr
      ({ path := path, extra := extra, extendsRefs := ext,
         tcs := content.tcs, includes := content.includes }, acc)

def teOptWalk (path : String) : Option TripleExpr → TeContent × Acc
  | none   => ({}, {})
  | some e => teWalk path e

def teWalk (path : String) : TripleExpr → TeContent × Acc
  | .ref l => ({ includes := [l] }, {})
  | .tripleConstraint tc => tcWalk path tc
  | .eachOf g => groupWalk path g
  | .oneOf g => groupWalk path g

def tcWalk (path : String) : TripleConstraint → TeContent × Acc
  | .mk id inv p v _ _ _ _ =>
      let (atoms, acc) := seOptWalk (path ++ "/value") v
      let node : TcNode := { predicate := p, inverse := inv, value := atoms }
      let entry : List TeEntry := match id with
        | some i => [{ id := i, tcs := [node], includes := [] }]
        | none   => []
      ({ tcs := [node] }, { acc with tes := entry ++ acc.tes })

def seOptWalk (path : String) : Option ShapeExpr → Atoms × Acc
  | none   => ({}, {})
  | some e => seWalk path false e

def groupWalk (path : String) : Group → TeContent × Acc
  | .mk id es _ _ _ _ =>
      let (content, acc) := teListWalk path 0 es
      let entry : List TeEntry := match id with
        | some i => [{ id := i, tcs := content.tcs, includes := content.includes }]
        | none   => []
      (content, { acc with tes := entry ++ acc.tes })

def teListWalk (path : String) (i : Nat) : List TripleExpr → TeContent × Acc
  | [] => ({}, {})
  | e :: es =>
      let (c1, a1) := teWalk (path ++ "/" ++ toString i) e
      let (c2, a2) := teListWalk path (i + 1) es
      (c1.append c2, a1.append a2)

end

/-- A schema, flattened: each declaration's top-level atoms, the start
    expression's, every Shape occurrence and every labelled triple
    expression. -/
structure Flat where
  decls  : List (String × Atoms)
  start  : Atoms
  shapes : List ShapeNode
  tes    : List TeEntry
deriving Inhabited

def flatten (sch : Schema) : Flat :=
  let declWalks := sch.shapes.map (fun d => (d.id, seWalk d.id false d.expr))
  let (startAtoms, startAcc) := match sch.start with
    | some e => seWalk "start" false e
    | none   => ({}, {})
  let acc := declWalks.foldl (fun a (_, (_, c)) => a.append c) startAcc
  { decls := declWalks.map (fun (l, (a, _)) => (l, a)),
    start := startAtoms, shapes := acc.shapes, tes := acc.tes }

/-! ## Closures -/

def dedupS (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def declAtoms (f : Flat) (l : String) : Atoms :=
  match f.decls.find? (fun (k, _) => k == l) with
  | some (_, a) => a
  | none        => {}

/-- The shapeExprRef closure of a list of directly referenced labels
    (§5.7.2), by fixed-point iteration bounded by the declaration
    count. -/
def refClosureGo (f : Flat) : Nat → List String → List String → List String
  | 0, seen, _ => seen
  | n + 1, seen, frontier =>
      let next := dedupS ((frontier.flatMap (fun l => (declAtoms f l).refs.map (·.1))).filter
        (fun l => !seen.contains l))
      if next.isEmpty then seen else refClosureGo f n (seen ++ next) next

def refClosure (f : Flat) (direct : List String) : List String :=
  let d := dedupS direct
  refClosureGo f (f.decls.length + 1) d d

def teEntry? (f : Flat) (l : String) : Option TeEntry :=
  f.tes.find? (fun e => e.id == l)

/-- The tripleExprRef closure (§5.7.3) of a list of included labels. -/
def teClosureGo (f : Flat) : Nat → List String → List String → List String
  | 0, seen, _ => seen
  | n + 1, seen, frontier =>
      let next := dedupS ((frontier.flatMap (fun l =>
          match teEntry? f l with
          | some e => e.includes
          | none   => [])).filter (fun l => !seen.contains l))
      if next.isEmpty then seen else teClosureGo f n (seen ++ next) next

def teClosure (f : Flat) (direct : List String) : List String :=
  let d := dedupS direct
  teClosureGo f (f.tes.length + 1) d d

/-- The atomic shapes of a set of atoms (§5.7.4 atomicShapes), each
    with its `ShapeNot` parity, following shape references. A
    (label, parity) pair is expanded once. -/
def atomicShapesGo (f : Flat) :
    Nat → List (String × Bool) → List (String × Bool) → List (String × Bool) →
    List (String × Bool)
  | 0, _, acc, _ => acc
  | n + 1, seen, acc, frontier =>
      let fresh := frontier.filter (fun p => !seen.contains p)
      if fresh.isEmpty then acc
      else
        let expanded : List (List (String × Bool) × List (String × Bool)) :=
          fresh.map (fun (p : String × Bool) =>
            let a := declAtoms f p.1
            (a.shapes.map (fun (q : String × Bool) => (q.1, p.2 != q.2)),
             a.refs.map (fun (q : String × Bool) => (q.1, p.2 != q.2))))
        atomicShapesGo f n (seen ++ fresh) (acc ++ expanded.flatMap (·.1))
          (expanded.flatMap (·.2))

def atomicShapes (f : Flat) (a : Atoms) : List (String × Bool) :=
  atomicShapesGo f (2 * f.decls.length + 2) [] a.shapes a.refs

/-- The atomic triple constraints of a Shape (§5.7.4
    atomicTripleConstraints): those written in it and those reached
    through `&label` inclusions. -/
def atomicTcs (f : Flat) (s : ShapeNode) : List TcNode :=
  s.tcs ++ (teClosure f s.includes).flatMap (fun l =>
    match teEntry? f l with
    | some e => e.tcs
    | none   => [])

/-! ## The dependency graph (§5.7.4) -/

/-- Edges `(from, to, negated)` between Shape paths. -/
def edges (f : Flat) : List (String × String × Bool) :=
  f.shapes.flatMap (fun s1 =>
    let viaTcs := (atomicTcs f s1).flatMap (fun tc =>
      let extraNeg := !tc.inverse && s1.extra.contains tc.predicate
      (atomicShapes f tc.value).map (fun (s2, neg) => (s1.path, s2, neg || extraNeg)))
    let viaExtends := s1.extendsRefs.flatMap (fun l =>
      (atomicShapes f { refs := [(l, false)] }).map (fun (s2, neg) => (s1.path, s2, neg)))
    viaTcs ++ viaExtends)

/-- Shapes reachable from `frontier` along any edge. -/
def reachGo (es : List (String × String × Bool)) :
    Nat → List String → List String → List String
  | 0, seen, _ => seen
  | n + 1, seen, frontier =>
      let next := dedupS ((frontier.flatMap (fun a =>
        es.filterMap (fun (x, y, _) => if x == a then some y else none))).filter
          (fun y => !seen.contains y))
      if next.isEmpty then seen else reachGo es n (seen ++ next) next

def reachable (es : List (String × String × Bool)) (n : Nat) (src dst : String) : Bool :=
  (reachGo es (n + 1) [src] [src]).contains dst

/-- The first negated edge that lies on a cycle, if any. -/
def negatedCycle (f : Flat) : Option (String × String) :=
  let es := edges f
  let n := f.shapes.length
  (es.find? (fun (a, b, neg) => neg && reachable es n b a)).map (fun (a, b, _) => (a, b))

/-! ## The requirements -/

/-- Every shape label a schema references, from declarations, the start
    expression, triple-constraint values and `EXTENDS`. -/
def referencedShapeLabels (f : Flat) : List String :=
  dedupS (f.decls.flatMap (fun (_, a) => a.refs.map (·.1)) ++ f.start.refs.map (·.1) ++
    f.shapes.flatMap (fun s => s.tcs.flatMap (fun tc => tc.value.refs.map (·.1)) ++ s.extendsRefs) ++
    f.tes.flatMap (fun e => e.tcs.flatMap (fun tc => tc.value.refs.map (·.1))))

def includedLabels (f : Flat) : List String :=
  dedupS (f.shapes.flatMap (·.includes) ++ f.tes.flatMap (·.includes))

/-- Every violation of the checked ShEx 2.1 §5.7 requirements. -/
def structureErrors (sch : Schema) : List String :=
  let f := flatten sch
  let shapeLabels := sch.shapes.map (·.id)
  let teLabels := f.tes.map (·.id)
  let local' := sch.imports.isEmpty
  let collisions := (dedupS shapeLabels).filter (teLabels.contains ·)
  let dupShapes := (dedupS shapeLabels).filter (fun l => (shapeLabels.filter (· == l)).length > 1)
  let dupTes := (dedupS teLabels).filter (fun l => (teLabels.filter (· == l)).length > 1)
  let missingShapes :=
    if local' then (referencedShapeLabels f).filter (fun l => !shapeLabels.contains l) else []
  let badIncludes := (includedLabels f).filter (fun l => !teLabels.contains l)
  let selfRefShapes := f.decls.filterMap (fun (l, a) =>
    if (refClosure f (a.refs.map (·.1))).contains l then some l else none)
  let selfRefTes := f.tes.filterMap (fun e =>
    if (teClosure f e.includes).contains e.id then some e.id else none)
  collisions.map (fun l => s!"{l} is both a shape expression label and a triple expression label") ++
  dupShapes.map (fun l => s!"shape expression label {l} is declared more than once") ++
  dupTes.map (fun l => s!"triple expression label {l} is declared more than once") ++
  missingShapes.map (fun l => s!"shape reference @{l} names no shape expression (§5.7.2)") ++
  badIncludes.filterMap (fun l =>
    if shapeLabels.contains l then some s!"&{l} names a shape expression, not a triple expression (§5.7.3)"
    else if local' then some s!"&{l} names no triple expression (§5.7.3)"
    else none) ++
  selfRefShapes.map (fun l => s!"shape label {l} is in the shapeExprRef closure of its own definition (§5.7.2)") ++
  selfRefTes.map (fun l => s!"triple expression label {l} is in the tripleExprRef closure of its own definition (§5.7.3)") ++
  (match negatedCycle f with
   | some (a, b) => [s!"the dependency graph has a cycle through the negated reference {a} -> {b} (§5.7.4)"]
   | none => [])

end L4Factoidal.ShEx.Structure
