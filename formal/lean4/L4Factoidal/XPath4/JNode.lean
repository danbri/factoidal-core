/-
L4Factoidal.XPath4.JNode — JNodes (XDM 4.0 §8.5): the j-children
accessor, the item axis, the parent, identity and document order
(XDM 4.0 §6.2), and the root identity that `fn:jtree` gives.

A JNode is the `Item.jnode` zipper: the identity of its root, the path
up to the root (nearest step first), its ·jvalue·, and the ·jvalue·s of
its ancestors. A child is made by pushing one step; the parent by
popping one. Nothing is stored in the maps and arrays themselves.

Root identity. The evaluator is pure and threads no counter, so a root
JNode's identity is a 64-bit hash of its ·jvalue· mixed with a salt that
names how the root was made: `fn:jtree` uses salt 0, and the implicit
`fn:jtree` of `E1/E2` and of an axis step uses the position of the item
in the sequence it came from. F&O 4.0 §16.1.1 allows this: two calls on
equal input "may return the same JNode, or distinct (but deep-equal)
JNodes". So `jtree($x) is jtree($x)` is true here, `($m, $m)/a` gives
two JNodes, and two equal maps at different positions of `E1` give
distinct trees. Identity within one tree is exact (root, then the step
positions); a collision of the 64-bit hash between two different roots
is the only way two distinct trees could compare as one.
-/
import L4Factoidal.XPath4.Syntax

namespace L4Factoidal.XPath4

/-! ## Hashing a value (for root identity) -/

def hMix (h x : UInt64) : UInt64 :=
  let h := h ^^^ (x + (0x9e3779b97f4a7c15 : UInt64) + (h <<< (6 : UInt64)) + (h >>> (2 : UInt64)))
  h * (0x100000001b3 : UInt64)

def hStr (s : String) : UInt64 := hash s

def hAtom (a : Atomic) : UInt64 := hMix (hStr a.ty.name) (hStr a.str)

/-- A structural hash of a value, with fuel for the nesting depth. -/
def hashSeqF : Nat → UInt64 → List Item → UInt64
  | 0, h, _ => h
  | f + 1, h, s => s.foldl (fun h i => hashItemF f h i) (hMix h 0x51)
where
  hashItemF : Nat → UInt64 → Item → UInt64
  | 0, h, _ => h
  | f + 1, h, i =>
    match i with
    | .atom a => hMix (hMix h 1) (hAtom a)
    | .node n => hMix (hMix (hMix h 2) n.doc.toUInt64) n.idx.toUInt64
    | .map kvs => kvs.foldl (fun h (k, v) => hashSeqF f (hMix h (hAtom k)) v) (hMix h 3)
    | .arr ms => ms.foldl (fun h m => hashSeqF f h m) (hMix h 4)
    | .fn (.builtin q k) => hMix (hMix (hMix h 5) (hStr q.eqn)) k.toUInt64
    | .fn _ => hMix h 6
    | .jnode r st _ _ => st.foldl (fun h s => hMix h s.pos.toUInt64) (hMix (hMix h 7) r)

def hashSeq (s : List Item) : UInt64 := hashSeqF 10000 0xcbf29ce484222325 s

/-- A new root JNode wrapping `v` (the result of `fn:jtree`). -/
def mkJRoot (salt : UInt64) (v : List Item) : Item :=
  .jnode (hMix (hashSeq v) salt) [] v []

/-- Wrap a map or array as a root JNode (the implicit `fn:jtree` of
    XPath 4.0 §4.7.3 and §4.7.5); other items are unchanged. -/
def jwrap (salt : UInt64) (i : Item) : Item :=
  match i with
  | .map _ | .arr _ => mkJRoot (hMix salt 0xa1) [i]
  | _ => i

/-! ## Accessors -/

def Item.isJNode : Item → Bool | .jnode .. => true | _ => false
def Item.isGNode : Item → Bool | .node _ | .jnode .. => true | _ => false

/-- ·jvalue· of a JNode. -/
def jvalOf : Item → List Item
  | .jnode _ _ v _ => v
  | _ => []

/-- ·jkey· of a JNode; `none` for a root. -/
def jkeyOf : Item → Option Atomic
  | .jnode _ (s :: _) _ _ => some s.key
  | _ => none

/-- The j-children of a JNode (XDM 4.0 §8.5), in order. -/
def jchildren : Item → List Item
  | .jnode r st v up =>
    let up' := v :: up
    match v with
    | [.map kvs] =>
        (kvs.zip (List.range kvs.length)).map (fun ((k, x), i) =>
          .jnode r (⟨k, i + 1⟩ :: st) x up')
    | [.arr ms] =>
        (ms.zip (List.range ms.length)).map (fun (m, i) =>
          .jnode r (⟨Atomic.ofInt (i + 1), i + 1⟩ :: st) m up')
    | _ :: _ :: _ =>
        (v.zip (List.range v.length)).map (fun (x, i) =>
          .jnode r (⟨Atomic.ofInt (i + 1), i + 1⟩ :: st) [x] up')
    | _ => []
  | _ => []

/-- The item axis (XPath 4.0 §4.7.5.1) of a JNode. -/
def jitems : Item → List Item
  | j@(.jnode r st v up) =>
    match v with
    | [] => []
    | [x] => [.jnode r (⟨Atomic.ofInt 1, 0⟩ :: st) [x] (v :: up)]
    | _ => jchildren j
  | _ => []

/-- ·jparent·. -/
def jparent : Item → Option Item
  | .jnode r (_ :: st) _ (p :: up) => some (.jnode r st p up)
  | _ => none

/-- The ancestors, nearest first. -/
def jancestors : Item → List Item
  | .jnode r st _ up =>
    let rec go : List JStep → List (List Item) → List Item → List Item
      | _ :: st', p :: up', acc => go st' up' (.jnode r st' p up' :: acc)
      | _, _, acc => acc.reverse
    go st up []
  | _ => []

/-- The root of the JTree. -/
def jrootOf : Item → Item
  | j@(.jnode r _ _ up) =>
    match up.getLast? with
    | some top => .jnode r [] top []
    | none => j
  | i => i

/-- The siblings that are j-children of the same parent, without the
    JNode itself: (before, after), each in document order. -/
def jsiblings (j : Item) : List Item × List Item :=
  match j, jparent j with
  | .jnode _ (s :: _) _ _, some p =>
      if s.pos == 0 then ([], []) else
      let cs := jchildren p
      (cs.take (s.pos - 1), cs.drop s.pos)
  | _, _ => ([], [])

/-- The descendants in document order (fuel-bounded worklist loop). -/
def jdescendants (j : Item) (fuel : Nat := 50000000) : List Item :=
  let rec go : Nat → List Item → Array Item → Array Item
    | 0, _, acc => acc
    | _, [], acc => acc
    | f + 1, x :: rest, acc => go f (jchildren x ++ rest) (acc.push x)
  (go fuel (jchildren j) #[]).toList

/-- The following JNodes in document order: the following siblings of the
    JNode and of each ancestor, each with its descendants (XPath 4.0
    §4.7.5.1, `ancestor-or-self::node()/following-sibling::node()/
    descendant-or-self::node()`). -/
def jfollowing (j : Item) : List Item :=
  (j :: jancestors j).flatMap (fun a => (jsiblings a).2.flatMap (fun s => s :: jdescendants s))

/-- The preceding JNodes in document order (the same with preceding
    siblings, root-most ancestor first). -/
def jpreceding (j : Item) : List Item :=
  (j :: jancestors j).reverse.flatMap (fun a => (jsiblings a).1.flatMap (fun s => s :: jdescendants s))

/-- An axis from a JNode origin, in axis order (reverse document order
    for a reverse axis). The attribute and namespace axes are type
    errors on a JNode; the caller raises them. -/
def jaxis (ax : Axis) (j : Item) : List Item :=
  match ax with
  | .child => jchildren j
  | .descendant => jdescendants j
  | .descendantOrSelf => j :: jdescendants j
  | .self => [j]
  | .parent => (jparent j).toList
  | .ancestor => jancestors j
  | .ancestorOrSelf => j :: jancestors j
  | .followingSibling => (jsiblings j).2
  | .followingSiblingOrSelf => j :: (jsiblings j).2
  | .precedingSibling => (jsiblings j).1.reverse
  | .precedingSiblingOrSelf => j :: (jsiblings j).1.reverse
  | .following => jfollowing j
  | .followingOrSelf => j :: jfollowing j
  | .preceding => (jpreceding j).reverse
  | .precedingOrSelf => j :: (jpreceding j).reverse
  | .item => jitems j
  | .attribute | .namespace => []

/-- Does the ·jkey· of `j` equal one of `ks` (`fn:atomic-equal`)? The
    selector of XPath 4.0 §4.7.5.4 and §4.7.3 (selector interpretation). -/
def jkeyIn (ks : List Atomic) (j : Item) : Bool :=
  match jkeyOf j with
  | some k => ks.any (fun a => atomicEqual a k)
  | none => false

/-- The j-children whose key is one of `ks`. -/
def jselect (j : Item) (ks : List Atomic) : List Item :=
  if ks.isEmpty then [] else (jchildren j).filter (jkeyIn ks)

/-! ## Identity and document order -/

/-- The step positions from the root down. -/
def jposPath : Item → List Nat
  | .jnode _ st _ _ => (st.map (·.pos)).reverse
  | _ => []

def jrootId : Item → UInt64
  | .jnode r _ _ _ => r
  | _ => 0

/-- JNode identity (XDM 4.0 §8.5). -/
def jsame (a b : Item) : Bool :=
  match a, b with
  | .jnode r1 s1 _ _, .jnode r2 s2 _ _ =>
      r1 == r2 && s1.length == s2.length && (s1.zip s2).all (fun (x, y) => x.pos == y.pos)
  | _, _ => false

def natListLt : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | _, [] => false
  | x :: xs, y :: ys => x < y || (x == y && natListLt xs ys)

/-- Document order between two JNodes: by root, then a parent before its
    children, then children in order (XPath 4.0 §2.7.1 / XDM 4.0 §6.2). -/
def jbefore (a b : Item) : Bool :=
  let ra := jrootId a
  let rb := jrootId b
  ra < rb || (ra == rb && natListLt (jposPath a) (jposPath b))

end L4Factoidal.XPath4
