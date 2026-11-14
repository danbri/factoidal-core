/-
L4Factoidal.MathML.CoreVocabulary — the Presentation output uses MathML Core elements only.

Specification: MathML Core, W3C Candidate Recommendation Snapshot 24 June 2025
(https://www.w3.org/TR/2025/CR-mathml-core-20250624/), section 2.1 "Elements and attributes": the list
of MathML Core elements, copied below as `coreElements`.

`Present.pres` builds a string. A statement about "every element name in the output" needs the
output as a tree, so `presTree` builds the same output as a tree of `PNode`, branch for branch, and
the theorem is a structural induction over that tree. `serializeList (presTree e) "" = pres e` is checked by
`#guard` on an expression for each branch of `pres`; it is not proved (see the design record
`docs/designissues/2026-10-28-mathml-finish.md`).

The output has no attributes: `PNode.elem` has no attribute field. The only attribute in
`toPresentationMathML e` is the namespace declaration `xmlns` that `mathDoc` writes on `math`.
-/
import L4Factoidal.MathML.Present
import L4Factoidal.MathML.Strict

namespace L4Factoidal.MathML

/-- The MathML Core elements (MathML Core CR Snapshot 2025-06-24, section 2.1). -/
def coreElements : List String :=
  ["annotation", "annotation-xml", "maction", "math", "merror", "mfrac", "mi", "mmultiscripts", "mn",
   "mo", "mover", "mpadded", "mphantom", "mprescripts", "mroot", "mrow", "ms", "mspace", "msqrt",
   "mstyle", "msub", "msubsup", "msup", "mtable", "mtd", "mtext", "mtr", "munder", "munderover",
   "semantics"]

/-- Presentation markup as a tree. `text` holds character data as it is written (escaped). -/
inductive PNode where
  | text (raw : String)
  | elem (name : String) (children : List PNode)
deriving Repr, Inhabited

mutual
/-- Every element name in the tree is a MathML Core element. -/
def namesOk : PNode → Bool
  | .text _       => true
  | .elem name cs => coreElements.contains name && namesOkList cs
def namesOkList : List PNode → Bool
  | []      => true
  | n :: ns => namesOk n && namesOkList ns
end

mutual
def serialize : PNode → String
  | .text raw     => raw
  | .elem name cs => serializeList cs ("<" ++ name ++ ">") ++ "</" ++ name ++ ">"
/-- The nodes of a list, appended to `acc` in order (a loop over the list). -/
def serializeList : List PNode → String → String
  | [], acc      => acc
  | n :: ns, acc => serializeList ns (acc ++ serialize n)
end

theorem namesOkList_append (a b : List PNode) :
    namesOkList (a ++ b) = (namesOkList a && namesOkList b) := by
  induction a with
  | nil => simp [namesOkList]
  | cons x xs ih => simp [namesOkList, ih, Bool.and_assoc]

/-! ## The tree `pres` writes -/

def moT (raw : String) : PNode := .elem "mo" [.text raw]

def fenceT (s : List PNode) : List PNode := [.elem "mrow" (moT "(" :: s ++ [moT ")"])]

def fencedT (minp p : Int) (s : List PNode) : List PNode := if p < minp then fenceT s else s

/-- `relationToken` as a node. -/
def relationTokenT (fn : String) : PNode :=
  if fn == "eq" then moT "="
  else if fn == "neq" then moT "&#x2260;"
  else if fn == "lt" then moT "&lt;"
  else if fn == "gt" then moT "&gt;"
  else if fn == "leq" then moT "&#x2264;"
  else moT "&#x2265;"

mutual

/-- `Present.pres`, as a tree: the same branches in the same order. -/
def presTree : Expr → List PNode
  | .int n   => [.elem "mn" [.text (toString n)]]
  | .rat n d => [.elem "mfrac" [.elem "mn" [.text (toString n)], .elem "mn" [.text (toString d)]]]
  | .bool b  => [.elem "mi" [.text (if b then "true" else "false")]]
  | .sym s   => [.elem "mi" [.text (escapeXmlFull s)]]
  | .mat rws => [.elem "mrow" [moT "(", .elem "mtable" (presRowsT rws), moT ")"]]
  | .vec xs  => [.elem "mrow" [moT "(", .elem "mtable" (presCellsT xs), moT ")"]]
  | .app fn args =>
      let fallback : Unit → List PNode := fun _ => presApplyT fn args
      if fn == "plus" then
        match args with
        | []        => [.elem "mn" [.text (toString (0 : Int))]]
        | a :: rest => fencedT 1 (prec a) (presTree a) ++ presJoinT (moT "+") 1 rest
      else if fn == "minus" then
        match args with
        | [a]    => moT "-" :: fencedT 2 (prec a) (presTree a)
        | [a, b] => fencedT 1 (prec a) (presTree a) ++ moT "-" :: fencedT 2 (prec b) (presTree b)
        | _      => fallback ()
      else if fn == "times" then
        match args with
        | []        => [.elem "mn" [.text (toString (1 : Int))]]
        | a :: rest => fencedT 2 (prec a) (presTree a) ++ presJoinT (moT "&#x2062;") 2 rest
      else if fn == "divide" then
        match args with
        | [a, b] => [.elem "mfrac" [.elem "mrow" (presTree a), .elem "mrow" (presTree b)]]
        | _      => fallback ()
      else if fn == "power" then
        match args with
        | [a, b] =>
            [.elem "msup" [.elem "mrow" (fencedT 4 (prec a) (presTree a)), .elem "mrow" (presTree b)]]
        | _ => fallback ()
      else if fn == "root" then
        match args with
        | [a]    => [.elem "msqrt" [.elem "mrow" (presTree a)]]
        | [d, a] => [.elem "mroot" [.elem "mrow" (presTree a), .elem "mrow" (presTree d)]]
        | _      => fallback ()
      else if isRelation fn then
        match args with
        | a :: rest => fencedT 1 (prec a) (presTree a) ++ presJoinT (relationTokenT fn) 1 rest
        | []        => fallback ()
      else if fn == "abs" then
        match args with
        | [a] => [.elem "mrow" (moT "|" :: presTree a ++ [moT "|"])]
        | _   => fallback ()
      else if fn == "factorial" then
        match args with
        | [a] => fencedT 4 (prec a) (presTree a) ++ [moT "!"]
        | _   => fallback ()
      else if fn == "exp" then
        match args with
        | [a] => [.elem "msup" [.elem "mi" [.text "e"], .elem "mrow" (presTree a)]]
        | _   => fallback ()
      else if fn == "diff_unsupported" then
        [.elem "merror" [.elem "mtext" [.text "unsupported derivative"]]]
      else fallback ()
termination_by e => (sizeOf e, 0)

def presJoinT (tok : PNode) (minp : Int) : List Expr → List PNode
  | []        => []
  | a :: rest => tok :: fencedT minp (prec a) (presTree a) ++ presJoinT tok minp rest
termination_by es => (sizeOf es, 1)

def presApplyT (fn : String) (args : List Expr) : List PNode :=
  [.elem "mrow" (.elem "mi" [.text (escapeXmlFull fn)] :: moT "&#x2061;" :: moT "(" ::
    presApplyArgsT args ++ [moT ")"])]
termination_by (sizeOf args, 2)

def presApplyArgsT : List Expr → List PNode
  | []        => []
  | [a]       => presTree a
  | a :: rest => presTree a ++ moT "," :: presApplyArgsT rest
termination_by es => (sizeOf es, 1)

def presRowsT : List (List Expr) → List PNode
  | []        => []
  | r :: rest => .elem "mtr" (presCellsT r) :: presRowsT rest
termination_by rws => (sizeOf rws, 1)

def presCellsT : List Expr → List PNode
  | []        => []
  | a :: rest => .elem "mtd" (presTree a) :: presCellsT rest
termination_by es => (sizeOf es, 1)

end

/-- The whole document as a tree: `math` around `presTree`. -/
def presentationTree (e : Expr) : PNode := .elem "math" (presTree e)

/-! ## The theorem -/

@[simp] theorem namesOk_moT (raw : String) : namesOk (moT raw) = true := by
  simp [moT, namesOk, namesOkList, coreElements]

@[simp] theorem namesOk_relationTokenT (fn : String) : namesOk (relationTokenT fn) = true := by
  unfold relationTokenT
  repeat' split
  all_goals simp

theorem namesOk_fencedT (minp p : Int) (s : List PNode) (h : namesOkList s = true) :
    namesOkList (fencedT minp p s) = true := by
  unfold fencedT
  split
  · simp [fenceT, namesOk, namesOkList, namesOkList_append, coreElements, h]
  · exact h

theorem namesOk_presJoinT (tok : PNode) (minp : Int) (htok : namesOk tok = true) :
    ∀ l : List Expr, (∀ c ∈ l, namesOkList (presTree c) = true) →
      namesOkList (presJoinT tok minp l) = true
  | [], _ => by simp [presJoinT, namesOkList]
  | a :: rest, h => by
      have ha := namesOk_fencedT minp (prec a) _ (h a (by simp))
      have hr := namesOk_presJoinT tok minp htok rest (fun c hc => h c (by simp [hc]))
      simp [presJoinT, namesOkList, namesOkList_append, htok, ha, hr]

theorem namesOk_presApplyArgsT :
    ∀ l : List Expr, (∀ c ∈ l, namesOkList (presTree c) = true) →
      namesOkList (presApplyArgsT l) = true
  | [], _ => by simp [presApplyArgsT, namesOkList]
  | [a], h => by simpa [presApplyArgsT] using h a (by simp)
  | a :: b :: rest, h => by
      have ha := h a (by simp)
      have hr := namesOk_presApplyArgsT (b :: rest) (fun c hc => h c (by simp [hc]))
      simp [presApplyArgsT, namesOkList, namesOkList_append, ha, hr]

theorem namesOk_presApplyT (fn : String) (l : List Expr)
    (h : ∀ c ∈ l, namesOkList (presTree c) = true) : namesOkList (presApplyT fn l) = true := by
  have := namesOk_presApplyArgsT l h
  simp [presApplyT, namesOk, namesOkList, namesOkList_append, coreElements, this]

theorem namesOk_presCellsT :
    ∀ l : List Expr, (∀ c ∈ l, namesOkList (presTree c) = true) →
      namesOkList (presCellsT l) = true
  | [], _ => by simp [presCellsT, namesOkList]
  | a :: rest, h => by
      have ha := h a (by simp)
      have hr := namesOk_presCellsT rest (fun c hc => h c (by simp [hc]))
      simp [presCellsT, namesOk, namesOkList, coreElements, ha, hr]

theorem namesOk_presRowsT :
    ∀ l : List (List Expr), (∀ r ∈ l, ∀ c ∈ r, namesOkList (presTree c) = true) →
      namesOkList (presRowsT l) = true
  | [], _ => by simp [presRowsT, namesOkList]
  | r :: rest, h => by
      have hr := namesOk_presCellsT r (h r (by simp))
      have hrest := namesOk_presRowsT rest (fun r' hr' => h r' (by simp [hr']))
      simp [presRowsT, namesOk, namesOkList, coreElements, hr, hrest]

/-- Theorem 3 of `docs/designissues/2026-10-28-mathml-finish.md` (invariant), on the tree. Says:
    every element name in `presTree e` is a MathML Core element (CR Snapshot 2025-06-24, section
    2.1), for every expression.
    Does not say: that the string `Present.pres e` is the serialisation of this tree (tested by
    `#guard`, not proved), that the nesting is valid MathML Core (a vector's `mtd` sits directly in
    `mtable`), or anything about rendering. -/
theorem presTree_core : ∀ e, namesOkList (presTree e) = true := by
  apply Expr.childInduction
  intro e ih
  cases e with
  | int n => simp [presTree, namesOk, namesOkList, coreElements]
  | rat n d => simp [presTree, namesOk, namesOkList, coreElements]
  | bool b => simp [presTree, namesOk, namesOkList, coreElements]
  | sym s => simp [presTree, namesOk, namesOkList, coreElements]
  | vec xs =>
      simp only [children] at ih
      have := namesOk_presCellsT xs ih
      simp [presTree, namesOk, namesOkList, coreElements, this]
  | mat rws =>
      simp only [children] at ih
      have := namesOk_presRowsT rws (fun r hr c hc => ih c (List.mem_flatten.mpr ⟨r, hr, hc⟩))
      simp [presTree, namesOk, namesOkList, coreElements, this]
  | app fn args =>
      simp only [children] at ih
      have hfb := namesOk_presApplyT fn args ih
      -- The facts each branch needs, stated over `args` so that they follow the case split.
      have hall : ∀ c ∈ args, namesOkList (presTree c) = true := ih
      have hfen : ∀ (m : Int), ∀ c ∈ args, namesOkList (fencedT m (prec c) (presTree c)) = true :=
        fun m c hc => namesOk_fencedT m _ _ (ih c hc)
      have hjoin : ∀ (tok : PNode) (m : Int), namesOk tok = true →
          namesOkList (presJoinT tok m args.tail) = true :=
        fun tok m ht => namesOk_presJoinT tok m ht args.tail
          (fun c hc => ih c (List.mem_of_mem_tail hc))
      unfold presTree
      -- Remove the `let`, and write each test `fn == "name"` as `fn = "name"`.
      simp only [beq_iff_eq]
      by_cases h0 : fn = "plus"
      · rw [if_pos h0]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h0]
      by_cases h1 : fn = "minus"
      · rw [if_pos h1]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h1]
      by_cases h2 : fn = "times"
      · rw [if_pos h2]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h2]
      by_cases h3 : fn = "divide"
      · rw [if_pos h3]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h3]
      by_cases h4 : fn = "power"
      · rw [if_pos h4]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h4]
      by_cases h5 : fn = "root"
      · rw [if_pos h5]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h5]
      by_cases h6 : isRelation fn = true
      · rw [if_pos h6]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h6]
      by_cases h7 : fn = "abs"
      · rw [if_pos h7]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h7]
      by_cases h8 : fn = "factorial"
      · rw [if_pos h8]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h8]
      by_cases h9 : fn = "exp"
      · rw [if_pos h9]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h9]
      by_cases h10 : fn = "diff_unsupported"
      · rw [if_pos h10]
        (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;>
          (try simp only [List.tail_cons, List.tail_nil] at hjoin) <;>
          first
            | exact hfb
            | (simp [namesOk, namesOkList, namesOkList_append, coreElements, hall, hfen, hjoin, hfb]; done))
      rw [if_neg h10]
      exact hfb

/-- Theorem 3, on the document. Says: every element name in the tree of the whole `math` document
    is a MathML Core element.
    Does not say: more than `presTree_core` does. -/
theorem presentationTree_core (e : Expr) : namesOk (presentationTree e) = true := by
  simp [presentationTree, namesOk, coreElements, presTree_core e]

/-! ## The tree against the string writer (tests) -/

private def sameAsPres (e : Expr) : Bool := serializeList (presTree e) "" == pres e

#guard sameAsPres (.int (-3))
#guard sameAsPres (.rat 1 2)
#guard sameAsPres (.bool true)
#guard sameAsPres (.sym "a<b")
#guard sameAsPres (.mat [[.int 1, .sym "x"], [.rat 1 2, .int 4]])
#guard sameAsPres (.vec [.int 1, .int 2])
#guard sameAsPres (.app "plus" [])
#guard sameAsPres (.app "plus" [.int 1, .app "times" [.int 2, .app "plus" [.sym "x", .int 3]], .int (-4)])
#guard sameAsPres (.app "minus" [.app "plus" [.int 1, .int 2]])
#guard sameAsPres (.app "minus" [.int 1, .app "minus" [.int 2, .int 3]])
#guard sameAsPres (.app "minus" [.int 1, .int 2, .int 3])
#guard sameAsPres (.app "times" [])
#guard sameAsPres (.app "divide" [.int 1, .app "plus" [.sym "x", .int 1]])
#guard sameAsPres (.app "divide" [.int 1])
#guard sameAsPres (.app "power" [.app "plus" [.sym "x", .int 1], .int 2])
#guard sameAsPres (.app "power" [.int 2])
#guard sameAsPres (.app "root" [.sym "x"])
#guard sameAsPres (.app "root" [.int 3, .sym "x"])
#guard sameAsPres (.app "root" [])
#guard sameAsPres (.app "lt" [.int 1, .sym "x", .app "eq" [.int 1, .int 2]])
#guard sameAsPres (.app "neq" [.int 1, .int 2])
#guard sameAsPres (.app "geq" [])
#guard sameAsPres (.app "abs" [.app "minus" [.sym "x"]])
#guard sameAsPres (.app "abs" [])
#guard sameAsPres (.app "factorial" [.app "plus" [.sym "n", .int 1]])
#guard sameAsPres (.app "factorial" [])
#guard sameAsPres (.app "exp" [.sym "x"])
#guard sameAsPres (.app "exp" [])
#guard sameAsPres (.app "diff_unsupported" [.sym "x"])
#guard sameAsPres (.app "f&g" [.int 1, .sym "y", .app "h" []])
#guard toPresentationMathML (.app "plus" [.int 1, .sym "x"])
  == "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">" ++
     serializeList (presTree (.app "plus" [.int 1, .sym "x"])) "" ++ "</math>"
#guard namesOk (presentationTree (.app "root" [.int 3, .mat [[.int 1]]]))
#guard !namesOk (.elem "mfenced" [])

#print axioms presTree_core
#print axioms presentationTree_core

end L4Factoidal.MathML
