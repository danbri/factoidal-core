/-
L4Factoidal.XSLT4.Streaming.Select — streamed evaluation of a core of
streamable XSLT: downward selection with burst-mode copies.

The core is the construct that XSLT Streaming 4.0 §4 uses as its first
example and that windowed streaming is built on (§12.4: "grounded consuming
constructs"):

    <xsl:source-document streamable="yes" href="...">
      <xsl:copy-of select="/a/b/c"/>   (or copy-of(/a/b/c), count(/a/b/c), ...)
    </xsl:source-document>

A path of child steps with name tests is striding (§12.8.10); `copy-of`
of a striding operand is grounded and consuming (§3.10). The streamed
evaluation reads the event stream once (`Streaming.Events`): outside a
selected element it keeps one status per open element (how many steps of
the path its ancestors matched); inside a selected element it builds that
element's subtree (burst mode) and gives it when the element ends.

Theorems (no `sorry`):
* `streamSelect_eventsList`, `streamSelect_docEvents`: the streamed
  evaluation gives exactly the nodes that the tree evaluation `selList`
  selects, in document order, as whole subtrees.
* `streamCount_docEvents`, `streamStrings_docEvents`: the same for the
  grounded results `count(P)` and the string values of `P` (the operands
  of `xsl:value-of`).

The other constructs of a streamable stylesheet are scored on the W3C
suite by the non-streaming evaluator after the analysis of
`Streaming.Check`; `l4xslt4 --stream-diff` compares this streamed core
with the XPath 4.0 evaluator on the suite's source documents.
-/
import L4Factoidal.XSLT4.Streaming.Events

namespace L4Factoidal.XSLT4.Streaming

open L4Factoidal.XML

/-- A name test: a name, or `*`. -/
def nameMatch (t tag : String) : Bool := t == "*" || t == tag

/-- The axis of a step of the core: `child` (striding) or `descendant`
    (crawling; read by scanning, §12.8.9). -/
inductive SAxis where
  | child | descendant
deriving DecidableEq, Repr, Inhabited

/-- A motionless predicate (§12.10): it reads only the attributes that the
    start tag shows. `has a` is `[@a]`; `eq a v` is `[@a = 'v']`. -/
inductive APred where
  | has (a : String)
  | eq (a v : String)
deriving DecidableEq, Repr, Inhabited

def APred.holds (attrs : List Attribute) : APred → Bool
  | .has a => attrs.any (·.name == a)
  | .eq a v => attrs.any (fun x => x.name == a && x.value == v)

/-- A step of the core: axis, name test, predicates. -/
structure SStep where
  axis : SAxis := .child
  name : String
  preds : List APred := []
deriving Repr, Inhabited

def SStep.matches (s : SStep) (t : String) (a : List Attribute) : Bool :=
  nameMatch s.name t && s.preds.all (·.holds a)

/-- A path of the core. A descendant step that is not the last one selects,
    on each branch, the outermost elements it matches (the paths of the
    suite have a descendant step only at the end, where this is the XPath
    reading). -/
abbrev SPath := List SStep

/-! ## The tree evaluation -/

mutual
/-- The nodes that the path `p`, from step `k` on, selects at node `n`
    (the steps before `k` matched the ancestors of `n`). When the last step
    is a descendant step, a selected element is followed by the matches in
    its subtree, so the result is in document order. -/
def selNode (p : SPath) (k : Nat) : Node → List Node
  | .element t a cs =>
    match p[k]? with
    | some s =>
      if s.matches t a then
        if k + 1 = p.length then
          .element t a cs :: (if s.axis = .descendant then selList p k cs else [])
        else selList p (k + 1) cs
      else if s.axis = .descendant then selList p k cs else []
    | none => []
  | _ => []

def selList (p : SPath) (k : Nat) : List Node → List Node
  | [] => []
  | n :: ns => selNode p k n ++ selList p k ns
end

/-! ## The streamed evaluation -/

inductive Mode where
  | normal
  /-- Inside a selected element: the number of its open elements
      (itself included), the builder of its subtree, and, when the last
      step is a descendant step `k`, that step (the matches inside the
      subtree are taken from the built subtree). -/
  | burst (d : Nat) (b : BSt) (inner : Option Nat)
deriving Inhabited

structure SSt where
  /-- One status per open element outside a burst, innermost first:
      `some k` when its ancestors-or-self matched `k` steps, `none` when
      the path cannot continue below it. -/
  ctl : List (Option Nat)
  mode : Mode
  /-- The selected subtrees so far, newest first. -/
  out : List Node
deriving Inhabited

/-- The status of the current position (the document node matched zero
    steps). -/
def SSt.cur (st : SSt) : Option Nat := st.ctl.head?.getD (some 0)

/-- The matches of descendant step `k` inside a built subtree. -/
def innerMatches (p : SPath) : Option Nat → Node → List Node
  | some k, .element _ _ cs => selList p k cs
  | _, _ => []

def SSt.step (p : SPath) (st : SSt) (e : Event) : Option SSt :=
  match st.mode with
  | .normal =>
    match e with
    | .start t a =>
      match st.cur with
      | some k =>
        match p[k]? with
        | some s =>
          if s.matches t a then
            if k + 1 = p.length then
              some { st with mode := .burst 1 { stack := [{ tag := t, attrs := a, kids := [] }], top := [] }
                                  (if s.axis = .descendant then some k else none) }
            else some { st with ctl := some (k + 1) :: st.ctl }
          else if s.axis = .descendant then some { st with ctl := some k :: st.ctl }
          else some { st with ctl := none :: st.ctl }
        | none => some { st with ctl := none :: st.ctl }
      | none => some { st with ctl := none :: st.ctl }
    | .stop => match st.ctl with
      | _ :: cs => some { st with ctl := cs }
      | [] => none
    | _ => some st
  | .burst d b inner =>
    match e with
    | .start _ _ => (b.step e).map (fun b' => { st with mode := .burst (d + 1) b' inner })
    | .stop =>
      if d = 1 then
        match b.step e with
        | some { stack := [], top := [n] } =>
          some { st with mode := .normal, out := (innerMatches p inner n).reverse ++ n :: st.out }
        | _ => none
      else (b.step e).map (fun b' => { st with mode := .burst (d - 1) b' inner })
    | _ => (b.step e).map (fun b' => { st with mode := .burst d b' inner })

def SSt.run (p : SPath) : List Event → SSt → Option SSt
  | [], st => some st
  | e :: es, st => (st.step p e).bind (SSt.run p es)

/-- The streamed evaluation of `copy-of(P)` over an event stream. -/
def streamSelect (p : SPath) (es : List Event) : Option (List Node) :=
  (SSt.run p es { ctl := [], mode := .normal, out := [] }).map (fun st => st.out.reverse)

theorem SSt.run_append (p : SPath) (xs ys : List Event) (st : SSt) :
    SSt.run p (xs ++ ys) st = (SSt.run p xs st).bind (SSt.run p ys) := by
  induction xs generalizing st with
  | nil => simp [SSt.run]
  | cons e es ih =>
    simp only [List.cons_append, SSt.run]
    cases st.step p e with
    | none => rfl
    | some st' => simp [ih]

/-! ### Burst mode is the tree builder -/

mutual
theorem burst_events (p : SPath) (n : Node) (st : SSt) (d : Nat) (b : BSt) (inner : Option Nat) :
    SSt.run p (events n) { st with mode := .burst (d + 1) b inner } =
      some { st with mode := .burst (d + 1) (b.add n) inner } := by
  match n with
  | .element t a cs =>
    simp only [events, SSt.run, SSt.step, BSt.step, Option.map_some, Option.bind_some]
    rw [SSt.run_append]
    have h := burst_eventsList p cs st (d + 1) { b with stack := { tag := t, attrs := a, kids := [] } :: b.stack } inner
    rw [h]
    simp only [Option.bind_some]
    rw [foldl_add_frame]
    simp [SSt.run, SSt.step, BSt.step]
  | .text s => simp [events, SSt.run, SSt.step, BSt.step]
  | .comment s => simp [events, SSt.run, SSt.step, BSt.step]
  | .cdata s => simp [events, SSt.run, SSt.step, BSt.step]
  | .pi t x => simp [events, SSt.run, SSt.step, BSt.step]

theorem burst_eventsList (p : SPath) (ns : List Node) (st : SSt) (d : Nat) (b : BSt) (inner : Option Nat) :
    SSt.run p (eventsList ns) { st with mode := .burst (d + 1) b inner } =
      some { st with mode := .burst (d + 1) (ns.foldl BSt.add b) inner } := by
  match ns with
  | [] => simp [eventsList, SSt.run]
  | n :: rest =>
    simp only [eventsList]
    rw [SSt.run_append, burst_events]
    simp only [Option.bind_some]
    have h := burst_eventsList p rest { st with mode := .burst (d + 1) (b.add n) inner } d (b.add n) inner
    simp only at h
    rw [h]
    simp
end

/-! ### Normal mode is the tree selection -/

/-- The selection below a status: nothing below a dead branch. -/
def selAt (p : SPath) : Option Nat → Node → List Node
  | some k, n => selNode p k n
  | none, _ => []

def selAtList (p : SPath) : Option Nat → List Node → List Node
  | some k, ns => selList p k ns
  | none, _ => []

theorem selAtList_cons (p : SPath) (s : Option Nat) (n : Node) (ns : List Node) :
    selAtList p s (n :: ns) = selAt p s n ++ selAtList p s ns := by
  cases s <;> simp [selAtList, selAt, selList]

/-- The events of an element's children, then its end tag, from normal
    mode with the status `s` pushed. -/
theorem normal_children (p : SPath) (s : Option Nat) (cs : List Node) (ctl : List (Option Nat))
    (out : List Node) (rest : List Event)
    (ih : SSt.run p (eventsList cs) { ctl := s :: ctl, mode := .normal, out } =
      some { ctl := s :: ctl, mode := .normal, out := (selAtList p s cs).reverse ++ out }) :
    SSt.run p (eventsList cs ++ [Event.stop] ++ rest) { ctl := s :: ctl, mode := .normal, out } =
      SSt.run p rest { ctl, mode := .normal, out := (selAtList p s cs).reverse ++ out } := by
  rw [List.append_assoc, SSt.run_append, ih]
  simp [SSt.run, SSt.step]

mutual
theorem normal_events (p : SPath) (n : Node) (ctl : List (Option Nat)) (out : List Node) :
    SSt.run p (events n) { ctl, mode := .normal, out } =
      some { ctl, mode := .normal, out := (selAt p (SSt.cur { ctl, mode := .normal, out }) n).reverse ++ out } := by
  match n with
  | .element t a cs =>
    simp only [events, SSt.run]
    generalize hk : SSt.cur { ctl, mode := .normal, out } = k
    -- the cases that push a status and read the children in normal mode
    have push : ∀ (s : Option Nat), SSt.step p { ctl, mode := .normal, out } (.start t a) =
        some { ctl := s :: ctl, mode := .normal, out } →
        (SSt.run p (eventsList cs ++ [Event.stop]) { ctl := s :: ctl, mode := .normal, out }) =
          some { ctl, mode := .normal, out := (selAtList p s cs).reverse ++ out } := by
      intro s _
      have h := normal_children p s cs ctl out [] (by
        rw [normal_eventsList]; cases s <;> simp [SSt.cur, selAtList])
      simpa [SSt.run] using h
    cases k with
    | none =>
      have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
          some { ctl := none :: ctl, mode := .normal, out } := by
        simp [SSt.step, hk]
      rw [hs]; simp only [Option.bind_some]; rw [push none hs]
      simp [selAtList, selAt]
    | some k =>
      cases hp : p[k]? with
      | none =>
        have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
            some { ctl := none :: ctl, mode := .normal, out } := by
          simp [SSt.step, hk, hp]
        rw [hs]; simp only [Option.bind_some]; rw [push none hs]
        simp [selAtList, selAt, selNode, hp]
      | some s =>
        by_cases hm : s.matches t a = true
        · by_cases hl : k + 1 = p.length
          · have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
                some { ctl, mode := .burst 1 { stack := [{ tag := t, attrs := a, kids := [] }], top := [] }
                         (if s.axis = .descendant then some k else none), out } := by
              simp [SSt.step, hk, hp, hm, hl]
            rw [hs]
            simp only [Option.bind_some]
            rw [SSt.run_append]
            have h := burst_eventsList p cs { ctl, mode := .normal, out } 0
              { stack := [{ tag := t, attrs := a, kids := [] }], top := [] }
              (if s.axis = .descendant then some k else none)
            simp only at h
            rw [h]
            simp only [Option.bind_some]
            rw [foldl_add_frame]
            by_cases hax : s.axis = .descendant
            · simp [SSt.run, SSt.step, BSt.step, BSt.add, selAt, selNode, hp, hm, hl, hax, innerMatches]
            · simp [SSt.run, SSt.step, BSt.step, BSt.add, selAt, selNode, hp, hm, hl, hax, innerMatches]
          · have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
                some { ctl := some (k + 1) :: ctl, mode := .normal, out } := by
              simp [SSt.step, hk, hp, hm, hl]
            rw [hs]; simp only [Option.bind_some]; rw [push (some (k + 1)) hs]
            simp [selAtList, selAt, selNode, hp, hm, hl]
        · by_cases hax : s.axis = .descendant
          · have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
                some { ctl := some k :: ctl, mode := .normal, out } := by
              simp [SSt.step, hk, hp, hm, hax]
            rw [hs]; simp only [Option.bind_some]; rw [push (some k) hs]
            simp [selAtList, selAt, selNode, hp, hm, hax]
          · have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
                some { ctl := none :: ctl, mode := .normal, out } := by
              simp [SSt.step, hk, hp, hm, hax]
            rw [hs]; simp only [Option.bind_some]; rw [push none hs]
            simp [selAtList, selAt, selNode, hp, hm, hax]
  | .text s => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [events, SSt.run, SSt.step, selAt, selNode, h]
  | .comment s => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [events, SSt.run, SSt.step, selAt, selNode, h]
  | .cdata s => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [events, SSt.run, SSt.step, selAt, selNode, h]
  | .pi x y => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [events, SSt.run, SSt.step, selAt, selNode, h]

theorem normal_eventsList (p : SPath) (ns : List Node) (ctl : List (Option Nat)) (out : List Node) :
    SSt.run p (eventsList ns) { ctl, mode := .normal, out } =
      some { ctl, mode := .normal, out := (selAtList p (SSt.cur { ctl, mode := .normal, out }) ns).reverse ++ out } := by
  match ns with
  | [] => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [eventsList, SSt.run, selAtList, selList, h]
  | n :: rest =>
    simp only [eventsList]
    rw [SSt.run_append, normal_events]
    simp only [Option.bind_some]
    rw [normal_eventsList]
    simp [SSt.cur, selAtList_cons]
end

/-- **Streamed evaluation equals tree evaluation** for downward selection
    (child steps, a final descendant step, motionless attribute predicates)
    with burst-mode copies. -/
theorem streamSelect_eventsList (p : SPath) (ns : List Node) :
    streamSelect p (eventsList ns) = some (selList p 0 ns) := by
  simp [streamSelect, normal_eventsList, SSt.cur, selAtList]

theorem streamSelect_docEvents (p : SPath) (d : Document) :
    streamSelect p (docEvents d) = some (selList p 0 d.children) :=
  streamSelect_eventsList p d.children

/-! ### Memory: one status per open element

At every point of the stream, the selection processor keeps at most one
status per open element outside the copied subtree (`SSt.ctl`), so the
stack it keeps is bounded by the depth of the document, not by its size
(`streamSelect_ctl_le_depth`). The burst buffer holds one selected
subtree. -/

/-- The number of open elements after a list of events, from `k`. -/
def openAfter : List Event → Nat → Nat
  | [], k => k
  | .start _ _ :: es, k => openAfter es (k + 1)
  | .stop :: es, k => openAfter es (k - 1)
  | _ :: es, k => openAfter es k

theorem le_maxOpen (es : List Event) (k : Nat) : k ≤ maxOpen es k := by
  cases es with
  | nil => simp [maxOpen]
  | cons e es => cases e <;> simp only [maxOpen] <;> exact Nat.le_max_left _ _

theorem openAfter_take_le (es : List Event) (k n : Nat) : openAfter (es.take n) k ≤ maxOpen es k := by
  induction es generalizing k n with
  | nil => simp [openAfter, maxOpen]
  | cons e es ih =>
    cases n with
    | zero => simp [openAfter, le_maxOpen]
    | succ n =>
      cases e <;> simp only [List.take_succ_cons, openAfter, maxOpen] <;>
        exact Nat.le_trans (ih _ n) (Nat.le_max_right _ _)

/-- The invariant: outside a burst at most one status per open element;
    in a burst, the open elements of the burst come on top of them. -/
def SSt.inv (st : SSt) (o : Nat) : Prop :=
  match st.mode with
  | .normal => st.ctl.length ≤ o
  | .burst d _ _ => st.ctl.length + d ≤ o

/-- In a burst, `d` is at least 1. -/
def SSt.burstOk (st : SSt) : Prop :=
  match st.mode with
  | .normal => True
  | .burst d _ _ => 1 ≤ d

theorem SSt.step_inv (p : SPath) (st st' : SSt) (e : Event) (o : Nat)
    (h : st.step p e = some st') (hi : st.inv o) (hb : st.burstOk) :
    st'.inv (openAfter [e] o) ∧ st'.burstOk := by
  obtain ⟨ctl, mode, out⟩ := st
  cases mode with
  | normal =>
    simp only [SSt.inv] at hi
    cases e with
    | start t a =>
      simp only [SSt.step] at h
      split at h
      · split at h
        · split at h
          · split at h
            · simp at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
            · simp at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
          · split at h <;> (simp at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega)
        · simp at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
      · simp at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | stop =>
      simp only [SSt.step] at h
      cases ctl with
      | nil => simp at h
      | cons c cs =>
        simp at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter] at hi ⊢; omega
    | text _ => simp [SSt.step] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | comment _ => simp [SSt.step] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | cdata _ => simp [SSt.step] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | pi _ _ => simp [SSt.step] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
  | burst d b inner =>
    simp only [SSt.inv] at hi
    simp only [SSt.burstOk] at hb
    cases e with
    | start t a =>
      simp only [SSt.step] at h
      cases hb' : b.step (.start t a) with
      | none => simp [hb'] at h
      | some b' => simp [hb'] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | stop =>
      simp only [SSt.step] at h
      split at h
      · split at h
        · simp at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
        · simp at h
      · cases hb' : b.step .stop with
        | none => simp [hb'] at h
        | some b' => simp [hb'] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | text x =>
      simp only [SSt.step] at h
      cases hb' : b.step (.text x) with
      | none => simp [hb'] at h
      | some b' => simp [hb'] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | comment x =>
      simp only [SSt.step] at h
      cases hb' : b.step (.comment x) with
      | none => simp [hb'] at h
      | some b' => simp [hb'] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | cdata x =>
      simp only [SSt.step] at h
      cases hb' : b.step (.cdata x) with
      | none => simp [hb'] at h
      | some b' => simp [hb'] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega
    | pi x y =>
      simp only [SSt.step] at h
      cases hb' : b.step (.pi x y) with
      | none => simp [hb'] at h
      | some b' => simp [hb'] at h; subst h; simp [SSt.inv, SSt.burstOk, openAfter]; omega

theorem openAfter_cons (e : Event) (es : List Event) (o : Nat) :
    openAfter (e :: es) o = openAfter es (openAfter [e] o) := by
  cases e <;> simp [openAfter]

theorem SSt.run_inv (p : SPath) (es : List Event) (st st' : SSt) (o : Nat)
    (h : SSt.run p es st = some st') (hi : st.inv o) (hb : st.burstOk) :
    st'.inv (openAfter es o) ∧ st'.burstOk := by
  induction es generalizing st o with
  | nil => simp [SSt.run] at h; subst h; exact ⟨by simpa [openAfter] using hi, hb⟩
  | cons e es ih =>
    simp only [SSt.run] at h
    cases hs : st.step p e with
    | none => simp [hs] at h
    | some s1 =>
      simp [hs] at h
      have ⟨hi1, hb1⟩ := SSt.step_inv p st s1 e o hs hi hb
      rw [openAfter_cons]
      exact ih s1 (openAfter [e] o) h hi1 hb1

/-- **Bounded memory.** At every point of the event stream of a list of
    nodes, the streamed selection keeps at most `depthList ns` statuses
    (one per open element), whatever the number of nodes. -/
theorem streamSelect_ctl_le_depth (p : SPath) (ns : List Node) (n : Nat) (st : SSt)
    (h : SSt.run p ((eventsList ns).take n) { ctl := [], mode := .normal, out := [] } = some st) :
    st.ctl.length ≤ depthList ns := by
  have ⟨hi, _⟩ := SSt.run_inv p _ _ st 0 h (by simp [SSt.inv]) (by simp [SSt.burstOk])
  have h1 := openAfter_take_le (eventsList ns) 0 n
  have h2 := maxOpen_eventsList ns
  have hl : st.ctl.length ≤ openAfter ((eventsList ns).take n) 0 := by
    unfold SSt.inv at hi
    split at hi <;> omega
  omega

/-! ## Grounded results -/

mutual
/-- The string value of a node (XDM: the concatenation of its text
    descendants). -/
def strValue : Node → String
  | .element _ _ cs => strValueList cs
  | .text s => s
  | .cdata s => s
  | _ => ""

def strValueList : List Node → String
  | [] => ""
  | n :: ns => strValue n ++ strValueList ns
end

/-! ## String values as a loop

`strValue` makes one frame per sibling; `strValueLoop` reads the text
events of the work-list loop `eventsLoop`. `@[csimp]` makes compiled code
use it. -/

/-- The text of an event list, appended to `acc` (a left fold). -/
def textAcc (acc : String) (es : List Event) : String :=
  es.foldl (fun a e => match e with
    | .text s => a ++ s
    | .cdata s => a ++ s
    | _ => a) acc

theorem textAcc_append (acc : String) (xs ys : List Event) :
    textAcc acc (xs ++ ys) = textAcc (textAcc acc xs) ys := by
  simp [textAcc, List.foldl_append]

mutual
theorem textAcc_events (acc : String) (n : Node) : textAcc acc (events n) = acc ++ strValue n := by
  match n with
  | .element t a cs =>
    simp only [events]
    rw [show (Event.start t a :: (eventsList cs ++ [Event.stop])) =
        [Event.start t a] ++ (eventsList cs ++ [Event.stop]) from rfl, textAcc_append, textAcc_append,
      textAcc_eventsList]
    simp [textAcc, strValue]
  | .text s => simp [textAcc, events, strValue]
  | .comment s => simp [textAcc, events, strValue]
  | .cdata s => simp [textAcc, events, strValue]
  | .pi x y => simp [textAcc, events, strValue]

theorem textAcc_eventsList (acc : String) (ns : List Node) :
    textAcc acc (eventsList ns) = acc ++ strValueList ns := by
  match ns with
  | [] => simp [textAcc, eventsList, strValueList]
  | n :: rest =>
    simp only [eventsList]
    rw [textAcc_append, textAcc_events, textAcc_eventsList]
    simp [strValueList, String.append_assoc]
end

def strValueLoop (n : Node) : String := textAcc "" (eventsListLoop [n])

def strValueListLoop (ns : List Node) : String := textAcc "" (eventsListLoop ns)

@[csimp] theorem strValue_eq_loop : @strValue = @strValueLoop := by
  funext n
  simp only [strValueLoop, ← eventsList_eq_loop]
  rw [show eventsList [n] = events n ++ [] by simp [eventsList]]
  simp [textAcc_events]

@[csimp] theorem strValueList_eq_loop : @strValueList = @strValueListLoop := by
  funext ns
  simp only [strValueListLoop, ← eventsList_eq_loop, textAcc_eventsList]
  simp

/-- `count(P)`, streamed. -/
def streamCount (p : SPath) (es : List Event) : Option Nat :=
  (streamSelect p es).map List.length

/-- The string values of `P` (what `xsl:value-of select="P"` joins),
    streamed. -/
def streamStrings (p : SPath) (es : List Event) : Option (List String) :=
  (streamSelect p es).map (List.map strValue)

theorem streamCount_docEvents (p : SPath) (d : Document) :
    streamCount p (docEvents d) = some (selList p 0 d.children).length := by
  simp [streamCount, streamSelect_docEvents]

theorem streamStrings_docEvents (p : SPath) (d : Document) :
    streamStrings p (docEvents d) = some ((selList p 0 d.children).map strValue) := by
  simp [streamStrings, streamSelect_docEvents]

end L4Factoidal.XSLT4.Streaming
