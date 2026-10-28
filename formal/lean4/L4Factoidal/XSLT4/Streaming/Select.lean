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

/-- A name test of a child step: a name, or `*`. -/
def nameMatch (t tag : String) : Bool := t == "*" || t == tag

/-! ## The tree evaluation -/

mutual
/-- The nodes that the path `p`, from step `k` on, selects at node `n`
    (the steps before `k` matched the ancestors of `n`). -/
def selNode (p : List String) (k : Nat) : Node → List Node
  | .element t a cs =>
    match p[k]? with
    | some nt =>
      if nameMatch nt t then
        if k + 1 = p.length then [.element t a cs] else selList p (k + 1) cs
      else []
    | none => []
  | _ => []

def selList (p : List String) (k : Nat) : List Node → List Node
  | [] => []
  | n :: ns => selNode p k n ++ selList p k ns
end

/-! ## The streamed evaluation -/

inductive Mode where
  | normal
  /-- Inside a selected element: the number of its open elements
      (itself included) and the builder of its subtree. -/
  | burst (d : Nat) (b : BSt)
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

def SSt.step (p : List String) (st : SSt) (e : Event) : Option SSt :=
  match st.mode with
  | .normal =>
    match e with
    | .start t a =>
      match st.cur with
      | some k =>
        match p[k]? with
        | some nt =>
          if nameMatch nt t then
            if k + 1 = p.length then
              some { st with mode := .burst 1 { stack := [{ tag := t, attrs := a, kids := [] }], top := [] } }
            else some { st with ctl := some (k + 1) :: st.ctl }
          else some { st with ctl := none :: st.ctl }
        | none => some { st with ctl := none :: st.ctl }
      | none => some { st with ctl := none :: st.ctl }
    | .stop => match st.ctl with
      | _ :: cs => some { st with ctl := cs }
      | [] => none
    | _ => some st
  | .burst d b =>
    match e with
    | .start _ _ => (b.step e).map (fun b' => { st with mode := .burst (d + 1) b' })
    | .stop =>
      if d = 1 then
        match b.step e with
        | some { stack := [], top := [n] } => some { st with mode := .normal, out := n :: st.out }
        | _ => none
      else (b.step e).map (fun b' => { st with mode := .burst (d - 1) b' })
    | _ => (b.step e).map (fun b' => { st with mode := .burst d b' })

def SSt.run (p : List String) : List Event → SSt → Option SSt
  | [], st => some st
  | e :: es, st => (st.step p e).bind (SSt.run p es)

/-- The streamed evaluation of `copy-of(P)` over an event stream. -/
def streamSelect (p : List String) (es : List Event) : Option (List Node) :=
  (SSt.run p es { ctl := [], mode := .normal, out := [] }).map (fun st => st.out.reverse)

theorem SSt.run_append (p : List String) (xs ys : List Event) (st : SSt) :
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
theorem burst_events (p : List String) (n : Node) (st : SSt) (d : Nat) (b : BSt) :
    SSt.run p (events n) { st with mode := .burst (d + 1) b } =
      some { st with mode := .burst (d + 1) (b.add n) } := by
  match n with
  | .element t a cs =>
    simp only [events, SSt.run, SSt.step, BSt.step, Option.map_some, Option.bind_some]
    rw [SSt.run_append]
    have h := burst_eventsList p cs st (d + 1) { b with stack := { tag := t, attrs := a, kids := [] } :: b.stack }
    rw [h]
    simp only [Option.bind_some]
    rw [foldl_add_frame]
    simp [SSt.run, SSt.step, BSt.step]
  | .text s => simp [events, SSt.run, SSt.step, BSt.step]
  | .comment s => simp [events, SSt.run, SSt.step, BSt.step]
  | .cdata s => simp [events, SSt.run, SSt.step, BSt.step]
  | .pi t x => simp [events, SSt.run, SSt.step, BSt.step]

theorem burst_eventsList (p : List String) (ns : List Node) (st : SSt) (d : Nat) (b : BSt) :
    SSt.run p (eventsList ns) { st with mode := .burst (d + 1) b } =
      some { st with mode := .burst (d + 1) (ns.foldl BSt.add b) } := by
  match ns with
  | [] => simp [eventsList, SSt.run]
  | n :: rest =>
    simp only [eventsList]
    rw [SSt.run_append, burst_events]
    simp only [Option.bind_some]
    have h := burst_eventsList p rest { st with mode := .burst (d + 1) (b.add n) } d (b.add n)
    simp only at h
    rw [h]
    simp
end

/-! ### Normal mode is the tree selection -/

/-- The selection below a status: nothing below a dead branch. -/
def selAt (p : List String) : Option Nat → Node → List Node
  | some k, n => selNode p k n
  | none, _ => []

def selAtList (p : List String) : Option Nat → List Node → List Node
  | some k, ns => selList p k ns
  | none, _ => []

theorem selAtList_cons (p : List String) (s : Option Nat) (n : Node) (ns : List Node) :
    selAtList p s (n :: ns) = selAt p s n ++ selAtList p s ns := by
  cases s <;> simp [selAtList, selAt, selList]

mutual
theorem normal_events (p : List String) (n : Node) (ctl : List (Option Nat)) (out : List Node) :
    SSt.run p (events n) { ctl, mode := .normal, out } =
      some { ctl, mode := .normal, out := (selAt p (SSt.cur { ctl, mode := .normal, out }) n).reverse ++ out } := by
  match n with
  | .element t a cs =>
    simp only [events, SSt.run]
    generalize hk : SSt.cur { ctl, mode := .normal, out } = k
    cases k with
    | none =>
      have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
          some { ctl := none :: ctl, mode := .normal, out } := by
        simp [SSt.step, hk]
      rw [hs]
      simp only [Option.bind_some]
      rw [SSt.run_append, normal_eventsList]
      simp [SSt.cur, selAtList, selAt, SSt.run, SSt.step]
    | some k =>
      cases hp : p[k]? with
      | none =>
        have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
            some { ctl := none :: ctl, mode := .normal, out } := by
          simp [SSt.step, hk, hp]
        rw [hs]
        simp only [Option.bind_some]
        rw [SSt.run_append, normal_eventsList]
        simp [SSt.cur, selAtList, selAt, selNode, hp, SSt.run, SSt.step]
      | some nt =>
        by_cases hm : nameMatch nt t = true
        · by_cases hl : k + 1 = p.length
          · have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
                some { ctl, mode := .burst 1 { stack := [{ tag := t, attrs := a, kids := [] }], top := [] }, out } := by
              simp [SSt.step, hk, hp, hm, hl]
            rw [hs]
            simp only [Option.bind_some]
            rw [SSt.run_append]
            have h := burst_eventsList p cs { ctl, mode := .normal, out } 0
              { stack := [{ tag := t, attrs := a, kids := [] }], top := [] }
            simp only at h
            rw [h]
            simp only [Option.bind_some]
            rw [foldl_add_frame]
            simp [SSt.run, SSt.step, BSt.step, BSt.add, selAt, selNode, hp, hm, hl]
          · have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
                some { ctl := some (k + 1) :: ctl, mode := .normal, out } := by
              simp [SSt.step, hk, hp, hm, hl]
            rw [hs]
            simp only [Option.bind_some]
            rw [SSt.run_append, normal_eventsList]
            simp [SSt.cur, selAtList, selAt, selNode, hp, hm, hl, SSt.run, SSt.step]
        · have hs : SSt.step p { ctl, mode := .normal, out } (.start t a) =
              some { ctl := none :: ctl, mode := .normal, out } := by
            simp [SSt.step, hk, hp, hm]
          rw [hs]
          simp only [Option.bind_some]
          rw [SSt.run_append, normal_eventsList]
          simp [SSt.cur, selAtList, selAt, selNode, hp, hm, SSt.run, SSt.step]
  | .text s => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [events, SSt.run, SSt.step, selAt, selNode, h]
  | .comment s => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [events, SSt.run, SSt.step, selAt, selNode, h]
  | .cdata s => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [events, SSt.run, SSt.step, selAt, selNode, h]
  | .pi x y => cases h : SSt.cur { ctl, mode := .normal, out } <;> simp [events, SSt.run, SSt.step, selAt, selNode, h]

theorem normal_eventsList (p : List String) (ns : List Node) (ctl : List (Option Nat)) (out : List Node) :
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
    with burst-mode copies. -/
theorem streamSelect_eventsList (p : List String) (ns : List Node) :
    streamSelect p (eventsList ns) = some (selList p 0 ns) := by
  simp [streamSelect, normal_eventsList, SSt.cur, selAtList]

theorem streamSelect_docEvents (p : List String) (d : Document) :
    streamSelect p (docEvents d) = some (selList p 0 d.children) :=
  streamSelect_eventsList p d.children

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
def streamCount (p : List String) (es : List Event) : Option Nat :=
  (streamSelect p es).map List.length

/-- The string values of `P` (what `xsl:value-of select="P"` joins),
    streamed. -/
def streamStrings (p : List String) (es : List Event) : Option (List String) :=
  (streamSelect p es).map (List.map strValue)

theorem streamCount_docEvents (p : List String) (d : Document) :
    streamCount p (docEvents d) = some (selList p 0 d.children).length := by
  simp [streamCount, streamSelect_docEvents]

theorem streamStrings_docEvents (p : List String) (d : Document) :
    streamStrings p (docEvents d) = some ((selList p 0 d.children).map strValue) := by
  simp [streamStrings, streamSelect_docEvents]

end L4Factoidal.XSLT4.Streaming
