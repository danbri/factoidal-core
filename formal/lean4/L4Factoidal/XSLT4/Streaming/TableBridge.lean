/-
L4Factoidal.XSLT4.Streaming.TableBridge — the event stream of
`Streaming/Events.lean` and the XPath 4.0 node table `Doc.ofNodes`
(`XPath4/Doc.lean`) hold the same nodes in the same order. Tracking:
https://github.com/danbri/factoidal/issues/1101 (XSLT Streaming 4.0).

`evShapes evs` reads an event stream from the end, as a streaming
processor that builds records would: a start event gives an element
record and one attribute record for each attribute that is not a
namespace declaration; a text or CDATA event joins the text record that
follows it (adjacent text is one text node, XDM 4.0 §6.7), and an empty
text gives no record; a stop event gives a `close` marker, so text on the
two sides of an end tag is not joined.

Proved (no `sorry`, no new axioms):

* `ofNodes_shapes` — for every `ns` that is not deeper than the fuel of
  `Doc.ofNodes` (`Fits 100000`), the records at the indices
  `1 .. size - 1` of `(Doc.ofNodes ns uri).nodes`, as (kind, value), are
  the records of `evShapes (eventsList ns)`, in order.
* `parse_table_shapes` — for every document that `XML.parseXML` returns,
  the same for the table of `Doc.ofNodes` over the tree that `build`
  rebuilds from the event stream `docEvents d`.

Method: `evShapes` is a right fold, so `foldr_shapes_append` splits it at
any suffix that does not start with text; `mergeText` (the text merging of
`Doc.ofNodes`) gives the same fold (`shapes_mergeText`); the table side is
the `BuiltA` / `BuiltList` layout of `XPath4/DocTheorems2.lean`, read by
induction on that layout.
-/
import L4Factoidal.XSLT4.Streaming.Events
import L4Factoidal.XPath4.DocTheorems2

namespace L4Factoidal.XSLT4.Streaming

open L4Factoidal.XML
open L4Factoidal.XPath4
open L4Factoidal.XPath4.DocProof

/-- An item of the record list read from an event stream: a record (kind
    and value) or the end of an element. -/
inductive Sh where
  | item (k : NKind) (v : String)
  | close
  deriving DecidableEq, Repr

/-- A text event of value `a` in front of the items `r`. -/
def mergeSh (a : String) : List Sh → List Sh
  | .item .text b :: r => .item .text (a ++ b) :: r
  | r => if a == "" then r else .item .text a :: r

/-- The items one event puts in front of the items of the events after it. -/
def shStep : Event → List Sh → List Sh
  | .start _ ats, r => .item .element "" :: (attrFilter ats).map (fun x => .item .attribute x.value) ++ r
  | .stop, r => .close :: r
  | .text a, r => mergeSh a r
  | .cdata a, r => mergeSh a r
  | .comment b, r => .item .comment b :: r
  | .pi _ d, r => .item .pi d :: r

/-- The record items of an event stream. -/
def evShapes (evs : List Event) : List Sh := evs.foldr shStep []

/-- The record of an item, if it is one. -/
def recOf : Sh → Option (NKind × String)
  | .item k v => some (k, v)
  | .close => none

/-- The records only, as (kind, value). -/
def recsOf (l : List Sh) : List (NKind × String) := l.filterMap recOf

theorem recsOf_append (l r : List Sh) : recsOf (l ++ r) = recsOf l ++ recsOf r :=
  List.filterMap_append

theorem recsOf_nil : recsOf [] = [] := rfl

theorem recsOf_item (k : NKind) (v : String) (l : List Sh) :
    recsOf (.item k v :: l) = (k, v) :: recsOf l := rfl

theorem recsOf_close (l : List Sh) : recsOf (.close :: l) = recsOf l := rfl

/-- The items do not start with a text record. -/
def NoTextHead : List Sh → Prop
  | .item .text _ :: _ => False
  | _ => True

theorem mergeSh_append (a : String) (Z Y : List Sh) (hY : NoTextHead Y) :
    mergeSh a (Z ++ Y) = mergeSh a Z ++ Y := by
  match Z with
  | [] =>
    match Y, hY with
    | [], _ => simp [mergeSh]
    | .close :: _, _ => by_cases h : a = "" <;> simp [mergeSh, h]
    | .item .element _ :: _, _ | .item .attribute _ :: _, _ | .item .comment _ :: _, _
    | .item .pi _ :: _, _ | .item .document _ :: _, _ | .item .namespace _ :: _, _ =>
      by_cases h : a = "" <;> simp [mergeSh, h]
  | .item .text b :: z => simp [mergeSh]
  | .close :: z => by_cases h : a = "" <;> simp [mergeSh, h]
  | .item .element _ :: z | .item .attribute _ :: z | .item .comment _ :: z | .item .pi _ :: z
  | .item .document _ :: z | .item .namespace _ :: z =>
    by_cases h : a = "" <;> simp [mergeSh, h]

theorem shStep_append (e : Event) (Z Y : List Sh) (hY : NoTextHead Y) :
    shStep e (Z ++ Y) = shStep e Z ++ Y := by
  cases e <;> simp [shStep, mergeSh_append _ _ _ hY]

/-- The fold splits at a suffix that does not start with text. -/
theorem foldr_shapes_append (evs : List Event) (Y : List Sh) (hY : NoTextHead Y) :
    evs.foldr shStep Y = evs.foldr shStep [] ++ Y := by
  induction evs with
  | nil => rfl
  | cons e evs ih => simp only [List.foldr_cons, ih, shStep_append _ _ _ hY]

/-- The fold over the events of one node that is not text: the items after
    it never join it. -/
theorem foldr_events_nontext (k : Node) (hk : ∀ s, k ≠ .text s ∧ k ≠ .cdata s) (Y : List Sh) :
    (events k).foldr shStep Y = (events k).foldr shStep [] ++ Y := by
  match k with
  | .text s => exact absurd rfl (hk s).1
  | .cdata s => exact absurd rfl (hk s).2
  | .comment _ | .pi _ _ => simp [events, shStep]
  | .element t ats cs =>
    simp only [events, List.foldr_cons, List.foldr_append, List.foldr_nil, shStep]
    rw [foldr_shapes_append _ (.close :: Y) trivial, foldr_shapes_append _ [.close] trivial]
    simp

theorem foldr_eventsList (ns : List Node) (Y : List Sh) :
    (eventsList ns).foldr shStep Y = ns.foldr (fun k r => (events k).foldr shStep r) Y := by
  induction ns with
  | nil => rfl
  | cons k ns ih => simp [eventsList, List.foldr_append, ih]

/-! ### `mergeText` gives the same fold -/

/-- The fold over the events of a list of nodes, onto `Y`. -/
def F (ns : List Node) (Y : List Sh) : List Sh := (eventsList ns).foldr shStep Y

theorem F_cons (k : Node) (ns : List Node) (Y : List Sh) :
    F (k :: ns) Y = (events k).foldr shStep (F ns Y) := by
  simp [F, eventsList, List.foldr_append]

theorem mergeSh_mergeSh (a b : String) (X : List Sh) :
    mergeSh a (mergeSh b X) = mergeSh (a ++ b) X := by
  match X with
  | .item .text c :: r => simp [mergeSh, String.append_assoc]
  | [] | .close :: _ | .item .element _ :: _ | .item .attribute _ :: _ | .item .comment _ :: _
  | .item .pi _ :: _ | .item .document _ :: _ | .item .namespace _ :: _ =>
    by_cases hb : b = "" <;> by_cases ha : a = "" <;>
      simp [mergeSh, hb, ha, String.append_eq_empty_iff]

/-- The step of `mergeText` for a text or CDATA node `a` in front of the
    merged list `m`. -/
def mergeT (a : String) : List Node → List Node
  | .text b :: r => .text (a ++ b) :: r
  | r => if a == "" then r else .text a :: r

theorem mergeText_text (a : String) (rest : List Node) :
    mergeText (.text a :: rest) = mergeT a (mergeText rest) := by
  simp only [mergeText]; rfl

theorem mergeText_cdata (a : String) (rest : List Node) :
    mergeText (.cdata a :: rest) = mergeT a (mergeText rest) := by
  simp only [mergeText]; rfl

/-- `mergeText` never gives a CDATA node at the head. -/
theorem mergeText_noCdata : ∀ (l : List Node) (b : String), (mergeText l).head? ≠ some (.cdata b)
  | [], _ => by simp [mergeText]
  | .text a :: rest, b | .cdata a :: rest, b => by
    first | rw [mergeText_text] | rw [mergeText_cdata]
    have ih := mergeText_noCdata rest b
    unfold mergeT
    split
    · simp
    · by_cases h : a = "" <;> simp [h, ih]
  | .element .. :: _, _ | .comment .. :: _, _ | .pi .. :: _, _ => by simp [mergeText]

/-- A list that does not start with a text or CDATA node: the fold over it,
    onto items that do not start with text, does not start with text. -/
theorem F_noTextHead (m : List Node) (Y : List Sh) (hY : NoTextHead Y)
    (hm : ∀ s, m.head? ≠ some (.text s) ∧ m.head? ≠ some (.cdata s)) : NoTextHead (F m Y) := by
  match m with
  | [] => simpa [F, eventsList] using hY
  | .text s :: _ => exact absurd rfl (hm s).1
  | .cdata s :: _ => exact absurd rfl (hm s).2
  | .comment _ :: _ | .pi _ _ :: _ => simp [F_cons, events, shStep, NoTextHead]
  | .element .. :: _ => simp [F_cons, events, List.foldr_append, shStep, NoTextHead]

theorem mergeSh_noText (a : String) (X : List Sh) (hX : NoTextHead X) :
    mergeSh a X = if a == "" then X else .item .text a :: X := by
  match X, hX with
  | [], _ | .close :: _, _ | .item .element _ :: _, _ | .item .attribute _ :: _, _
  | .item .comment _ :: _, _ | .item .pi _ :: _, _ | .item .document _ :: _, _
  | .item .namespace _ :: _, _ => rfl

theorem F_mergeT (a : String) (m : List Node) (Y : List Sh) (hY : NoTextHead Y)
    (hm : ∀ b, m.head? ≠ some (.cdata b)) : F (mergeT a m) Y = mergeSh a (F m Y) := by
  match m with
  | .text b :: r =>
    simp [mergeT, F_cons, events, shStep, mergeSh_mergeSh]
  | .cdata b :: _ => exact absurd rfl (hm b)
  | [] | .element .. :: _ | .comment .. :: _ | .pi .. :: _ =>
    by_cases h : a = ""
    · subst h
      rw [mergeSh_noText _ _ (F_noTextHead _ Y hY (by intro s; simp))]
      simp [mergeT]
    · simp [mergeT, h, F_cons, events, shStep]

theorem F_mergeText (ks : List Node) (Y : List Sh) (hY : NoTextHead Y) :
    F (mergeText ks) Y = F ks Y := by
  induction ks with
  | nil => rfl
  | cons n rest ih =>
    rw [F_cons]
    cases n with
    | element t ats cs => simp only [mergeText]; rw [F_cons, ih]
    | comment b => simp only [mergeText]; rw [F_cons, ih]
    | pi t d => simp only [mergeText]; rw [F_cons, ih]
    | text a =>
      rw [mergeText_text, F_mergeT _ _ _ hY (mergeText_noCdata rest), ih]
      simp [events, shStep]
    | cdata a =>
      rw [mergeText_cdata, F_mergeT _ _ _ hY (mergeText_noCdata rest), ih]
      simp [events, shStep]

/-! ### The table side -/

/-- A node that gives exactly one record: not CDATA (`mergeText` turns it
    into text) and not empty text. -/
def NodeOK : Node → Prop
  | .cdata _ => False
  | .text s => s ≠ ""
  | _ => True

/-- The form of a list that `mergeText` gives: every node gives one record,
    and no text node follows a text node. -/
def TN : List Node → Prop
  | [] => True
  | k :: r => NodeOK k ∧ (∀ s, k = .text s → ∀ t, r.head? ≠ some (.text t)) ∧ TN r

theorem TN_mergeText : ∀ l : List Node, TN (mergeText l)
  | [] => trivial
  | .text a :: rest | .cdata a :: rest => by
    first | rw [mergeText_text] | rw [mergeText_cdata]
    have ih := TN_mergeText rest
    have hc := mergeText_noCdata rest
    generalize mergeText rest = m at ih hc
    match m, ih with
    | .text b :: r, ⟨hb, hn, hr⟩ =>
      refine ⟨?_, fun s _ t => hn b rfl t, hr⟩
      simp only [NodeOK] at hb ⊢
      intro h
      exact hb (String.append_eq_empty_iff.mp h).2
    | [], _ => by_cases h : a = "" <;> simp [mergeT, h, TN, NodeOK]
    | .cdata b :: _, _ => exact absurd rfl (hc b)
    | .element .. :: r, ih | .comment .. :: r, ih | .pi .. :: r, ih =>
      by_cases h : a = ""
      · simpa [mergeT, h] using ih
      · simp only [mergeT, h, beq_iff_eq, if_false]
        exact ⟨h, fun _ _ t => by simp, ih⟩
  | .element t ats kids :: rest => by
    simp only [mergeText, TN, NodeOK, true_and]
    exact ⟨fun _ h => Node.noConfusion h, TN_mergeText rest⟩
  | .comment b :: rest => by
    simp only [mergeText, TN, NodeOK, true_and]
    exact ⟨fun _ h => Node.noConfusion h, TN_mergeText rest⟩
  | .pi t d :: rest => by
    simp only [mergeText, TN, NodeOK, true_and]
    exact ⟨fun _ h => Node.noConfusion h, TN_mergeText rest⟩

/-- A record as (kind, value). -/
def shape (r : NRec) : NKind × String := (r.kind, r.value)

/-- The records at the indices `lo, ..., lo + n - 1`, as (kind, value). -/
def slice (a : Array NRec) (lo n : Nat) : List (Option (NKind × String)) :=
  (List.range' lo n).map (fun i => a[i]?.map shape)

theorem slice_add (a : Array NRec) (lo m n : Nat) :
    slice a lo (m + n) = slice a lo m ++ slice a (lo + m) n := by
  unfold slice
  rw [← List.map_append]
  congr 1
  simp

theorem slice_one (a : Array NRec) (j : Nat) : slice a j 1 = [a[j]?.map shape] := rfl

theorem attrsOK_slice {a : Array NRec} {sc : List (String × String)} {i : Nat} :
    ∀ {lo : Nat} {xs : List Attribute}, AttrsOK a sc i lo xs →
      slice a lo xs.length = xs.map (fun x => some (NKind.attribute, x.value))
  | _, [], _ => rfl
  | lo, x :: xs, ⟨h, t⟩ => by
    have := attrsOK_slice t
    rw [List.length_cons, Nat.add_comm, slice_add, slice_one, h, this]
    rfl

theorem F_one (k : Node) : F [k] [] = (events k).foldr shStep [] := by
  simp [F, eventsList]

theorem F_element (t : String) (ats : List Attribute) (kids : List Node) :
    F [.element t ats kids] [] =
      .item .element "" :: (attrFilter ats).map (fun x => .item .attribute x.value) ++
        (F kids [] ++ [.close]) := by
  rw [F_one]
  simp only [events, List.foldr_cons, List.foldr_append, List.foldr_nil, shStep]
  rw [foldr_shapes_append _ [.close] trivial]
  rfl

theorem recsOf_attrs (xs : List Attribute) :
    recsOf (xs.map (fun x => Sh.item .attribute x.value)) = xs.map (fun x => (NKind.attribute, x.value)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [recsOf_item, ih]

mutual
theorem builtA_shapes {a : Array NRec} {sc p j e k} : BuiltA a sc p j e k → NodeOK k →
    slice a j (e + 1 - j) = (recsOf (F [k] [])).map some
  | .text h, hk => by
    rw [Nat.add_sub_cancel_left, slice_one, h, F_one]
    simp only [NodeOK] at hk
    simp [events, shStep, mergeSh, hk, recsOf_nil, recsOf_item, shape]
  | .cdata _, hk => nomatch hk
  | .comment h, _ => by
    rw [Nat.add_sub_cancel_left, slice_one, h, F_one]; simp [events, shStep, recsOf_nil, recsOf_item, shape]
  | .pi h, _ => by
    rw [Nat.add_sub_cancel_left, slice_one, h, F_one]; simp [events, shStep, recsOf_nil, recsOf_item, shape]
  | .element (attrs := attrs) (kids := kids) (e := e) r h1 h2 _ _ _ h5 _ _ h9 h10, _ => by
    have hl := h10.le
    have hc := builtList_shapes h10 (TN_mergeText kids)
    rw [F_mergeText _ [] trivial] at hc
    have hsplit : e + 1 - j = 1 + ((attrFilter attrs).length + (e + 1 - (j + 1 + (attrFilter attrs).length))) := by
      omega
    rw [hsplit, slice_add, slice_add, slice_one, h1, attrsOK_slice h9, hc, F_element]
    simp [shape, h2, h5, recsOf_nil, recsOf_item, recsOf_close, recsOf_append, recsOf_attrs]
theorem builtList_shapes {a : Array NRec} {sc p lo cs ks hi} : BuiltList a sc p lo cs ks hi → TN ks →
    slice a lo (hi - lo) = (recsOf (F ks [])).map some
  | .nil, _ => by simp [slice, F, eventsList, recsOf_nil]
  | .cons (k := k) (ks := ks) (e := e) h t, ⟨hk, hn, hks⟩ => by
    have h1 := h.le
    have h2 := t.le
    have hsplit : hi - lo = (e + 1 - lo) + (hi - (e + 1)) := by omega
    rw [hsplit, slice_add, Nat.add_sub_cancel' (by omega), builtA_shapes h hk, builtList_shapes t hks]
    have hcat : F (k :: ks) [] = F [k] [] ++ F ks [] := by
      rw [F_cons, F_one]
      match k, hk with
      | .text s, _ =>
        refine foldr_shapes_append _ _ (F_noTextHead _ _ trivial (fun u => ⟨hn s rfl u, ?_⟩))
        intro hc
        match ks, hks, hc with
        | .cdata _ :: _, ⟨hb, _⟩, _ => exact hb
      | .cdata _, hk => exact nomatch hk
      | .element .., _ | .comment .., _ | .pi .., _ =>
        exact foldr_events_nontext _ (fun s => ⟨by simp, by simp⟩) _
    rw [hcat, recsOf_append, List.map_append]
end

/-- The node table of `Doc.ofNodes ns` holds, ats the indices
    `1 .. size - 1`, the records that the event stream of `ns` gives, in
    order, as (kind, value). -/
theorem ofNodes_shapes (ns : List Node) (uri : String) (hfit : ∀ n ∈ ns, Fits 100000 n) :
    slice (Doc.ofNodes ns uri).nodes 1 ((Doc.ofNodes ns uri).nodes.size - 1) =
      (recsOf (evShapes (eventsList ns))).map some := by
  obtain ⟨_, _, hb⟩ := ofNodes_built ns uri hfit
  rw [builtList_shapes hb (TN_mergeText ns), F_mergeText _ [] trivial]
  rfl

/-- For every document that the XML parser returns: the tree that `build`
    rebuilds from the event stream gives a node table whose records are the
    records of the event stream, in order. -/
theorem parse_table_shapes (s uri : String) (d : Document) (_h : parseXML s = .ok d)
    (hfit : ∀ n ∈ d.children, Fits 100000 n) :
    ∃ ns, build (docEvents d) = some ns ∧
      slice (Doc.ofNodes ns uri).nodes 1 ((Doc.ofNodes ns uri).nodes.size - 1) =
        (recsOf (evShapes (docEvents d))).map some :=
  ⟨d.children, build_docEvents d, ofNodes_shapes _ _ hfit⟩

end L4Factoidal.XSLT4.Streaming
