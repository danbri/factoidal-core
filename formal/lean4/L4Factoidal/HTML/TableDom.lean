/-
L4Factoidal.HTML.TableDom — what the script interface of tables reads from the tree (HTML
§4.9): a table's `rows` (its `thead` rows, then its own `tr` children and those of its
`tbody` children in tree order, then its `tfoot` rows), `tBodies`, `caption`, `tHead` and
`tFoot`; a section's `rows`; a row's `cells`, `rowIndex` and `sectionRowIndex`; a cell's
`cellIndex`; and where `insertRow` puts a new row.

The page makes the elements and moves them; which nodes the collections hold, what the
indices are and whether an index is in range are decided here (`answer`, node_query 199).
-/
import L4Factoidal.DOM.Forms
import L4Factoidal.DOM.OfHtml

namespace L4Factoidal.HTML.TableDom
open L4Factoidal.DOM L4Factoidal.DOM.Forms

/-- The element children of a node, in tree order. -/
def childElements (d : Dom) (k : NodeId) : List NodeId :=
  (d.get k).kids.toList.filter fun c => (d.get c).type == .element

/-- The `tr` children of a node. -/
def rowChildren (d : Dom) (k : NodeId) : List NodeId :=
  (childElements d k).filter (isHtml d · ["tr"])

/-- A table's `rows` (HTML §4.9.1). -/
def tableRows (d : Dom) (t : NodeId) : List NodeId :=
  let kids := childElements d t
  (kids.filter (isHtml d · ["thead"])).flatMap (rowChildren d) ++
    kids.flatMap (fun c => if isHtml d c ["tr"] then [c] else if isHtml d c ["tbody"] then rowChildren d c else []) ++
    (kids.filter (isHtml d · ["tfoot"])).flatMap (rowChildren d)

/-- A row's `cells` (HTML §4.9.8): its `td` and `th` children. -/
def cells (d : Dom) (r : NodeId) : List NodeId :=
  (childElements d r).filter (isHtml d · ["td", "th"])

def indexIn (xs : List NodeId) (k : NodeId) : Option Nat := xs.findIdx? (· == k)

def section? (d : Dom) (k : NodeId) : Bool := isHtml d k ["thead", "tbody", "tfoot"]

/-- `rowIndex` (HTML §4.9.8): the row's index in its table's `rows` when its parent is the
table or a section whose parent is a table; else -1. -/
def rowIndex (d : Dom) (r : NodeId) : Int :=
  match (d.get r).parent with
  | none => -1
  | some p =>
    let table := if isHtml d p ["table"] then some p
      else if section? d p then (d.get p).parent.filter (isHtml d · ["table"]) else none
    match table with
    | some t => ((indexIn (tableRows d t) r).map (fun i => (i : Int))).getD (-1)
    | none => -1

/-- `sectionRowIndex`: the index in the parent's `rows` (a table's or a section's), else -1. -/
def sectionRowIndex (d : Dom) (r : NodeId) : Int :=
  match (d.get r).parent with
  | none => -1
  | some p =>
    let rows := if isHtml d p ["table"] then tableRows d p else if section? d p then rowChildren d p else []
    ((indexIn rows r).map (fun i => (i : Int))).getD (-1)

/-- `cellIndex` (HTML §4.9.9): the index in the parent row's `cells`, else -1. -/
def cellIndex (d : Dom) (c : NodeId) : Int :=
  match (d.get c).parent with
  | some p => if isHtml d p ["tr"] then ((indexIn (cells d p) c).map (fun i => (i : Int))).getD (-1) else -1
  | none => -1

/-- Where `insertRow(index)` of table `t` puts its row (HTML §4.9.1): "E" an IndexSizeError;
"B" append a new `tbody` to the table and the row to it; "A" k append the row to node k (the
last `tbody`); "I" p r insert the row into p before the row r. -/
def insertRowAt (d : Dom) (t : NodeId) (index : Int) : String :=
  let rows := tableRows d t
  if index < -1 || index > rows.length then "E"
  else if index == -1 || index == rows.length then
    match ((childElements d t).filter (isHtml d · ["tbody"])).getLast? with
    | some b => "A " ++ toString b
    | none => "B"
  else
    match rows[index.toNat]? with
    | some r => "I " ++ toString ((d.get r).parent.getD t) ++ " " ++ toString r
    | none => "E"

/-- The item a delete with `index` removes from a list of `n` items (HTML §4.9.1 `deleteRow`,
§4.9.8 `deleteCell`): an error (IndexSizeError) out of range; nothing for -1 on an empty
list; -1 is the last item. -/
def deletePos (n : Nat) (index : Int) : Except Unit (Option Nat) :=
  if index == -1 then .ok (if n == 0 then none else some (n - 1))
  else if index < 0 || index ≥ n then .error ()
  else .ok (some index.toNat)

/-- `deletePos` on the wire: "E", "" or the position. -/
def deleteAt (n : Nat) (index : Int) : String :=
  match deletePos n index with
  | .error _ => "E"
  | .ok none => ""
  | .ok (some j) => toString j

def ids (xs : List NodeId) : String := " ".intercalate (xs.map toString)

/-- node_query 199 on node `k`: "r" a table's rows, "R" a section's rows, "b" tBodies, "c" a
row's cells, "i" rowIndex, "s" sectionRowIndex, "x" cellIndex, "C" the first caption, "H" the
first thead, "F" the first tfoot child ("" for none), "+" index: `insertRowAt`, "-" index: a
table's `deleteRow` position among its rows, "d" index: a section's or a row's delete
position among its rows or cells; "e" index: whether a section's or a row's insert index is
in range ("E" when not). -/
def answer (d : Dom) (k : NodeId) (q : String) : String :=
  let first := fun (names : List String) => ((childElements d k).find? (isHtml d · names)).map toString |>.getD ""
  match q.splitOn "\x00" with
  | ["r"] => ids (tableRows d k)
  | ["R"] => ids (rowChildren d k)
  | ["b"] => ids ((childElements d k).filter (isHtml d · ["tbody"]))
  | ["c"] => ids (cells d k)
  | ["i"] => toString (rowIndex d k)
  | ["s"] => toString (sectionRowIndex d k)
  | ["x"] => toString (cellIndex d k)
  | ["C"] => first ["caption"]
  | ["H"] => first ["thead"]
  | ["F"] => first ["tfoot"]
  | ["+", i] => match i.toInt? with | some i => insertRowAt d k i | none => "E"
  | ["-", i] => match i.toInt? with | some i => deleteAt (tableRows d k).length i | none => "E"
  | ["d", i] => match i.toInt? with
    | some i => deleteAt (if isHtml d k ["tr"] then cells d k else rowChildren d k).length i
    | none => "E"
  | ["e", i] => match i.toInt? with
    | some i => if i < -1 || i > (if isHtml d k ["tr"] then cells d k else rowChildren d k).length then "E" else ""
    | none => "E"
  | _ => ""

/-! ## What is proved -/

theorem rowChildren_tr (d : Dom) (k r : NodeId) (h : r ∈ rowChildren d k) : isHtml d r ["tr"] = true := by
  unfold rowChildren at h
  exact (List.mem_filter.mp h).2

/-- Says: a table's `rows` holds only `tr` elements. -/
theorem tableRows_tr (d : Dom) (t r : NodeId) (h : r ∈ tableRows d t) : isHtml d r ["tr"] = true := by
  unfold tableRows at h
  simp only [List.mem_append, List.mem_flatMap] at h
  rcases h with (⟨s, _, hs⟩ | ⟨c, _, hc⟩) | ⟨s, _, hs⟩
  · exact rowChildren_tr d s r hs
  · split at hc
    · rename_i htr; simp at hc; subst hc; exact htr
    · split at hc
      · exact rowChildren_tr d c r hc
      · simp at hc
  · exact rowChildren_tr d s r hs

/-- Says: a row's `cells` holds only `td` and `th` elements. -/
theorem cells_cell (d : Dom) (r c : NodeId) (h : c ∈ cells d r) : isHtml d c ["td", "th"] = true := by
  unfold cells at h
  exact (List.mem_filter.mp h).2

/-- Says: an index found in a list is below its length. -/
theorem indexIn_lt (xs : List NodeId) (k i : NodeId) (h : indexIn xs k = some i) : i < xs.length := by
  unfold indexIn at h
  exact List.findIdx?_eq_some_iff_findIdx_eq.mp h |>.1

/-- Says: what a delete removes is an item of the list. -/
theorem deletePos_lt (n : Nat) (i : Int) (j : Nat) (h : deletePos n i = .ok (some j)) : j < n := by
  unfold deletePos at h
  by_cases h1 : (i == -1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (n == 0) = true
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h; cases h; simp at h2; omega
  · rw [if_neg h1] at h
    by_cases h2 : (decide (i < 0) || decide (i ≥ (n : Int))) = true
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h; cases h
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt, Int.not_le] at h2
      omega

/-! ## Tests (html/semantics/tabular-data) -/

private def d0 : Dom := DOM.parseHtmlDocument ("<table id=t><caption>c</caption><tfoot><tr id=f><td>f</td></tr></tfoot>" ++
  "<tbody><tr id=a><td>a</td><th>b</th></tr></tbody><thead><tr id=h><td>h</td></tr></thead><tbody><tr id=x><td>x</td></tr></tbody></table>")
private def byId (s : String) : NodeId :=
  ((List.range d0.size).find? fun i => (d0.get i).attrs.any fun a => a.lname == "id" && a.value == s).getD 0

#guard tableRows d0 (byId "t") == [byId "h", byId "a", byId "x", byId "f"]
#guard rowIndex d0 (byId "f") == 3 && rowIndex d0 (byId "h") == 0 && rowIndex d0 (byId "x") == 2
#guard sectionRowIndex d0 (byId "x") == 0 && sectionRowIndex d0 (byId "a") == 0
#guard (cells d0 (byId "a")).map (cellIndex d0) == [0, 1]
#guard insertRowAt d0 (byId "t") 5 == "E" && insertRowAt d0 (byId "t") (-2) == "E"
#guard insertRowAt d0 (byId "t") (-1) == s!"A {(d0.get (byId "x")).parent.getD 0}"
#guard insertRowAt d0 (byId "t") 0 == s!"I {(d0.get (byId "h")).parent.getD 0} {byId "h"}"
#guard deleteAt 0 (-1) == "" && deleteAt 3 (-1) == "2" && deleteAt 3 3 == "E" && deleteAt 3 (-2) == "E" && deleteAt 3 1 == "1"
#guard answer d0 (byId "t") "C" != "" && answer d0 (byId "t") "b" == s!"{(d0.get (byId "a")).parent.getD 0} {(d0.get (byId "x")).parent.getD 0}"
#guard answer d0 (byId "a") "e\x003" == "E" && answer d0 (byId "a") "e\x002" == ""

end L4Factoidal.HTML.TableDom
